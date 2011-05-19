#!/usr/bin/perl

my $img_base = 0x8048000;

sub load_names(\%$) {
    my ($rhash, $fname) = @_;
    
    if (open N, $fname) {
        while (<N>) {
            next unless /^([0-9a-f]+)\s+(\S.*\S|\S)\s*$/;
            $rhash->{hex $1} = $2;
        }
        close N;
    }
}

sub lookup_name(\%\%$$$$) {
    my ($rhash, $rcache, $addr, $range, $filter, $default) = @_;
    
    return $rcache->{$addr} if exists $rcache->{$addr};
    my $av = $addr;
    $av =~ s/^0x//;
    $av = hex $av;
    for (my $i = 0; $i < $range; $i++) {
        my $name = $rhash->{$av - $i};
        next unless $name;
        $name = &{$filter}($name) if $filter;
        return $rcache->{$addr} = $name . ($i ? "+$i" : '');
    }
    return $rcache->{$addr} = $default;
}

my %func_names;
load_names %func_names, 'Dwarf_Fortress.func_names';

sub simplify_name($) {
    my ($name) = @_;
    # Collapse templates
    while ($name =~ s/<[^<>]*>//g) {}
    # Collapse parentheses
    while ($name =~ s/\([^\(\)]*\)//g) {}
    # Drop the classname
    #$name =~ s/^.*:://;
    return $name;
}

my %name_cache;

sub addr_to_name($) {
    return lookup_name %func_names, %name_cache, $_[0], 16, \&simplify_name, $_[0];
}

my @funcs;
my %fcache;

open F, 'Dwarf_Fortress.func_ranges' or die "Can't read funcs";
while (<F>) {
    next unless /^([0-9a-f]+)\s+([0-9a-f]+)(?:\s+(\S|\S.*\S))?\s*$/;
    my ($start, $end, $name) = (hex $1, hex $2, $3);
    for (my $i = ($start&~0xF); $i <= $end; $i+=16) {
        $fcache{$i} = $start;
    }
    $func_names{$start} ||= $name if $name;
}

my %calls;

open C, 'Dwarf_Fortress.call_info' or die "Can't read calls";
while (<C>) {
    next unless /^([0-9a-f]+)\s+([0-9a-f]+)/;
    push @{$calls{hex $2}}, hex $1;
}

my %data;
my $div2 = 0x4000;

open IN, $ARGV[0] or die "Can't open $ARGV[0]";

while (<IN>) {
   last if /vdso/;
   /^\s*(\S+)\s+(\S+)\s+(\S+)\s*$/ or next;
   my ($addr, $cnt, $p) = ($1, $2, $3);
   my $xaddr = $img_base + (hex($addr) & ~0xF);
   my $raddr = $fcache{$xaddr};
   $raddr = ($xaddr & ~($div2-1)) unless defined $raddr;
   my $rdata = ($data{$raddr} ||= [ 0, 0, {} ]);
   $rdata->[0] += $cnt;
   $rdata->[1] += $p;
   $rdata->[2]{$xaddr} ||= [ 0, 0 ];
   $rdata->[2]{$xaddr}[0] += $cnt;
   $rdata->[2]{$xaddr}[1] += $p;
}

my %visible;
my $cutoff = $ARGV[1] || 1.0;

for my $raddr (keys %data) {
    $visible{$raddr}++ if ($data{$raddr}[1] >= $cutoff);
}

my @queue = keys %visible;
while (@queue) {
    my $item = pop @queue;
    my @scallers = @{$calls{$item}||[]};
    my @callers;
    for my $caller (sort { ($data{$b}[0]||0) <=> ($data{$a}[0]||0) } @scallers) {
        last if ($data{$caller}[0]||0) == 0;
        push @callers, $caller;
    }
    if (@callers == 0) {
        @callers = @scallers;
    }
    if (@callers > 3) {
        @callers = @callers[0..2];
    }
    for my $caller (@callers) {
        next if $visible{$caller};
        $visible{$caller}++;
        $data{$caller} = [ 0, 0, {} ] unless $data{$caller};
        push @queue, $caller;
    }
}

my $total = 0;
for my $raddr (keys %visible) {
  $total += $data{$raddr}[1];
}

open OUT, ">$ARGV[0].dot" or die "Can't open output";

printf OUT "digraph \"calls (%.1f%% shown)\" {\n", $total;

for my $raddr (keys %visible) {
    my $rdata = $data{$raddr};
    my $opts = '';
    my @callers = @{$calls{$raddr}||[]};
    for my $caller (@callers) {
        next if $visible{$caller};
        $opts .= ' style=bold';
        last;
    }
    if ($rdata->[1] >= 10) {
        $opts .= ' color=red';
    } elsif ($rdata->[1] >= 1) {
        $opts .= ' color=blue';
    }
    my $saddr = sprintf('%x',$raddr);
    my $cnt = ($rdata->[0] > 0 ? sprintf("\\n%d %.2f%%",$rdata->[0], $rdata->[1]) : '');
    printf OUT "x%x [label=\"%s%s\"%s];\n", $raddr, addr_to_name($saddr), $cnt, $opts;
    for my $caller (@callers) {
        next unless $visible{$caller};
        printf OUT "x%x -> x%x;\n", $caller, $raddr;
    }
}

print OUT "}\n";
close OUT;

open OUT, ">$ARGV[0].txt" or die "Can't open output";

my $i = 1;
my $ts2 = 0;
my $tp2 = 0;

print OUT "#fn|  address |  events  |% events|cum.events|cum.%evs| function name\n";


for my $raddr (sort { $data{$b}[0] <=> $data{$a}[0] } keys %data) {
    my $rdata = $data{$raddr};
    my $saddr = sprintf('0x%08x',$raddr);
    my $name = addr_to_name($saddr);
    $name = ($name eq $saddr ? '' : '  '.$name);
    $ts2 += $rdata->[0];
    $tp2 += $rdata->[1];
    printf OUT "%3d %s %10d %8.4f %10d %8.4f%s\n", $i++, $saddr, $rdata->[0], $rdata->[1], $ts2, $tp2, $name;

    my $ts = 0;
    my $tp = 0;

    for my $xaddr (sort { $rdata->[2]{$b}[0] <=> $rdata->[2]{$a}[0] } keys %{$rdata->[2]}) {
        last if ($rdata->[2]{$xaddr}[1] < 0.1);
        $ts += $rdata->[2]{$xaddr}[0];
        $tp += $rdata->[2]{$xaddr}[1];
        my $sxaddr = sprintf('0x%08x',$xaddr);
        my $iname = addr_to_name($sxaddr);
        $iname = (($iname eq $sxaddr || ('  '.$iname) eq $name) ? '' : '  '.$iname);
        printf OUT "    %s %10d %8.4f %10d %8.4f%s\n", $sxaddr, $rdata->[2]{$xaddr}[0], $rdata->[2]{$xaddr}[1], $ts, $tp, $iname;
    }
}

close OUT;

print STDERR "Running dot...\n";
system "dot -Tsvg -o $ARGV[0].svg $ARGV[0].dot";



