#!/usr/bin/perl

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

sub addr_to_name($;$) {
    return lookup_name %func_names, %name_cache, $_[0], 16, \&simplify_name, ($_[1]||$_[0]);
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


my %funcs1;

open IN1, $ARGV[0] or die "Can't open $ARGV[0]";
while (<IN1>) {
   next unless /^\s*(\d+)\s+0x([0-9a-f]+)\s+\S+\s+(\S+)\s/;
   $funcs1{hex $2} = $3;
}
close IN1;

my %funcs2;

open IN2, $ARGV[1] or die "Can't open $ARGV[1]";
while (<IN2>) {
   next unless /^\s*(\d+)\s+0x([0-9a-f]+)\s+\S+\s+(\S+)\s/;
   $funcs2{hex $2} = $3;
}
close IN2;

my %funcs = %funcs1;
$funcs{$_} = 1 for keys %funcs2;

my $cutoff = $ARGV[2]||0.1;

for my $func (sort { abs(($funcs2{$b}||0)-($funcs1{$b}||0)) <=> abs(($funcs2{$a}||0)-($funcs1{$a}||0)) } keys %funcs) {
    my $diff = ($funcs2{$func}||0)-($funcs1{$func}||0);
    last if abs($diff) < $cutoff;
    my $saddr = sprintf('0x%08x',$func);
    printf "%s: %8.4f %8.4f %+8.4f %s\n", $saddr, ($funcs1{$func}||0), ($funcs2{$func}||0), $diff, addr_to_name($saddr,'?');
}
