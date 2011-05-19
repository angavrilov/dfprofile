#!/usr/bin/perl

use strict;
use warnings;

my $df_name = $ARGV[0] || 'Dwarf_Fortress';

my @ranges;
my %known;

open FS, "objdump --dwarf $df_name |";
while (<FS>) {
    next unless /pc=([0-9a-f]+)\.\.([0-9a-f]+)/;
    my $item = [hex $1, hex $2];
    $item->[0] or die "foo";
    push @ranges, $item;
    $known{$item->[0]} = $item;
}
close FS;

print STDERR scalar(@ranges), "\n";

my %call_targets;
my @calls;

open CS, "objdump --disassemble --demangle --no-show-raw-insn $df_name |";
while (<CS>) {
    next unless /^\s*([0-9a-f]+):\s+call\s+([0-9a-f]+)(?:\s*<(.+)>)?/;
    my ($pc, $tgt, $info) = (hex $1, hex $2, $3);
    $info = undef if $info && $info =~ /\+0x/;
    push @calls, [ $pc, $tgt, $info ];
    $call_targets{$tgt} ||= ($info||'');
}
close CS;

for my $addr (keys %call_targets) {
    unless ($known{$addr}) {
        my $item = [$addr, undef];
        $item->[0] or die "foo";
        push @ranges, $item;
        $known{$item->[0]} = $item;
    }
}

print STDERR scalar(@ranges), "\n";

open DFR, '>', 'Dwarf_Fortress.func_ranges';

my %funcs;
my %faddrs;

my $pos = 0;
my @nodes = sort { $a->[0] <=> $b->[0] } @ranges;
my $cnt = scalar(@nodes);
print STDERR $cnt, "\n";

for (my $n = 0; $n < $cnt; $n++) {
    my $range = $nodes[$n];
    my $start = $range->[0];
    my $end = $range->[1];
    #print "$n $start ",($end||''),"\n";
    $end = ($nodes[$n+1][0]||0) - 1 unless defined $end;

    next unless $start >= $pos && $end && $end >= $start;
    
    my $name = $call_targets{$start}||'';
    printf DFR "%x %x %s\n", $start, $end, $name;
    
    $funcs{$start} = { -start => $start, -end => $end, -called => 0 };
    for (my $i = ($start&~0xF); $i <= $end; $i += 16) {
        $faddrs{$i} = $start;
    }

    $pos = $end;
}

close DFR;

for my $cinfo (@calls) {
    my ($pc, $tgt, $info) = @$cinfo;
    
    my $cfstart = $faddrs{$pc&~0xF} or next;
    my $cfunc = $funcs{$cfstart} or next;
    my $tfunc = $funcs{$tgt} or next;
    
    $cfunc->{-calls}{$tgt}++;
    $tfunc->{-called}++ if $cfunc->{-calls}{$tgt} == 1;
}

my $num_funcs = keys %funcs;
printf STDERR "%d functions\n", $num_funcs;

open CFR, '>', 'Dwarf_Fortress.call_info';

for my $faddr (keys %funcs) {
    my $info = $funcs{$faddr};
    for my $tgt (keys %{$info->{-calls}||{}}) {
        printf CFR "%x %x %d\n", $faddr, $tgt, $info->{-calls}{$tgt};
    }
}


