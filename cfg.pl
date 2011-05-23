#!/usr/bin/perl

use strict;
use warnings;

my $img_base = 0x8048000;

sub compact_ranges(@) {
    my @values = @_;
    my @items;
    for (my $iv = 0; $iv <= $#values; $iv++) {
        my $v = $values[$iv];
        my $ev = $v;
        while ($iv < $#values && $values[$iv+1] == $ev+1) {
            $ev++; $iv++;
        }
        push @items, ($ev>$v ? "$v-$ev" : $v);
    }
    return @items;
}

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

my %stack_names = (
  0 => 'parm0', 4 => 'parm1',
  8 => 'parm2', 12 => 'parm3',
  16 => 'parm4', 20 => 'parm5'
);
my %stack_name_cache;

sub stack_to_name($) {
    return lookup_name %stack_names, %stack_name_cache, $_[0], 4, sub { "{$_[0]}" }, "[esp+$_[0]]";
}

sub add_names($) {
    my ($str) = @_;
    $str =~ s/\[esp\]/stack_to_name('0x0')/ge;
    $str =~ s/\[esp\s*\+\s*(0x[0-9a-f]+)\]/stack_to_name($1)/ge;
    $str =~ s/((?:0x)?[0-9a-f]+)/addr_to_name($1)/ge;
    return $str;
}

sub replace_code_patterns($) {
  my ($name) = @_;
  $name =~ s/
    mov\s+(e[a-z]x),(e[a-z]x)\\l
    sar\s+\1,0x1f\\l
    shr\s+\1,0x1c\\l
    add\s+\2,\1\\l
    and\s+\2,0xf\\l
    sub\s+\2,\1\\l
  /$2 <- $2 % 16; $1 = sgn $2 & 15;\\l/gx;
  return $name;
}

my $addr = hex $ARGV[0] or die "Address expected";

my $rstart;
my $rend;

open F, 'Dwarf_Fortress.func_ranges' or die "Can't read funcs";
while (<F>) {
    next unless /^([0-9a-f]+)\s+([0-9a-f]+)\s+(\S.*\S|\S)?\s*$/;
    my ($start, $end, $name) = (hex $1, hex $2, $3);
    $func_names{$start} ||= $name;
    if ($addr >= $start && $addr <= $end) {
        $rstart = $start;
        $rend = $end;
    }
}
close F;

$rstart or die "Could not find function\n";

my $sname = sprintf("func-%x", $rstart);

load_names %stack_names, "$sname.stack";

my $asmcmd = "objdump --disassemble -M intel-mnemonic --no-show-raw-insn --start-address=$rstart --stop-address=$rend Dwarf_Fortress |";
#print $asmcmd, "\n";
open D, $asmcmd
    or die "Could not disassemble";

my @disass;
my %addr_idx;

while (<D>) {
    next unless /^\s*([0-9a-f]+)\s*:\s*(\S.*?\S)(?:\s*<([^>]+)>)?\s*$/;
    my ($pc, $insn, $aux) = (hex $1, lc $2, $3);
    my $nop = 0;
    $nop = 1 if $insn eq 'nop';
    $nop = 1 if $insn =~ /^lea\s+([a-z]+),\[([a-z]+)(?:\+eiz\*1)?\+0x0\]$/ && $1 eq $2;
    $nop = 1 if $insn =~ /^(?:xchg|mov)\s+([a-z]+),([a-z]+)$/ && $1 eq $2;
    my $entry = { idx => 1+$#disass, pc => $pc, insn => $insn, aux => $aux, nop => $nop };
    push @disass, $entry;
    $addr_idx{$pc} = $entry;
}
close D;

my %next;
my %prev;

open IMG, '<:raw', 'Dwarf_Fortress' or die "Can't open the executable";

my $dsize = $#disass;

my @switch_jmps;

for my $entry (@disass) {
    my $pc = $entry->{pc};
    local $_ = $entry->{insn};
    if ($_ eq 'ret') {
        $entry->{stop} = 1;
    } elsif (/^jmp\s+([0-9a-f]+)$/) {
        my $tgt = hex $1;
        $entry->{stop} = 1;
        if ($addr_idx{$tgt}) {
            $next{$pc}{$tgt} = '';
            $prev{$tgt}{$pc} = '';
        } else {
            print STDERR "Unknown target $1 at $pc\n";
        }
    } elsif (/^j(n?[ablgse]e?)\s+([0-9a-f]+)$/) {
        my $tgt = hex $2;
        if ($addr_idx{$tgt}) {
            $next{$pc}{$tgt} = $1;
            $prev{$tgt}{$pc} = $1;
        } else {
            print STDERR "Unknown target $2 at $pc\n";
        }
    } elsif (/^jmp\s+dword\s+ptr\s+\[([a-z]+)\*4\+0x([0-9a-f]+)\]$/) {
        my ($reg, $base) = ($1, hex $2);
        $entry->{stop} = 1;
        push @switch_jmps, [ $entry, $reg, $base ];
    } elsif (/^j/) {
        print STDERR "Unrecognized jump: '$_'\n";
    }
}

sub find_switch_range($$) {
    my ($entry, $reg) = @_;
    
    my $pentry = $disass[$entry->{idx}-1];
    
    # Walk jumps
    for (;;) {
        my @injmp = %{$prev{$entry->{pc}}||{}};
        if (@injmp >= 2 && $injmp[1] eq '') {
            $entry = $addr_idx{$injmp[0]};
        } elsif (@injmp >= 2 && $injmp[1] eq 'be') {
            $pentry = $addr_idx{$injmp[0]};
            last;
        } elsif ($pentry->{insn} =~ /^mov\s+(\S+),(\S.*\S)$/ && $1 eq $reg) {
            $reg = $2;
            $entry = $pentry;
        } elsif ($pentry->{nop}) {
            $entry = $pentry;
        } else {
            last;
        }
        $pentry = $disass[$entry->{idx}-1];
    }
    
    return undef unless $pentry->{insn} =~ /^j(a|be)\s/;
    
    my $centry = $disass[$pentry->{idx}-1];
    return undef unless $centry->{insn} =~ /^cmp\s+(\S.*\S)\s*,\s*0x([0-9a-f]+)$/;
    return undef unless $1 eq $reg;
    return hex $2;
}

for my $rjmp (@switch_jmps) {
    my ($entry, $reg, $base) = @$rjmp;
    my $pc = $entry->{pc};
    
    my $range = find_switch_range($entry, $reg);
    my $bound = $range;
    unless (defined $range) {
        printf STDERR "Could not parse range check for jmp at %08x\n", $pc;
        $bound = 1000000;
    }
    
    # Read the jump table from the executable
    my $offset = $base - $img_base;
    seek(IMG, $offset, 0) or die "Can't seek to $offset";
    my %idxset;
    for (my $id = 0; $id <= $bound; $id++) {
        my $buf;
        read(IMG, $buf, 4) == 4 or last;
        my $tgt = unpack 'L', $buf;
        if ($addr_idx{$tgt}) {
            push @{$idxset{$tgt}}, $id;
        } else {
            # Guess the end by invalid target address
            printf STDERR "Clipping jmp range at %08x by invalid target %08x (%d)\n", $pc, $tgt, $id;
            last;
        }
    }
    for my $tgt (keys %idxset) {
        my $ids = join ',',compact_ranges(@{$idxset{$tgt}});
        $next{$pc}{$tgt} = $ids;
        $prev{$tgt}{$pc} = $ids;
    }
}

open O, ">$sname.dot";

printf O "digraph \"%s\" {\n", addr_to_name(sprintf('%x',$rstart));
printf O "node [fontname=\"serif\" fontsize=8];\n";
printf O "edge [fontname=\"serif\" fontsize=8];\n";

my $cnt = 0;

for (my $i = 0; $i <= $dsize; $i++) {
    my $entry = $disass[$i];
    my $name = sprintf("<%x>\\n", $entry->{pc});
    my $opts = '';
    my $last_nop = 0;
    
    my $cent = $entry;
    for (;;) {
        if ($cent->{nop}) {
            $name .= "NOP\\l" unless $last_nop;
            $last_nop = 1;
        } else {
            $last_nop = 0;
            $name .= add_names($cent->{insn}) . "\\l";
        }
        
        last if $cent->{stop};
        last if $next{$cent->{pc}};
        last if $i >= $dsize;
        
        my $nxent = $disass[$i+1];
        last if $prev{$nxent->{pc}};
        # Suppress jump to self to reduce confusion
        last if $next{$nxent->{pc}} && exists $next{$nxent->{pc}}{$entry->{pc}};
        
        $cent = $nxent;
        $i++;
    }

    $name = replace_code_patterns($name);

    $cnt++;
    printf O "n%x [label=\"%s\" shape=box%s];\n", $entry->{pc}, $name, $opts;
    printf O "n%x -> n%x;\n", $entry->{pc}, $disass[$i+1]{pc}
        unless $cent->{stop} || $i >= $dsize;
    
    if (my $ntbl = $next{$cent->{pc}}) {
        for my $ntgt (keys %$ntbl) {
            if (length $ntbl->{$ntgt}) {
                printf O "n%x -> n%x [label=\"%s\" style=bold];\n", $entry->{pc}, $ntgt, $ntbl->{$ntgt};
            } else {
                printf O "n%x -> n%x;\n", $entry->{pc}, $ntgt;
            }
        }
    }
}

printf STDERR "%d basic blocks.\n", $cnt;

printf O "}\n";
close O;

printf STDERR "Wrote $sname.dot\nRunning dot...\n";
system "dot -Tsvg -o$sname.svg $sname.dot";
