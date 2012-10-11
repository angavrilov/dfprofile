#!/usr/bin/perl

use strict;
use warnings;

my $img_base = 0x8048000;

sub find_base($$) {
    my ($table, $addr) = @_;

    my $svec = $table->{addrlist};
    unless (defined $svec) {
        $svec = $table->{addrlist} = [ sort { $a <=> $b } keys %$table ];
    }
    
    my $min = -1;
    my $max = $#$svec+1;

    for (;;) {
        use integer;
        my $mid = (($min+$max)>>1);
        last if $mid <= $min;
        my $val = $svec->[$mid];
        if ($val == $addr) {
            return $val;
        } elsif ($val < $addr) {
            $min = $mid;
        } else {
            $max = $mid;
        }
    }

    if ($min >= 0) {
        return $svec->[$min];
    } else {
        return undef;
    }
}

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

sub load_names(\%$;\%) {
    my ($rhash, $fname, $bitfields) = @_;
    
    if (open N, $fname) {
        while (<N>) {
            last if /^===/;
            next unless /^([0-9a-f]+)\s+(\S+)(?:\s+(\S+))?(?:\s+(\S+))?\s*$/;
            my ($addr, $name, $type, $offset) = ($1,$2,$3,$4);
            my $aval = hex $addr;

            $rhash->{$aval}{name} = $name;
            $rhash->{$aval}{type} = $type;

            if ($type && $type =~ /^(.*)\*$/) {
                $rhash->{$aval}{target} = $1;
                $rhash->{$aval}{target_offset} = hex $offset if $offset;
            } elsif ($type && $bitfields && $bitfields->{$type}) {
                $rhash->{$aval}{target} = '!BITS:'.$type;
            }
        }
        close N;
    }
}

sub load_bitfields(\%$) {
    my ($ihash, $fname) = @_;

    if (open N, $fname) {
        while (<N>) {
            next unless /^\"([^\"]*)\",\"(\d+)\",\"0x([0-9a-fA-F]+)(?:\.(\d))?\",\"[^\"]*\",\"([^\"]*)\",\"([^\"]*)\",\"([^\"]*)\"/;
            my ($top, $level, $addr, $bit, $type, $name, $target) = ($1,$2,$3,$4,$5,$6,$7);
            if ($level == 0 && $type eq 'bitfield-type') {
                $ihash->{$top} ||= {};
            } elsif ($level == 1 && $ihash->{$top}) {
                my $off = hex($addr)*8 + ($bit||0);
                $ihash->{$top}{$off} = { name => $name };
            }
        }
        close N;
    }
}

sub load_csv_names(\%$;$\%) {
    my ($ihash, $fname, $named, $bitfields) = @_;

    if (open N, $fname) {
        while (<N>) {
            next unless /^\"([^\"]*)\",\"(\d+)\",\"0x([0-9a-fA-F]+)(?:\.(\d))?\",\"[^\"]*\",\"([^\"]*)\",\"([^\"]*)\",\"([^\"]*)\"/;
            my ($top, $level, $addr, $bit, $type, $name, $target) = ($1,$2,$3,$4,$5,$6,$7);
            next if $named && $level == 0 && $top !~ /[:]anon\d+$/;
            next if $type =~ /^(flag-bit|bitfield-type)$/;
            next if $bitfields && $bitfields->{$top};
            next if $bit;
            my $rhash = $named ? ($ihash->{$top} ||= {}) : $ihash;
            my $aval = hex $addr;
            if ($type =~ /^(df-linked-list|static-array)$/) {
                $type = $target; $target = '';
            }
            unless ($rhash->{$aval}) {
                $type = $name if $type =~ /-type$/;
                $rhash->{$aval}{type} = $type;
            }
            $rhash->{$aval}{name} = $name;
            if ($target) {
                $target =~ s/\*$// if $type eq 'vmethod';
                #$target .= '*' if $type eq 'stl-vector';
                $rhash->{$aval}{target} = $target;
            } elsif ($bitfields && $bitfields->{$type}) {
                $rhash->{$aval}{target} = '!BITS:'.$type;
            }
        }
        close N;
    }
}

my %all_types;

sub lookup_name($$;$) {
    my ($rhash, $addr, $limit) = @_;
    
    my $base = find_base($rhash, $addr);
    return undef unless defined $base;

    my $delta = $addr-$base;
    my $info = $rhash->{$base};
    my $binfo = $info;
    my $name = $info->{name};

    while ($info->{type}) {
        my $thash = $all_types{$info->{type}} or last;
        my $dbase = find_base($thash, $delta);
        last unless defined $dbase;
        my $dinfo = $thash->{$dbase} or last;
        $binfo = $info unless $delta == 0;
        $delta = $delta - $dbase;
        $info = $dinfo;
        $name .= '.'.$info->{name};
    }

    return undef if defined $limit && $delta >= $limit;
    
    return ($delta, $name, $binfo->{type}, $info->{target}, $info->{target_offset});
}

sub concat_delta($$) {
    my ($name, $delta) = @_;
    $name .= sprintf('+0x%x', $delta) if $name && $delta;
    return $name;
}

my %func_names;
my %ptr_types;
my %bit_names;

load_bitfields %bit_names, 'all.csv';
load_csv_names %all_types, 'all.csv', 1, %bit_names;

load_names %func_names, 'Dwarf_Fortress.func_names', %bit_names;
load_csv_names %func_names, 'globals.csv', 0, %bit_names;

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

my %stack_names = (
  0 => { name => 'parm0' }, 4 => { name => 'parm1' },
  8 => { name => 'parm2' }, 12 => { name => 'parm3' },
  16 => { name => 'parm4' }, 20 => { name => 'parm5' }
);

sub stack_to_name($$;$) {
    my ($text, $addr, $entry) = @_;

    my $off = $addr ? hex($addr) : 0;

    my ($delta, $name, $type, $ptype, $poff) = lookup_name(\%stack_names, $off, 1 + ($off % 4));

    if ($name) {
        if ($entry && $entry->{out_reg}) {
            if ($entry->{is_lea}) {
                $entry->{ptr_type} = $type;
                $entry->{ptr_offset} = $delta;
            } elsif (!$delta) {
                $entry->{ptr_type} = $ptype;
                $entry->{ptr_offset} = $poff;
            } elsif ($ptype && $ptype =~ /^!BITS:/) {
                $entry->{ptr_type} = $ptype;
                $entry->{ptr_offset} = $delta*8;
            }
        }

        return '{'.concat_delta($name,$delta).'}';
    }

    return $text;
}

sub replace_code_patterns($) {
  my ($name) = @_;
  $name =~ s/
                mov\s+(e[a-z]x),(e[a-z]x)\\l
    [0-9a-f]+\s+sar\s+\1,0x1f\\l
    [0-9a-f]+\s+shr\s+\1,0x1c\\l
    [0-9a-f]+\s+add\s+\2,\1\\l
    [0-9a-f]+\s+and\s+\2,0xf\\l
    [0-9a-f]+\s+sub\s+\2,\1\\l
  /$2 <- $2 % 16; $1 = sgn $2 & 15;\\l/gx;
  return $name;
}

my %arg_flags;

while (@ARGV && $ARGV[0] =~ /^--(.*)$/) {
    $arg_flags{$1} = 1;
    shift @ARGV;
}

my $addr = hex $ARGV[0] or die "Address expected";

my $rstart;
my $rend;

open F, 'Dwarf_Fortress.func_ranges' or die "Can't read funcs";
while (<F>) {
    next unless /^([0-9a-f]+)\s+([0-9a-f]+)\s+(\S.*\S|\S)?\s*$/;
    my ($start, $end, $name) = (hex $1, hex $2, $3);
    $func_names{$start} ||= { name => simplify_name($name) } if $name;
    if ($addr >= $start && $addr <= $end) {
        $rstart = $start;
        $rend = $end;
    }
}
close F;

if ($ARGV[1]) {
    $rstart = $addr;
    $rend = hex $ARGV[1];
}

$rstart or die "Could not find function\n";

my $sname = sprintf("func-%x", $rstart);

load_names %stack_names, "$sname.stack";

#
# DISASSEMBLE CODE
#

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
    my $entry = {
        idx => 1+$#disass, pc => $pc, aux => $aux,
        nop => $nop, defs => {}, live => {},
    };

    my ($explicit_target,$explicit_offset);
    if ($stack_names{$pc}) {
        $explicit_target = $stack_names{$pc}{target};
        $explicit_offset = $stack_names{$pc}{target_offset};
    }

    if ($insn =~ /^call\s+/) {
        $entry->{out_reg} = 'eax';
        $entry->{defs}{eax} = 1;
        if ($insn =~ /^call\s+([0-9a-fA-F]+)$/) {
            my $faddr = hex $1;
            my ($delta, $name, $type, $ptype) = lookup_name(\%func_names, $faddr, 1);
            $insn = 'call '.concat_delta($name,$delta) if $name;
            $entry->{ptr_type} = $ptype;
        }
    } elsif ($insn =~ /^(\S+)\s+(e[a-z][a-z]),/) {
        my ($cmd, $reg) = ($1, $2);
        unless (!$explicit_target && $cmd =~ /^(cmp|test)$/) {
            $entry->{out_reg} = $reg;
            $entry->{is_lea} = lc($cmd) eq 'lea';
            $entry->{defs}{$reg} = 1;
            if ($insn =~ /^mov\s+[a-z]+,(e[a-z][a-z])$/) {
                $entry->{in_reg} = $1;
            } elsif ($insn =~ /^mov\s+[a-z]+,dword ptr (\[esp\+0x[0-9a-f]+\])$/) {
                $entry->{in_reg} = $1;
            }
        }
    } elsif ($insn =~ /^mov\s+dword ptr (\[esp\+0x[0-9a-f]+\]),(e[a-z][a-z])$/) {
        $entry->{out_reg} = $1;
        $entry->{defs}{$1} = 1;
        $entry->{in_reg} = $2;
        $entry->{is_lea} = 0;
    }

    if ($explicit_target) {
        $entry->{ptr_type} = $explicit_target;
        $entry->{ptr_offset} = $explicit_offset;
    }

    $insn =~ s/(\[esp(?:\+0x([0-9a-f]+))?\]),/stack_to_name($1,$2).','/ie;
    $insn =~ s/(\[esp(?:\+0x([0-9a-f]+))?\])$/stack_to_name($1,$2,$entry)/ie;

    $entry->{insn} = $insn;

    push @disass, $entry;
    $addr_idx{$pc} = $entry;
}
close D;

my %next;
my %prev;

open IMG, '<:raw', 'Dwarf_Fortress' or die "Can't open the executable";

#
# BUILD STATIC CFG
#

my $dsize = $#disass;

print "Building CFG from $dsize instructions.\n";

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

#
# BUILD SWITCH CFG
#

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

#
# BUILD CFG EDGES
#

for my $entry (@disass) {
    my $pc = $entry->{pc};

    my @outs;
    @outs = keys %{$next{$pc}} if $next{$pc};
    push @outs, $disass[$entry->{idx}+1]{pc}
        if $entry->{idx} < $dsize && !$entry->{stop};

    $entry->{all_ins} ||= [];
    $entry->{all_outs} = \@outs;
    $entry->{all_out_entries} = [ map { $addr_idx{$_}; } @outs ];

    for my $out (@outs) {
        push @{$addr_idx{$out}{all_ins}}, $pc;
        push @{$addr_idx{$out}{all_in_entries}}, $entry;
    }
}

sub get_all_ins($) {
    return @{$_[0]{all_ins}};
}

#
# BUILD REGISTER DATA FLOW
#

my @dfqueue;

sub propagate_data_flow {
    my ($entry, $reg, $def) = @_;

    for my $rout (@{$entry->{all_out_entries}}) {
        next if $rout->{live}{$reg}{$def};
        $rout->{live}{$reg}{$def} = 1;
        next if $rout->{defs}{$reg};
        push @dfqueue, [ $rout, $reg, $def ];
    }
}

my %data_flow_ready;

sub build_data_flow($) {
    my ($reg) = @_;

    return if $data_flow_ready{$reg};
    $data_flow_ready{$reg} = 1;

    for my $entry (@disass) {
        if ($entry->{defs}{$reg}) {
            propagate_data_flow($entry, $reg, $entry->{pc});
        }
    }

    while (@dfqueue) {
        my $info = shift @dfqueue;
        propagate_data_flow(@$info);
    }
}

for my $entry (@disass) {
    next unless $entry->{out_reg} && $entry->{ptr_type};
    build_data_flow($entry->{out_reg});
}

#
# DECODE POINTER DEREFERENCES
#

sub lookup_ptr_info($$) {
    my ($entry, $reg) = @_;

    return (undef, undef) unless $reg;

    my $live = $entry->{live}{$reg};
    for my $pc (keys %$live) {
        next unless $addr_idx{$pc}{ptr_type};
        return ($addr_idx{$pc}{ptr_type}, $addr_idx{$pc}{ptr_offset});
    }

    for my $pc (keys %$live) {
        next unless $addr_idx{$pc}{ptr_offset};
        return (undef, $addr_idx{$pc}{ptr_offset});
    }

    return (undef, undef);
}

sub decode_insn_addr($;$) {
    my ($entry, $lea) = @_;

    my $deref = 1;
    my $insn = $entry->{insn};
    my $reg;
    my $offset = 0;

    if ($insn =~ /,dword ptr (\[esp\+0x[0-9a-f]+\])/) {
        $deref = 0;
        $reg = $1;
    } elsif ($insn =~ /\[(e[a-z][a-z])(?:\+([a-z]+)\*([124]))?\]/) {
        $reg = $1;
        my ($r2, $mul) = ($2, $3);
        my ($rt2, $off2) = lookup_ptr_info($entry, $r2);
        $offset += $off2 * $mul if $off2;
    } elsif ($insn =~ /\[(e[a-z][a-z])(?:\+([a-z]+)\*([124]))?\+0x([0-9a-f]+)\]/) {
        $reg = $1;
        $offset = hex $4;
        my ($r2, $mul) = ($2, $3);
        my ($rt2, $off2) = lookup_ptr_info($entry, $r2);
        $offset += $off2 * $mul if $off2;
    } elsif ($insn =~ /ds:(?:0x)?([0-9a-f]+)/) {
        $offset = hex $1;
    } elsif ($insn =~ /,(e[a-z][a-z])$/) {
        $deref = 0;
        $reg = $1;
    } elsif ($insn =~/^(?:test|or|and)\s+([a-d])([hl]),/) {
        $deref = 0;
        $reg = 'e'.$1.'x';
        $offset = ($2 eq 'h' ? 8 : 0);
    } elsif ($insn =~/^(?:test|or|and)\s+(e[a-z][a-z]),/) {
        $deref = 0;
        $reg = $1;
    } elsif ($insn =~ /^add\s+(e[a-z][a-z]),0x([0-9a-f]+)$/) {
        $deref = 0;
        $reg = $1;
        $offset = hex $2;
    } elsif ($insn =~ /(?:0x)([0-9a-f]+)(?:$|,|\s)/) {
        $deref = 0;
        $offset = hex $1;
    } else {
        return undef
    }

    $deref = 0 if $lea;

    my ($delta, $name, $type, $ptype);

    my $pdelta = 0;
    my $orig_offset = $offset;

    if ($reg) {
        if ($reg eq 'esp') {
            ($delta, $name, $type, $ptype) = lookup_name(\%stack_names, $offset);
            ($type, $ptype) = (undef, undef) if $delta;
        } else {
            my ($ptr_type, $ptr_offset) = lookup_ptr_info($entry, $reg);

            $ptr_offset ||= 0;
            $offset += $ptr_offset;

            if ($ptr_type) {
                if ($ptr_type =~ /^(.*)\*$/) {
                    $delta = 0;
                    $pdelta = $offset;
                    $type = $ptr_type;
                    $ptype = $1;
                } elsif ($ptr_type =~ /^!BITS:(.*)$/ && !$deref) {
                    $name = $1;
                    $delta = $offset;
                    $type = $ptr_type;
                    $ptype = $ptr_type;
                } else {
                    my $tinfo = $all_types{$ptr_type} or return undef;

                    ($delta, $name, $type, $ptype) = lookup_name($tinfo, $offset);

                    $name = $ptr_type.'.'.$name if $name;

                    if ($offset == $ptr_offset || $type =~ /^(compound)$/) {
                        $type = $ptr_type;
                        $pdelta = $offset - $delta;
                    }
                }
            } else {
                ($delta, $name, $type, $ptype) = lookup_name(\%func_names, $offset, 64);
            }
        }
    } else {
        ($delta, $name, $type, $ptype) = lookup_name(\%func_names, $offset, 64);
    }

    return (undef, undef, undef, $deref ? 0 : $offset) unless defined $delta;

    if ($deref) {
        if ($ptype && $ptype =~ /^!BITS:/) {
            return ($name, $delta, $ptype, 8*$delta);
        } else {
            return ($name, $delta, ($delta == 0) ? $ptype : undef, 0);
        }
    } else {
        $name = undef unless $orig_offset;
        return ($name, $delta, $type, $pdelta + $delta);
    }
}

print "Computing pointers.\n";

my $ptr_changed = 1;

while ($ptr_changed) {
    $ptr_changed = 0;

    for my $entry (@disass) {
        my $pc = $entry->{pc};
        next unless $entry->{out_reg};
        next if $entry->{ptr_type};
        my $insn = $entry->{insn};
        next unless $insn =~ /^(?:(?:lea|mov|call|movzx)\s|add\s+e[a-z][a-z],0x)/;
        my ($name, $delta, $ptype, $poff);
        if ($entry->{in_reg}) {
            $delta = 0;
            ($ptype, $poff) = lookup_ptr_info($entry, $entry->{in_reg});
        } else {
            ($name, $delta, $ptype, $poff) = decode_insn_addr($entry, $insn =~ /^lea\s/);
        }
        my $changed = 0;
        if (defined $delta && $ptype) {
            $entry->{ptr_type} = $ptype;
            $entry->{ptr_offset} = $poff;
            $changed = 1;
        } elsif ($poff && !$entry->{ptr_offset}) {
            $entry->{ptr_offset} = $poff;
            $changed = 1;
        }
        if ($changed) {
            $ptr_changed = 1;
            build_data_flow($entry->{out_reg});
        }
    }
}

open O, ">$sname.dot";

my ($delta, $name) = lookup_name \%func_names, $rstart, 1;
my $func_name = ($name ? concat_delta($name,$delta) : sprintf('%x',$rstart));

print "Function $func_name\n";

printf O "digraph \"%s\" {\n", $func_name;
printf O "node [fontname=\"serif\" fontsize=8];\n";
printf O "edge [fontname=\"serif\" fontsize=8];\n";

my %str_cache;

sub check_string($) {
    my ($addr) = @_;
    
    return $str_cache{$addr} if exists $str_cache{$addr};
    
    my $offset = $addr - $img_base;
    seek(IMG, $offset, 0) or return $str_cache{$addr} = undef;
    
    my $str = '';
    my $bad = 0;
    
    for (my $cnt = 1;;$cnt++) {
        my $buf;
        read(IMG, $buf, 1) == 1
            or return $str_cache{$addr} = undef;
        last if (ord $buf == 0);

        if (($cnt%40)==0) {
            if (length($str)>200) {
                $str .= '...';
                last
            }
            $str .= "\n";
        }

        if (ord $buf < 0x20) {
            $bad++;
            $str .= sprintf("\\x%02x",ord($buf));
        } else {
            $str .= $buf;
        }
    }
    
    $str = undef if $bad > 5;
    return $str_cache{$addr} = $str;
}

sub add_string($) {
    my ($hex) = @_;
    my $str = check_string(hex $hex);
    if (defined $str && $str ne '') {
        $str =~ s/\\/\\\\/g;
        $str =~ s/\"/\\\"/g;
        $str =~ s/\n/'\\l'/g;
        return "0x$hex\\l'$str'";
    } else {
        return "0x$hex";
    }
}

my $cnt = 0;

sub format_bits($$$) {
    my ($bitfield, $poff, $bitval) = @_;

    my @names;

    for (my $i = 0; $i < 32; $i++) {
        my $bit = 1<<$i;
        last if $bit > $bitval;
        next unless ($bit & $bitval) != 0;
        my ($delta, $name, $type, $ptype) = lookup_name($bit_names{$bitfield}, $poff+$i, 32);
        push @names, ($name ? concat_delta($name, $delta) : 'bit'.($poff+$i));
    }

    return join(',', @names);
}

sub invert_bits($) {
    my ($val) = @_;
    return ($val^0xff) if ($val&~0xff) == 0;
    return ($val^0xffff) if ($val&~0xffff) == 0;
    return ($val^0xffffffff) if ($val&~0xffffffff) == 0;
    return ~$val;
}

for (my $i = 0; $i <= $dsize; $i++) {
    my $entry = $disass[$i];
    my $name = sprintf("<%x>\\n", $entry->{pc});
    my $opts = '';
    my $last_nop = 0;
    my $start_pc = $entry->{pc};

    if ($entry->{nop}) {
        my @ins = get_all_ins($entry);
        next unless @ins;
    }

    my $cent = $entry;
    for (;;) {
        my $apfix = sprintf("%02x   ", $cent->{pc} - $start_pc);

        if ($cent->{nop}) {
            $name .= $apfix."NOP\\l" unless $last_nop;
            $last_nop = 1;
        } else {
            $last_nop = 0;
            my $str = $cent->{insn};

            my ($pname, $delta, $ptype, $poff) = decode_insn_addr($cent);
            ($ptype||'') =~ /^!BITS:(\S+)$/;
            my $bitfield = $1;

            if ($pname) {
                $str .= "\\l          ; ".concat_delta($pname,$delta);
            } elsif ($ptype) {
                $str .= "\\l          ; --> ".concat_delta($ptype,$poff);
            }
            #$str .= "\\l          ; ? $ptype" if $ptype && !$pname;
            if ($bitfield && $cent->{insn} =~ /^(test|or|and)\s.*,0x([0-9a-f]+)$/) {
                my ($cmd,$val) = ($1, hex $2);
                my $bits = format_bits($bitfield, $poff, $val);
                my $rbits = format_bits($bitfield, $poff, invert_bits($val));
                $bits = '~'.$rbits if length($rbits) < length($bits);
                $str .= "\\l          ; ".$bits if $bits;
            }
            $name .= $apfix.$str."\\l";
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
    if ($name =~ /string/) {
        $name =~ s/0x([0-9a-f]+)/add_string($1)/ge;
    }

    $cnt++;
    printf O "n%x [label=\"%s\" shape=box%s];\n", $entry->{pc}, $name, $opts;
    printf O "n%x -> n%x;\n", $entry->{pc}, $disass[$i+1]{pc}
        unless $cent->{stop} || $i >= $dsize;

    if (my $ntbl = $next{$cent->{pc}}) {
        for my $ntgt (keys %$ntbl) {
            my $tgtname = sprintf('%x',$ntgt);

            my $tag = $ntbl->{$ntgt};
            if ($stack_names{$ntgt} && $stack_names{$ntgt}{name} ne 'retval:') {
                $tgtname .= 'a'.sprintf('%x',$entry->{pc});
                printf O "n%s [label=\"<%x>\\n%s\\l\" shape=box];\n", $tgtname, $ntgt, $stack_names{$ntgt}{name};
            }

            if (length $tag) {
                printf O "n%x -> n%s [label=\"%s\" style=bold];\n", $entry->{pc}, $tgtname, $tag;
            } else {
                printf O "n%x -> n%s;\n", $entry->{pc}, $tgtname;
            }
        }
    }
}

printf STDERR "%d basic blocks.\n", $cnt;

printf O "}\n";
close O;

my @gopts = ();
push @gopts, '-Gsplines=line' if $arg_flags{line};
push @gopts, '-Gsplines=polyline' if $arg_flags{polyline};
push @gopts, '-Gsplines=ortho' if $arg_flags{ortho};
push @gopts, '-Gnslimit=0.1', '-Gmclimit=0.1' if $arg_flags{turbo};


printf STDERR "Wrote $sname.dot\nRunning dot...\n";

my $fail = 0;
my $cpid = fork();
if ($cpid == 0) {
    exec("dot", "-Tsvg", "-Gcharset=latin1", @gopts, "-o$sname.svg.tmp", "$sname.dot");
} else {
    local $SIG{INT} = sub { $fail = 1; };
    waitpid $cpid, 0;
    $fail = 1 unless $? == 0;
}

if ($fail) {
    -f "$sname.svg" or die "Dot failed.\n";
    print "Opening the existing file.\n";
} else {
    rename "$sname.svg.tmp", "$sname.svg";
}

system "firefox ./$sname.svg";
system "./run-kwrite.sh Dwarf_Fortress.func_names";
system "./run-kwrite.sh $sname.stack";
