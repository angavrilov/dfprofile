#!/usr/bin/perl

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

sub concat_delta($$) {
    my ($name, $delta) = @_;
    $name .= sprintf('+0x%x', $delta) if $name && $delta;
    return $name;
}

sub lookup_name($$;$) {
    my ($rhash, $addr, $limit) = @_;
    
    my $base = find_base($rhash, $addr);
    return undef unless defined $base;
    my $delta = $addr - $base;
    return undef if defined $limit && $delta >= $limit;
    my $name = $rhash->{$base};
    return wantarray ? $name : ($name, $delta);
}

sub load_names(\%$) {
    my ($rhash, $fname) = @_;
    
    if (open N, $fname) {
        while (<N>) {
            next unless /^([0-9a-f]+)\s+(\S+)/;
            $rhash->{hex $1} = $2;
        }
        close N;
    }
}

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

my %func_names;
my %func_ends;

load_names %func_names, 'Dwarf_Fortress.func_names';

open F, 'Dwarf_Fortress.func_ranges' or die "Can't read funcs";
while (<F>) {
    next unless /^([0-9a-f]+)\s+([0-9a-f]+)(?:\s+(\S|\S.*\S))?\s*$/;
    my ($start, $end, $name) = (hex $1, hex $2, $3);
    $func_ends{$start} = $end;
    $func_names{$start} ||= ($name || $1);
}
close F;

my %callers;
my %callees;
my %call_spots;

open C, 'Dwarf_Fortress.call_list' or die "Can't read calls";
while (<C>) {
    next unless /^([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)/;
    push @{$call_spots{hex $1}{hex $2}}, hex $3;
}
close C;

for my $caller (keys %call_spots) {
    for my $callee (keys %{$call_spots{$caller}}) {
        push @{$callers{$callee}}, $caller;
        push @{$callees{$caller}}, $callee;
    }
}

my %data;
my $div2 = 0x4000;

sub get_data(\%$;$) {
    my ($rdata, $addr, $name) = @_;

    return $rdata->{$addr} if $rdata->{$addr};

    my $tag;
    if ($name) {
        $tag = $addr;
    } else {
        $tag = sprintf('%x', $addr);
        $name = simplify_name($func_names{$addr} || "?$tag?");
    }

    return $rdata->{$addr} = {
        base => $addr, tag => $tag, name => $name,
        cnt => 0, perc => 0, cur_perc => 0, min_cnt => 0, chunks => {}
    };
}

open IN, $ARGV[0] or die "Can't open $ARGV[0]";

while (<IN>) {
    last if /vdso/;
    /^\s*(\S+)\s+(\S+)\s+(\S+)\s*$/ or next;
    my ($addr, $cnt, $p) = (hex $1, $2, $3);

    $addr += $img_base;

    my $base = find_base(\%func_names, $addr);
    my $bend = $base ? $func_ends{$base} : undef;

    unless ($base && (!$bend || $bend > $addr)) {
        $base = $addr & ~($div2-1);
        $base = $bend if $bend && $bend > $base;
    }

    my $rdata = get_data(%data, $base);

    $rdata->{cnt} += $cnt;
    $rdata->{perc} += $p;
    $rdata->{min_cnt} ||= $cnt;

    my $rchunks = $rdata->{chunks};
    my $xaddr = $addr & ~0xF;
    $rchunks->{$xaddr} ||= { cnt => 0, perc => 0 };
    $rchunks->{$xaddr}{cnt} += $cnt;
    $rchunks->{$xaddr}{perc} += $p;
}

my @queue;

# Walk to callers
my %has_callees;
$has_callees{$_} = 1 for keys %data;

@queue = keys %data;
while (@queue) {
    my $item = pop @queue;
    for my $parent (@{$callers{$item}||[]}) {
        next if $has_callees{$parent};
        $has_callees{$parent} = 1;
        push @queue, $parent;
    }
}

# Propagate weight to callees
my %parent_weight;
my %parent_weight_actual;

sub push_weight($$$$) {
    my ($rwalked, $addr, $parent, $weight) = @_;

    return if $rwalked->{$addr};
    $rwalked->{$addr} = 1;

    $parent_weight{$addr}{$parent} += $weight;
    return if $data{$addr};

    my @children;
    for my $child (@{$callees{$addr}||[]}) {
        next if !$has_callees{$child} || $rwalked->{$child};
        push @children, $child;
    }

    if (@children) {
        my $split = $weight / @children;
        return if $split < 1e-5;
        for my $child (@children) {
            &push_weight($rwalked, $child, $addr, $split);
        }
    }
}

for my $key (keys %data) {
    my $rdata = $data{$key};
    my $rchunks = $rdata->{chunks};
    for my $child (@{$callees{$key}||[]}) {
        my %spots;
        for my $spot (@{$call_spots{$key}{$child}}) {
            $spots{$spot & ~0xF}++;
            $spots{($spot + 5) & ~0xF}++;
        }
        my $cweight = 0;
        for my $xspot (keys %spots) {
            $cweight += $rchunks->{$xspot}{cnt} if $rchunks->{$xspot};
        }
        $cweight ||= $rdata->{min_cnt};
        my %walked;
        $parent_weight_actual{$child}{$key} += $cweight;
        push_weight(\%walked, $child, $key, $cweight);
    }    
}

# Propagate cumulative to callers
my %cum_path;

sub push_cumulative($$$) {
    my ($rwalked, $addr, $weight) = @_;

    return if $weight < 1e-5;
    $rwalked->{$addr} = 1;

    my $rdata = get_data(%data, $addr);
    $rdata->{cum_perc} += $weight;

    my $wmap = $parent_weight_actual{$addr};
    my @callers = grep { $wmap->{$_} > 1e-3 && !$rwalked->{$_}; } @{$callers{$addr}||[]};

    unless (@callers) {
        $wmap = $parent_weight{$addr};
        @callers = grep { $wmap->{$_} > 1e-3 && !$rwalked->{$_}; } @{$callers{$addr}||[]};
    }

    my $sum = 0;
    for my $parent (@callers) {
        $sum += $wmap->{$parent};
    }
    for my $parent (@callers) {
        my $split = $weight * $wmap->{$parent} / $sum;
        $cum_path{$addr}{$parent} += $split;
        push_cumulative($rwalked, $parent, $split);
    }

    $rwalked->{$addr} = 0;
}

for my $key (keys %data) {
    my %walked;
    push_cumulative(\%walked, $key, $data{$key}{perc});
}

my %visible;

# Instantiate self in cutoff
my $cutoff = $ARGV[1] || 1.0;
for my $key (keys %data) {
    $visible{$key} = $data{$key} if ($data{$key}{cum_perc} >= $cutoff);
}

# Instantiate callers
@queue = keys %visible;
while (@queue) {
    my $item = pop @queue;
    my @scallers = @{$callers{$item}||[]};
    my @callers;
    for my $caller (sort { ($data{$b}{cum_perc}||0) <=> ($data{$a}{cum_perc}||0) } @scallers) {
        last if ($data{$caller}{cum_perc}||0) < 1e-2;
        push @callers, $caller;
    }
    if (@callers == 0) {
        @callers = sort { ($parent_weight{$item}{$b}||0) <=> ($parent_weight{$item}{$a}||0) } @scallers;
    }
    if (@callers > 3) {
        @callers = @callers[0..2];
    }
    for my $caller (@callers) {
        next if $visible{$caller};
        $visible{$caller} = get_data(%data, $caller);
        push @queue, $caller;
    }
}

# Add globs for classes
my %globs;
for my $raddr (keys %data) {
    next if $visible{$raddr};
    my $rdata = $data{$raddr};
    if ($rdata->{name} =~ /^([_0-9a-z]+)::/i) {
        my $tgt = get_data(%globs, 'glob_class_'.$1, $1.'::*');
        $tgt->{cnt} += $rdata->{cnt};
        $tgt->{perc} += $rdata->{perc};
        $tgt->{cum_perc} += $rdata->{cum_perc};
    }
    if ($rdata->{name} =~ /::([_0-9a-z]+)$/i) {
        my $tgt = get_data(%globs, 'glob_fun_'.$1, '*::'.$1);
        $tgt->{cnt} += $rdata->{cnt};
        $tgt->{perc} += $rdata->{perc};
        $tgt->{cum_perc} += $rdata->{cum_perc};
    }
}
for my $key (keys %globs) {
    $visible{$key} = $globs{$key} if ($globs{$key}{perc} >= $cutoff);
}

# Compute total visible
my $total = 0;
for my $raddr (keys %visible) {
  $total += $data{$raddr}{perc};
}

open OUT, ">$ARGV[0].dot" or die "Can't open output";

printf OUT "digraph \"calls (%.1f%% shown)\" {\n", $total;

for my $key (keys %visible) {
    my $rdata = $visible{$key};
    my $opts = '';
    my @callers = @{$callers{$key}||[]};
    for my $caller (@callers) {
        next if $visible{$caller};
        $opts .= ' style=bold';
        last;
    }
    if ($rdata->{perc} >= 10) {
        $opts .= ' color=red';
    } elsif ($rdata->{perc} >= 1) {
        $opts .= ' color=blue';
    }
    my $cnt = '';
    if ($rdata->{cum_perc} > 0) {
        $cnt = sprintf("\\n%d %.2f%%",$rdata->{cnt}, $rdata->{perc});
        $cnt .= sprintf(" (%.2f%%)", $rdata->{cum_perc}) if $rdata->{cum_perc} > $rdata->{perc};
    }
    printf OUT "x%s [label=\"%s%s\"%s];\n", $rdata->{tag}, $rdata->{name}, $cnt, $opts;
    for my $caller (@callers) {
        next unless $visible{$caller};
        my $opts = '';
        if ($cum_path{$key}{$caller} > 2) {
            $opts .= ' style=bold';
        } elsif ($cum_path{$key}{$caller} < 0.1) {
            $opts .= ' style=dotted';
        } elsif ($cum_path{$key}{$caller} < 0.5) {
            $opts .= ' style=dashed';
        }
        printf OUT "x%x -> x%s%s;\n", $caller, $rdata->{tag}, ($opts ? " [$opts]" : '');
    }
}

print OUT "}\n";
close OUT;

open OUT, ">$ARGV[0].txt" or die "Can't open output";

my $i = 1;
my $ts2 = 0;
my $tp2 = 0;

print OUT "#fn|  address |  events  |% events|cum.events|cum.%evs| function name\n";

for my $raddr (sort { $data{$b}{cnt} <=> $data{$a}{cnt} } keys %data) {
    my $rdata = $data{$raddr};
    my $saddr = sprintf('0x%08x',$raddr);
    my $name = $rdata->{name};
    $ts2 += $rdata->{cnt};
    $tp2 += $rdata->{perc};
    $name = '  '.$name if $name;
    printf OUT "%3d %s %10d %8.4f %10d %8.4f%s\n", $i++, $saddr, $rdata->{cnt}, $rdata->{perc}, $ts2, $tp2, $name;

    my $ts = 0;
    my $tp = 0;

    my $rchunks = $rdata->{chunks};
    for my $xaddr (sort { $rchunks->{$b}{cnt} <=> $rchunks->{$a}{cnt} } keys %$rchunks) {
        last if ($rchunks->{$xaddr}{perc} < 0.1);
        $ts += $rchunks->{$xaddr}{cnt};
        $tp += $rchunks->{$xaddr}{perc};
        my $sxaddr = sprintf('0x%08x',$xaddr);
        my ($xname, $delta) = lookup_name \%func_names, $xaddr;
        $xname = simplify_name($xname) if $xname;
        my $iname = ($xname && $xname ne $rdata->{name} ? '  '.concat_delta($xname, $delta) : '');
        printf OUT "    %s %10d %8.4f %10d %8.4f%s\n", $sxaddr,
                   $rchunks->{$xaddr}{cnt}, $rchunks->{$xaddr}{perc}, $ts, $tp, $iname;
    }
}

close OUT;

print STDERR "Running dot...\n";
system "dot -Tsvg -o $ARGV[0].svg $ARGV[0].dot";
system "firefox ./$ARGV[0].svg";
