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

my %calls;

open C, 'Dwarf_Fortress.call_info' or die "Can't read calls";
while (<C>) {
    next unless /^([0-9a-f]+)\s+([0-9a-f]+)/;
    push @{$calls{hex $2}}, hex $1;
}
close C;

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
        cnt => 0, perc => 0, chunks => {}
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

    my $rchunks = $rdata->{chunks};
    my $xaddr = $addr & ~0xF;
    $rchunks->{$xaddr} ||= { cnt => 0, perc => 0 };
    $rchunks->{$xaddr}{cnt} += $cnt;
    $rchunks->{$xaddr}{perc} += $p;
}

my %visible;
my $cutoff = $ARGV[1] || 1.0;

# Instantiate self in cutoff
for my $key (keys %data) {
    $visible{$key} = $data{$key} if ($data{$key}{perc} >= $cutoff);
}

# Instantiate callers
my @queue = keys %visible;
while (@queue) {
    my $item = pop @queue;
    my @scallers = @{$calls{$item}||[]};
    my @callers;
    for my $caller (sort { ($data{$b}{cnt}||0) <=> ($data{$a}{cnt}||0) } @scallers) {
        last if ($data{$caller}{cnt}||0) == 0;
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
    }
    if ($rdata->{name} =~ /::([_0-9a-z]+)$/i) {
        my $tgt = get_data(%globs, 'glob_fun_'.$1, '*::'.$1);
        $tgt->{cnt} += $rdata->{cnt};
        $tgt->{perc} += $rdata->{perc};
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
    my @callers = @{$calls{$key}||[]};
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
    my $cnt = ($rdata->{cnt} > 0 ? sprintf("\\n%d %.2f%%",$rdata->{cnt}, $rdata->{perc}) : '');
    printf OUT "x%s [label=\"%s%s\"%s];\n", $rdata->{tag}, $rdata->{name}, $cnt, $opts;
    for my $caller (@callers) {
        next unless $visible{$caller};
        printf OUT "x%x -> x%s;\n", $caller, $rdata->{tag};
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
