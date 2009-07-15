$numargs = $#ARGV + 1;

($numargs == 2) || die "usage: filter.pl input-log output-log\n";

$input = $ARGV[0];
$output = $ARGV[1];

open(IN, "<$input") || die "can't open $input"; 
open(OUT, ">$output") || die "can't open $output";

my @array = ();

while (<IN>) {
    s/^\s*.:.*\\//;
    s/^Microsoft .*//;
    s/^for Microsoft \(R\) .NET.*//;
    s/^Copyright \(C\).*//;
    if ($_ !~ m/^\s*$/) 		# don't write out blank lines
    {
	push(@array, ($_));
    }
}

#
# if we want to compare only sorted output uncomment this
#@sorted = sort(@array);
@sorted = @array;


#  eliminate duplicates in the output 
$last = "";
foreach (@sorted)
{
    if ($_ ne $last) {
	print(OUT $_);
	$last = $_;
    }
}
