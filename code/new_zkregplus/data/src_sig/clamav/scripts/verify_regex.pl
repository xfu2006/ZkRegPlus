# verify a given regex

open my $rh, '<', "/home/xiang/Desktop/NewResearch/Projects/ZkregPlus/code/zkregplus/data/binexec/doxygen" or die "error open file";
my $s = do {local $/; <$fh> };
print "It matches\n" if $s =~  /^.*<xsl\x3a[^>]*?(test|value|select)\s*=\s*\x5c[\x22\x27][^\x22\x27]*?\w+(\s*\x5b\s*\d+\s*\x5d){10}.*$/i;
