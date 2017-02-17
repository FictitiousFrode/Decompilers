use strict;					# 'Safest' operation level
use warnings;				# Give warnings
use File::Basename;			# Interpreting resource filenames
use File::Path 'make_path';	# Creating directories for resources
use File::Slurp;			# Read entire file at once
use Compress::Zlib;			# ZLib compression
use Data::Dumper;			# Dumping data structures
use Carp;					# For stack tracing at errors

my $Time_Start	= time();	# Epoch time for start of processing

##Version History
my $Decompiler_Version		= '0.2';
#v0.1:	Initial structure for flow and storage
#v0.2:	Signature parsing, inflation/decryption of source

##Global variables##
#File handling
my $FileName_Bytecode;		# Filename for the compiled gamefile to decompile
my $FileName_Mapping;		# Filename for the mapping/translation file, if any.
my $FileName_Generate;		# Filename for the generated mapping file
my $FileName_Path;			# Path to place output files in
my $FileName_Sourcecode;	# Filename for the resulting sourcecode
my $FileName_Log;			# Filename for the decompilation log
my $File_Bytecode;			# File handle for input compiled gamefile
my $File_Mapping;			# File handle for name mapping
my $File_Sourcecode;		# File handle for output decompiled sourcecode
my $File_Log;				# File handle for logging output

#Input
my @Lines;					# Stores the lines which form the basis of ADRIFT files
my $Lines_Next;				# Index of next entry in @Lines 

#Option handling
my $Option_Minimal;		# Skip output directory and embedded resources
my $Option_Generate;	# Generate a new symbol file
my $Option_Verbose;		# Extra information dumped to story file
my $Option_Naming;		# Be extra aggressive on trying to determine names
						# TODO: This will create duplicate names, remake to avoid that
my $Options	= "Available Options:\n";
$Options	.= "-m\t\tMinimalist mode: Skip resources and output directory\n";
$Options	.= "-v\t\tVerbose: Extra information printed to log\n";
$Options	.= "-a\t\tAggressive naming: Try extra hard to find names of objects and properties\n";
$Options	.= "+s\t\tGenerate symbol file: Store symbol mapping in output directory\n";
$Options	.= "-s [file]:\tSymbol file: Parse the file for symbol mappings\n";

#Constants
my $Signature_Size	= 14;
my $Signature_Extra	= 8;
my $Signature_Base	= chr(0x3c).chr(0x42).chr(0x3f).chr(0xc9).chr(0x6a).chr(0x87).chr(0xc2).chr(0xcf);
my $Signature_v4	= $Signature_Base.chr(0x93).chr(0x45).chr(0x3e).chr(0x61).chr(0x39).chr(0xfa);
my $Signature_v39	= $Signature_Base.chr(0x94).chr(0x45).chr(0x37).chr(0x61).chr(0x39).chr(0xfa);
my $Signature_v38	= $Signature_Base.chr(0x94).chr(0x45).chr(0x36).chr(0x61).chr(0x39).chr(0xfa);

my $Gamefile_Version;

##Translation

#Mappings

#Namings

#Mapping File Handling

##File Handling
#PRNG/Decryption
my $PRNG_CST1 		= 0x43fd43fd;
my $PRNG_CST2 		= 0x00c39ec3;
my $PRNG_CST3 		= 0x00ffffff;
my $PRNG_INITIAL	= 0x00a09e86;
my $PRNG_STATE		= 0x00a09e86;
#Generate the next value of the PRNG
sub nextPRNG(){
	$PRNG_STATE = ($PRNG_STATE * $PRNG_CST1 + $PRNG_CST2) & $PRNG_CST3;
	return (255 * $PRNG_STATE) / ($PRNG_CST3 + 1);
}

##Parsing
sub parseSignature(){
	my $block_signature;
	my $bytes_read = read ($File_Bytecode, $block_signature, $Signature_Size);
	die 'Unable to read file signature' unless $bytes_read eq $Signature_Size;
	if ($block_signature eq $Signature_v4){
		$Gamefile_Version	= '4.00';
		parseV4();
	}
	if ($block_signature eq $Signature_v39){
		$Gamefile_Version	= '3.90';
		parseV3();
	}
	if ($block_signature eq $Signature_v38){
		$Gamefile_Version	= '3.80';
		parseV3();
	}
	die 'Unable to determine version' unless defined $Gamefile_Version;
}
#Parse a v3.X version file into lines, using PRNG decryption
sub parseV3(){
	#Read in encrypted file
	my $encrypted			= read_file ( $FileName_Bytecode, binmode => ':raw' );
	#Generate decryption mask
	my $size				= length($encrypted);
	my $mask				= '';
	for my $i (1 .. $size) { $mask .= chr(nextPRNG()) }
	#Decrypt
	my $decrypted			= $encrypted ^ $mask;
	#Split and store lies
	@Lines = split(chr(13).chr(10), $decrypted);
}
#Parse a v4.0 version file into lines, using zlib deflation
sub parseV4(){
	#Read in the compressed file
	my $compressed			= read_file ( $FileName_Bytecode, binmode => ':raw' );
	#Skip file signature
	$compressed				= substr($compressed, $Signature_Size + $Signature_Extra);
	#Initiate inflation stream
	my $stream 				= inflateInit() or die 'Cannot create inflation stream';
	#Inflate
	my $inflated;
	my $status;
	($inflated, $status)	= $stream->inflate($compressed);
	#Split and store lies
	@Lines = split(chr(13).chr(10), $inflated);
}

sub parseHeader(){
	#Write to log
	print $File_Log "Decompiler v$Decompiler_Version on $FileName_Bytecode ";

}

##Analyzing

##Output
sub printSource(){
	#generateInform();		# Generate equivalent Inform-source
	#generateXML();			# Generate XML based on bytecode
}


##Main Program Loop
#Parse command-line arguments
for (;;) {
	if		($#ARGV >= 1 && $ARGV[0] eq '-s') {		# Read symbol mapping file
		$FileName_Mapping	= $ARGV[1];
		splice(@ARGV, 0, 2);
	}
	elsif	($#ARGV >= 0 && $ARGV[0] eq '+s') {		# Create symbol file template
		$Option_Generate	= 1;
		splice(@ARGV, 0, 1);
	}
	elsif($#ARGV >= 0 && $ARGV[0] eq '-a') {		# Aggressive naming
		$Option_Naming		= 1;
		splice(@ARGV, 0, 1);
	}
	elsif($#ARGV >= 0 && $ARGV[0] eq '-v') {		# Verbose
		$Option_Verbose		= 1;
		splice(@ARGV, 0, 1);
	}
	elsif($#ARGV >= 0 && $ARGV[0] eq '-m') {		# Minimalist mode
		$Option_Minimal		= 1;
		splice(@ARGV, 0, 1);
	}
	else { last }
}
$FileName_Bytecode	= $ARGV[0];	# There should be only one argument left, giving the name of the file to parse.
die "Use: adrift [options] file.taf\n$Options" if ($#ARGV != 0);	# Too many unparsed arguments

#Determine names to use
$FileName_Path	= './';	# Default to no directory
if ($ARGV[0] =~ m/([-_\w\s]*)\.(taf)/i) {	# Use the name of the input file if possible
	$FileName_Path			= $1 . '/'		unless defined $Option_Minimal;
	$FileName_Generate		= $1 . '.sym'	if defined $Option_Generate;
	$FileName_Sourcecode	= $1 . '.src';
	$FileName_Log			= $1 . '.log';
}
else{
	$FileName_Path			= 'decoded/'	unless defined $Option_Minimal;
	$FileName_Sourcecode	= 'source.src';
	$FileName_Log			= 'decompile.log';
	$FileName_Generate		= $1 . '.sym'	if defined $Option_Generate;
}

#Some sanity checking
die "$FileName_Bytecode is not a valid file"	unless -f $FileName_Bytecode;
die "Overwriting existing symbol file with autogenerated is not supported in minimal mode"
	if defined $FileName_Generate && $Option_Minimal && -e $FileName_Generate ;

#Create output path
mkdir $FileName_Path						unless -e $FileName_Path;
die "$FileName_Path is not a valid path"	unless -d $FileName_Path;

#Open file handles
open($File_Log, "> :raw :bytes :unix", $FileName_Path . $FileName_Log) # Use :unix to flush the log as we write to it
	or die "$0: can't open $FileName_Path$FileName_Log for writing: $!";

print "Parsing $FileName_Bytecode\n";
open($File_Bytecode, "< :raw :bytes", $FileName_Bytecode)
	or die("Couldn't open $FileName_Bytecode for reading.");
#preloadConstants();							# Populate arrays with constants
parseSignature();								# Read the file signature to determine version
parseHeader();									# Read header and determine version/type of file
#parseFile();									# Parse the input file into the local data structures
close($File_Bytecode);
#preloadMapping();								# Load mapping defaults
#parseMapping() if defined $FileName_Mapping;	# Read symbol file if called for
print "Analyzing...\n";
#analyze();
#generateMapping() if $Option_Generate;			# Generate symbol file if called for

open($File_Sourcecode, "> :raw :bytes", $FileName_Path . $FileName_Sourcecode)
	or die "$0: can't open $FileName_Path$FileName_Sourcecode for writing: $!";
print "Writing results...\n";
#printSource();

#Close file output
close($File_Sourcecode);
close($File_Log);
print "Decompiling completed in ".(time - $Time_Start)." seconds.\n";