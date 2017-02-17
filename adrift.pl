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
my $Decompiler_Version		= '0.4';
#v0.1:	Initial structure for flow and storage
#v0.2:	Signature parsing, inflation/decryption of source
#v0.3:	Raw dump
#v0.4:	Parse header

##Global variables##
#File handling
my $FileName_Compiled;		# Filename for the compiled gamefile to decompile
my $FileName_Mapping;		# Filename for the mapping/translation file, if any.
my $FileName_Generate;		# Filename for the generated mapping file
my $FileName_Path;			# Path to place output files in
my $FileName_Decompiled;	# Filename for the decompiled sourcecode
my $FileName_Log;			# Filename for the log
my $File_Compiled;			# File handle for input compiled gamefile
my $File_Mapping;			# File handle for name mapping
my $File_Decompiled;		# File handle for output decompiled sourcecode
my $File_Log;				# File handle for logging output

#Input
my @Lines;					# Stores the lines which form the basis of ADRIFT files
my $Lines_Next;				# Index of next entry in @Lines 

#Option handling
my $Option_Minimal;		# Skip output directory and embedded resources
my $Option_Generate;	# Generate a new symbol file
my $Option_Verbose;		# Extra information dumped to story file
my $Option_Rawdump;		# Dump raw decompiled source
my $Option_Naming;		# Be extra aggressive on trying to determine names
						# TODO: This will create duplicate names, remake to avoid that
my $Options	= "Available Options:\n";
$Options	.= "-m\t\tMinimalist mode: Skip resources and output directory\n";
$Options	.= "-v\t\tVerbose: Extra information printed to log\n";
$Options	.= "-a\t\tAggressive naming: Try extra hard to find names of objects and properties\n";
$Options	.= "+s\t\tGenerate symbol file: Store symbol mapping in output directory\n";
$Options	.= "-s [file]:\tSymbol file: Parse the file for symbol mappings\n";
$Options	.= "+r\t\tRaw dump of decompiled source\n";

#Constants
my $Signature_Size	= 14;
my $Signature_Extra	= 8;
my $Signature_Base	= chr(0x3c).chr(0x42).chr(0x3f).chr(0xc9).chr(0x6a).chr(0x87).chr(0xc2).chr(0xcf);
my $Signature_v4	= $Signature_Base.chr(0x93).chr(0x45).chr(0x3e).chr(0x61).chr(0x39).chr(0xfa);
my $Signature_v39	= $Signature_Base.chr(0x94).chr(0x45).chr(0x37).chr(0x61).chr(0x39).chr(0xfa);
my $Signature_v38	= $Signature_Base.chr(0x94).chr(0x45).chr(0x36).chr(0x61).chr(0x39).chr(0xfa);

#Game Details
my $Gamefile_Version;
my %Game;
my %Settings;
##Translation

#Mappings

#Namings

#Mapping File Handling

##File Handling
#The next Single-Line Value
sub nextSLV(){
	return $Lines[$Lines_Next++];
}
#The next Multi-Line Value
sub nextMLV(){
	my $block;
	my $terminated;
	my $terminator;
	$terminator		= chr( 42).chr( 42)	if $Gamefile_Version eq '3.80';
	$terminator		= chr( 42).chr( 42)	if $Gamefile_Version eq '3.90';
	$terminator		= chr(189).chr(208)	if $Gamefile_Version eq '4.00';
	do {
		my $line	= nextSLV();
		$terminated	= 1			if $terminator eq substr ($line, -2);
		$block		.= "\n"		if defined $block;
		$block		.=  $line;
	} until defined $terminated;
	return $block;
}
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
#Read in the file, using signature to determine version
sub readFile(){
	my $block_signature;
	my $bytes_read = read ($File_Compiled, $block_signature, $Signature_Size);
	die 'Unable to read file signature' unless $bytes_read eq $Signature_Size;
	if ($block_signature eq $Signature_v4){
		$Gamefile_Version	= '4.00';
		inflateFile();
	}
	if ($block_signature eq $Signature_v39){
		$Gamefile_Version	= '3.90';
		decryptFile();
	}
	if ($block_signature eq $Signature_v38){
		$Gamefile_Version	= '3.80';
		decryptFile();
	}
	die 'Unable to determine version' unless defined $Gamefile_Version;
}
#Decrypt a file using PRNG, for v3.X0
sub decryptFile(){
	#Read in encrypted file
	my $encrypted			= read_file ( $FileName_Compiled, binmode => ':raw' );
	#Generate decryption mask
	my $size				= length($encrypted);
	my $mask				= '';
	for my $i (1 .. $size) { $mask .= chr(nextPRNG()) }
	#Decrypt
	my $decrypted			= $encrypted ^ $mask;
	print $File_Decompiled $decrypted if defined $Option_Rawdump;
	#Split and store lines
	@Lines = split(chr(13).chr(10), $decrypted);
}
#Inflate a file using zlib, for v4.00
sub inflateFile(){
	#Read in the compressed file
	my $compressed			= read_file ( $FileName_Compiled, binmode => ':raw' );
	#Skip file signature
	$compressed				= substr($compressed, $Signature_Size + $Signature_Extra);
	#Initiate inflation stream
	my $stream 				= inflateInit() or die 'Cannot create inflation stream';
	#Inflate
	my $inflated;
	my $status;
	($inflated, $status)	= $stream->inflate($compressed);
	print $File_Decompiled $inflated if defined $Option_Rawdump;
	#Split and store lines
	@Lines = split(chr(13).chr(10), $inflated);
}
##Parsing
sub parseHeader(){
	#Intro Text
	$Game{Intro}			= nextMLV();
	$Game{Start}			= nextSLV() + 1;	# The only place rooms are indexed from 0
	$Game{Ending}			= nextMLV();
	#text	GameName
	$Game{GameName}			= nextSLV();
	#text	GameAuthor 
	$Game{GameAuthor}		= nextSLV();
	#number	MaxCarried
	my $max_carried			= nextSLV()	if $Gamefile_Version eq '3.80'; #TODO postprocessing into MaxSize and MaxWeight
	#text	DontUnderstand 
	$Game{Error}			= nextSLV();
	#number	Perspective 
	$Game{Perspective}		= nextSLV();
	#truth	ShowExits 
	$Game{ShowExits}		= nextSLV();
	#number	WaitTurns
	$Game{WaitTurns}		= nextSLV();
	#truth	DispFirstRoom 
	$Game{InitialLook}		= 0			if $Gamefile_Version eq '3.80';
	$Game{InitialLook}		= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#truth	BattleSystem
	$Game{EnableBattle}		= 0			if $Gamefile_Version eq '3.80';
	$Game{EnableBattle}		= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#number	MaxScore
	$Game{MaxScore}			= 0			if $Gamefile_Version eq '3.80';
	$Game{MaxScore}			= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#text	PlayerName
	$Game{PlayerName}		= ''		if $Gamefile_Version eq '3.80';
	$Game{PlayerName}		= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#truth	PromptName
	$Game{PromptName}		= 0			if $Gamefile_Version eq '3.80';
	$Game{PromptName}		= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#text	PlayerDesc
	$Game{PlayerDesc}		= ''		if $Gamefile_Version eq '3.80';
	$Game{PlayerDesc}		= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#number	Task
	$Game{AltDescTask}		= 0			if $Gamefile_Version eq '3.80';
	$Game{AltDescTask}		= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#text	AltDesc
	$Game{AltDesc}			= nextSLV()	if $Game{AltDescTask};
	#number	Position
	$Game{Position}			= 0			if $Gamefile_Version eq '3.80';
	$Game{Position}			= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#number	ParentObject
	$Game{ParentObject}		= 0			if $Gamefile_Version eq '3.80';
	$Game{ParentObject}		= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#number	PlayerGender
	$Game{PlayerGender}		= 0			if $Gamefile_Version eq '3.80';
	$Game{PlayerGender}		= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#number	MaxSize
	$Game{MaxSize}			= 0			if $Gamefile_Version eq '3.80';	#TODO Process $max_carried into this
	$Game{MaxSize}			= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#number	MaxWeight
	$Game{MaxWeight}		= 0			if $Gamefile_Version eq '3.80';	#TODO Process $max_carried into this
	$Game{MaxWeight}		= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#battle	PlayerStats
	$Game{PlayerStats}		= parseBattle()	if $Game{EnableBattle};
	#truth	EightPointCompass
	$Game{ExpandedCompass}	= 0			if $Gamefile_Version eq '3.80';
	$Game{ExpandedCompass}	= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#truth	NoDebug			SKIP
	nextSLV()							if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#truth	NoScoreNotify
	$Game{NoScoreNotify}	= 1			if $Gamefile_Version eq '3.80';
	$Game{NoScoreNotify}	= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#truth	DisableMap
	$Game{DisableMap}		= 0			if $Gamefile_Version eq '3.80';
	$Game{DisableMap}		= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#truth	NoAutoComplete	SKIP
	nextSLV()							if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#truth	NoControlPanel	SKIP
	nextSLV()							if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#truth	NoMouse			SKIP
	nextSLV()							if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#truth	Sound
	$Game{EnableSound}		= 0			if $Gamefile_Version eq '3.80';
	$Game{EnableSound}		= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#truth	Graphics
	$Game{EnableGraphics}	= 0			if $Gamefile_Version eq '3.80';
	$Game{EnableGraphics}	= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#resource	IntroRes
	$Game{IntroRes}			= parseResource()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#resource	WinRes
	$Game{WinRes}			= parseResource()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#truth	StatusBox
	$Game{EnableStatusBox}	= 0			if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	$Game{EnableStatusBox}	= nextSLV()	if $Gamefile_Version eq '4.00';
	#text	StatusBoxText
	$Game{StatusBoxText}	= ''		if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	$Game{StatusBoxText}	= nextSLV()	if $Gamefile_Version eq '4.00';
	#2x	Unknown				SKIP
	nextSLV()							if $Gamefile_Version eq '4.00';
	nextSLV()							if $Gamefile_Version eq '4.00';
	#truth	Embedded
	$Game{Embedded}			= 0			if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	$Game{Embedded}			= nextSLV()	if $Gamefile_Version eq '4.00';
	#Write to log
	print $File_Log "Decompiler v$Decompiler_Version on $FileName_Compiled, $Game{GameName} by $Game{GameAuthor} (ADRIFT v$Gamefile_Version)\n";
	print $File_Log "\tBattles\n"		if $Game{EnableBattle};
	print $File_Log "\tCompass\n"		if $Game{ExpandedCompass};
	print $File_Log "\tGraphics\n"		if $Game{EnableGraphics};
	print $File_Log "\tSound\n"			if $Game{EnableSound};
}
sub parseBattle(){
	die 'Fatal error: Battle system is not implemented';
}
sub parseResource(){
	my %resource;
	if($Game{EnableSound}){
		#text	SoundFile
		$resource{SoundFile}	= nextSLV();
		#number	SoundLen
		$resource{SoundSize}	= 0			if $Gamefile_Version eq '3.90';
		$resource{SoundSize}	= nextSLV()	if $Gamefile_Version eq '4.00';
	}
	if($Game{EnableGraphics}){
		#text	GraphicFile
		$resource{GraphicFile}	= nextSLV();
		#number	GraphicLen
		$resource{GraphicSize}	= 0			if $Gamefile_Version eq '3.90';
		$resource{GraphicSize}	= nextSLV()	if $Gamefile_Version eq '4.00';
	}
	return \%resource;
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
	elsif($#ARGV >= 0 && $ARGV[0] eq '+r') {		# Rawdump mode
		$Option_Rawdump		= 1;
		splice(@ARGV, 0, 1);
	}
	else { last }
}
$FileName_Compiled	= $ARGV[0];	# There should be only one argument left, giving the name of the file to parse.
die "Use: adrift [options] file.taf\n$Options" if ($#ARGV != 0);	# Too many unparsed arguments

#Determine names to use
$FileName_Path	= './';	# Default to no directory
if ($ARGV[0] =~ m/([-_\w\s]*)\.(taf)/i) {	# Use the name of the input file if possible
	$FileName_Log			= $1 . '.log';
	$FileName_Generate		= $1 . '.sym'	if defined $Option_Generate;
	$FileName_Decompiled	= $1 . '.src'	if defined $Option_Rawdump;
	$FileName_Path			= $1 . '/'	unless defined $Option_Minimal;
}
else{
	$FileName_Log			= 'decompile.log';
	$FileName_Generate		= 'decompile.sym'	if defined $Option_Generate;
	$FileName_Decompiled	= 'decompile.src'	if defined $Option_Rawdump;
	$FileName_Path			= 'decoded/'	unless defined $Option_Minimal;
}

#Some sanity checking
die "$FileName_Compiled is not a valid file"	unless -f $FileName_Compiled;
die "Overwriting existing symbol file with autogenerated is not supported in minimal mode"
	if defined $FileName_Generate && $Option_Minimal && -e $FileName_Generate ;

#Create output path
mkdir $FileName_Path						unless -e $FileName_Path;
die "$FileName_Path is not a valid path"	unless -d $FileName_Path;

#Open file handles
open($File_Log, "> :raw :bytes :unix", $FileName_Path . $FileName_Log) # Use :unix to flush the log as we write to it
	or die "$0: can't open $FileName_Path$FileName_Log for writing: $!";

print "Parsing $FileName_Compiled\n";
open($File_Compiled, "< :raw :bytes", $FileName_Compiled)
	or die("Couldn't open $FileName_Compiled for reading: $!");
open($File_Decompiled, "> :raw :bytes", $FileName_Path . $FileName_Decompiled)
	or die "$0: can't open $FileName_Path$FileName_Decompiled for writing: $!";
readFile();										# Read the file, determining version from signature
close($File_Compiled);
close($File_Decompiled);
#preloadConstants();							# Populate arrays with constants
parseHeader();									# Read header and determine version/type of file
#parseFile();									# Parse the input file into the local data structures
#preloadMapping();								# Load mapping defaults
#parseMapping() if defined $FileName_Mapping;	# Read symbol file if called for
print "Analyzing...\n";
#analyze();
#generateMapping() if $Option_Generate;			# Generate symbol file if called for

print "Writing results...\n";
#printSource();

#Close file output
close($File_Log);
print "Decompiling completed in ".(time - $Time_Start)." seconds.\n";