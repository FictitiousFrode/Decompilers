use strict;			# 'Safest' operation level
use warnings;		# Give warnings

##Version History
my $Decompiler_Version		= 0.1;
#v0.1:	Initial structure for flow and storage

##Global variables##
#File handling
my $FileName_Input;		# Filename for the compiled gamefile to decompile
my $FileName_Mapping;	# Filename for the mapping/translation file, if any.
my $FileName_Path;		# Path to place output files in
my $FileName_Output;	# Filename for the resulting sourcecode
my $FileName_Log;		# Filename for the decompilation log
my $File_Input;			# File handle for input compiled gamefile
my $File_Mapping;		# File handle for name mapping
my $File_Output;		# File handle for output decompiled sourcecode
my $File_Log;			# File handle for logging output

#Option handling
my $Option_Minimal;		# Skip output directory and embedded resources
my $Option_Generate;	# Generate a new symbol file
my $Option_Verbose;		# Extra information dumped to story file
my $Options	= "Available Options:\n";
$Options	.= "-m\t\tMinimalist mode: Skip resources and output directory\n";
$Options	.= "-s [file]:\tSymbol file: Parse the file for symbol mappings\n";
$Options	.= "+s [file]:\tGenerate symbol file: Generate a new symbol file\n";

#TADS Constants
my $Size_Header				= 48;
my $Size_Signature			= 11;
my $Signature_TADS2_Game	= chr(84).chr(65).chr(68).chr(83).chr(50).chr(32).chr( 98).chr(105).chr(110).chr(10).chr(13);
my $Signature_TADS2_Res		= chr(84).chr(65).chr(68).chr(83).chr(50).chr(32).chr(114).chr(115).chr( 99).chr(10).chr(13);
my $Encryption_Seed			= 0x3f;
my $Encryption_Increment	= 0x40;

#Game Details
my $Flag_SymbolTable;		# include symbol table in output file
my $Flags_SourceTracking;	# include source file tracking information
my $Flags_Preinit;			# preinit needs to be run after reading game
my $Flags_Encrypted;		# 'encrypt' objects prior to writing them
my $Flags_Precompiled;		# writing precompiled header
my $Flags_Fastload;			# fast-load records are in file
my $Flags_CaseFolding;		# case folding was turned on in original compile
my $Flags_NewStyleLine;		# new-style line records

##File Handling
#Decrypts the block of text passed in
sub decrypt ($){
	my $block	= shift;
	my $size	= length($block);
	my $mask	= $Encryption_Seed;
	my $block_mask;
	for my $i (1 .. $size) {
		$block_mask	.= chr($mask);
		$mask		= ($mask + $Encryption_Increment) % 256;
	}
	$block	= $block ^ $block_mask;
}

##Parsing
sub parseHeader(){
	#The header is 48 bytes long. Detailed specification is not available
	#	 0-10	File header signature
	#	11-12	Reserved but unused (?)
	#	13-18	Compiler version (?)
	#	19-20	Flags
	#	   21	Unknown
	#	22-45	Build date
	#	46-47	Unknown
	my $block_header;
	my $bytes_read = read ($File_Input, $block_header, $Size_Header);
	die "Unable to read file header." unless $bytes_read eq $Size_Header;
	#Check the signature
	my $signature	= substr($block_header, 0, $Size_Signature);
	die "$FileName_Input is not a valid TADS file."
		unless	$signature eq $Signature_TADS2_Game
			||	$signature eq $Signature_TADS2_Res;
	#Parse the rest of the header
	my $unknown1	= unpack('S', substr($block_header, 11, 2));	# substr($block_header, 11, 2);
	my $version		= substr($block_header, 13, 6);
	my $flags		= unpack('n', substr($block_header, 19, 2));	# Flags are stored as a bitmap, so read in as big-endian UINT-16
#	my $flags		= unpack('C', substr($block_header, 20, 1));	# Flags might be stored only in byte 19 though...
	my $unknown2	= unpack('C', substr($block_header, 21, 1));	# substr($block_header, 21, 1);
	my $timestamp	= substr($block_header, 22, 24);
	my $unknown3	= unpack('S', substr($block_header, 46, 2));	# substr($block_header, 46, 2);
	#Parse Flags
	$Flag_SymbolTable		=	$flags & 1;
	$Flags_SourceTracking	=	$flags & 2;
	$Flags_Preinit			=	$flags & 4;
	$Flags_Encrypted		=	$flags & 8;
	$Flags_Precompiled		=	$flags & 16;
	$Flags_Fastload			=	$flags & 32;
	$Flags_CaseFolding		=	$flags & 64;
	$Flags_NewStyleLine		=	$flags & 128;
	
	#Write to log
	print $File_Log "Decompiler v$Decompiler_Version on $FileName_Input ";
	print $File_Log "(a TADS2-Game file)\n"		if $signature eq $Signature_TADS2_Game;
	print $File_Log "(a TADS2-Resource file)\n"	if $signature eq $Signature_TADS2_Res;
	print $File_Log "Compiled by $version at $timestamp\n";
	print $File_Log "\tUnknown 1: $unknown1\n";
	print $File_Log "\tUnknown 2: $unknown2\n";
	print $File_Log "\tUnknown 3: $unknown3\n";
	print $File_Log "Enabled flags ($flags):\n";
	print $File_Log "\tInclude symbol table in output file\n"				if $Flag_SymbolTable;
	print $File_Log "\tInclude source file tracking information\n"			if $Flags_SourceTracking;
	print $File_Log "\tPreinit needs to be run after reading game\n"		if $Flags_Preinit;
	print $File_Log "\t'encrypt' objects prior to writing them\n"			if $Flags_Encrypted;
	print $File_Log "\tWriting precompiled header\n"						if $Flags_Precompiled;
	print $File_Log "\tFast-load records are in file\n"						if $Flags_Fastload;
	print $File_Log "\tCase folding was turned on in original compile\n"	if $Flags_CaseFolding;
	print $File_Log "\tNew-style line records\n"							if $Flags_NewStyleLine;
}

##Main Program Loop
#Parse command-line arguments
for (;;) {
	if		($#ARGV >= 1 && $ARGV[0] eq '-s') {		# Read symbol mapping file
		$FileName_Mapping	= $ARGV[1];
		splice(@ARGV, 0, 2);
	}
	elsif	($#ARGV >= 1 && $ARGV[0] eq '+s') {		# Create symbol  file template
		$FileName_Mapping	= $ARGV[1];
		$Option_Generate	= 1;
		splice(@ARGV, 0, 2);
	}
	elsif($#ARGV >= 0 && $ARGV[0] eq '-v'){			# Verbose
		$Option_Verbose		= 1;
		splice(@ARGV, 0, 1);
	}
	elsif($#ARGV >= 0 && $ARGV[0] eq '-m'){			# Minimalist mode
		$Option_Minimal		= 1;
		splice(@ARGV, 0, 1);
	}
	else { last }
}
$FileName_Input	= $ARGV[0];	# There should be only one argument left, giving the name of the file to parse.
die "Use: tads2 [options] file.taf\n$Options" if ($#ARGV != 0);	# Too many unparsed arguments

#Determine names to use
$FileName_Path	= './';	# Default to no directory
if ($ARGV[0] =~ m/([\w\s]*)\.gam/i){	# Use the name of the input file if possible
	$FileName_Path		= $1 . '/'		unless defined $Option_Minimal;
	$FileName_Output	= $1 . '.t';
	$FileName_Log		= $1 . '.log';
}
else{
	$FileName_Path		= 'decoded/'	unless defined $Option_Minimal;
	$FileName_Output	= 'source.t';
	$FileName_Log		= 'decompile.log';
}

#Create output path
mkdir $FileName_Path						unless -e $FileName_Path;
die "$FileName_Path is not a valid path"	unless -d $FileName_Path;

#Open file handles
die "$FileName_Input is not a valid file"	unless -f $FileName_Input;
open($File_Input, "< :raw :bytes", $FileName_Input)
	|| die("Couldn't open $FileName_Input for reading.");
open($File_Log, "> :raw :bytes :unix", $FileName_Path . $FileName_Log) # Use :unix to flush the log as we write to it
	|| die "$0: can't open " . $FileName_Path . $FileName_Log . " for writing: $!";
open($File_Output, "> :raw :bytes", $FileName_Path . $FileName_Output)
	|| die "$0: can't open " . $FileName_Path . $FileName_Output . "for writing: $!";

#Process the game archive
parseHeader();	#Read header and determine version/type of file
#parse();		# Parse the input file into the local data structures
close($File_Input);
#TODO: Read symbol file if called for
#TODO: Analyze the game file
#TODO: Generate symbol file if called for
#TODO: Generate source code

#Close file output
close($File_Output);
close($File_Log);