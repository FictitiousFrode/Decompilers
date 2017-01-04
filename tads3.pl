use strict;					# 'Safest' operation level
use warnings;				# Give warnings
use File::Basename;			# Interpreting resource filenames
use File::Path 'make_path';	# Creating directories for resources

#The T3 image format is well documented, available at:
#	http://www.tads.org/t3doc/doc/techman/t3spec/format.htm

##Version History
my $Decompiler_Version		= 0.2;
#v0.1:	Initial structure for flow and storage
#v0.2:	Parsing of data blocks

##Global variables##
#File handling
my $FileName_Bytecode;		# Filename for the compiled gamefile to decompile
my $FileName_Mapping;		# Filename for the mapping/translation file, if any.
my $FileName_Generate;		# Filename for the generated mapping file
my $FileName_Path;			# Path to place output files in
my $FileName_SourceCode;	# Filename for the resulting sourcecode
my $FileName_Log;			# Filename for the decompilation log
my $File_ByteCode;			# File handle for input compiled gamefile
my $File_Mapping;			# File handle for name mapping
my $File_SourceCode;		# File handle for output decompiled sourcecode
my $File_Log;				# File handle for logging output

#Option handling
my $Option_Minimal;		# Skip output directory and embedded resources
my $Option_Generate;	# Generate a new symbol file
my $Option_Verbose;		# Extra information dumped to story file
my $Options	= "Available Options:\n";
$Options	.= "-m\t\tMinimalist mode: Skip resources and output directory\n";
$Options	.= "-s [file]:\tSymbol file: Parse the file for symbol mappings\n";
$Options	.= "+s\t\tGenerate symbol file: Store symbol mapping in output directory\n";

#TADS Constants
my $Size_File_Header		= 69;
my $Size_File_Signature		= 11;
my $Size_Block_Header		= 10;

my $Signature_TADS3_Image	= chr(0x54).chr(0x33).chr(0x2D).chr(0x69).chr(0x6D).chr(0x61).chr(0x67).chr(0x65).chr(0x0D).chr(0x0A).chr(0x1A);

#Game Details
my $Timestamp_Image;		# Timestamp for when the image was written, for comparison
my $Version_Image;			# Version of the image file
my $Version_Debug;
my $Offset_Startup_Code;	# Bytecode offset to startup code
my $Size_Method_Header;
my $Size_Exception_Entry;
my $Size_Debug_Line;
my $Size_Debug_Header;
my $Size_Debug_Local;
my $Size_Debug_Frame;
#Game Contents
my %Symbols					= ();
my @Function_Set			= ();
my @Constant_Definitions	= ();
my @Constant_Pages			= ();

##File Handling

##Parsing
sub parseHeader(){
	#The header is 68 bytes long
	# 0-10	Signature
	#11-12	Version number, UINT16
	#13-40	Reserved, unused
	#41-44	Build configuration hash
	#45-68	Timestamp
	my $block_header;
	my $bytes_read		= read ($File_ByteCode, $block_header, $Size_File_Header);
	die "Unable to read file header" unless $bytes_read eq $Size_File_Header;
	#Check the signature
	my $signature		= substr($block_header, 0, $Size_File_Signature);
	die "$FileName_Bytecode is not a valid TADS file."
		unless	$signature eq $Signature_TADS3_Image;
	#Parse the rest of the header
	$Version_Image		= unpack('S', substr($block_header, 11, 2));
	$Timestamp_Image	= substr($block_header, 45, 24);
	#Write to log
	print $File_Log "Decompiler v$Decompiler_Version on $FileName_Bytecode ";
	print $File_Log "(a TADS3-Image file)\n"		if $signature eq $Signature_TADS3_Image;
	print $File_Log "Compiled by $Version_Image at $Timestamp_Image\n";
}
sub parseFile(){
	#The compiled file consists of several blocks of varying length.
	for (;;){
		#Each block has a 10-byte header:
		# 0-4	Block type
		# 5-8	Block size UINT32
		# 9-10	Flags
		my $block_header;
		my $bytes_read		= read ($File_ByteCode, $block_header, $Size_Block_Header);
		die "Unable to read next block header" unless $bytes_read eq $Size_Block_Header;
		my $block_type		= substr($block_header, 0, 4);
		my $block_size		= unpack('L', substr($block_header, 4, 4));
		my $block_flags		= unpack('S', substr($block_header, 8, 2));
		#Log the block type, and break out at the end of the file.
		print $File_Log "$block_type: $block_size bytes ";
		print $File_Log '(mandatory)'		if $block_flags & 1;	# Mandatory flag
		print $File_Log "\n";
		last unless $block_size;
		my $block;
		#read the contents of the block and parse it
		read ($File_ByteCode, $block, $block_size);
		if	($block_type eq 'EOF ')		{ last }						# End of file marker; usually not reached due to zero size
		#TODO: Verify that each file has one and only one ENTP block
		if	($block_type eq 'ENTP')		{ parseBlockENTP($block) }		# ENTry Point
		#OBJS
		if	($block_type eq 'CPDF')		{ parseBlockCPDF($block) }		# Constant Pool DeFinition
		if	($block_type eq 'CPPG')		{ parseBlockCPPG($block) }		# Constant Pool PaGe
		if	($block_type eq 'MRES')		{ parseBlockMRES($block) }		# Multimedia RESources
		#MREL
		#MCLD
		if	($block_type eq 'FNSD')		{ parseBlockFNSD($block) }		# FuNction Set Dependency list
		if	($block_type eq 'SYMD')		{ parseBlockSYMD($block) }		# SYMbolic name Definition
		#SRCF
		#GSYM
		#MHLS
		#MACR
		#SINI
	}
}
#ENTryPoint blocks contains setup/startup data for the image
sub parseBlockENTP($){
	my $block = shift;
	#The ENTP contains the following, which we store in global variables
	#UINT4	code pool offset of byte code to execute after loading image
	#UINT2 	method header size of all methods in image file
	#UINT2	exception table entry size for all exception tables
	#UINT2	debugger line table entry size for all line tables
	#UINT2	debug table header size for all debug tables
	#UINT2	debug table local symbol record header size for all debug tables
	#UINT2	debug records version number
	#UINT2	debug table frame header size (version 2+)
	$Offset_Startup_Code	= unpack('L', substr($block, 0, 4));
	$Size_Method_Header		= unpack('S', substr($block, 4, 2));
	$Size_Exception_Entry	= unpack('S', substr($block, 6, 2));
	$Size_Debug_Line		= unpack('S', substr($block, 8, 2));
	$Size_Debug_Header		= unpack('S', substr($block, 10, 2));
	$Size_Debug_Local		= unpack('S', substr($block, 12, 2));
	$Version_Debug			= unpack('S', substr($block, 10, 2));
	$Size_Debug_Frame		= unpack('S', substr($block, 10, 2))	if $Version_Image >= 2;
}
#TODO OBJS
#CPDF Defines the parameters for the constant pools
sub parseBlockCPDF($){
	my $block = shift;
	#Containes the following definitions:
	# 0-1	Pool type, UINT16. 1=bytecode, 2=constant
	# 2-5	Number of pages in the pool; UINT32
	# 6-9	Size of each page, UINT32
	my $type		= unpack('S', substr($block, 0, 2));
	my $pages		= unpack('L', substr($block, 2, 4));
	my $size		= unpack('L', substr($block, 6, 9));
	die "Duplicate Code Pool Definition of type $type" if defined $Constant_Definitions[$type];
	$Constant_Definitions[$type]	= {
		pages		=> $pages,
		size		=> $size
	};
	print $File_Log "\tBytecode"			if $Option_Verbose && $type eq 1;
	print $File_Log "\tConstant"			if $Option_Verbose && $type eq 2;
	print $File_Log "\t$pages x $size\n"	if $Option_Verbose;
}
#CPPG contains one page of the constant pool
sub parseBlockCPPG($){
	my $block	= shift;
	my $size	= length($block);
	#Header:
	# 0-1	Pool type, UINT16
	# 2-5	page index
	#   6	XOR byte mask
	my $type	= unpack('S', substr($block, 0, 2));
	my $page	= unpack('L', substr($block, 2, 4));
	my $mask	= substr($block, 6, 1); #ord(substr($block, 6, 1));
	#Sanity check:
	die "Code Pool Page duplicate of type $type for page $page" if defined $Constant_Pages[$type][$page];
	#TODO: Size check, not that we really care
	#The rest is the xor 'encrypted' datablock
	my $data	= '';
	for my $i(7..$size-1){ $data .= substr($block, $i, 1) ^ $mask; }
	my $bytes	= length $data;
	$Constant_Pages[$type][$page]	= $data;
	print $File_Log "\tBytecode\tPage$page ($bytes bytes)\n"		if $Option_Verbose && $type eq 1;
	print $File_Log "\tConstant\tPage$page ($bytes bytes)\n"		if $Option_Verbose && $type eq 2;
}
#MRES contains embedded multimedia resources
sub parseBlockMRES($) {
	#The block is divided into two distinct parts:
	#* Table of Contents with metadata for each entry
	#* Embedded data for each entry
	my $block	= shift;
	my $length	= length($block);
	#ToC
	# 2 Bytes: Number of entries
	my $entries	= unpack('S', substr($block, 0, 2));
	print $File_Log "\t$entries Entries\n";
	#Read metadata and embedded data for each entry in one pass
	my $pos		= 2;
	for my $i (1 .. $entries){
		#Metadata
		my $data_pos	= unpack('L', substr($block, $pos, 4));
		my $size		= unpack('L', substr($block, $pos + 4, 4));
		my $name_size	= ord(substr($block, $pos + 8, 1));
		my $name		= substr($block, $pos + 9, $name_size);
		my $decrypted	= '';
		for my $i(0..$name_size-1){ $decrypted .= substr($name, $i, 1) ^ chr(0xFF); }
		$pos += $name_size + 9;
		print $File_Log "\t$decrypted ($size bytes) at $data_pos\n";
#		die "\t$decrypted ($size bytes) at $data_pos\n";
		#Embedded data, only read when not in minimal mode
		unless ($Option_Minimal){
			my $path = $FileName_Path.(dirname $decrypted);
			make_path($path);
			my $file_resource;
			open($file_resource, "> :raw :bytes", $FileName_Path . $decrypted)
				|| die "$0: can't open ".$FileName_Path . $decrypted . " in write-open mode: $!";
			print $file_resource substr($block, $data_pos, $size);
			close $file_resource;
		}
	}
}
#TODO	MREL
#TODO	MCLD
#FNSD provides the mapping from function set index numbers to function entrypoint vectors in the VM
sub parseBlockFNSD($){
	my $block = shift;
	#SYMD blocks contains a UINT16 defining the number of entries, each of which has it's size coded into it.
	#Symbols are stored sequentially with no dividers, so we need to read the entire block sequentially
	my $entries	= unpack('s', substr($block, 0, 2));
	my $entry	= 0;
	my $pos		= 2;
	my $size	= length ($block);
	while ($pos < $size){
		my $size	= ord(substr($block, $pos, 1));		# Length of function name
		my $name	= substr($block, $pos+1, $size);	# Name of the function
		#Store the function name and advance to the next
		$Function_Set[$entry]	= $name;
		print $File_Log "\t$entry\t$name\n"		if $Option_Verbose;
		$pos += 1+$size;
		$entry++;
	}
	warn "Expected $entries, found $entry"	unless $entries eq $entry;
}
#SYMbolic name Definition
sub parseBlockSYMD($){
	my $block = shift;
	#SYMD blocks contains a UINT16 defining the number of entries, each of which has it's size coded into it.
	#Symbols are stored sequentially with no dividers, so we need to read the entire block sequentially
	my $entries	= unpack('s', substr($block, 0, 2));
	my $entry	= 0;
	my $pos		= 2;
	my $size	= length ($block);
	while ($pos < $size){
		my $symbol_value	= substr($block, $pos, 5);				# DATA_HOLDER object, unparsed
		my $symbol_size		= ord(substr($block, $pos+5, 1));		# Length of symbol name
		my $symbol_name		= substr($block, $pos+6, $symbol_size);	# Name of the symbol, should be unique
		die "Non-unique symbol $symbol_name "	if defined  $Symbols{$symbol_name};
		#Store the symbol and advance to the next
		$Symbols{$symbol_name}	= $symbol_value;
		print $File_Log "\t$entry\t$symbol_name\n"		if $Option_Verbose;	#TODO: Add type-name for DATA_HOLDER
		$pos += $symbol_size + 6;
		$entry++;
	}
	warn "Expected $entries, found $entry"	unless $entries eq $entry;
}
#TODO	SRCF
#TODO	GSYM
#TODO	MHLS
#TODO	MACR
#TODO	SINI

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
$FileName_Bytecode	= $ARGV[0];	# There should be only one argument left, giving the name of the file to parse.
die "Use: tads3 [options] file.taf\n$Options" if ($#ARGV != 0);	# Too many unparsed arguments

#Determine names to use
$FileName_Path	= './';	# Default to no directory
if ($ARGV[0] =~ m/([\w\s]*)\.t3/i){	# Use the name of the input file if possible
	$FileName_Path			= $1 . '/'		unless defined $Option_Minimal;
	$FileName_Generate		= $1 . '.sym'	if defined $Option_Generate;
	$FileName_SourceCode	= $1 . '.t';
	$FileName_Log			= $1 . '.log';
}
else{
	$FileName_Path			= 'decoded/'	unless defined $Option_Minimal;
	$FileName_SourceCode	= 'source.t';
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
	|| die "$0: can't open " . $FileName_Path . $FileName_Log . " for writing: $!";

#Process the game archive
open($File_ByteCode, "< :raw :bytes", $FileName_Bytecode)
	|| die("Couldn't open $FileName_Bytecode for reading.");
parseHeader();									# Read header and determine version/type of file
parseFile();									# Parse the input file into the local data structures
close($File_ByteCode);
#TODO	preloadMapping();								# Load mapping defaults
#TODO	parseMapping() if defined $FileName_Mapping;	# Read symbol file if called for
#TODO	analyze();
#TODO	generateMapping() if $Option_Generate;			# Generate symbol file if called for

#TODO: Generate source code
open($File_SourceCode, "> :raw :bytes", $FileName_Path . $FileName_SourceCode)
	|| die "$0: can't open " . $FileName_Path . $FileName_SourceCode . "for writing: $!";

#Close file output
close($File_SourceCode);
close($File_Log);