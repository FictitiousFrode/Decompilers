use strict;					# 'Safest' operation level
use warnings;				# Give warnings
use File::Basename;			# Interpreting resource filenames
use File::Path 'make_path';	# Creating directories for resources
use Data::Dumper;			# Dumping data structures
use Carp;					# For stack tracing at errors

#The T3 image format is well documented, available at:
#	http://www.tads.org/t3doc/doc/techman/t3spec/format.htm

my $Time_Start	= time();	# Epoch time for start of processing

##Version History
my $Decompiler_Version		= '0.6';
#v0.1:	Initial structure for flow and storage
#v0.2:	Parsing of basic data blocks
#v0.3:	Object block parsing and initial analysis
#v0.4:	Object printing, datatype decoding
#v0.5:	Constant pool handling
#v0.6:	Symbol file parsing

##Global variables##
#File handling
my $FileName_Bytecode;		# Filename for the compiled gamefile to decompile
my $FileName_Mapping;		# Filename for the mapping/translation file, if any.
my $FileName_Generate;		# Filename for the generated mapping file
my $FileName_Path;			# Path to place output files in
my $FileName_Sourcecode;	# Filename for the resulting sourcecode
my $FileName_Log;			# Filename for the decompilation log
my $File_ByteCode;			# File handle for input compiled gamefile
my $File_Mapping;			# File handle for name mapping
my $File_Sourcecode;		# File handle for output decompiled sourcecode
my $File_Log;				# File handle for logging output

#Option handling
my $Option_Minimal;		# Skip output directory and embedded resources
my $Option_Generate;	# Generate a new symbol file
my $Option_Verbose;		# Extra information dumped to story file
my $Options	= "Available Options:\n";
$Options	.= "-m\t\tMinimalist mode: Skip resources and output directory\n";
$Options	.= "-v\t\tVerbose: Extra information printed to log\n";
$Options	.= "-s [file]:\tSymbol file: Parse the file for symbol mappings\n";
$Options	.= "+s\t\tGenerate symbol file: Store symbol mapping in output directory\n";

#TADS Constants
my $Size_File_Header		= 69;
my $Size_File_Signature		= 11;
my $Size_Block_Header		= 10;

my $Signature_TADS3_Image	= chr(0x54).chr(0x33).chr(0x2D).chr(0x69).chr(0x6D).chr(0x61).chr(0x67).chr(0x65).chr(0x0D).chr(0x0A).chr(0x1A);

my @Constant_Dataholder_Type	= ();

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
my @Metaclass_Names			= ();
my @Metaclass_Versions		= ();
my @Objects					= ();
#Mappings
my @Translate_Object_Name		= ();
my @Translate_Object_Argument	= ();
my @Translate_Object_Local		= ();
my @Translate_Property_Name		= ();
my @Translate_Property_Argument	= ();
my @Translate_Property_Local	= ();


#Mapping File Handling
sub preloadConstants() {
	$Constant_Dataholder_Type[1]	= 'VM_NIL';		# boolean "false" or null pointer
	$Constant_Dataholder_Type[2]	= 'VM_TRUE';	# boolean "true"
	$Constant_Dataholder_Type[3]	= 'VM_STACK';	# Reserved for implementation use for storing native machine pointers to stack frames
	$Constant_Dataholder_Type[4]	= 'VM_CODEPTR';	# Reserved for implementation use for storing native machine pointers to code
	$Constant_Dataholder_Type[5]	= 'VM_OBJ';		# object reference as a 32-bit unsigned object ID number
	$Constant_Dataholder_Type[6]	= 'VM_PROP';	# property ID as a 16-bit unsigned number
	$Constant_Dataholder_Type[7]	= 'VM_INT';		# integer as a 32-bit signed number
	$Constant_Dataholder_Type[8]	= 'VM_SSTRING';	# single-quoted string; 32-bit unsigned constant pool offset
	$Constant_Dataholder_Type[9]	= 'VM_DSTRING';	# double-quoted string; 32-bit unsigned constant pool offset
	$Constant_Dataholder_Type[10]	= 'VM_LIST';	# list constant; 32-bit unsigned constant pool offset
	$Constant_Dataholder_Type[11]	= 'VM_CODEOFS';	# code offset; 32-bit unsigned code pool offset
	$Constant_Dataholder_Type[12]	= 'VM_FUNCPTR';	# function pointer; 32-bit unsigned code pool offset
	$Constant_Dataholder_Type[13]	= 'VM_EMPTY';	# no value
	$Constant_Dataholder_Type[14]	= 'VM_NATIVE_CODE';	# Reserved for implementation use for storing native machine pointers to native code
	$Constant_Dataholder_Type[15]	= 'VM_ENUM';	# enumerated constant; 32-bit integer
	$Constant_Dataholder_Type[16]	= 'VM_BIFPTR';	# built-in function pointer; 32-bit integer, encoding the function set dependency table index in the high-order 16 bits, and the function's index within its set in the low-order 16 bits.
	$Constant_Dataholder_Type[17]	= 'VM_OBJX';	# Reserved for implementation use for an executable object, as a 32-bit object ID number
}
sub parseMapping() {
	open($File_Mapping, "< :raw :bytes", $FileName_Mapping)
		|| die("Couldn't open $FileName_Mapping for reading.");
	my $line;
	while ($line = <$File_Mapping>) {
		#Pre-process the line
		chomp $line;
		next if $line eq '';					# Skip empty lines
		next if (substr($line, 0, 1) eq '#');	# Skip full-line comments
		$line	= (split('#', $line))[0];		# Remove comments
		my $parsed;
		#Builtins are not translated
#		if($line =~ m/(Action|Act)s?\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ) {
#			$parsed 									= $3;
#			$Translate_Action[$2]						= $parsed;
#		}
		if($line =~ m/(Object|Obj)s?\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 									= $3;
			$Translate_Object_Name[$2]					= $parsed;
		}
		if($line =~ m/(Object|Obj)s?[-_]?(Arg|Argument)?\[?(\d*)[.-](\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 									= $5;
			$Translate_Object_Argument[$3][$4 - 1]		= $parsed;
		}
		if($line =~ m/(Object|Obj)s?[-_]?(Loc|Local)?\[?(\d*)[.-](\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 									= $5;
			$Translate_Object_Local[$3][$4 - 1]			= $parsed;
		}
		if($line =~ m/(Property|Properties|Props|Prop)\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 									= $3;
			$Translate_Property_Name[$2]				= $parsed;
		}
		if($line =~ m/(Property|Props|Prop)[-_]?(Arg|Argument)?\[?(\d*)[.-](\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 									= $5;
			$Translate_Property_Argument[$3][$4 - 1]	= $parsed;
		}
		if($line =~ m/(Property|Props|Prop)[-_]?(Loc|Local)?\[?(\d*)[.-](\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 									= $5;
			$Translate_Property_Local[$3][$4 - 1]		= $parsed;
		}
		print "Unable to parse $line\n" unless defined $parsed;
	}
	close $File_Mapping;
}
##Translation
sub nameObject($) {
	my $id = shift;
	return 'nullObj'					unless defined $id;
#	return 'nullObj'					if $id eq $Null_Value;
	return $Translate_Object_Name[$id]	if defined $Translate_Object_Name[$id];
	return "Obj$id";
}
sub nameProperty($) {
	my $id = shift;
	return 'nullprop'						unless defined $id;
#	return 'nullprop'						if $id eq $Null_Value;
	return $Translate_Property_Name[$id]	if defined $Translate_Property_Name[$id];
	return "prop$id";
}
sub nameLocal($$) {
	my $id		= shift;	# Negative for object functions, positive for properties
	my $value	= shift;	# Negative for arguments, positive for locals
	return 'UnknownArg' unless defined $value;
	# Arg1 is stored at index 0, etc
	if ($value > 0) {
		my $local	= $value;
		if ($id > 0) {	# Properties
			return $Translate_Property_Local[$id][$local - 1]	if defined $Translate_Property_Local[$id][$local - 1];
		}
		else {			# Functions
			return $Translate_Object_Local[-$id][$local - 1]	if defined $Translate_Object_Local[-$id][$local - 1];
		}
		return "local$local";
	}
	else {
		my $arg		= -1 * $value;
		if ($id > 0) {	# Properties
			return $Translate_Property_Argument[$id][$arg - 1]	if defined $Translate_Property_Argument[$id][$arg - 1];
		}
		else {			# Functions
			return $Translate_Object_Argument[-$id][$arg - 1]	if defined $Translate_Object_Argument[-$id][$arg - 1];
		}
		return "arg$arg";
	}
}


##File Handling
sub debug($;$) {
	my $block	= shift;
	my $id		= shift;
	my $size	= length $block;
	print $File_Log "Debug dump for $id\n"	if defined $id;
	for (my $i=0 ; $i<$size ; $i++) {
		my $char	= substr($block, $i, 1);
		my $byte	= ord($char);
		$char		= '' if $byte > 128 || $byte < 32;
		my $int		= '';
		$int		= unpack('s', substr($block, $i, 2)) if $i < ($size-1);
		print $File_Log "\t$i\t$byte\t$char\t$int\n"
	}
}

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
		if	($block_type eq 'OBJS')		{ parseBlockOBJS($block) }		# OBJects Static
		if	($block_type eq 'CPDF')		{ parseBlockCPDF($block) }		# Constant Pool DeFinition
		if	($block_type eq 'CPPG')		{ parseBlockCPPG($block) }		# Constant Pool PaGe
		if	($block_type eq 'MRES')		{ parseBlockMRES($block) }		# Multimedia RESources
		#MREL	Multimedia REsource Link
		if	($block_type eq 'MCLD')		{ parseBlockMCLD($block) }		# MetaCLass Dependecy
		if	($block_type eq 'FNSD')		{ parseBlockFNSD($block) }		# FuNction Set Dependency list
		if	($block_type eq 'SYMD')		{ parseBlockSYMD($block) }		# SYMbolic name Definition
		if	($block_type eq 'SRCF')		{ parseBlockSRCF($block) }		# SouRCe File descriptor - debug mode
		#GSYM	Global SYMbol definition - debug mode
		#MHLS	Method Header LiSt - debug mode
		#MACR	MACRo - debug mode
		if	($block_type eq 'SINI')		{ parseBlockSINI($block) }		# Static INItializer
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
#Static Objects
sub parseBlockOBJS($){
	my $block	= shift;
	my $length	= length($block);
	#The block has a header containing:
	#UINT16	Number of object entries
	#UINT16	Metaclass ID
	#UINT16	Flags
	my $entries			= unpack('S', substr($block, 0, 2));
	my $metaclass		= unpack('S', substr($block, 2, 2));
	my $flags			= unpack('S', substr($block, 4, 2));
	my $flag_large		= $flags & 0x01;
	my $flag_transient	= $flags & 0x02;
	print $File_Log "\t$entries objects of meta-class $Metaclass_Names[$metaclass]\n";
	#TODO: Some classes can be safely ignored
	#Read in each object
	my $pos	= 6;
	foreach my $entry (1..$entries){
		my $id		= unpack('L', substr($block, $pos, 4));
		my $size;	#Size depends on flags
		$size		= unpack('S', substr($block, $pos+4, 2))	unless	$flag_large;
		$size		= unpack('L', substr($block, $pos+4, 4))	if		$flag_large;
		$pos		+= 6 unless	$flag_large;
		$pos		+= 8 if		$flag_large;
		my $data	= substr($block, $pos, $size);
		$pos		+= $size;
		#Store the object
		$Objects[$id]	= {
			id			=> $id,
			metaclass	=> $metaclass,
			data		=> $data
		};
		print $File_Log "\t$id ($size bytes)\n"		if $Option_Verbose;
	}
}
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
	print 	"Extracting $entries Resources...\n" if $entries;
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
#MCLD contains the definitions of the meta classes, mapped to index numbers
sub parseBlockMCLD($) {
	my $block	= shift;
	my $length	= length($block);
	#The block has a small header indicating the number of list entries
	# 2 Bytes: Number of entries
	my $entries	= unpack('S', substr($block, 0, 2));
	print $File_Log "\t$entries meta-classes\n";
	my $pos		= 2;
	for my $i (1 .. $entries){
		#Each entry contains the following encoded meta-data
		#UINT16	Offset to next entry
		#UBYTE	Number of bytes in entry name
		#STRING	Entry name
		#UINT16	Number of property IDs
		#UINT16	Size of each property record
		#	List of property IDs, each of the given size
		my $offset		= unpack('S', substr($block, $pos, 2));
		my $size		= ord(substr($block, $pos + 2, 1));
		my $metaclass	= substr($block, $pos+3, $size);
		print $File_Log "\t$metaclass\n";
		if ($metaclass =~ m/^([-_.,a-zA-Z0-9]*)\/(\d{6})/){
			push @Metaclass_Names,		$1;
			push @Metaclass_Versions,	$2;
		}
		else {
			print $File_Log "\t\tUnhandled metaclass\n";
			push @Metaclass_Names,		'';
			push @Metaclass_Versions,	'000000';
		}
		#TODO Parse and store properties
		$pos += $offset;
	}
}
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
	my $entries	= unpack('S', substr($block, 0, 2));
	my $entry	= 0;
	my $pos		= 2;
	my $size	= length ($block);
	print $File_Log "\t$entries symbols\n";
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
#Debug information related to source file
sub parseBlockSRCF($){
	my $block = shift;
	#Header
	#UINT16	Number of entries
	#UINT16	Size of each source line record
	my $entries				= unpack('S', substr($block, 0, 2));
	my $size_line_record	= unpack('S', substr($block, 2, 2));
	print $File_Log "\tINFO: This blocktype has not been properly decoded\n";
	print $File_Log "\t$entries definitions\n";
	my $pos	= 6;
	foreach my $entry (1..$entries){
		my $size		 	= unpack('L', substr($block, $pos+0, 4));
		my $master_index	= unpack('S', substr($block, $pos+4, 2));
		my $filename_size	= unpack('S', substr($block, $pos+6, 2));
		my $filename		= substr($block, $pos+8, $filename_size);
		my $pos_rec			= $pos + 8 + $filename_size;
		my $records			= unpack('L', substr($block, $pos_rec, 4));
		$pos_rec 			+= 4;
		print $File_Log "\t$filename with $records records\n";
		foreach my $record (1..$records){
			my $line_no		= unpack('L', substr($block, $pos_rec + 0, 4));
			my $bytecode	= unpack('L', substr($block, $pos_rec + 4, 4));
		}
		#TODO: Store these
		$pos	+= $size;
	}
}
#TODO	GSYM
#TODO	MHLS
#TODO	MACR
#Static Initializing 
#TODO: Store the parsed data
sub parseBlockSINI($){
	my $block = shift;
	#Header:
	#UINT32	Size of header
	#UINT32	Offset of static code pool that can be discarded
	#UINT32	Number of initializers
	my $header_size			= unpack('L', substr($block, 0, 4));
	my $discard_offset		= unpack('L', substr($block, 4, 4));
	my $entries				= unpack('L', substr($block, 12, 4));
	my $pos					= $header_size;
	foreach my $entry (1..$entries){
		my $object		= unpack('L', substr($block, $pos+0, 4));
		my $property	= unpack('L', substr($block, $pos+4, 2));
	}
}
##Analyzing
sub analyze(){
	print "Analyzing Objects...\n";
	analyzeObjects();
}
sub analyzeObjects(){
	#tads-object
	print $File_Log "Analyzing tads-object:\n";
	for my $obj (0 .. $#Objects) {
		#Not all Object ID's are actually used
		next unless defined $Objects[$obj];
		#Only analyze TADS objects
		my $metaclass	= $Metaclass_Names[$Objects[$obj]{metaclass}];
		next unless $metaclass eq 'tads-object';
		#Read Object data:
		my $data			= $Objects[$obj]{data};
		my $superclasses	= unpack('S', substr($data, 0, 2));
		my $properties		= unpack('S', substr($data, 2, 2));
		my $flags			= unpack('S', substr($data, 4, 2));
		my @superclass		= ();
		my %property		= ();
		my $pos				= 6;
		foreach my $class (1..$superclasses) {
			push @superclass, unpack('L', substr($data, $pos, 4));
			$pos += 4;
		}
		foreach my $class (1..$properties) {
			my $prop			= unpack('S', substr($data, $pos, 2));
			my $dataholder		= substr($data, $pos+2, 5);
			$property{$prop}	= $dataholder;
			$pos += 7;
		}
		#Store data
		$Objects[$obj]{superclass}	= \@superclass;
		$Objects[$obj]{property}	= \%property;
		$Objects[$obj]{isclass}		= $flags & 0x01;
		print $File_Log "\tObj$obj: $superclasses superclasses, $properties properties\n";# if $Option_Verbose;
	}
}
sub propertyString($$){
	my $obj		= shift;
	my $prop	= shift;
	die "propertyString needs both Object and Property id"		unless defined $obj && defined $prop;
	die "Can't access property $prop on undefined object $obj"	unless defined $Objects[$obj];
	my $data	= $Objects[$obj]{property}{$prop};
	return decodeDataHolder($data);
}
sub decodeDataHolder($);
sub decodeDataHolder($) {
	my $data	= shift;
	#Determine type and name from first byte
	my $type	= ord(substr($data, 0, 1));
	my $name	= $Constant_Dataholder_Type[$type];
	#All dataholders should be 5 bytes long, with the last 4 for payload
	my $payload_short	= unpack('s', substr($data, 1, 2));
	my $payload_long	= unpack('l', substr($data, 1, 4));
	#Reserved types, these should never occur
	return $name	if $name eq 'VM_STACK';			# 3
	return $name	if $name eq 'VM_CODEPTR';		# 4
	return $name	if $name eq 'VM_NATIVE_CODE';	# 14
	return $name	if $name eq 'VM_OBJX';			# 17
	#Simple dataholders without payload
	return 'nil'	if $name eq 'VM_NIL';			# 1
	return 'true'	if $name eq 'VM_TRUE';			# 2
	return 'NULL'	if $name eq 'VM_EMPTY';			# 13
	#Payload that can be resolved immediately
	return nameObject($payload_long)		if $name eq 'VM_OBJ';	# 5
	return nameProperty($payload_short)		if $name eq 'VM_PROP';	# 6
	return $payload_long					if $name eq 'VM_INT';	# 7
	return "enum$payload_long"				if $name eq 'VM_ENUM';	# 15
	return $payload_long					if $name eq 'VM_BIFPTR';# 16 - TODO use naming
	#Constant Pool Data
	#TODO: Check if quotes are included for these
	return interpretString($payload_long, "'")	if $name eq 'VM_SSTRING';	# 8	
	return interpretString($payload_long, '"')	if $name eq 'VM_DSTRING';	# 9
	return interpretList($payload_long, $data)	if $name eq 'VM_LIST';		# 10	
	#Constant Pool Data
	return interpretCode($payload_long)		if $name eq 'VM_CODEOFS';	# 11
	return interpretCode($payload_long)		if $name eq 'VM_FUNCPTR';	# 12
	
	#Unknown dataholder
	warn "Unknown dataholder $data";
	return "UNKNOWN$data";
}

#Strings are stored in the Constant Pool with a UINT16 size followed by that number of characters
sub interpretString($$){
	use integer;		# Integer division is needed for determining correct codepage
	my $address	= shift;
	my $quoted	= shift;
	my $page	= $address / $Constant_Definitions[2]{size};
	my $offset	= $address % $Constant_Definitions[2]{size};
	my $size	= unpack('S', substr($Constant_Pages[2][$page], $offset, 2));
	my $text	= substr($Constant_Pages[2][$page], $offset+2, $size);
	return "$quoted$text$quoted";
#	print $File_Log "DEBUG\tInterpreting constant pool address $address to page $page offset $offset\n";
#	print "Constant $address -> $page:$offset\n";
#	my $test	= substr($Constant_Pages[2][$page], $offset, $size+2);
#	debug $test;
#	return "Constant $page:$offset";
}
#Lists are stored in the Constant Pool with a UINT16 number of entries followed by that number of data holders (5 bytes each)
sub interpretList($){
	use integer;		# Integer division is needed for determining correct codepage
	my $address	= shift;
	my $quoted	= shift;
	my $page	= $address / $Constant_Definitions[2]{size};
	my $offset	= $address % $Constant_Definitions[2]{size};
	my $entries	= unpack('S', substr($Constant_Pages[2][$page], $offset, 2));
	my $list	= '[';
	for (my $entry = 0 ; $entry < $entries ; $entry++){
		$list	.= decodeDataHolder(substr($Constant_Pages[2][$page], $offset + 2 + $entry * 5, 5));
		$list	.= ', ' if $entry != $entries-1;
	}
	$list	.= ']';
	return $list;
#	print $File_Log "DEBUG\tInterpreting constant pool address $address to page $page offset $offset\n";
#	print "Constant $address -> $page:$offset\n";
#	my $test	= substr($Constant_Pages[2][$page], $offset, 2 + 5 * $entries);
#	debug $test;
#	return "Constant $page:$offset";
}
sub interpretCode($){
	my $address	= shift;
	return "Code@ $address";
}

##Output
#Generate and print the corresponding TADS source code
sub printSource() {
	print $File_Log "Printing Object Source\n";
	print $File_Sourcecode "\n\n//\t## Objects ##\n";
	for my $obj (0 .. $#Objects) {
		#Not all Object ID's are actually used
		next unless defined $Objects[$obj];
		#Only analyze TADS objects
		my $metaclass	= $Metaclass_Names[$Objects[$obj]{metaclass}];
		next unless $metaclass eq 'tads-object';
		printObjectSource($obj);
	}
}
sub printObjectSource($){
	my $obj	= shift;
	print $File_Sourcecode 'class ' if $Objects[$obj]{flags}{isClass};
	print $File_Sourcecode nameObject($obj) . ': ';
	if (defined $Objects[$obj]{superclass}) {
		my @parents	= @{ $Objects[$obj]{superclass} };
		for my $i (0 .. $#parents) {
			print $File_Sourcecode ', ' if $i > 0;
			print $File_Sourcecode nameObject($parents[$i]);
		}
	}
	else {
		print $File_Sourcecode 'object';
	}
	print $File_Sourcecode "\n";
	#Decode information
	print $File_Sourcecode	"\t//\tObj$obj\t = '".nameObject($obj)."'\n";
	#Data properties
	if (defined $Objects[$obj]{property}) {
		my $count = keys %{ $Objects[$obj]{property} };
		print $File_Sourcecode "\t// $count properties\n";
		for my $prop ( sort {$a <=> $b} keys %{ $Objects[$obj]{property} } ) {
			my $name	= nameProperty($prop);
			my $value	= propertyString($obj, $prop);
			print $File_Sourcecode "\t$name\t= $value\n";
		}
	}
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
	$FileName_Sourcecode	= $1 . '.t';
	$FileName_Log			= $1 . '.log';
}
else{
	$FileName_Path			= 'decoded/'	unless defined $Option_Minimal;
	$FileName_Sourcecode	= 'source.t';
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
print "Parsing $FileName_Bytecode\n";
open($File_ByteCode, "< :raw :bytes", $FileName_Bytecode)
	|| die("Couldn't open $FileName_Bytecode for reading.");
preloadConstants();								# Populate arrays with TADS3 constants
parseHeader();									# Read header and determine version/type of file
parseFile();									# Parse the input file into the local data structures
close($File_ByteCode);
#TODO	preloadMapping();								# Load mapping defaults
parseMapping() if defined $FileName_Mapping;	# Read symbol file if called for
print "Analyzing...\n";
analyze();
#TODO	generateMapping() if $Option_Generate;			# Generate symbol file if called for

#TODO: Generate source code
open($File_Sourcecode, "> :raw :bytes", $FileName_Path . $FileName_Sourcecode)
	|| die "$0: can't open " . $FileName_Path . $FileName_Sourcecode . "for writing: $!";
print "Writing results...\n";
printSource();									# Print TADS source based on bytecode

#Close file output
close($File_Sourcecode);
close($File_Log);
print "Decompiling completed in ".(time - $Time_Start)." seconds.\n";