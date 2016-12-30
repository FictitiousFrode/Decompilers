use strict;			# 'Safest' operation level
use warnings;		# Give warnings

##Version History
my $Decompiler_Version		= 0.3;
#v0.1:	Initial structure for flow and storage
#v0.2:	Parsing of data blocks
#v0.3:	Symbol mapping fundamentals

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

sub namePropertyType($){
	my $type = shift;
	if	($type eq 1) {return 'number'}
	if	($type eq 2) {return 'object'}
	if	($type eq 3) {return 's-string'}
	if	($type eq 4) {return 'baseptr'}
	if	($type eq 5) {return 'nil'}
	if	($type eq 6) {return 'code'}
	if	($type eq 7) {return 'list'}
	if	($type eq 8) {return 'true'}
	if	($type eq 9) {return 'd-string'}
	if	($type eq 10) {return 'fnaddr'}
	if	($type eq 11) {return 'tpl'}
	if	($type eq 13) {return 'property'}
	if	($type eq 14) {return 'demand'}
	if	($type eq 15) {return 'synonym'}
	if	($type eq 16) {return 'redir'}
	if	($type eq 17) {return 'tpl2'}
	return 'unknown';

}

#Game Details
my $Flag_SymbolTable;		# include symbol table in output file
my $Flags_SourceTracking;	# include source file tracking information
my $Flags_Preinit;			# preinit needs to be run after reading game
my $Flags_Encrypted;		# 'encrypt' objects prior to writing them
my $Flags_Precompiled;		# writing precompiled header
my $Flags_Fastload;			# fast-load records are in file
my $Flags_CaseFolding;		# case folding was turned on in original compile
my $Flags_NewStyleLine;		# new-style line records

#Game Contents
my @Objects 		= ();	# In-game objects

##Translation 
#Mappings
my @Translate_Action			= ();	# Names for actions aren't stored anywhere
my @Translate_Builtin			= ();
my @Translate_Object			= ();
my @Translate_Object_Argument	= ();
my @Translate_Object_Local		= ();
my @Translate_Property			= ();
my @Translate_Property_Argument	= ();
my @Translate_Property_Local	= ();
#Namings
sub nameAaction($) {
	my $id = shift;
	return $Translate_Action[$id]	if defined $Translate_Action[$id];
	return "Action$id";
}
sub nameBuiltin($) {
	my $id = shift;
	return $Translate_Builtin[$id]	if defined $Translate_Builtin[$id];
	return "Builtin$id";
}
sub nameObject($) {
	my $id = shift;
	return 'nullObj'				if ($id eq 65535);
	return $Translate_Object[$id]	if defined $Translate_Object[$id];
	return "Obj$id";
}
sub nameProperty($) {
	my $id = shift;
	return $Translate_Property[$id] if defined $Translate_Property[$id];
	return "prop$id";
}
sub nameArgument($$) {
	my $id		= shift;	# Negative for object functions, positive for properties
	my $value	= shift;	# Negative for arguments, positive for locals
	# Arg1 is stored at index 0, etc
	if ($value > 0) {	# Locals
		my $local	= $value;
		if ($id > 0) {	# Properties
			return $Translate_Property_Local[$id][$local - 1]	if defined $Translate_Property_Local[$id][$local - 1];
		} else {		# Functions
			return $Translate_Object_Local[-$id][$local - 1]	if defined $Translate_Object_Local[-$id][$local - 1];
		}
		return "local$local";
	} else {	# Arguments
		my $arg		= -1 * $value;
		if ($id > 0) {	# Properties
			return $Translate_Property_Argument[$id][$arg - 1]	if defined $Translate_Property_Argument[$id][$arg - 1];
		} else {		# Functions
			return $Translate_Object_Argument[-$id][$arg - 1]	if defined $Translate_Object_Argument[-$id][$arg - 1];
		}
		return "arg$arg";
	}
}

sub parseMapping(){
	my $line;
	while ($line = <$File_Mapping>){
		#Pre-process the line
		next if ($line eq "\n" || $line eq '');		# Skip empty lines
		next if (substr($line, 0, 1) eq '#');		# Skip full-line comments
		$line	= (split('#', $line))[0];			# Remove comments
		my $parsed;
		if($line =~ m/(Object_Names|Objs|Obj)\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ){
			$parsed 					= $3;
			$Translate_Object[$2]		= $parsed;
		}
		if($line =~ m/(Property_?Names?|Props|Prop)\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ){
			$parsed 					= $3;
			$Translate_Property[$2]		= $parsed;
		}
		if($line =~ m/(Property|Props|Prop)_?(Arg|Argument)?\[?(\d*)[.-](\d*)\]?\s*=\s*['"](.*)['"]/i ){
			$parsed 									= $5;
			$Translate_Property_Argument[$3][$4 - 1]	= $parsed;
		}
		print "unable to parse $line" unless defined $parsed;
	}
#	my @Translate_Action			= ();
#	my @Translate_Builtin			= ();
#	my @Translate_Object_Argument	= ();
#	my @Translate_Object_Local		= ();
#	my @Translate_Property_Local	= ();
}

##File Handling
#Decrypts the block of text passed in
sub decrypt($){
	return unless $Flags_Encrypted;
	my $block	= shift;
	my $size	= length($block);
	my $mask	= $Encryption_Seed;
	my $block_mask;
	for my $i (1 .. $size) {
		$block_mask	.= chr($mask);
		$mask		= ($mask + $Encryption_Increment) % 256;
	}
	return $block ^ $block_mask;
}
sub debug($;$){
	my $block	= shift;
	my $id		= shift;
	my $size	= length $block;
	print $File_Log "Debug dump for $id\n"	if defined $id;
	for (my $i=0 ; $i<$size ; $i++) {
		my $char	= substr($block, $i, 1);
		my $byte	= ord($char);
		$char		= '' if $byte > 128 || $byte < 32;
		my $int		= '';
		$int		= unpack('S', substr($block, $i, 2)) if $i < ($size-1);
		print $File_Log "\t$i\t$byte\t$char\t$int\n"
	}
}

##Parsing
sub parseHeader(){
	#The header is 48 bytes long
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
	print $File_Log "\tEnabled flags ($flags):\n";
	print $File_Log "\t\tInclude symbol table in output file\n"				if $Flag_SymbolTable;
	print $File_Log "\t\tInclude source file tracking information\n"		if $Flags_SourceTracking;
	print $File_Log "\t\tPreinit needs to be run after reading game\n"		if $Flags_Preinit;
	print $File_Log "\t\t'encrypt' objects prior to writing them\n"			if $Flags_Encrypted;
	print $File_Log "\t\tWriting precompiled header\n"						if $Flags_Precompiled;
	print $File_Log "\t\tFast-load records are in file\n"					if $Flags_Fastload;
	print $File_Log "\t\tCase folding was turned on in original compile\n"	if $Flags_CaseFolding;
	print $File_Log "\t\tNew-style line records\n"							if $Flags_NewStyleLine;
}
sub parseFile(){
	#The compiled file consists of several blocks of varying length.
	for (;;){
		#Each block starts with a header of varying length
		my $size_type;	# 1 byte; size of the type field
		my $block_type;	# X bytes as defined by size_type; the type of data block
		my $next_block;	# 4 bytes; location of the next block.
		my $block_size;
		my $block;
		read ($File_Input, $size_type, 1);
		read ($File_Input, $block_type, unpack('C', $size_type));
		read ($File_Input, $next_block, 4);
		$block_size	= unpack('L', $next_block) - tell($File_Input);
		#Log the block type, and break out at the end of the file.
		print $File_Log "$block_type: $block_size bytes\n";
		last unless $block_size;
		last if	$block_type eq '$EOF';
		#read the contents of the block and parse it
		read ($File_Input, $block, $block_size);
		if	($block_type eq 'XSI')	{ parseBlockXSI($block) }	# XOR Seed Information
		if	($block_type eq 'OBJ')	{ parseBlockOBJ($block) }	# OBJects
		#FST - does not contain anything useful for decompilation, no need to parse.
		#INH
		#FMTSTR
		#REQ
		#CMPD
		#SPECWORD
		#VOC
		if	($block_type eq 'HTMLRES')	{ parseBlockRES($block) }	# Embedded (HTML) RESources
	}
}
#XSI blocks contains the XOR Seed Information for the compiled file.
sub parseBlockXSI($){
	my $block = shift;
	#Read initial seed value and increment value
	$Encryption_Seed		= unpack('C', substr($block, 0, 1));
	$Encryption_Increment	= unpack('C', substr($block, 1, 1));
	print $File_Log "\t($Encryption_Seed+$Encryption_Increment)\n";
}
#OBJect blocks contain all the objects of the game
sub parseBlockOBJ($) {
	my $block	= shift;
	my $length	= length($block);
	#Objects are stored sequentially with no dividers or indication of how many there are;
	#We need to read the entire block sequentially.
	my $pos		= 0;
	my $count	= 0;				# Number of objects found
	my $verbs	= 0;				# Number of verbs found in preparsing
	while ($pos < $length) {
		#Object Header:
		# 0		Object type
		# 1-2	Object ID (UINT16)
		# 3-4	Unknown (often the same as size)
		# 5-6	Size (UINT16)
		my $type			= unpack('C', substr($block, $pos, 1));
		my $id				= unpack('S', substr($block, $pos + 1, 2));
		my $unknown			= unpack('S', substr($block, $pos + 3, 2));
		my $size			= unpack('S', substr($block, $pos + 5, 2));
		#Read object data, stored in encrypted form
		my $data			= decrypt(substr($block, $pos + 7, $size));
		$pos	+= 7 + $size;
		$count++;
		#Check type and stored
		if		($type eq 1) { # Function
			#Functions are just code, so we simply store it
			print $File_Log "\tObj$id: function ($size bytes)\n";
			print $File_Log "\t\tUnknown is $unknown\n" unless $size eq $unknown;
			$Objects[$id]	= {
				type		=> $type,
				code		=> $data
			};
		}
		elsif	($type eq 2) { # Meta-Object
			#Meta-Objects have their own sub-header, followed by data
			#  0-1	Workspace (UINT16)
			#  2-3	Flags (bitmap)
			#  4-5	Superclass count
			#  6-7	Property count
			#  8-9	offset to next free byte in prop area (UInt16): Not needed for decompile
			# 10-11	offset to end of static area, reset point (UInt16): Not needed for decompile
			# 12-13 size of 'static' (stored) properties (UInt16)
			my $workspace		= unpack('S', substr($data, 0, 2));
			my $flags			= unpack('S', substr($data, 2, 2));
			my $superclasses	= unpack('S', substr($data, 4, 2));
			my $properties		= unpack('S', substr($data, 6, 2));
			print $File_Log "\tObj$id: object ($size bytes) in $workspace with $superclasses parents and $properties properties\n";
			#Read superclasses, a list of UINT16 object ids
			my @superclass;
			for (my $i=0 ; $i<$superclasses ; $i++) {
				push @superclass, unpack('S', substr($data, 14 + 2*$i, 2));
			}
			#Parse properties
			my %property	= ();
			my $pos_data	= 14 + 2 * $superclasses;				# Skip past header and super classes
			$pos_data 		+= 2 * $properties if $flags & 2;	# Skip past property index if needed
			for (my $i=0 ; $i<$properties ; $i++) {
				#Parse property header
				my $prop_id			= unpack('S',	substr($data, $pos_data + 0, 2));
				my $prop_type		= ord	(		substr($data, $pos_data + 2));
				my $prop_size		= unpack('S',	substr($data, $pos_data + 3, 2));
				my $prop_flag		= ord	(		substr($data, $pos_data + 5));
				my $prop_data		= 				substr($data, $pos_data + 6, $prop_size);
				#Store the relevant data
				$property{$prop_id}	= {
					type	=> $prop_type,
					data	=> $prop_data
				};
				print $File_Log "\t\tProp$prop_id ($prop_size bytes): ".namePropertyType($prop_type)." ($prop_flag)\n";
				$pos_data += 6 + $prop_size;
			}
			#Store the decompiled info
			$Objects[$id]	= {
				type		=> $type,
				workspace	=> $workspace,
				flags		=> {
					isClass		=> ($flags & 1),	# Is the object a class
					hasPropInd	=> ($flags & 2),	# Is there an encoded property index
					isModified	=> ($flags & 4)		# Modified by a newer definition
				},
				superclass	=> \@superclass,
				properties	=> \%property
			};
		}
		else{
			print $File_Log "\tObj$id: Unhandled type: $type\n";
			#TODO: Add translation of type
		}
	}
}
#RESource blocks contain embedded files
sub parseBlockRES($) {
	#The block is divided into three distinct parts:
	#* Header, defining number of entries
	#* Metadata for each entry
	#* Embedded data for each entry
	my $block	= shift;
	my $length	= length($block);
	#Block header
	# 4 Bytes: Number of entries
	# 4 Bytes: Offset to where data begins
	my $entries	= unpack("L", substr($block, 0, 4));
	my $offset	= unpack("L", substr($block, 4, 4));
	#Read metadata and embedded data for each entry in one pass
	my $pos		= 8;
	for my $i (1 .. $entries){
		#Metadata
		my $data_pos	= unpack("L", substr($block, $pos, 4));
		my $size		= unpack("L", substr($block, $pos + 4, 4));
		my $name_size	= unpack("S", substr($block, $pos + 8, 2));
		my $name		= substr($block, $pos + 10, $name_size);
		$pos += $name_size + 10;
		print $File_Log "\t$name ($size bytes) at $data_pos\n";
		#Embedded data, only read when not in minimal mode
		unless ($Option_Minimal){
			#TODO: Make directory
			my $file_resource;
			open($file_resource, "> :raw :bytes", $FileName_Path . $name)
				|| die "$0: can't open ".$FileName_Path .  $name . " in write-open mode: $!";
			print $file_resource substr($block, $data_pos + $offset, $size);
			close $file_resource;
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
parseHeader();									# Read header and determine version/type of file
parseFile();									# Parse the input file into the local data structures
close($File_Input);
parseMapping() if defined $FileName_Mapping;	# Read symbol file if called for
#TODO: Analyze the game file
#TODO: generatemapping() if $Option_Generate;			# Generate symbol file if called for

#TODO: Generate source code

#Close file output
close($File_Output);
close($File_Log);