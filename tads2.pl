use strict;					# 'Safest' operation level
use warnings;				# Give warnings
use File::Basename;			# Interpreting resource filenames
use File::Path 'make_path';	# Creating directories for resources
use Data::Dumper;			# Dumping data structures
use Carp;					# For stack tracing at errors

my $Time_Start	= time();	# Epoch time for start of processing

##Version History
my $Decompiler_Version		= '0.9.2';
#v0.1:	Initial structure for flow and storage
#v0.2:	Parsing of data blocks (Headers + XSI/OBJ/RES)
#v0.3:	Generation and parsing of symbol file
#v0.4:	Verbose mode implementation, parsing of VOC/CMPD/FMTSTR
#v0.5:	Action analyzis and property decoding; working resource paths
#v0.6:	Basic source printing, vocabulary analysis
#v0.7:	Code analysis: instruction set parsing
#v0.8:	Code analysis: instruction printing
#v0.9:	Minor tweaks
#	 .0	Time analysis
#	 .1	Improved handling of 'junk data'
#	 .2	Labeling

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

#TADS Constants
my $Size_Header				= 48;
my $Size_Signature			= 11;
my $Signature_TADS2_Game	= chr(84).chr(65).chr(68).chr(83).chr(50).chr(32).chr( 98).chr(105).chr(110).chr(10).chr(13);
my $Signature_TADS2_Res		= chr(84).chr(65).chr(68).chr(83).chr(50).chr(32).chr(114).chr(115).chr( 99).chr(10).chr(13);
my $Encryption_Seed			= 0x3f;
my $Encryption_Increment	= 0x40;
my $Null_Value				= 65535;

my @Constant_Property_Type	= ();
my @Constant_Opcode			= ();
my @Constant_Opcode_Payload	= ();

#Names corresponding to the property types
sub preloadConstants() {
	#Property Types
	$Constant_Property_Type[1]	= 'number';
	$Constant_Property_Type[2]	= 'object';
	$Constant_Property_Type[3]	= 's-string';
	$Constant_Property_Type[4]	= 'baseptr';
	$Constant_Property_Type[5]	= 'nil';
	$Constant_Property_Type[6]	= 'code';
	$Constant_Property_Type[7]	= 'list';
	$Constant_Property_Type[8]	= 'true';
	$Constant_Property_Type[9]	= 'd-string';
	$Constant_Property_Type[10]	= 'fnaddr';
	$Constant_Property_Type[11]	= 'tpl';
	$Constant_Property_Type[13]	= 'property';
	$Constant_Property_Type[14]	= 'demand';
	$Constant_Property_Type[15]	= 'synonym';
	$Constant_Property_Type[16]	= 'redir';
	$Constant_Property_Type[17]	= 'tpl2';
	#Opcodes
	#based on	https://github.com/garglk/garglk/blob/master/tads/tads2/opc.h
	$Constant_Opcode[0x01]	= 'OPCPUSHNUM';		#  1
	$Constant_Opcode[0x02]	= 'OPCPUSHOBJ';		#  2
	$Constant_Opcode[0x03]	= 'OPCNEG';			#  3
	$Constant_Opcode[0x04]	= 'OPCNOT';			#  4
	$Constant_Opcode[0x05]	= 'OPCADD';			#  5
	$Constant_Opcode[0x06]	= 'OPCSUB';			#  6
	$Constant_Opcode[0x07]	= 'OPCMUL';			#  7
	$Constant_Opcode[0x08]	= 'OPCDIV';			#  8
	$Constant_Opcode[0x09]	= 'OPCAND';			#  9
	$Constant_Opcode[0x0A]	= 'OPCOR';			# 10
	$Constant_Opcode[0x0B]	= 'OPCEQ';			# 11
	$Constant_Opcode[0x0C]	= 'OPCNE';			# 12
	$Constant_Opcode[0x0D]	= 'OPCGT';			# 13
	$Constant_Opcode[0x0E]	= 'OPCGE';			# 14
	$Constant_Opcode[0x0F]	= 'OPCLT';			# 15
	$Constant_Opcode[0x10]	= 'OPCLE';			# 16
	$Constant_Opcode[0x11]	= 'OPCCALL';		# 17
	$Constant_Opcode[0x12]	= 'OPCGETP';		# 18
	$Constant_Opcode[0x13]	= 'OPCGETPDATA';	# 19
	$Constant_Opcode[0x14]	= 'OPCGETLCL';		# 20
	$Constant_Opcode[0x15]	= 'OPCPTRGETPDATA';	# 21
	$Constant_Opcode[0x16]	= 'OPCRETURN';		# 22
	$Constant_Opcode[0x17]	= 'OPCRETVAL';		# 23
	$Constant_Opcode[0x18]	= 'OPCENTER';		# 24
	$Constant_Opcode[0x19]	= 'OPCDISCARD';		# 25
	$Constant_Opcode[0x1A]	= 'OPCJMP';			# 26
	$Constant_Opcode[0x1B]	= 'OPCJF';			# 27
	$Constant_Opcode[0x1C]	= 'OPCPUSHSELF';	# 28
	$Constant_Opcode[0x1D]	= 'OPCSAY';			# 29
	$Constant_Opcode[0x1E]	= 'OPCBUILTIN';		# 30
	$Constant_Opcode[0x1F]	= 'OPCPUSHSTR';		# 31
	$Constant_Opcode[0x20]	= 'OPCPUSHLST';		# 32
	$Constant_Opcode[0x21]	= 'OPCPUSHNIL';		# 33
	$Constant_Opcode[0x22]	= 'OPCPUSHTRUE';	# 34
	$Constant_Opcode[0x23]	= 'OPCPUSHFN';		# 35
	$Constant_Opcode[0x24]	= 'OPCGETPSELFDATA';# 36
	#37 is unused
	$Constant_Opcode[0x26]	= 'OPCPTRCALL';		# 38
	$Constant_Opcode[0x27]	= 'OPCPTRINH';		# 39
	$Constant_Opcode[0x28]	= 'OPCPTRGETP';		# 40
	$Constant_Opcode[0x29]	= 'OPCPASS';		# 41
	$Constant_Opcode[0x2A]	= 'OPCEXIT';		# 42
	$Constant_Opcode[0x2B]	= 'OPCABORT';		# 43
	$Constant_Opcode[0x2C]	= 'OPCASKDO';		# 44
	$Constant_Opcode[0x2D]	= 'OPCASKIO';		# 45
	$Constant_Opcode[0x2E]	= 'OPCEXPINH';		# 46
	$Constant_Opcode[0x2F]	= 'OPCEXPINHPTR';	# 47
	$Constant_Opcode[0x30]	= 'OPCCALLD';		# 48
	$Constant_Opcode[0x31]	= 'OPCGETPD';		# 49
	$Constant_Opcode[0x32]	= 'OPCBUILTIND';	# 50
	$Constant_Opcode[0x33]	= 'OPCJE';			# 51
	$Constant_Opcode[0x34]	= 'OPCJNE';			# 52
	$Constant_Opcode[0x35]	= 'OPCJGT';			# 53
	$Constant_Opcode[0x36]	= 'OPCJGE';			# 54
	$Constant_Opcode[0x37]	= 'OPCJLT';			# 55
	$Constant_Opcode[0x38]	= 'OPCJLE';			# 56
	$Constant_Opcode[0x39]	= 'OPCJNAND';		# 57
	$Constant_Opcode[0x3A]	= 'OPCJNOR';		# 58
	$Constant_Opcode[0x3B]	= 'OPCJT';			# 59
	$Constant_Opcode[0x3C]	= 'OPCGETPSELF';	# 60
	$Constant_Opcode[0x3D]	= 'OPCGETPSLFD';	# 61
	$Constant_Opcode[0x3E]	= 'OPCGETPOBJ';		# 62
	$Constant_Opcode[0x3F]	= 'OPCGETPOBJD';	# 63
	$Constant_Opcode[0x40]	= 'OPCINDEX';		# 64
	#65 is unused
	#66 is unused
	$Constant_Opcode[0x43]	= 'OPCPUSHPN';		# 67
	$Constant_Opcode[0x44]	= 'OPCJST';			# 68
	$Constant_Opcode[0x45]	= 'OPCJSF';			# 69
	$Constant_Opcode[0x46]	= 'OPCJMPD';		# 70
	$Constant_Opcode[0x47]	= 'OPCINHERIT';		# 71
	$Constant_Opcode[0x48]	= 'OPCCALLEXT';		# 72
	$Constant_Opcode[0x49]	= 'OPCDBGRET';		# 73
	$Constant_Opcode[0x4A]	= 'OPCCONS';		# 74
	$Constant_Opcode[0x4B]	= 'OPCSWITCH';		# 75
	$Constant_Opcode[0x4C]	= 'OPCARGC';		# 76
	$Constant_Opcode[0x4D]	= 'OPCCHKARGC';		# 77
	$Constant_Opcode[0x4E]	= 'OPCLINE';		# 78
	$Constant_Opcode[0x4F]	= 'OPCFRAME';		# 79
	$Constant_Opcode[0x50]	= 'OPCBP';			# 80
	$Constant_Opcode[0x51]	= 'OPCGETDBLCL';	# 81
	$Constant_Opcode[0x52]	= 'OPCGETPPTRSELF';	# 82
	$Constant_Opcode[0x53]	= 'OPCMOD';			# 83
	$Constant_Opcode[0x54]	= 'OPCBAND';		# 84
	$Constant_Opcode[0x55]	= 'OPCBOR';			# 85
	$Constant_Opcode[0x56]	= 'OPCXOR';			# 86
	$Constant_Opcode[0x57]	= 'OPCBNOT';		# 87
	$Constant_Opcode[0x58]	= 'OPCSHL';			# 88
	$Constant_Opcode[0x59]	= 'OPCSHR';			# 89
	$Constant_Opcode[0x5A]	= 'OPCNEW';			# 90
	$Constant_Opcode[0x5B]	= 'OPCDELETE';		# 91
	#Opcode Payloads
	#based on detads, naming convention, and trial and error.
	$Constant_Opcode_Payload[0x01]	= ['INT32'];						# 1		OPCPUSHNUM
	$Constant_Opcode_Payload[0x02]	= ['OBJECT'];						# 2		OPCPUSHOBJ
	$Constant_Opcode_Payload[0x03]	= ['NONE'];							# 3		OPCNEG
	$Constant_Opcode_Payload[0x04]	= ['NONE'];							# 4		OPCNOT
	$Constant_Opcode_Payload[0x05]	= ['NONE'];							# 5		OPCADD
	$Constant_Opcode_Payload[0x06]	= ['NONE'];							# 6		OPCSUB
	$Constant_Opcode_Payload[0x07]	= ['NONE'];							# 7		OPCMUL
	$Constant_Opcode_Payload[0x08]	= ['NONE'];							# 8		OPCDIV
	$Constant_Opcode_Payload[0x09]	= ['NONE'];							# 9		OPCAND
	$Constant_Opcode_Payload[0x0A]	= ['NONE'];							# 10	OPCOR
	$Constant_Opcode_Payload[0x0B]	= ['NONE'];							# 11	OPCEQ
	$Constant_Opcode_Payload[0x0C]	= ['NONE'];							# 12	OPCNE
	$Constant_Opcode_Payload[0x0D]	= ['NONE'];							# 13	OPCGT
	$Constant_Opcode_Payload[0x0E]	= ['NONE'];							# 14	OPCGE
	$Constant_Opcode_Payload[0x0F]	= ['NONE'];							# 15	OPCLT
	$Constant_Opcode_Payload[0x10]	= ['NONE'];							# 16	OPCLE
	$Constant_Opcode_Payload[0x11]	= ['UINT8', 'OBJECT'];				# 17	OPCCALL
	$Constant_Opcode_Payload[0x12]	= ['UINT8', 'PROPERTY'];			# 18	OPCGETP
	$Constant_Opcode_Payload[0x13]	= ['UINT8', 'PROPERTY'];			# 19	OPCGETPDATA		Experimental based on 0x12
	$Constant_Opcode_Payload[0x14]	= ['LOCAL'];						# 20	OPCGETLCL
	$Constant_Opcode_Payload[0x15]	= ['UINT8'];						# 21	OPCPTRGETPDATA	Experimental based on 0x28
	$Constant_Opcode_Payload[0x16]	= ['UNKNOWN2'];						# 22	OPCRETURN
	$Constant_Opcode_Payload[0x17]	= ['UNKNOWN2'];						# 23	OPCRETVAL
	$Constant_Opcode_Payload[0x18]	= ['UINT16'];						# 24	OPCENTER
	$Constant_Opcode_Payload[0x19]	= ['NONE'];							# 25	OPCDISCARD
	$Constant_Opcode_Payload[0x1A]	= ['OFFSET'];						# 26	OPCJMP
	$Constant_Opcode_Payload[0x1B]	= ['OFFSET'];						# 27	OPCJF
	$Constant_Opcode_Payload[0x1C]	= ['NONE'];							# 28	OPCPUSHSELF
	$Constant_Opcode_Payload[0x1D]	= ['STRING'];						# 29	OPCSAY
	$Constant_Opcode_Payload[0x1E]	= ['UINT8', 'BUILTIN'];				# 30	OPCBUILTIN
	$Constant_Opcode_Payload[0x1F]	= ['STRING'];						# 31	OPCPUSHSTR
	$Constant_Opcode_Payload[0x20]	= ['LIST'];							# 32	OPCPUSHLST
	$Constant_Opcode_Payload[0x21]	= ['NONE'];							# 33	OPCPUSHNIL
	$Constant_Opcode_Payload[0x22]	= ['NONE'];							# 34	OPCPUSHTRUE
	$Constant_Opcode_Payload[0x23]	= ['FUNCTION'];						# 35	OPCPUSHFN
	$Constant_Opcode_Payload[0x24]	= ['UINT8', 'PROPERTY'];			# 36	OPCGETPSELFDATA		Experimental based on 0x3C
	#37 is unused
	$Constant_Opcode_Payload[0x26]	= ['UINT8'];						# 38	OPCPTRCALL
	$Constant_Opcode_Payload[0x27]	= ['UNKNOWN'];						# 39	OPCPTRINH
	$Constant_Opcode_Payload[0x28]	= ['UINT8'];						# 40	OPCPTRGETP
	$Constant_Opcode_Payload[0x29]	= ['PROPERTY'];						# 41	OPCPASS
	$Constant_Opcode_Payload[0x2A]	= ['NONE'];							# 42	OPCEXIT
	$Constant_Opcode_Payload[0x2B]	= ['NONE'];							# 43	OPCABORT
	$Constant_Opcode_Payload[0x2C]	= ['NONE'];							# 44	OPCASKDO
	$Constant_Opcode_Payload[0x2D]	= ['PROPERTY'];						# 45	OPCASKIO
	$Constant_Opcode_Payload[0x2E]	= ['UINT8', 'PROPERTY', 'OBJECT'];	# 46	OPCEXPINH
	$Constant_Opcode_Payload[0x2F]	= ['UNKNOWN'];						# 47	OPCEXPINHPTR
	$Constant_Opcode_Payload[0x30]	= ['UNKNOWN'];						# 48	OPCCALLD
	$Constant_Opcode_Payload[0x31]	= ['UNKNOWN'];						# 49	OPCGETPD
	$Constant_Opcode_Payload[0x32]	= ['UNKNOWN'];						# 50	OPCBUILTIND
	$Constant_Opcode_Payload[0x33]	= ['UNKNOWN'];						# 51	OPCJE
	$Constant_Opcode_Payload[0x34]	= ['UNKNOWN'];						# 52	OPCJNE
	$Constant_Opcode_Payload[0x35]	= ['UNKNOWN'];						# 53	OPCJGT
	$Constant_Opcode_Payload[0x36]	= ['UNKNOWN'];						# 54	OPCJGE
	$Constant_Opcode_Payload[0x37]	= ['UNKNOWN'];						# 55	OPCJLT
	$Constant_Opcode_Payload[0x38]	= ['UNKNOWN'];						# 56	OPCJLE
	$Constant_Opcode_Payload[0x39]	= ['UNKNOWN'];						# 57	OPCJNAND
	$Constant_Opcode_Payload[0x3A]	= ['UNKNOWN'];						# 58	OPCJNOR
	$Constant_Opcode_Payload[0x3B]	= ['UNKNOWN'];						# 59	OPCJT
	$Constant_Opcode_Payload[0x3C]	= ['UINT8', 'PROPERTY'];			# 60	OPCGETPSELF
	$Constant_Opcode_Payload[0x3D]	= ['UINT8', 'PROPERTY'];			# 61	OPCGETPSLFD		Experimental based on 0x3C
	$Constant_Opcode_Payload[0x3E]	= ['UINT8', 'OBJECT', 'PROPERTY'];	# 62	OPCGETPOBJ
	$Constant_Opcode_Payload[0x3F]	= ['UINT8', 'OBJECT', 'PROPERTY'];	# 63	OPCGETPOBJD		Experimental based on 0x3E
	$Constant_Opcode_Payload[0x40]	= ['NONE'];							# 64	OPCINDEX
	#65-66 are unused
	$Constant_Opcode_Payload[0x43]	= ['POINTER'];						# 67	OPCPUSHPN
	$Constant_Opcode_Payload[0x44]	= ['OFFSET'];						# 68	OPCJST
	$Constant_Opcode_Payload[0x45]	= ['OFFSET'];						# 69	OPCJSF
	$Constant_Opcode_Payload[0x46]	= ['UNKNOWN'];						# 70	OPCJMPD
	$Constant_Opcode_Payload[0x47]	= ['UINT8', 'PROPERTY'];			# 71	OPCINHERIT
	$Constant_Opcode_Payload[0x48]	= ['UNKNOWN'];						# 72	OPCCALLEXT
	$Constant_Opcode_Payload[0x49]	= ['UNKNOWN'];						# 73	OPCDBGRET
	$Constant_Opcode_Payload[0x4A]	= ['UINT16'];						# 74	OPCCONS
	$Constant_Opcode_Payload[0x4B]	= ['SWITCH'];						# 75	OPCSWITCH
	$Constant_Opcode_Payload[0x4C]	= ['NONE'];							# 76	OPCARGC
	$Constant_Opcode_Payload[0x4D]	= ['UINT8'];						# 77	OPCCHKARGC
	$Constant_Opcode_Payload[0x4E]	= ['UNKNOWN'];						# 78	OPCLINE
	$Constant_Opcode_Payload[0x4F]	= ['FRAME'];						# 79	OPCFRAME
	$Constant_Opcode_Payload[0x50]	= ['UNKNOWN'];						# 80	OPCBP
	$Constant_Opcode_Payload[0x51]	= ['UNKNOWN'];						# 81	OPCGETDBLCL
	$Constant_Opcode_Payload[0x52]	= ['UINT8'];						# 82	OPCGETPPTRSELF	Experimental
	$Constant_Opcode_Payload[0x53]	= ['NONE'];							# 83	OPCMOD
	$Constant_Opcode_Payload[0x54]	= ['NONE'];							# 84	OPCBAND
	$Constant_Opcode_Payload[0x55]	= ['NONE'];							# 85	OPCBOR
	$Constant_Opcode_Payload[0x56]	= ['NONE'];							# 86	OPCXOR
	$Constant_Opcode_Payload[0x57]	= ['NONE'];							# 87	OPCBNOT
	$Constant_Opcode_Payload[0x58]	= ['NONE'];							# 88	OPCSHL
	$Constant_Opcode_Payload[0x59]	= ['NONE'];							# 89	OPCSHR
	$Constant_Opcode_Payload[0x5A]	= ['NONE'];							# 90	OPCNEW
	$Constant_Opcode_Payload[0x5B]	= ['NONE'];							# 91	OPCDELETE
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
my $Timestamp_Image;		# Timestamp for when the image was written, for comparison
my $Version_Image;			# Version of the image file

#Game Contents
my @Objects 			= ();	# Array of hash-map representing the decompiled objects
my @Formats				= ();	# Array of strings storing the formated strings
my @Compounds 			= ();	# Array of strings storing the compunded tokens
my %Property_Actions	= ();	# Mapping of which properties refer to which actions

##Translation
#Start points; used for skipping printing of basic objects and properties
my $Translate_Property_Start = 0;	# Property ID to start autogenerated symbol mapping from.
my $Translate_Object_Start = 0;		# Object ID to start autogenerated symbol mapping from.
#Mappings
my @Translate_Action			= ();	# Names for actions aren't stored anywhere
my @Translate_Builtin			= ();
my @Translate_Object_Name		= ();
my @Translate_Object_Argument	= ();
my @Translate_Object_Local		= ();
my @Translate_Property			= ();
my @Translate_Property_Argument	= ();
my @Translate_Property_Local	= ();
#Namings
sub nameAction($) {
	my $id = shift;
	croak unless defined $id;
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
	return 'nullObj'					unless defined $id;
	return 'nullObj'					if $id eq $Null_Value;
	return $Translate_Object_Name[$id]	if defined $Translate_Object_Name[$id];
	return "Obj$id";
}
sub nameProperty($) {
	my $id = shift;
	return 'nullprop'				unless defined $id;
	return 'nullprop'				if $id eq $Null_Value;
	return $Translate_Property[$id] if defined $Translate_Property[$id];
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
#Mapping File Handling
sub preloadMapping() {
	#Names for builtins and constant properties are taken from detads by Daniel Schepler
	$Translate_Property[1]	= 'doAction';
	$Translate_Property[2]	= 'verb';
	$Translate_Property[3]	= 'noun';
	$Translate_Property[4]	= 'adjective';
	$Translate_Property[5]	= 'preposition';
	$Translate_Property[6]	= 'article';
	$Translate_Property[7]	= 'plural';
	$Translate_Property[8]	= 'sdesc';
	$Translate_Property[9]	= 'thedesc';
	$Translate_Property[10]	= 'doDefault';
	$Translate_Property[11]	= 'ioDefault';
	$Translate_Property[12]	= 'ioAction';
	$Translate_Property[13]	= 'location';
	$Translate_Property[14]	= 'value';
	$Translate_Property[15]	= 'roomAction';
	$Translate_Property[16]	= 'actorAction';
	$Translate_Property[17]	= 'contents';
	$Translate_Property[18]	= 'tpl';
	$Translate_Property[19]	= 'prepDefault';
	$Translate_Property[20]	= 'verActor';
	$Translate_Property[21]	= 'validDo';
	$Translate_Property[22]	= 'validIo';
	$Translate_Property[23]	= 'lookAround';
	$Translate_Property[24]	= 'roomCheck';
	$Translate_Property[25]	= 'statusLine';
	$Translate_Property[26]	= 'locationOK';
	$Translate_Property[27]	= 'isVisible';
	$Translate_Property[28]	= 'cantReach';
	$Translate_Property[29]	= 'isHim';
	$Translate_Property[30]	= 'isHer';
	$Translate_Property[31]	= 'action';
	$Translate_Property[32]	= 'validDoList';
	$Translate_Property[33]	= 'validIoList';
	$Translate_Property[34]	= 'iobjGen';
	$Translate_Property[35]	= 'dobjGen';
	$Translate_Property[36]	= 'nilPrep';
	$Translate_Property[37]	= 'rejectMultiDobj';
	$Translate_Property[38]	= 'moveInto';
	$Translate_Property[39]	= 'construct';
	$Translate_Property[40]	= 'destruct';
	$Translate_Property[41]	= 'validActor';
	$Translate_Property[42]	= 'preferredActor';
	$Translate_Property[43]	= 'isEquivalent';
	$Translate_Property[44]	= 'adesc';
	$Translate_Property[45]	= 'multisdesc';
	$Translate_Property[46]	= 'tpl2';
	$Translate_Property[47]	= 'anyvalue';
	$Translate_Property[48]	= 'newNumbered';
	$Translate_Property[49]	= 'unknown';
	$Translate_Property[50]	= 'parseUnknownDobj';
	$Translate_Property[51]	= 'parseUnknownIobj';
	$Translate_Property[52]	= 'dobjCheck';
	$Translate_Property[53]	= 'iobjCheck';
	$Translate_Property[54]	= 'verbAction';
	$Translate_Property[55]	= 'disambigDobj';
	$Translate_Property[56]	= 'disambigIobj';
	$Translate_Property[57]	= 'prefixdesc';
	$Translate_Property[58]	= 'isThem';
	#Argument names
	$Translate_Property_Argument[10] = ['actor', 'prep', 'iobj'];					# doDefault
	$Translate_Property_Argument[11] = ['actor', 'prep'];							# ioDefault
	$Translate_Property_Argument[14] = ['actor', 'verb', 'dobj', 'prep', 'iobj'];	# roomAction
	$Translate_Property_Argument[15] = ['verb', 'dobj', 'prep', 'iobj'];			# actorAction
	$Translate_Property_Argument[21] = ['actor', 'obj', 'seqno'];					# validDo
	$Translate_Property_Argument[22] = ['actor', 'obj', 'seqno'];					# validIo
	$Translate_Property_Argument[23] = ['verbosity'];								# lookAround
	$Translate_Property_Argument[24] = ['verb'];									# roomCheck
	$Translate_Property_Argument[27] = ['vantage'];									# isVisible
	$Translate_Property_Argument[28] = ['actor', 'dolist', 'iolist', 'prep'];		# cantReach
	$Translate_Property_Argument[31] = ['actor'];									# action
	$Translate_Property_Argument[32] = ['actor', 'prep', 'iobj'];					# validDoList
	$Translate_Property_Argument[33] = ['actor', 'prep', 'dobj'];					# validIoList
	$Translate_Property_Argument[34] = ['actor', 'verb', 'dobj', 'prep'];			# iobjGen
	$Translate_Property_Argument[35] = ['actor', 'verb', 'iobj', 'prep'];			# dobjGen
	$Translate_Property_Argument[37] = ['prep'];									# rejectMultiDobj
	$Translate_Property_Argument[38] = ['dest'];									# moveInto
	$Translate_Property_Argument[47] = ['num'];										# anyvalue
	$Translate_Property_Argument[48] = ['actor', 'verb', 'num'];					# newNumbered
	$Translate_Property_Argument[50] = ['actor', 'prep', 'iobj', 'wordlist'];		# parseUnknownDobj
	$Translate_Property_Argument[51] = ['actor', 'prep', 'iobj', 'wordlist'];		# parseUnknownIobj
	$Translate_Property_Argument[52] = ['actor', 'prep', 'iobj', 'prep'];			# dobjCheck
	$Translate_Property_Argument[53] = ['actor', 'prep', 'iobj', 'prep'];			# iobjCheck
	$Translate_Property_Argument[54] = ['actor', 'dobj', 'prep', 'iobj'];			# verbAction
	$Translate_Property_Argument[55] = ['actor', 'prep', 'iobj', 'verprop', 'wordlist', 'objlist', 'flaglist', 'numberWanted', 'isAmbiguous', 'silent'];	# disambigDobj
	$Translate_Property_Argument[56] = ['actor', 'prep', 'dobj', 'verprop', 'wordlist', 'objlist', 'flaglist', 'numberWanted', 'isAmbiguous', 'silent'];	# disambigIobj
	$Translate_Property_Argument[57] = ['show', 'current_index', 'count', 'multi_flags'];	# prefixdesc
	#Builtin functions
	$Translate_Builtin[0]	= 'say'; 
	$Translate_Builtin[1]	= 'car'; 
	$Translate_Builtin[2]	= 'cdr'; 
	$Translate_Builtin[3]	= 'length'; 
	$Translate_Builtin[4]	= 'randomize'; 
	$Translate_Builtin[5]	= 'rand'; 
	$Translate_Builtin[6]	= 'substr'; 
	$Translate_Builtin[7]	= 'cvtstr'; 
	$Translate_Builtin[8]	= 'cvtnum'; 
	$Translate_Builtin[9]	= 'upper'; 
	$Translate_Builtin[10]	= 'lower'; 
	$Translate_Builtin[11]	= 'caps'; 
	$Translate_Builtin[12]	= 'find'; 
	$Translate_Builtin[13]	= 'getarg'; 
	$Translate_Builtin[14]	= 'datatype'; 
	$Translate_Builtin[15]	= 'setdaemon'; 
	$Translate_Builtin[16]	= 'setfuse'; 
	$Translate_Builtin[17]	= 'setversion'; 
	$Translate_Builtin[18]	= 'notify'; 
	$Translate_Builtin[19]	= 'unnotify'; 
	$Translate_Builtin[20]	= 'yorn'; 
	$Translate_Builtin[21]	= 'remfuse'; 
	$Translate_Builtin[22]	= 'remdaemon'; 
	$Translate_Builtin[23]	= 'incturn'; 
	$Translate_Builtin[24]	= 'quit'; 
	$Translate_Builtin[25]	= 'save'; 
	$Translate_Builtin[26]	= 'restore'; 
	$Translate_Builtin[27]	= 'logging'; 
	$Translate_Builtin[28]	= 'input'; 
	$Translate_Builtin[29]	= 'setit'; 
	$Translate_Builtin[30]	= 'askfile'; 
	$Translate_Builtin[31]	= 'setscore'; 
	$Translate_Builtin[32]	= 'firstobj'; 
	$Translate_Builtin[33]	= 'nextobj'; 
	$Translate_Builtin[34]	= 'isclass'; 
	$Translate_Builtin[35]	= 'restart';
	$Translate_Builtin[36]	= 'debugTrace'; 
	$Translate_Builtin[37]	= 'undo'; 
	$Translate_Builtin[38]	= 'defined'; 
	$Translate_Builtin[39]	= 'proptype'; 
	$Translate_Builtin[40]	= 'outhide'; 
	$Translate_Builtin[41]	= 'runfuses'; 
	$Translate_Builtin[42]	= 'rundaemons'; 
	$Translate_Builtin[43]	= 'gettime'; 
	$Translate_Builtin[44]	= 'getfuse'; 
	$Translate_Builtin[45]	= 'intersect'; 
	$Translate_Builtin[46]	= 'inputkey'; 
	$Translate_Builtin[47]	= 'objwords'; 
	$Translate_Builtin[48]	= 'addword'; 
	$Translate_Builtin[49]	= 'delword'; 
	$Translate_Builtin[50]	= 'getwords'; 
	$Translate_Builtin[51]	= 'nocaps'; 
	$Translate_Builtin[52]	= 'skipturn'; 
	$Translate_Builtin[53]	= 'clearscreen'; 
	$Translate_Builtin[54]	= 'firstsc'; 
	$Translate_Builtin[55]	= 'verbinfo'; 
	$Translate_Builtin[56]	= 'fopen'; 
	$Translate_Builtin[57]	= 'fclose'; 
	$Translate_Builtin[58]	= 'fwrite'; 
	$Translate_Builtin[59]	= 'fread'; 
	$Translate_Builtin[60]	= 'fseek'; 
	$Translate_Builtin[61]	= 'fseekeof'; 
	$Translate_Builtin[62]	= 'ftell'; 
	$Translate_Builtin[63]	= 'outcapture'; 
	$Translate_Builtin[64]	= 'systemInfo'; 
	$Translate_Builtin[65]	= 'morePrompt'; 
	$Translate_Builtin[66]	= 'parserSetMe'; 
	$Translate_Builtin[67]	= 'parserGetMe'; 
	$Translate_Builtin[68]	= 'reSearch'; 
	$Translate_Builtin[69]	= 'reGetGroup'; 
	$Translate_Builtin[70]	= 'inputevent'; 
	$Translate_Builtin[71]	= 'timeDelay'; 
	$Translate_Builtin[72]	= 'setOutputFilter'; 
	$Translate_Builtin[73]	= 'execCommand'; 
	$Translate_Builtin[74]	= 'parserGetObj'; 
	$Translate_Builtin[75]	= 'parseNounList'; 
	$Translate_Builtin[76]	= 'parserTokenize'; 
	$Translate_Builtin[77]	= 'parserGetTokTypes';
	$Translate_Builtin[78]	= 'parserDictLookup'; 
	$Translate_Builtin[79]	= 'parserResolveObjects';
	$Translate_Builtin[80]	= 'parserReplaceCommand'; 
	$Translate_Builtin[81]	= 'exitobj'; 
	$Translate_Builtin[82]	= 'inputdialog'; 
	$Translate_Builtin[83]	= 'resourceExists';
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
		if($line =~ m/(Action|Act)s?\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 					= $3;
			$Translate_Action[$2]		= $parsed;
		}
		if($line =~ m/(Object|Obj)s?\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 					= $3;
			$Translate_Object_Name[$2]		= $parsed;
		}
		if($line =~ m/(Object|Obj)s?[-_]?(Arg|Argument)?\[?(\d*)[.-](\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 									= $5;
			$Translate_Object_Argument[$3][$4 - 1]	= $parsed;
		}
		if($line =~ m/(Object|Obj)s?[-_]?(Loc|Local)?\[?(\d*)[.-](\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 									= $5;
			$Translate_Object_Local[$3][$4 - 1]		= $parsed;
		}
		if($line =~ m/(Property|Properties|Props|Prop)\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 					= $3;
			$Translate_Property[$2]		= $parsed;
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
sub generateMapping() {
	open($File_Mapping, "> :raw :bytes", $FileName_Path . $FileName_Generate)
		|| die "$0: can't open " . $FileName_Path . $FileName_Generate . "for writing: $!";
	print $File_Mapping "#Actions\n";
	for (my $action=0 ; $action<$#Translate_Action ; $action++) {
		print $File_Mapping '#' unless defined $Translate_Action[$action];
		print $File_Mapping "Action$action\t= '";
		print $File_Mapping nameAction($action) if defined $Translate_Action[$action];
		print $File_Mapping "'\n";
	}
	#Builtins are skipped on purpose
	print $File_Mapping "#Objects\n";
	for my $obj ( $Translate_Object_Start .. $#Translate_Object_Name) {
		if (defined $Translate_Object_Name[$obj]) {
			print $File_Mapping "Obj$obj\t= '" . nameObject($obj) . "'\n";
			if (defined $Translate_Object_Argument[$obj]) {
				for my $arg ( 0 .. $#{ $Translate_Object_Argument[$obj] } ) {
					print $File_Mapping "\tObjArg$obj-".($arg+1)."\t= '$Translate_Object_Argument[$obj][$arg]'\n" if defined $Translate_Object_Argument[$obj][$arg];
				}
			}
			if (defined $Translate_Object_Local[$obj]) {
				for my $loc ( 0 .. $#{ $Translate_Object_Local[$obj] } ) {
					print $File_Mapping "\tObjLoc$obj-".($loc+1)."\t= '$Translate_Object_Local[$obj][$loc]'\n" if defined $Translate_Object_Local[$obj][$loc];
				}
			}
		}
	}
	print $File_Mapping "#Properties\n";
	for my $prop ( $Translate_Property_Start .. $#Translate_Property) {
		if (defined $Translate_Property[$prop]) {
			print $File_Mapping "Prop$prop\t= '" . nameProperty($prop) . "'\n";
			if (defined $Translate_Property_Argument[$prop]) {
				for my $arg ( 0 .. $#{ $Translate_Property_Argument[$prop] } ) {
					print $File_Mapping "\tPropArg$prop-".($arg+1)."\t= '$Translate_Property_Argument[$prop][$arg]'\n" if defined $Translate_Property_Argument[$prop][$arg];
				}
			}
			if (defined $Translate_Property_Local[$prop]) {
				for my $loc ( 0 .. $#{ $Translate_Property_Local[$prop] } ) {
					print $File_Mapping "\tPropLoc$prop-".($loc+1)."\t= '$Translate_Property_Local[$prop][$loc]'\n" if defined $Translate_Property_Local[$prop][$loc];
				}
			}
		}
	}
	close $File_Mapping;
}
##File Handling
#Decrypts the block of text passed in
sub decrypt($) {
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
sub parseHeader() {
	#The header is 48 bytes long
	# 0-10	File header signature
	#11-12	Reserved but unused (?)
	#13-18	Compiler version (?)
	#19-20	Flags
	#   21	Unknown
	#22-45	Build date
	#46-47	Unknown
	my $block_header;
	my $bytes_read = read ($File_Bytecode, $block_header, $Size_Header);
	die "Unable to read file header" unless $bytes_read eq $Size_Header;
	#Check the signature
	my $signature	= substr($block_header, 0, $Size_Signature);
	die "$FileName_Bytecode is not a valid TADS file."
		unless	$signature eq $Signature_TADS2_Game
			||	$signature eq $Signature_TADS2_Res;
	#Parse the rest of the header
	my $unknown1		= unpack('S', substr($block_header, 11, 2));	# substr($block_header, 11, 2);
	$Version_Image		= substr($block_header, 13, 6);
	my $flags			= unpack('n', substr($block_header, 19, 2));	# Flags are stored as a bitmap, so read in as big-endian UINT-16
#	my $flags			= unpack('C', substr($block_header, 20, 1));	# Flags might be stored only in byte 19 though...
	my $unknown2		= unpack('C', substr($block_header, 21, 1));	# substr($block_header, 21, 1);
	$Timestamp_Image	= substr($block_header, 22, 24);
	my $unknown3		= unpack('S', substr($block_header, 46, 2));	# substr($block_header, 46, 2);
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
	print $File_Log "Decompiler v$Decompiler_Version on $FileName_Bytecode ";
	print $File_Log "(a TADS2-Game file)\n"		if $signature eq $Signature_TADS2_Game;
	print $File_Log "(a TADS2-Resource file)\n"	if $signature eq $Signature_TADS2_Res;
	print $File_Log "Compiled by $Version_Image at $Timestamp_Image\n";
	print $File_Log "\tUnknown 1: $unknown1\n"	if $Option_Verbose;
	print $File_Log "\tUnknown 2: $unknown2\n"	if $Option_Verbose;
	print $File_Log "\tUnknown 3: $unknown3\n"	if $Option_Verbose;
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
sub parseFile() {
	#The compiled file consists of several blocks of varying length.
	for (;;) {
		#Each block starts with a header of varying length
		my $size_type;	# 1 byte; size of the type field
		my $block_type;	# X bytes as defined by size_type; the type of data block
		my $next_block;	# 4 bytes; location of the next block.
		my $block_size;
		my $block;
		read ($File_Bytecode, $size_type, 1);
		read ($File_Bytecode, $block_type, unpack('C', $size_type));
		read ($File_Bytecode, $next_block, 4);
		$block_size	= unpack('L', $next_block) - tell($File_Bytecode);
		#Log the block type, and break out at the end of the file.
		print $File_Log "$block_type: $block_size bytes\n";
		last unless $block_size;
		#read the contents of the block and parse it
		if	($block_type eq '$EOF')		{ last }						# End of file marker; usually not reached due to negative size
		read ($File_Bytecode, $block, $block_size);
		if	($block_type eq 'XSI')		{ parseBlockXSI($block) }		# XOR Seed Information
		if	($block_type eq 'OBJ')		{ parseBlockOBJ($block) }		# OBJects
		#FST	Fast load information; does not contain anything useful for decompilation
		#INH	Inheritances; not parsed
		if	($block_type eq 'FMTSTR')	{ parseBlockFMTSTR($block) }	# Format Strings
		if	($block_type eq 'REQ')		{ parseBlockREQ($block) }		# REQuired (?)
		if	($block_type eq 'CMPD')		{ parseBlockCMPD($block) }		# CoMPounD words
		#SPECWORD
		if	($block_type eq 'VOC')		{ parseBlockVOC($block) }		# VOCabulary
		if	($block_type eq 'HTMLRES')	{ parseBlockRES($block) }		# Embedded (HTML) RESources
	}
}
#XSI blocks contains the XOR Seed Information for the compiled file.
sub parseBlockXSI($) {
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
	my $found	= 0;				# Number of objects found
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
		$found++;
		#Check type and stored
		if		($type eq 1) { # Function
			#Functions are just code, so we simply store it
			print $File_Log "\tObj$id: function ($size bytes)\n"	if $Option_Verbose;
			print $File_Log "\t\tUnknown is $unknown\n"				if $Option_Verbose && $size != $unknown;
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
			print $File_Log "\tObj$id: object ($size bytes) in $workspace with $superclasses parents and $properties properties\n"
				if $Option_Verbose;
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
				} unless $Constant_Property_Type[$prop_type] eq 'demand'; # Demand properties are useless and skipped
				print $File_Log "\t\tProp$prop_id ($prop_size bytes): $Constant_Property_Type[$prop_type] ($prop_flag)\n"
					if $Option_Verbose;
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
		}
	}
	print $File_Log "\tFound $found objects in total\n";
}
#ForMaT STRing block
sub parseBlockFMTSTR($) {
	my $block	= shift;
	my $length	= length($block);
	#FMTSTR has a sub-header which contains the size of the block.
	my $size	= unpack('S', substr($block, 0, 2));
	$block		= decrypt(substr($block, 2));
	warn "FMTSTR block contains unparsed space" unless $size eq ($length - 2);
	#Compounds are stored sequentially with no dividers or indication of how many there are;
	#We need to read the entire block sequentially.
	my $pos		= 0;
	my $found	= 0;
	while ($pos < $size) {
		my $prop	= unpack('S', substr($block, $pos, 2));
		my $size	= unpack('S', substr($block, $pos + 2, 2));
		my $text	= substr($block, $pos + 4, $size - 2);
		$pos		+= 2 + $size;
		my $prep_rename;
		my $prep_name					= uniformName('fmt '.$text);
		$Translate_Property[$prop]		= $prep_name unless defined $Translate_Property[$prop];
		$prep_rename					= 1		unless $prep_name eq $Translate_Property[$prop];
		print $File_Log	"\tProp$prop: $prep_name"			if $prep_rename || $Option_Verbose;
		print $File_Log "\t -> ".nameObject($prep_name)		if $prep_rename;
		print $File_Log	"\t($text)\n"						if $prep_rename || $Option_Verbose;
		my $format	= "'$text' " . nameProperty($prop);
		push @Formats, $format;
		$found++;
	}
	print $File_Log "\tFound $found formated strings\n";
}
#REQuired Functionality block
sub parseBlockREQ($) {
	my $block	= shift;
	my $length	= length($block);
	#Names and arguments for required functions are taken from detads by Daniel Schepler
	#Also used fio.c (from line 589)
	my @req_names	= [];
	$req_names[0]	= 'Me'; 
	$req_names[1]	= 'takeVerb'; 
	$req_names[2]	= 'strObj'; 
	$req_names[3]	= 'numObj'; 
	$req_names[4]	= 'pardon';
	$req_names[5]	= 'againVerb'; 
	$req_names[6]	= 'init'; 
	$req_names[7]	= 'preparse'; 
	$req_names[8]	= 'parseError';
	$req_names[9]	= 'commandPrompt'; 
	$req_names[10]	= 'parseDisambig'; 
	$req_names[11]	= 'parseError2';
	$req_names[12]	= 'parseDefault'; 
	$req_names[13]	= 'parseAskobj'; 
	$req_names[14]	= 'preparseCmd';
	$req_names[15]	= 'parseAskobjActor'; 
	$req_names[16]	= 'parseErrorParam'; 
	$req_names[17]	= 'commandAfterRead';
	$req_names[18]	= 'initRestore'; 
	$req_names[19]	= 'parseUnknownVerb'; 
	$req_names[20]	= 'parseNounPhrase';
	$req_names[21]	= 'postAction'; 
	$req_names[22]	= 'endCommand'; 
	$req_names[23]	= 'preCommand';
	$req_names[24]	= 'parseAskobjIndirect';
	$req_names[25]	= 'preparseExt';		# From fio.c
	$req_names[26]	= 'parseDefaultExt';	# From fio.c
	my @req_args	= [];
	$req_args[7]	= ['cmd'];							# preparse
	$req_args[8]	= ['num', 'str'];					# parseError
	$req_args[9]	= ['type'];							# commandPrompt
	$req_args[10]	= ['nameString', 'objList'];		# parseDisambig
	$req_args[11]	= ['verb', 'dobj', 'prep', 'iobj'];	# parseError2
	$req_args[12]	= ['obj', 'prep'];					# parseDefault
	$req_args[13]	= ['verb'];							# parseAskobj
	$req_args[14]	= ['wordList'];						# preparseCmd
	$req_args[15]	= ['actor', 'verb'];				# parseAskobjActor
	$req_args[16]	= ['num', 'str'];					# parseErrorParam
	$req_args[17]	= ['type'];							# commandAfterRead
	$req_args[19]	= ['actor', 'wordlist', 'typelist', 'errnum'];				# parseUnknownVerb
	$req_args[20]	= ['wordlist', 'typelist', 'currentIndex', 'complainOnNoMatch', 'isActorCheck'];	# parseNounPhrase
	$req_args[21]	= ['actor', 'verb', 'dobj', 'prep', 'iobj', 'status'];		# postAction
	$req_args[22]	= ['actor', 'verb', 'dobj_list', 'prep', 'iobj', 'status'];	# endCommand
	$req_args[23]	= ['actor', 'verb', 'dobj_list', 'prep', 'iobj'];			# preCommand
	$req_args[24]	= ['actor', 'verb', 'prep', 'objectList'];					# parseAskobjIndirect
	#Required functions are stored as an array of UINT16 pointing to the ID of the implementing object; 65535 as null value
	#Exactly how many there are depends on the version of TADS; we currently know the names of 25.
	my $found	= $length / 2;
	if ($found > $#req_names + 1) {
		my $message = "REQ: Found $found entries, only the first ". ($#req_names + 1) . " are processed";
		print $File_Log	"\t$message\n";
		warn $message;
		$found	= $#req_names + 1;
	}
	for my $i(0 .. $found - 1) {
		my $object	= unpack('S', substr($block, $i * 2, 2));
		unless ($object eq $Null_Value) {
			print $File_Log	"\t$i:\tObj$object\t($req_names[$i])\n" if $Option_Verbose;
			print $File_Log	"\t$i:\tObj$object is named $Translate_Object_Name[$object]\n"
				if defined $Translate_Object_Name[$object] 
					&& $Translate_Object_Name[$object] != $req_names[$i];
			$Translate_Object_Name[$object]			= $req_names[$i];
			print $File_Log	"\t$i:\tObj$object has arguments\n"
				if defined $Translate_Object_Argument[$object];
			$Translate_Object_Argument[$object]	= $req_args[$i] if defined $req_args[$i];
		}
	}
}
#CoMPounD word blocks contains contractions for the token parser
sub parseBlockCMPD($) {
	my $block	= shift;
	my $length	= length($block);
	#CMPD has a sub-header which contains the size of the block.
	my $size	= unpack('S', substr($block, 0, 2));
	$block		= decrypt(substr($block, 2));
	warn "CMPD block contains unparsed space" unless $size eq ($length - 2);
	#Compounds are stored sequentially with no dividers or indication of how many there are;
	#We need to read the entire block sequentially.
	my $pos		= 0;
	my $found	= 0;
	while ($pos < $size) {
		#Each CMPD record consists of 3 strings stored sequentially
		my $size1	= unpack('S', substr($block, $pos, 2));
		my $text1	= substr($block, $pos + 2, $size1 - 2);
		$pos		+= $size1;
		my $size2	= unpack('S', substr($block, $pos, 2));
		my $text2	= substr($block, $pos + 2, $size2 - 2);
		$pos		+= $size2;
		my $size3	= unpack('S', substr($block, $pos, 2));
		my $text3	= substr($block, $pos + 2, $size3 - 2);
		$pos		+= $size3;
		#Assemble and store the compound
		my $compound = "'$text1' '$text2' '$text3'";
		push @Compounds, $compound;
		$found++;
		print $File_Log	"\t$compound\n" if $Option_Verbose;
	}
	print $File_Log "\tFound $found compounds\n";
}
#VOCabulary blocks contain text properties that are used by the parser
sub parseBlockVOC($) {
	my $block	= shift;
	my $length	= length($block);
	#Vocabulary properties are stored sequentially with no dividers or indication of how many there are;
	#We need to read the entire block sequentially.
	my $pos			= 0;
	my $found		= 0;
	my $found_total	= 0;
	while ($pos < $length) {
		#Each VOC record has a 10 byte header:
		# 0-1	Size of first vocabulary token
		# 2-3	Size of second vocabulary token, 0 if not used
		# 4-5	Property ID
		# 6-7	Object ID
		# 8-9	Flags
		#		2: Inherited
		my $size1	= unpack('S', substr($block, $pos + 0, 2));
		my $size2	= unpack('S', substr($block, $pos + 2, 2));
		my $prop_id	= unpack('S', substr($block, $pos + 4, 2));
		my $obj_id	= unpack('S', substr($block, $pos + 6, 2));
		my $flag	= unpack('S', substr($block, $pos + 8, 2));
		unless($flag & 2) {	# Skip inherited VOCabulary
			$found++;
			# Decrypt and extract the text string(s)
			my $data	= decrypt(substr($block, $pos + 10, $size1+$size2));
			my $text	= substr($data, 0, $size1);
			$text		.= ' '.substr($data, $size1, $size2) if ($size2 > 0);
			# Store in object's vocabulary list
			die "Vocabulary for undefined Object: Obj$obj_id"	unless defined $Objects[$obj_id];
			$Objects[$obj_id]{vocabulary}			= {}		unless $Objects[$obj_id]{vocabulary};
			$Objects[$obj_id]{vocabulary}{$prop_id}	= []		unless defined $Objects[$obj_id]{vocabulary}{$prop_id};
			push @{ $Objects[$obj_id]{vocabulary}{$prop_id} }, $text;
#			print $File_Log "\tObj$obj_id.prop$prop_id\t= '$text'\n";
		}
		#Advance to next record
		$pos += 10 + $size1 + $size2;
		$found_total++;
	}
	print $File_Log "\tFound $found vocabulary records ($found_total including inherited)\n";
}
#RESource blocks contain embedded files
sub parseBlockRES($) {
	#The block is divided into three distinct parts:
	#* Header, defining number of entries and start of data area
	#* ToC with metadata for each entry
	#* Embedded data for each entry
	my $block	= shift;
	my $length	= length($block);
	#Block header
	# 4 Bytes: Number of entries
	# 4 Bytes: Offset to where data begins
	my $entries	= unpack('L', substr($block, 0, 4));
	my $offset	= unpack('L', substr($block, 4, 4));
	print $File_Log "\t$entries Entries\n";
	print 	"Extracting $entries Resources...\n" if $entries;
	#Read metadata and embedded data for each entry in one pass
	my $pos		= 8;
	for my $i (1 .. $entries) {
		#Metadata
		my $data_pos	= unpack('L', substr($block, $pos, 4));
		my $size		= unpack('L', substr($block, $pos + 4, 4));
		my $name_size	= unpack('S', substr($block, $pos + 8, 2));
		my $name		= substr($block, $pos + 10, $name_size);
		$pos += $name_size + 10;
		print $File_Log "\t$name ($size bytes) at $data_pos\n";
		#Embedded data, only read when not in minimal mode
		unless ($Option_Minimal) {
			my $path = $FileName_Path.(dirname $name);
			make_path($path);
			my $file_resource;
			open($file_resource, "> :raw :bytes", $FileName_Path . $name)
				|| die "$0: can't open $FileName_Path$name in write-open mode: $!";
			print $file_resource substr($block, $data_pos + $offset, $size);
			close $file_resource;
		}
	}
}
##Analyzing
sub analyze() {
	#Look for action definitions, and use those to name the related actions, objects and properties
	print $File_Log "Analyzing Actions\n";
	analyzeActions();
	#Look through the vocabulary and try to use that to name objects.
	#We do this after actions because the action naming often gives better results.
	print $File_Log "Analyzing Vocabulary\n";
	analyzeVocabulary();
	#Look through the function code, converting the bytecode into an array of instructions
	print $File_Log "Analyzing Function Code Segments\n";
	analyzeFunctionCode();
	#Look through the property code, converting the bytecode into an array of instructions
	print $File_Log "Analyzing Property Code Segments\n";
	analyzePropertyCode();
}
#Look through all objects, trying to find actions and verbs
sub analyzeActions() {
	#Actions aren't explicitly numbered so we keep a running tally
	my $action	= 0;
	for my $obj (0 .. $#Objects) {
		#Not all Object ID's are actually used
		next unless defined $Objects[$obj];
		#Not all objects have properties
		next unless defined $Objects[$obj]{properties};
		#Look through all properties
		for my $prop ( keys %{ $Objects[$obj]{properties} } ) {
			my $type	= $Objects[$obj]{properties}{$prop}{type};
			unless (defined $type) {
				print $File_Log "\tUnable to analyze $obj.$prop - Missing type";
				warn "Unable to analyze $obj.$prop - Missing type";
				next;
			}
			#TPL2 contains the action defintions we are looking for
			next unless $Constant_Property_Type[$type] eq 'tpl2';
			#As actions aren't numbered in the file, we store a reference from the property to the action for later use
			$Objects[$obj]{properties}{$prop}{action}	= $action;
			#Extract and analyze data
			my $data	= $Objects[$obj]{properties}{$prop}{data};
			unless (defined $data) {
				print $File_Log "\tUnable to analyze $obj.$prop - Missing data";
				warn "Unable to analyze $obj.$prop - Missing data";
				next;
			}
			my $header_needed			= 1;
			print $File_Log "\t$action\tObj$obj\n"			if $Option_Verbose;
			undef $header_needed							if $Option_Verbose;
			my $action_name	= nameAction($action);
			#Try to use the short description as name for action and verb (property id 8)
			if (defined $Objects[$obj]{properties}{8}) {
				#Name the action
				$action_name	= uniformName(propertyString($obj, 8));
				$Translate_Action[$action]	= $action_name			unless defined $Translate_Action[$action];
				#Name the verb
				my $verb_name	= $action_name."Verb";
				$Translate_Object_Name[$obj]		= $verb_name unless defined $Translate_Object_Name[$obj];
				#Log results
				my $action_rename;
				my $verb_rename;
				$action_rename				= 1 	unless $action_name eq $Translate_Action[$action];
				$verb_rename				= 1		unless $verb_name eq $Translate_Object_Name[$obj];
				print $File_Log "\t$action\tObj$obj\n"			if ($verb_rename || $action_rename) && $header_needed;
				print $File_Log	"\t\tAction: $action_name"		if $action_rename || $Option_Verbose;
				print $File_Log "\t -> ".nameAction($action)	if $action_rename;
				print $File_Log	"\n"							if $action_rename || $Option_Verbose;
				print $File_Log "\t$action\tObj$obj\n"			if $verb_rename && $header_needed;
				print $File_Log	"\t\tObject: $verb_name"		if $verb_rename || $Option_Verbose;
				print $File_Log "\t -> ".nameObject($obj)		if $verb_rename;
				print $File_Log	"\n"							if $verb_rename || $Option_Verbose;
				undef $header_needed							if $verb_rename || $action_rename;
			}
			#Mapping of action properties for prepositions
			my $templates	= ord(substr($data, 0));
			for (my $i=0 ; $i < $templates ; $i++) {
				#Read identifiers for template
				my $prep_obj	= unpack('S', substr($data, $i * 16 + 1, 2));	# Preposition object
				my $ver_io_prop	= unpack('S', substr($data, $i * 16 + 3, 2));	# IndrectObject verify property
				my $exc_io_prop	= unpack('S', substr($data, $i * 16 + 5, 2));	# IndrectObject execute property
				my $ver_do_prop	= unpack('S', substr($data, $i * 16 + 7, 2));	# DirectObject verify property
				my $exc_do_prop	= unpack('S', substr($data, $i * 16 + 9, 2));	# DirectObject execute property
				#5 extra bytes at the end, which seems to be at least in part flag data.
				#Try to rename the preposition object
				my $prep_name;
				my $subheader_needed	= 1;
				unless ($prep_obj eq $Null_Value) { #No preposition
					#Rename object
					$prep_name							= uniformName(propertyString($prep_obj, 8) . ' Prep');
					$Translate_Object_Name[$prep_obj]	= $prep_name	unless defined $Translate_Object_Name[$prep_obj];
					#Log results
					my $rename;
					$rename							= 1				unless $prep_name eq $Translate_Object_Name[$prep_obj];
					print $File_Log "\t$action\tObj$obj\n"					if $rename && $header_needed;
					print $File_Log	"\t\t$prep_name($prep_obj):"			if $rename || $Option_Verbose;
					print $File_Log "\t -> ".nameObject($prep_name)			if $rename;
					print $File_Log	"\n"									if $rename || $Option_Verbose;
					undef $header_needed									if $rename;
					undef $subheader_needed									if $rename || $Option_Verbose;
				}
				if ($ver_io_prop) { #Indirect Object Verification
					#Property Arguments
					@{ $Translate_Property_Argument[$ver_io_prop] }	= ('actor');
					#Property Rename
					my $name	= uniformName('Ver Io '.$action_name);
					$Translate_Property[$ver_io_prop]	= $name		unless defined $Translate_Property[$ver_io_prop];
					#Property-Action Mapping
					$Property_Actions{$ver_io_prop}		= $action	unless defined $Property_Actions{$ver_io_prop};
					#Log results
					my $rename;
					my $mapping;
					$rename							= 1		unless $name	eq $Translate_Property[$ver_io_prop];
					$mapping						= 1		unless $action	eq $Property_Actions{$ver_io_prop};
					print $File_Log "\t$action\tObj$obj\n"					if ($rename || $mapping) && $header_needed;
					print $File_Log	"\t\t$prep_name:\n"						if $subheader_needed && $prep_obj != $Null_Value
																				&& ($rename || $mapping || $Option_Verbose);
					print $File_Log	"\t\tNoPrep:\n"							if $subheader_needed && $prep_obj eq $Null_Value
																				&& ($rename || $mapping || $Option_Verbose);
					print $File_Log	"\t\t\t$ver_io_prop\tVerIo\t$name"		if $rename || $mapping || $Option_Verbose;
					print $File_Log "\t -> ".nameProperty($ver_io_prop)		if $rename || $mapping;
					print $File_Log	"\n"									if $rename || $mapping || $Option_Verbose;
					undef $header_needed									if $rename || $mapping;
					undef $subheader_needed									if $rename || $mapping || $Option_Verbose;
				}
				if ($exc_io_prop) { #Indirect Object Execution
					#Property Arguments
					@{ $Translate_Property_Argument[$exc_io_prop] }	= ('actor', 'dobj');
					#Property Rename
					my $name	= uniformName('Io '.$action_name);
					$Translate_Property[$exc_io_prop]	= $name		unless defined $Translate_Property[$exc_io_prop];
					#Property-Action Mapping
					$Property_Actions{$exc_io_prop}		= $action	unless defined $Property_Actions{$exc_io_prop};
					#Log results
					my $rename;
					my $mapping;
					$rename							= 1		unless $name	eq $Translate_Property[$exc_io_prop];
					$mapping						= 1		unless $action	eq $Property_Actions{$exc_io_prop};
					print $File_Log "\t$action\tObj$obj\n"					if ($rename || $mapping) && $header_needed;
					print $File_Log	"\t\t$prep_name:\n"						if $subheader_needed && $prep_obj != $Null_Value
																				&& ($rename || $mapping || $Option_Verbose);
					print $File_Log	"\t\tNoPrep:\n"							if $subheader_needed && $prep_obj eq $Null_Value
																				&& ($rename || $mapping || $Option_Verbose);
					print $File_Log	"\t\t\t$exc_io_prop\tIo\t$name"		if $rename || $mapping || $Option_Verbose;
					print $File_Log "\t -> ".nameProperty($exc_io_prop)		if $rename || $mapping;
					print $File_Log	"\n"									if $rename || $mapping || $Option_Verbose;
					undef $header_needed									if $rename || $mapping;
					undef $subheader_needed									if $rename || $mapping || $Option_Verbose;
				}
				if ($ver_do_prop) { #Direct Object Verification
					#Property Arguments
					@{ $Translate_Property_Argument[$ver_do_prop] }	= ('actor', 'iobj')	if ($exc_io_prop);
					@{ $Translate_Property_Argument[$ver_do_prop] }	= ('actor')		unless ($exc_io_prop);
					#Property Rename
					my $name	= uniformName('Ver Do '.$action_name);
					$Translate_Property[$ver_do_prop]	= $name		unless defined $Translate_Property[$ver_do_prop];
					#Property-Action Mapping
					$Property_Actions{$ver_do_prop}		= $action	unless defined $Property_Actions{$ver_do_prop};
					#Log results
					my $rename;
					my $mapping;
					$rename							= 1		unless $name	eq $Translate_Property[$ver_do_prop];
					$mapping						= 1		unless $action	eq $Property_Actions{$ver_do_prop};
					print $File_Log "\t$action\tObj$obj\n"					if ($rename || $mapping) && $header_needed;
					print $File_Log	"\t\t$prep_name:\n"						if $subheader_needed && $prep_obj != $Null_Value
																				&& ($rename || $mapping || $Option_Verbose);
					print $File_Log	"\t\tNoPrep:\n"							if $subheader_needed && $prep_obj eq $Null_Value
																				&& ($rename || $mapping || $Option_Verbose);
					print $File_Log	"\t\t\t$ver_do_prop\tVerDo\t$name"		if $rename || $mapping || $Option_Verbose;
					print $File_Log "\t -> ".nameProperty($ver_do_prop)		if $rename || $mapping;
					print $File_Log	"\n"									if $rename || $mapping || $Option_Verbose;
					undef $header_needed									if $rename || $mapping;
					undef $subheader_needed									if $rename || $mapping || $Option_Verbose;

				}
				if ($exc_do_prop) { #Direct Object Execution
					#Property Arguments
					@{ $Translate_Property_Argument[$exc_do_prop] }	= ('actor', 'iobj')	if ($exc_io_prop);
					@{ $Translate_Property_Argument[$exc_do_prop] }	= ('actor')		unless ($exc_io_prop);
					#Property Rename
					my $name	= uniformName('Do '.$action_name);
					$Translate_Property[$exc_do_prop]	= $name		unless defined $Translate_Property[$exc_do_prop];
					#Property-Action Mapping
					$Property_Actions{$exc_do_prop}		= $action	unless defined $Property_Actions{$exc_do_prop};
					#Log results
					my $rename;
					my $mapping;
					$rename							= 1		unless $name	eq $Translate_Property[$exc_do_prop];
					$mapping						= 1		unless $action	eq $Property_Actions{$exc_do_prop};
					print $File_Log "\t$action\tObj$obj\n"					if ($rename || $mapping) && $header_needed;
					print $File_Log	"\t\t$prep_name:\n"						if $subheader_needed && $prep_obj != $Null_Value
																				&& ($rename || $mapping || $Option_Verbose);
					print $File_Log	"\t\tNoPrep:\n"							if $subheader_needed && $prep_obj eq $Null_Value
																				&& ($rename || $mapping || $Option_Verbose);
					print $File_Log	"\t\t\t$exc_do_prop\tDo\t$name"		if $rename || $mapping || $Option_Verbose;
					print $File_Log "\t -> ".nameProperty($exc_do_prop)		if $rename || $mapping;
					print $File_Log	"\n"									if $rename || $mapping || $Option_Verbose;
					undef $header_needed									if $rename || $mapping;
					undef $subheader_needed									if $rename || $mapping || $Option_Verbose;
				}
			}
			$action++;
		}
	}
}
#Look through the vocabulary of each object to see if we find a suitable name
sub analyzeVocabulary() {
	#There are four properties we use for naming:
	#2: Verb
	#3: Noun
	#4: Adjective
	#5: Preposition
	#Each can have several string tokens associated, so we take the longest one
	for my $obj (0 .. $#Objects) {
		#Not all Object ID's are actually used
		next unless defined $Objects[$obj];
		#Not all objects have vocabulary
#		next unless defined $Objects[$obj]{vocabulary};
		my $name;
		#First priority is to use the verb
		my $verb_token;
		$verb_token	= bestVocabularyToken($obj, 2, 1)		unless defined $name;
		$name		= uniformName($verb_token . " Verb")	if defined $verb_token;
		#Second priority is to use the preposition
		my $prep_token;
		$prep_token	= bestVocabularyToken($obj, 5, 1)		unless defined $name;
		$name		= uniformName($prep_token . " Prep")	if defined $prep_token;
		#Try to use the adjective and noun, if we are aggressive on name search
		if ($Option_Naming && not defined $name) {
			my $token_noun;
			$token_noun	= bestVocabularyToken($obj, 3, 1);
			my $token_adj;
			$token_adj	= bestVocabularyToken($obj, 4, 1);
			$token_adj	= ''	unless defined $token_adj;
			$name	= uniformName($token_adj . ' ' . $token_noun)	if defined $token_noun;
		}
		#No naming alternatives available
		next unless defined $name;
		
		my $rename;
		$Translate_Object_Name[$obj]	= $name unless defined $Translate_Object_Name[$obj];
		$rename							= 1		unless $name eq $Translate_Object_Name[$obj];
		print $File_Log	"\tObj$obj: $name"			if $rename || $Option_Verbose;
		print $File_Log "\t -> ".nameObject($obj)	if $rename;
		print $File_Log	"\n"						if $rename || $Option_Verbose;
	}
}
#Look through all objects, analyzing the code segments of function objects
sub analyzeFunctionCode() {
	for my $obj (0 .. $#Objects) {
		#Not all Object ID's are actually used
		next unless defined $Objects[$obj];
		#Not all objects have properties
		next unless $Objects[$obj]{type} eq 1;
		my $codeblock = $Objects[$obj]{code};
		if (defined $Objects[$obj]{decoded}) {
			print $File_Log "\tObj$obj\tCode already analyzed\n";
			warn "$obj: Code already analyzed";
			return;
		}	
		$Objects[$obj]{instructions}	= analyzeCodeblock(-$obj, $codeblock);	# Note the negative ID for object function code
	}
}
#Look through all objects, analyzing the code segments of code properties
sub analyzePropertyCode() {
	for my $obj (0 .. $#Objects) {
		#Not all Object ID's are actually used
		next unless defined $Objects[$obj];
		#Not all objects have properties
		next unless defined $Objects[$obj]{properties};
		#Look through all properties
		for my $prop ( keys %{ $Objects[$obj]{properties} } ) {
			my $type	= $Objects[$obj]{properties}{$prop}{type};
			unless (defined $type) {
				print $File_Log "\tUnable to analyze $obj.$prop - Missing type";
				warn "Unable to analyze $obj.$prop - Missing type";
				next;
			}
			#Look for code properties
			next unless $Constant_Property_Type[$type] eq 'code';
			my $codeblock = $Objects[$obj]{properties}{$prop}{data};
			unless (defined $codeblock) {
				print $File_Log "\tUnable to analyze $obj.$prop - Missing data";
				warn "Unable to analyze $obj.$prop - Missing data";
				next;
			}
			if (defined $Objects[$obj]{properties}{$prop}{decoded}) {
				print $File_Log "\tProp$prop:\tCode already analyzed\n";
				warn "$prop: Code already analyzed";
				next;
			}
			$Objects[$obj]{properties}{$prop}{instructions}	= analyzeCodeblock($prop, $codeblock);	# Note the positive ID for property code
		}
	}
}
#Analyzes the bytecode and stores the result as easier-to-handle opcodes, which can then be printed
sub analyzeCodeblock($$) {
	my $id					= shift;	# Negative for object functions, positive for property code
	my $codeblock			= shift;
	#We store the analyzed code as an array of hashes
	my @instructions		= ();
	#Bytecode has no stored structure and has to be parsed sequentially.
	#Some codes have embedded payload which alters the size
	my $pos					= 0;
	my $length				= length $codeblock;
	#There are also some areas that shouldn't be parsed, mainly the switch tables
	my @exclusion_intervals	= ();
	my $exclusion_start		= $length;
	my $exclusion_end		= $length;
	#Make a log header if needed
	print $File_Log	"\tObj".(-$id).":\t$length\n"	if $id < 0 && defined $Option_Verbose;
	print $File_Log	"\tProp$id:\t$length\n"			if $id > 0 && defined $Option_Verbose;
	while ($pos < $length) {
		my %instruction	= %{ analyzeOpcode($id, $codeblock, $pos) };
		push @instructions, \%instruction;
		#Read the opcode
		my $opcode	= $instruction{opcode};
		my $size	= $instruction{size};
		my $payload	= arrayString($instruction{payload});
		#All valid opcodes below 192 are defined in the Constant_Opcode list
		unless (defined $Constant_Opcode[$opcode] || $opcode >= 192) {
			my $bytes = $length - ($pos + $size);
			print $File_Log	"\tObj".(-$id)."\n"	if $id < 0 && not defined $Option_Verbose;
			print $File_Log	"\tProp$id\n"		if $id > 0 && not defined $Option_Verbose;
			print $File_Log	"\t\t$pos\tUnknown opcode $opcode - possible junk code ($bytes/$length left)\n";
#			debug($codeblock)					if defined $Option_Verbose;
			return \@instructions;
		}
		print $File_Log	"\t\t$pos\t$opcode - $Constant_Opcode[$opcode] ($size bytes):\t$payload\n"	if $Option_Verbose && $opcode < 192;
		print $File_Log	"\t\t$pos\t$opcode - Assignment ($size bytes)\n"	if $Option_Verbose && $opcode >= 192;
		$pos += $size;
		#If we got a switch table, remember to skip over it later on.
		if ($opcode eq 0x4B) {
			my $start	= $instruction{switch_start};
			my $end		= $instruction{switch_end};
			push @exclusion_intervals, {
				start	=> $start,
				end		=> $end
			};
			if ($exclusion_start > $start){
				$exclusion_start	= $start;
				$exclusion_end		= $end;
			}
			print $File_Log	"\t\t\t($start - $end)\n"	if $Option_Verbose;
		}
		#See if we have to skip
		if ($pos >= $exclusion_start){
			#Update position
			$pos	= $exclusion_end;
			#Update next exclusion interval
			my $next_exclusion_start	= $length;
			my $next_exclusion_end		= $length;
			foreach my $ref (@exclusion_intervals){
				my %interval	= %{ $ref };
				if ($exclusion_start < $interval{start} && $interval{start} < $next_exclusion_start){
					$next_exclusion_start	= $interval{start};
					$next_exclusion_end		= $interval{end};
				}
			}
			$exclusion_start	= $next_exclusion_start;
			$exclusion_end		= $next_exclusion_end;
		}
	}
	return \@instructions;
}
#Analyzes a codeblock at a given position to find the resulting instruction
#Called recursively for SWITCH statements.
sub analyzeOpcode($$$);
sub analyzeOpcode($$$) {
	my $id			= shift;	# Negative for object functions, positive for property code
	my $codeblock	= shift;
	my $pos			= shift;
	my $opcode		= ord(substr($codeblock, $pos));
	my $size		= 1;	# The size of the current instruction including embedded payload
	my @payload		= ();
	my %instruction	= ();
	$instruction{pos}		= $pos;
	$instruction{opcode}	= $opcode;
	$instruction{name}		= $Constant_Opcode[$opcode];
	#Opcodes 192 and above are reserved for assignment, which is handled in a special way
	if ($opcode < 192) {
		#Some tads compilations contain unused "junk code"
		#If we find unknown opcodes we have to stop gracefully
		#Read embedded payload
		my @templates	= ();
		@templates		= @{ $Constant_Opcode_Payload[$opcode] } if defined $Constant_Opcode_Payload[$opcode];
		foreach my $template (@templates) {
			if	  ($template eq 'UNKNOWN') {
				#Payload is unknown for this opcode
				#We delay raising an error, as this might come from 'junk code' that is never called
				push @payload, 'UNKNOWN';
			}
			elsif ($template eq 'INT32') {
				#Number embedded as INT32
				my $value	= unpack('l', substr($codeblock, $pos + $size, 4));
				$size+=4;
				push @payload, $value;
			}
			elsif ($template eq 'UINT16') {
				#Number embedded as UINT16
				my $value	= unpack('S', substr($codeblock, $pos + $size, 2));
				$size+=2;
				push @payload, $value;
			}
			elsif ($template eq 'UINT8') {
				#Number embedded as UINT8
				my $value	= ord(substr($codeblock, $pos + $size, 1));
				$size++;
				push @payload, $value;
			}
			elsif ($template eq 'OBJECT') {
				#Object ID stored as UINT16
				my $value	= decodeProperty(2, substr($codeblock, $pos + $size, 2));
				$size+=2;
				push @payload, $value;
			}
			elsif ($template eq 'FUNCTION') {
				#Object ID stored as UINT16
				my $value	= decodeProperty(10, substr($codeblock, $pos + $size, 2));
				$size+=2;
				push @payload, $value;
			}
			elsif ($template eq 'PROPERTY') {
				#Property ID stored as UINT16
				my $value	= decodeProperty(13, substr($codeblock, $pos + $size, 2));
				$size+=2;
				push @payload, $value;
			}
			elsif ($template eq 'POINTER') {
				#Property ID stored as UINT16
				my $value	= '&'.decodeProperty(13, substr($codeblock, $pos + $size, 2));
				$size+=2;
				push @payload, $value;
			}
			elsif ($template eq 'LOCAL') {
				#Local variable ID stored as INT16
				my $value	= nameLocal($id, unpack('s', substr($codeblock, $pos + $size, 2)));
				$size+=2;
				push @payload, $value;
			}
			elsif ($template eq 'BUILTIN') {
				#Builtin macro ID stored as UINT16
				my $value	= nameBuiltin(unpack('S', substr($codeblock, $pos + $size, 2)));
				$size+=2;
				push @payload, $value;
			}
			elsif ($template eq 'OFFSET') {
				#Address in code block, stored as relative location in INT16
				my $value	= unpack('s', substr($codeblock, $pos + $size, 2));
				$value		+= $pos + $size if defined $value;
				$size		+= 2;
				push @payload, $value;
			}
			elsif ($template eq 'STRING') {
				#String stored as a UINT16 denoting the total length
				my $length	= unpack('S', substr($codeblock, $pos + $size, 2));
				my $value	= '';
				$value		= decodeProperty(9, substr($codeblock, $pos + $size, $length)) if defined $length;
				$size+=$length if defined $length;
				push @payload, $value;
			}
			elsif ($template eq 'LIST') {
				#List stored as a UINT16 denoting the total length
				my $length	= unpack('S', substr($codeblock, $pos + $size, 2));
				#Code for handling junk code that's interpreted as OPCPUSHLST (0x20)
				my $value	= '[LISTERROR]';
				$value		= decodeProperty(7, substr($codeblock, $pos + $size, $length)) unless $pos + $length > length $codeblock;
				$size+=$length;
				push @payload, $value;
			}
			elsif ($template eq 'FRAME') {
				#Debug frame, stored as UINT16 denoting the total length.
				#Skipped in full.
				my $length	= unpack('S', substr($codeblock, $pos + $size, 2));
				$size+=$length;
			}
			elsif ($template eq 'SWITCH') {
				#Switch table at offset position
				my $offset	= unpack('S', substr($codeblock, $pos + $size, 2));
				my $subpos	= $pos + $size + $offset;
				$size+=2;
				#Read Switch table
				#UINT16		n Entries
				#n times:
				#	OPCODE
				#	INT16 Offset
				#INT16	Default offset
				$instruction{switch_start}	= $subpos;
				my $entries	= unpack('S', substr($codeblock, $subpos, 2));
				$subpos+=2;
				for (my $entry=0 ; $entry<$entries ; $entry++){
					my %switch_op		= %{ analyzeOpcode($id, $codeblock, $subpos) };
					$subpos				+= $switch_op{size};
					$switch_op{target}	= $subpos + unpack('s', substr($codeblock, $subpos, 2));
					$subpos+=2;
					push @payload, \%switch_op;
				}
				$instruction{switch_default}	= $subpos + unpack('s', substr($codeblock, $subpos, 2));
				$subpos+=2;
				$instruction{switch_end}	= $subpos;
			}
			elsif ($template eq 'UNKNOWN2') {
				#Payload of known size but unknown function; skipped
				my $value	= unpack('s', substr($codeblock, $pos + $size, 2));
				$size+=2;
			}
			else{
				die "Unhandled payload $template for opcode $opcode" unless $template eq 'NONE';
			}
		}
	}
	else {
		#Assignment opcodes are handled as a bitflag
		if    (($opcode & 0x03) eq 0x00){
			#Local ID embedded as INT16
			my $value	= nameLocal($id, unpack('s', substr($codeblock, $pos + $size, 2)));
			$size+=2;
			push @payload, $value;
		}
		elsif (($opcode & 0x03) eq 0x01){
			#Object ID embedded as INT16
			my $value	= nameObject(unpack('s', substr($codeblock, $pos + $size, 2)));
			$size+=2;
			push @payload, $value;
		}
		if    (($opcode & 0x03) eq 0x1c) {
			#Extended opcode
			my $value	= ord(substr($codeblock, $pos + $size, 1));
			$size++;
			push @payload, $value;
		}
		return {
			pos		=> $pos,
			opcode	=> $opcode,
			size	=> $size,
			payload	=> \@payload
		};
	}
	$instruction{size}		= $size,
	$instruction{payload}	= \@payload;
	return \%instruction;
}
#Find the best (currently: longest) vocabulary token for an object, with optional recursion
sub bestVocabularyToken($$;$);
sub bestVocabularyToken($$;$) {
	my $obj		= shift;
	my $voc		= shift;
	my $recurse	= shift;
	my $best_token;
	if	(defined $Objects[$obj]{vocabulary}{$voc}) {
		my @tokens	= @{ $Objects[$obj]{vocabulary}{$voc} };
		foreach my $token (@tokens) {
			$best_token = $token unless defined $best_token && length($best_token)>length($token);
		}
	}
	#Only look recursively if we don't have a token yet
	if ($recurse && not defined $best_token) {
		my @parents	= ();
		@parents	= @{ $Objects[$obj]{superclass} } if defined $Objects[$obj]{superclass};
		#Do a width-first search:
		foreach my $parent (@parents) {
			my $token = bestVocabularyToken($parent, $voc);
			$best_token = $token unless defined $best_token && defined $token && length($best_token) > length($token);
		}
		#Only recursive further if we don't find a match.
		unless (defined $best_token) {
			foreach my $parent (@parents) {
				my $token = bestVocabularyToken($parent, $voc, $recurse+1);
				$best_token = $token unless defined $best_token && defined $token && length($best_token) > length($token);
			}
		}
	}
	return $best_token;
}
#Convert text into uniform naming without spaces or quotes
sub uniformName($) {
	my $text	= lc(shift);				# Lower case
	$text		=~ s/\s+/ /;				# Convert all whitespace to spaces, and trim multiples
	$text		=~ s/[-_'\"]//g;				# Trim all unwanted characters
	$text		=~ s/^\s+|\s+$//g;			# Trim leading/trailing whitespace
	$text		=~ s/ (.)/uc($1)/ge;		# Remove spaces, capitalizing the next letter
	return $text;
}
#Converts a property of a given object to a string
sub propertyString($$) {
	my $obj		= shift;
	my $prop	= shift;
	die "propertyString needs both Object and Property id"		unless defined $obj && defined $prop;
	die "Can't access property $prop on undefined object $obj"	unless defined $Objects[$obj];
	my $type	= $Objects[$obj]{properties}{$prop}{type};
	my $data	= $Objects[$obj]{properties}{$prop}{data};
	unless (defined $type && defined $data) {
		warn "Unable to convert Obj$obj.Prop$prop to string; missing type or data";
		return 'Obj$obj.Prop$prop (ERROR)';
	}
	#Hand over the working to the decoding function
	return decodeProperty($type, $data);
}
#Converts an array into a comma-separated string with an optional value delimiter
sub arrayString($;$) {
	my $listref		= shift;
	my $delimiter	= shift;
	$delimiter		= '' unless defined $delimiter;
	my @list		= @{ $listref };
	my $text = '';
	for my $i (0 .. $#list) {
		my $item	= 'ERROR-NIL';
		$item		= $list[$i] if defined $list[$i];
		$text		.= ', ' if $i > 0;
		$text		.= "$delimiter$item$delimiter";
	}
	return $text;
}
#Decode a property given it's type; lists need to be interpreted recursively
sub decodeProperty($$);
sub decodeProperty($$) {
	my $type	= shift;
	my $data	= shift;
	croak "Can't decode without type"	unless defined $type;
	croak "Can't decode empty data"		unless defined $data;
	#Default value is the name of the property; This covers:
	# 4	BASEPTR
	# 5	NIL		type is the same as value
	# 6	CODE	Code is too long to print; use decodeCode for detailed code breakdown
	# 8	TRUE	type is the same as value
	#11	TPL
	#14	DEMAND
	#15	SYNONYM
	#16	REDIR
	#17	TPL2
	my $text	= $Constant_Property_Type[$type];
	if ($text eq 'number')		{ $text	= unpack('l', $data) }							# 1
	if ($text eq 'object')		{ $text	= nameObject(unpack('S', $data)) }				# 2
	if ($text eq 's-string')	{ $text	= "'".substr($data, 2)."'" }					# 3
	if ($text eq 'd-string')	{ $text	= '"'.substr($data, 2).'"' }					# 9
	if ($text eq 'fnaddr')		{ $text	= '&'.nameObject(unpack('S', $data)) }			# 10
	if ($text eq 'property')	{ $text	= nameProperty(unpack('S', $data)) }			# 13
	#Lists (7) require some special handling, as they are recursive
	if ($text eq 'list') {
		#Only the total size is given; each entry has to be read sequentially from the start.
		my @entries;
		my $size	= unpack('S', substr($data, 0, 2));
		my $pos		= 2;
		while ($pos < $size) {
			my $entry_type	=	ord(substr($data, $pos));
			my $entry_data;
			my $entry_size;
			$pos++;	# Adjust for typecode
			if 		($Constant_Property_Type[$entry_type] eq 'number') {
				#Fixed 1 + 4 byte size
				$entry_data	= substr($data, $pos, 4);
				$entry_size	= 4;
			}
			elsif (	$Constant_Property_Type[$entry_type] eq 'object'
				||	$Constant_Property_Type[$entry_type] eq 'fnaddr'
				||	$Constant_Property_Type[$entry_type] eq 'property') {
				#Fixed 1 + 2 byte size
				$entry_data	= substr($data, $pos, 2);
				$entry_size	= 2;
			}
			elsif (	$Constant_Property_Type[$entry_type] eq 'nil'
				||	$Constant_Property_Type[$entry_type] eq 'true') {
				#Fixed 1 + 0 byte size
				$entry_size	= 0;
				$entry_data	= '';
			}
			elsif (	$Constant_Property_Type[$entry_type] eq 's-string'
				||	$Constant_Property_Type[$entry_type] eq 'd-string'
				||	$Constant_Property_Type[$entry_type] eq 'list') {
				#Variable size;
				#We need to peek into the element to find the size;
				#Remember to *not* chop off the size
				$entry_size 	= unpack('S', substr($data, $pos, 2));
				$entry_data		= substr($data, $pos, $entry_size);
			}
			else {
				die "Illegal list entry: $Constant_Property_Type[$entry_type] ($entry_type)";
			}
			$pos 	+= $entry_size;
			push @entries, decodeProperty($entry_type, $entry_data);
		}
		$text = "[".arrayString(\@entries)."]";
	}
	return $text;
}
##Output
#Generate and print the corresponding TADS source code
sub printSource() {
	print $File_Sourcecode "//Source generated by v$Decompiler_Version of tads2 decompiler by Fictitious Frode\n";
	print $File_Sourcecode "//Based on $FileName_Bytecode compiled by $Version_Image at $Timestamp_Image\n";
	#TODO: formatstrings
	#TODO: compoundwords
	#TODO: specialwords
	#Print objects, one type at a time
	print $File_Sourcecode "\n\n//\t## Function Definitions ##\n";
	#Forward-declare all functions, with naming
	for my $obj (0 .. $#Objects) {
		next unless( defined $Objects[$obj]);	#Not all objects are used
		my $type	= $Objects[$obj]{type};
		print $File_Sourcecode nameObject($obj) . ": function;\n"			if ($type eq 1);	# Functions
		print $File_Sourcecode "\t//\tObj$obj\t = '".nameObject($obj)."'\n"	if ($type eq 1);	# Functions
	}
	print $File_Sourcecode "\n\n//\t## Function Source ##\n";
	print $File_Log "Printing Function Source\n";
	for my $obj (0 .. $#Objects) {
		next unless( defined $Objects[$obj]);	#Not all objects are used
		my $type	= $Objects[$obj]{type};
		printInstructions(-$obj, $Objects[$obj]{instructions})				if ($type eq 1);	# Functions
	}
	print $File_Log "Printing Object Source\n";
	print $File_Sourcecode "\n\n//\t## Objects ##\n";
	for my $obj (0 .. $#Objects) {
		next unless( defined $Objects[$obj]);	#Not all objects are used
		my $type	= $Objects[$obj]{type};
		printObjectSource($obj)		if ($type eq 2);	# Meta-Objects
	}
}
#Generate and print the source for a meta-object 
sub printObjectSource($) {
	my $obj	= shift;
	#Object header
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
	#Vocabulary properties
	if (defined $Objects[$obj]{vocabulary}) {
		my $count = keys %{ $Objects[$obj]{vocabulary} };
		print $File_Sourcecode "\t// $count vocabulary items\n"		if $count;
		for my $voc ( sort {$a <=> $b} keys %{ $Objects[$obj]{vocabulary} } ) {
			my $name	= nameProperty($voc);
			my $tokens	= arrayString($Objects[$obj]{vocabulary}{$voc}, "'");
			print $File_Sourcecode "\t$name\t= $tokens\n";
		}
	}
	#Data properties
	if (defined $Objects[$obj]{properties}) {
		my $count = keys %{ $Objects[$obj]{properties} };
		print $File_Sourcecode "\t// $count properties\n";
		for my $prop ( sort {$a <=> $b} keys %{ $Objects[$obj]{properties} } ) {
			my $prop_type	= $Objects[$obj]{properties}{$prop}{type};
			my $prop_data	= $Objects[$obj]{properties}{$prop}{data};
			unless (defined $prop_type ) {
				warn "Undefined type for $obj.$prop (".nameObject($obj).'.'.nameProperty($prop).')';
				next;
			}
			unless (defined $prop_data ) {
				warn "Undefined data for $obj.$prop (".nameObject($obj).'.'.nameProperty($prop).')';
				next;
			}
			if		($Constant_Property_Type[$prop_type] eq 'demand') {
				next;	# This property is nothing to print
			}
			elsif	($Constant_Property_Type[$prop_type] eq 'synonym') {
				my $property_target	= unpack('S', $prop_data);
				my $action_type		= substr(nameProperty($prop), 0, 2);
				if (defined $Property_Actions{$prop} && defined $Property_Actions{$property_target}){
					my $action_target	= nameAction($Property_Actions{$property_target});
					my $action_this		= nameAction($Property_Actions{$prop});				
					undef $action_type	unless $action_type eq 'do' || $action_type eq 'io';
					print $File_Sourcecode "\t" . $action_type . "Synonym('$action_target')\t= '$action_this'\n" if $action_type;
				}
				else {
					print $File_Log "\tSynonym for unknown action at Prop$prop referencing Prop$property_target\n";
				}
			}
			elsif	($Constant_Property_Type[$prop_type] eq 'redir') {
				my $action_type		= substr(nameProperty($prop), 0, 2);
				my $object_target	= nameObject(unpack('S', $prop_data));
				my $name			= nameProperty($prop);
				undef $action_type	unless $action_type eq 'do' || $action_type eq 'io';
				print $File_Sourcecode "\t$name\t= $object_target\n" if $action_type;
			}
			elsif	($Constant_Property_Type[$prop_type] eq 'tpl2') {
				my $templates	= ord(substr($prop_data, 0));
				for (my $i=0 ; $i<$templates ; $i++) {
					# Read relevant identifiers for template
					my $prep_obj= unpack('S', substr($prop_data, $i * 16 + 1, 2)); # Object for preposition
					my $exc_io	= unpack('S', substr($prop_data, $i * 16 + 5, 2)); # Property for IndrectObject execute
					my $exc_do	= unpack('S', substr($prop_data, $i * 16 + 9, 2)); # Property for DirectObject execute
					# Determine output
					my $name		= nameAction($Objects[$obj]{properties}{$prop}{action});
					my $act_type	= 'doAction';
					my $prep		= '';
					$act_type 		= 'ioAction' 						unless $Null_Value eq $exc_io;
					$prep			= '(' . nameObject($prep_obj) . ')'	unless $Null_Value eq $prep_obj;
					# Write output
					print $File_Sourcecode "\t$act_type$prep\t= '$name'\n";
				}
			}
			elsif	($Constant_Property_Type[$prop_type] eq 'code') {
				printInstructions($prop, $Objects[$obj]{properties}{$prop}{instructions});
			}
			else {
				#Works for NUMBER, SSTRING, DSTRING, OBJECT, PROPNUM, FNADDR, NIL, TRUE, DAT_LIST
				#Also covers BASEPTR and TPL which we don't know what to print for
				my $name	= nameProperty($prop);
				my $value	= propertyString($obj, $prop);
				print $File_Sourcecode "\t$name\t= $value\n";
			}
			
		}
	}
}
sub printInstructions($){
	my $id	= shift;	
	my $ref	= shift;
	#Virtual Machine Simulation
	my @instructions	= @{ $ref };
	my @stack			= ();	# The current stack
	my @lines			= ();	# The lines so far 
	my @branching		= ();	# Keeping track of code branching
	my @labels			= ();	# Which positions need a label statement
	my $label			= 0;	# The code position where text was last pushed
	# Negative ID for object functions, positive for properties
	my $mode_obj;
	my $mode_prop;
	$mode_obj		= 1			if $id < 0;
	$mode_prop		= 1			if $id > 0;
	my $print_id;
	$print_id		= "Obj".(-$id)		if $mode_obj;
	$print_id		= "Prop$id"			if $mode_prop;
	print $File_Log "\t$print_id:\n"	if $Option_Verbose;
	#function header
	my $function_arguments	= 0;
	my $function_locals		= 0;
	push @branching, { 
		type	=> 'MAIN',
		start	=> 0,
		end		=> $instructions[$#instructions]{pos}
	};
	for (my $instruction=0 ; $instruction<$#instructions ; $instruction++){
		#Read instruction details
		my $opcode		= $instructions[$instruction]{opcode};
		my $pos			= $instructions[$instruction]{pos};
		my $next_label	= $instructions[$instruction]{size} + $pos;
		my @payload		= @{ $instructions[$instruction]{payload} };
		#Flag for fatal error in parsing
		my $fatal;
		#Property Assignments
		if	($opcode >= 192) {		# Bitflag encoded assignment
			#0-1	Variable type	0x03
			#	00	LOCAL	embedded(UINT16)
			#	01	PROP	embedded(UINT16) applied to object from stack
			#	10	(index, list)	from stack
			#	11	(prop, obj)		from stack
			my $variable;
			my $variable_mask	= $opcode & 0x03;
			if ($variable_mask eq 0x00) {
				#Local, stored in payload
				$variable		= shift @payload;
			}
			if ($variable_mask eq 0x01) {
				my $property	= shift @payload;
				#Object from stack, property from payload
				my $obj_ref		= pop @stack;
				my $object		= 'nil';
				my $precedence	= 14;
				$object			= %{ $obj_ref }{value}		if defined $obj_ref;
				$precedence		= %{ $obj_ref }{precedence}	if defined $obj_ref;
				$object			= "($object)" if $precedence < 13;
				$variable		=	$object . '.' . $property;
			}
			if ($variable_mask eq 0x02) {
				#Index from stack applied to list from stack
				my $index_ref	= pop @stack;
				my $index		= 'nil';
				$index			= %{ $index_ref }{value}		if defined $index_ref;
				my $list_ref	= pop @stack;
				my $list		= 'nil';
				my $precedence	= 14;
				$list			= %{ $list_ref }{value}			if defined $list_ref;
				$precedence		= %{ $list_ref }{precedence}	if defined $list_ref;
				$list			= "($list)" if $precedence < 13;
				$variable		= $list . '[' . $index . ']';
			}
			if ($variable_mask eq 0x03) {
				#Property from stack applied to object from stack
				my $prop_ref	= pop @stack;
				my $property	= 'nil';
				$property		= %{ $prop_ref }{value}		if defined $prop_ref;
				my $obj_ref		= pop @stack;
				my $object		= 'nil';
				my $precedence	= 14;
				$object			= %{ $obj_ref }{value}			if defined $obj_ref;
				$precedence		= %{ $obj_ref }{precedence}		if defined $obj_ref;
				$object			= "($object)" if ($precedence < 13);
				$variable		= $object . '(' . $property . ')';
			}
			#2-4	Operation type	0x1c
			#	000		:=	direct assignment
			#	001		+=	add tos to variable
			#	010		-=	subtract tos from variable
			#	011		*=	multiply variable by tos
			#	100		/=	divide variable by tos
			#	101		++	increment tos
			#	110		--	decrement tos
			#	111			extension flag
			my $operator_mask		= $opcode & 0x1C;
			my $operator;
			$operator	= ':='	if $operator_mask eq 0x00;
			$operator	= '+='	if $operator_mask eq 0x04;
			$operator	= '-='	if $operator_mask eq 0x08;
			$operator	= '*='	if $operator_mask eq 0x0C;
			$operator	= '/='	if $operator_mask eq 0x10;
			$operator	= '++'	if $operator_mask eq 0x14;
			$operator	= '--'	if $operator_mask eq 0x18;
			#If extension flag is set, contains an extra byte:
			#	1	%=	modulo and assign
			#	2	&=	binary AND and assign
			#	3	|=	binary OR and assign
			#	4	^=	binary XOR and assign
			#	5	<<=	shift left and assign
			#	6	>>=	shift right and assign
			if ($operator_mask eq 0x1c){
				my $extended	= shift @payload;
				$operator	= '%='	if $extended eq 1;
				$operator	= '&='	if $extended eq 2;
				$operator	= '|='	if $extended eq 3;
				$operator	= '^='	if $extended eq 4;
				$operator	= '<<='	if $extended eq 5;
				$operator	= '>>='	if $extended eq 6;
			}
			#5	Destinationtype
			#	0	leave on stack	implies pre increment/decrement
			#	1	discard 		implies post increment/decrement
			my $destination_mask	= $opcode & 0x20;
			#Get the value to modify by, and build the assignment
			my $assignment;
			my $precedence;
			if ($operator eq '++' || $operator eq '--'){
				#Implied value operator
				#Discard flag indicates post or pre assignment
				$assignment		= "$operator$variable" if $destination_mask;
				$assignment		= "$variable$operator" unless $destination_mask;
				$precedence		= 12;
			}
			else {
				#Get value from stack
				my $value_ref	= pop @stack;
				my $value		= 'nil';
				$value			= %{ $value_ref }{value}		if defined $value_ref;
				$assignment		= "$variable\t$operator $value";
				$precedence		= 0;
			}
			#Leave the assignment based on destination mask
			if($destination_mask){
				#Treat as discard; ie add to lines.
				push @lines, {
					text	=> $assignment,
					label	=> $label,
					indent	=> $#branching
				};
				$label		= $next_label;
			}
			else{
				#Push back on stack
				push @stack, {
					value		=> $assignment,
					precedence	=> $precedence
				};
			}
		}
		#Function header arguments
		elsif	($opcode eq 0x18) {	# OPCENTER			24
			$fatal					= "Duplicate OPCENTER for $print_id" if $function_locals != 0;
			$function_locals		= shift @payload;
			$label					= $next_label;
			$branching[0]{start}	= $label;
		}
		elsif	($opcode eq 0x4D) {	# OPCCHKARGC		77
			$fatal					= "Duplicate OPCENTER for $print_id" if $function_arguments != 0;
			$function_arguments		= shift @payload;
			$label					= $next_label;
			$branching[0]{start}	= $label;
		}
		elsif	($opcode eq 0x4F) {	# OPCFRAME			79
			#Ignored
			$label					= $next_label;
			$branching[0]{start}	= $label;
		}
		#Push value
		elsif	($opcode eq 0x01	# OPCPUSHNUM		01
			||	 $opcode eq 0x02	# OPCPUSHOBJ		02
			||	 $opcode eq 0x14	# OPCGETLCL			20
			||	 $opcode eq 0x1F	# OPCPUSHSTR		31
			||	 $opcode eq 0x20	# OPCPUSHLST		32
			||	 $opcode eq 0x23	# OPCPUSHFN			35
			||	 $opcode eq 0x43	# OPCPUSHPN			67
			) {	# Push value to stack from payload
			push @stack, {
				value		=> shift @payload,
				precedence	=> 14
			};
		}
		elsif	($opcode eq 0x1C	# OPCPUSHSELF		28
			||	 $opcode eq 0x21	# OPCPUSHNIL		33
			||	 $opcode eq 0x22	# OPCPUSHTRUE		28
			) {	# Push single word to stack
			my $word;
			$word	= 'self'	if $opcode eq 0x1C;
			$word	= 'nil'		if $opcode eq 0x21;
			$word	= 'true'	if $opcode eq 0x22;
			push @stack, {
				value		=> $word,
				precedence	=> 14
			};
		}
		#Unary operators
		elsif	($opcode eq 0x03	# OPCNEG			03
			||	 $opcode eq 0x04	# OPCNOT			04
			||	 $opcode eq 0x57	# OPCBNOT			87
			||	 $opcode eq 0x5A	# OPCNEW			90
			||	 $opcode eq 0x5B	# OPCDELETE			91
			) {	# Push result of unary operation on top of stack
			my $precedence	= 11;	#Same for all operators
			my $operator;	# Assign operator based on opcode
			$operator		= '-'		if $opcode eq 0x03;
			$operator		= 'not '	if $opcode eq 0x04;
			$operator		= '~'		if $opcode eq 0x57;
			$operator		= 'new '	if $opcode eq 0x5A;
			$operator		= 'delete '	if $opcode eq 0x5B;
			#Get arguments from stack
			my $argument_ref	= pop @stack;
			my $argument		= 'nil';
			my $argument_prec	= 14;
			$argument			= %{ $argument_ref }{value}			if defined $argument_ref;
			$argument_prec		= %{ $argument_ref }{precedence}	if defined $argument_ref;
			#Paranthesize as needed
			$argument		= "($argument)" if ($argument_prec < $precedence);
			#Perform operation and push back to stack
			push @stack, {
				value		=> "$operator$argument",
				precedence	=> $precedence
			};
		}
		#Binary operators
		elsif	($opcode eq 0x05	# OPCADD			05
			||	 $opcode eq 0x06	# OPCSUB			06
			||	 $opcode eq 0x07	# OPCMUL			07
			||	 $opcode eq 0x08	# OPCDIV			08
			||	 $opcode eq 0x09	# OPCAND			09
			||	 $opcode eq 0x0A	# OPCOR				10
			||	 $opcode eq 0x0B	# OPCEQ				11
			||	 $opcode eq 0x0C	# OPCNE				12
			||	 $opcode eq 0x0D	# OPCGT				13
			||	 $opcode eq 0x0E	# OPCGE				14
			||	 $opcode eq 0x0F	# OPCLT				15
			||	 $opcode eq 0x10	# OPCLE				16
			||	 $opcode eq 0x53	# OPCMOD			83
			||	 $opcode eq 0x54	# OPCBAND			84
			||	 $opcode eq 0x55	# OPCBOR			85
			||	 $opcode eq 0x56	# OPCXOR			86
			||	 $opcode eq 0x58	# OPCSHL			88
			||	 $opcode eq 0x59	# OPCSHR			89
			) {	# Push result of binary operation on top two of stack
			my $operator;	# Assign operator based on opcode
			$operator	=	'+'		if $opcode eq 0x05;
			$operator	=	'-'		if $opcode eq 0x06;
			$operator	=	'*'		if $opcode eq 0x07;
			$operator	=	'/'		if $opcode eq 0x08;
			$operator	=	'and'	if $opcode eq 0x09;	# &&
			$operator	=	'or'	if $opcode eq 0x0A;	# ||
			$operator	=	'='		if $opcode eq 0x0B;	# eq
			$operator	=	'<>'	if $opcode eq 0x0C;	# !=
			$operator	=	'>'		if $opcode eq 0x0D;
			$operator	=	'>='	if $opcode eq 0x0E;
			$operator	=	'<'		if $opcode eq 0x0F;
			$operator	=	'<='	if $opcode eq 0x10;
			$operator	=	'%'		if $opcode eq 0x53;
			$operator	=	'&'		if $opcode eq 0x54;
			$operator	=	'|'		if $opcode eq 0x55;
			$operator	=	'^'		if $opcode eq 0x56;
			$operator	=	'<<'	if $opcode eq 0x58;
			$operator	=	'>>'	if $opcode eq 0x59;
			my $precedence;		# Precedence varies by operator
			$precedence	= 10	if ( $opcode eq 0x07 || $opcode eq 0x08 || $opcode eq 0x53 );
			$precedence	= 9		if ( $opcode eq 0x05 || $opcode eq 0x06 );
			$precedence	= 8		if ( $opcode eq 0x58 || $opcode eq 0x59 );
			$precedence	= 7		if (($opcode >= 0x0B && $opcode <= 0x10));
			$precedence	= 6		if ( $opcode eq 0x54 );
			$precedence	= 5		if ( $opcode eq 0x56 );
			$precedence	= 4		if ( $opcode eq 0x55 );
			$precedence	= 3		if ( $opcode eq 0x09 );
			$precedence	= 2		if ( $opcode eq 0x0A );
			#Get arguments from stack
			my $argument2_ref	= pop @stack;
			my $argument2		= 'nil';
			my $argument2_prec	= 14;
			$argument2			= %{ $argument2_ref }{value}		if defined $argument2_ref;
			$argument2_prec		= %{ $argument2_ref }{precedence}	if defined $argument2_ref;
			my $argument1_ref	= pop @stack;
			my $argument1		= 'nil';
			my $argument1_prec	= 14;
			$argument1			= %{ $argument1_ref }{value}		if defined $argument1_ref;
			$argument1_prec		= %{ $argument1_ref }{precedence}	if defined $argument1_ref;
			#Paranthesize as needed
			$argument2		= "($argument2)" if ($argument2_prec <= $precedence);
			$argument1		= "($argument1)" if ($argument1_prec < $precedence); # Note difference in prec comparison
			#Perform operation and push back to stack
			push @stack, {
				value		=> "$argument1 $operator $argument2",
				precedence	=> $precedence
			};
		}
		#Function call/reference
		elsif	($opcode eq 0x11	# OPCCALL			17
			||	 $opcode eq 0x12	# OPCGETP			18
			||	 $opcode eq 0x13	# OPCGETPDATA		19	EXPERIMENTAL
			||	 $opcode eq 0x15	# OPCPTRGETPDATA	21	EXPERIMENTAL
			||	 $opcode eq 0x24	# OPCGETPSELFDATA	36	EXPERIMENTAL
			||	 $opcode eq 0x26	# OPCPTRCALL		38
			||	 $opcode eq 0x28	# OPCPTRGETP		40
			||	 $opcode eq 0x3C	# OPCGETPSELF		60
			||	 $opcode eq 0x3D	# OPCGETPSLFD		61	EXPERIMENTAL
			||	 $opcode eq 0x3E	# OPCGETPOBJ		62
			||	 $opcode eq 0x3F	# OPCGETPOBJD		63	EXPERIMENTAL
			||	 $opcode eq 0x47	# OPCINHERIT		71
			||	 $opcode eq 0x52	# OPCGETPPTRSELF	82	EXPERIMENTAL
			) {	# Push result of function call
			#Number of arguments is encoded in payload
			my $argument_count	= shift @payload;
			#Function is based on opcode
			my $function;
			my $precedence	= 13;
			if ($opcode eq 0x11){						#Call to object in payload
				$function		= shift @payload;
			}
			if ($opcode eq 0x12 || $opcode eq 0x13){	#Call to property in payload on object from stack
				#EXPERIMENTAL: Assumed to be functionally identical
				my $property	= shift @payload;
				my $object		= 'nil';
				my $object_prec	= 14;
				my $object_ref	= pop @stack;
				$object			= %{ $object_ref }{value}		if defined $object_ref;
				$object_prec	= %{ $object_ref }{precedence}	if defined $object_ref;
				$object			= "($object)" if $object_prec < $precedence;
				$function		= "$object.$property";
			}
			if ($opcode eq 0x15 || $opcode eq 0x28){	#Call to property in stack on object in stack
				#EXPERIMENTAL: Assumed to be functionally identical
				my $property		= 'nil';
				my $property_ref	= pop @stack;
				$property			= %{ $property_ref }{value}	if defined $property_ref;
				$property			= "($property)";	# Always need paranthesis 
				my $object			= 'nil';
				my $object_prec		= 14;
				my $object_ref		= pop @stack;
				$object				= %{ $object_ref }{value}		if defined $object_ref;
				$object_prec		= %{ $object_ref }{precedence}	if defined $object_ref;
				$object				= "($object)" if $object_prec < $precedence;
				$function			= "$object.$property";
			}
			if ($opcode eq 0x26){						#Call to property on stack
				my $property		= 'nil';
				my $property_ref	= pop @stack;
				$property			= %{ $property_ref }{value}	if defined $property_ref;
				$function			= "$property";
			}
			if ($opcode eq 0x2E){						#Inherited call to property in payload on object in payload
				my $property		= shift @payload;
				my $object			= shift @payload;
				my $function		= "inherited $object.$property";
			}
			if ($opcode eq 0x24 || $opcode eq 0x3C || $opcode eq 0x3D){	#Call to property on self
			
				#EXPERIMENTAL: Assumed to be functionally identical
				my $property		= shift @payload;
				$function			= "self.$property";
			}
			if ($opcode eq 0x3E || $opcode eq 0x3F){	#Call to property in payload on object in payload
				my $property		= shift @payload;
				my $object			= shift @payload;
				$function			= "$object.$property";
			}
			if ($opcode eq 0x47){						#Inherited call to property in payload
				my $property		= shift @payload;
				$function		= "inherited $property";
			}
			if ($opcode eq 0x52){						#Call to property on stack
				#EXPERIMENTAL: Based on naming
				my $property		= 'nil';
				my $property_ref	= pop @stack;
				$property			= %{ $property_ref }{value}	if defined $property_ref;
				$function			= "self.$property";
			}
			#Extract arguments from stack
			my $arguments	= '(';
			for (my $i=0 ; $i<$argument_count ; $i++) {
				$arguments		.= ', '		if $i > 0;
				my $object		= 'nil';
				my $object_ref	= pop @stack;
				$object			= %{ $object_ref }{value}	if defined $object_ref;
				$arguments		.= $object;
			}
			$arguments		.= ')';
			#Push function with arguments back to stack
			push @stack, {
				value		=> $function . $arguments,
				precedence	=> $precedence
			};
		}
		elsif	($opcode eq 0x1E){	# OPCBUILTIN		30
			#Number of arguments is encoded in payload
			my $argument_count	= shift @payload;
			#Type of builtin is encoded in payload
			my $type 			= shift @payload;
			unless ($type eq $Translate_Builtin[0] && $argument_count eq 2){
				#Say (type0) with 2 arguments is a special case
				my $arguments	= '(';
				for (my $i=0 ; $i<$argument_count ; $i++) {
					$arguments		.= ', '		if $i > 0;
					my $object		= 'nil';
					my $object_ref	= pop @stack;
					$object			= %{ $object_ref }{value}	if defined $object_ref;
					$arguments		.= $object;
				}
				$arguments		.= ')';
				#Push function with arguments back to stack
				push @stack, {
					value		=> $type . $arguments,
					precedence	=> 13
				};
			}
			else{
				#Say (type0) with 2 arguments is inline text substitution: "<< expr >"
				#The first arugment is the expression, second argument should be nil
				my $expr_ref	= pop @stack;
				my $expr		= 'nil';
				$expr			= %{ $expr_ref }{value}		if defined $expr_ref;
				my $discard_ref	= pop @stack;
				my $discard		= 'nil';
				$discard		= %{ $discard_ref }{value}	if defined $discard_ref;
				#Build and combine 
#DEPRECATED: This was good for aesthetics, but ruined GOTOs to the middle of the text.
#				if ( defined $lines[$#lines] && substr($lines[$#lines]{text}, - 2) eq '";') {
#					# If previous printed line was a say expression, we can combine them
#					$lines[$#lines]{text}	= substr($lines[$#lines]{text}, 0, -2)
#											. "<< $expr >>\";";
#					$lines[$#lines]{label}	= $label;
#				}
#				else {
				push @lines, {
					text	=> "\"<< $expr >>\";",
					label	=> $label,
					indent	=> $#branching
				};
#				}
				$label		= $next_label;
				#Log warning if we discarded something (TODO: Improved header handling)
				print $File_Log "BUILTIN SAY discarded $discard\n" unless $discard eq 'nil';
			}
		}
		#Utility
		elsif	($opcode eq 0x19) {	# OPCDISCARD		25
			#Discard the top element of the stack, which implies we should print it.
			my $text_ref	= pop @stack;
			my $text		= '//Discard on empty stack';
			$text			= %{ $text_ref }{value}	if defined $text_ref;
			# Push output to lines, with the reference to the first instruction that resulted in this text
			push @lines, {
				text	=> $text.';',
				label	=> $label,
				indent	=> $#branching
			};
			$label		= $next_label;
		}
		elsif	($opcode eq 0x1D) {	# OPCSAY			29
			my $text	= shift @payload;
			#See if we can append to previous line
#DEPRECATED: This was good for aesthetics, but ruined GOTOs to the middle of the text.
#			if ( defined $lines[$#lines] && substr($lines[$#lines]{text}, -4) eq '>>";') {
#				#>> indicated that the the current line ends in an inline text substitution, so we continue that line
#				$lines[$#lines]{text}	= substr($lines[$#lines]{text}, 0, -2)	# Trim the trailing ;"
#										. substr($text, 1)	# Trim the leading ", keeping the trailing "
#										. ";";
#				$lines[$#lines]{label}	= $pos;
#			}
			#Push a new line
#			else {
			push @lines, {
				text	=> $text.';',
				label	=> $label,
				indent	=> $#branching
			};
#			}
			$label		= $next_label;
		}
		elsif	($opcode eq 0x29	# OPCPASS			41
			||   $opcode eq 0x2A	# OPCEXIT			42
			||	 $opcode eq 0x2B	# OPCABORT			43
			||	 $opcode eq 0x2C	# OPCASKDO			44
			||	 $opcode eq 0x2D	# OPCASKIO			45
			) {	# single word operators
			my $text;
			$text			= 'pass'	if $opcode eq 0x29;
			$text			= 'exit'	if $opcode eq 0x2A;
			$text			= 'abort'	if $opcode eq 0x2B;
			$text			= 'askdo'	if $opcode eq 0x2C;
			$text			= 'askio'	if $opcode eq 0x2D;
			my $property	= '';
			$property		= shift @payload if $opcode eq 0x29 || $opcode eq 0x2D;
			$property		= "($property)" unless $property eq '';
			push @lines, {
				text	=> "$text$property;",
				label	=> $label,
				indent	=> $#branching
			};
			$label		= $next_label;
		}
		elsif	($opcode eq 0x40) {	# OPCINDEX			64
			#Index from stack applied to list from stack
			my $index_ref	= pop @stack;
			my $index		= 'nil';
			$index			= %{ $index_ref }{value}		if defined $index_ref;
			my $list_ref	= pop @stack;
			my $list		= 'nil';
			my $list_prec	= 14;
			$list			= %{ $list_ref }{value}			if defined $list_ref;
			$list_prec		= %{ $list_ref }{precedence}	if defined $list_ref;
			#Paranthesize as needed
			$list			= "($list)"	if ($list_prec < 13);
			push @stack, {
				value		=> $list .'['. $index . ']',
				precedence	=> 13
			};
		}
		elsif	($opcode eq 0x4A) {	# OPCCONS			74
			#Construct a new list with the number embedded in payload elements from top of stack
			#Number of elements is encoded in payload
			my $element_count	= shift @payload;
			#Extract elements from stack
			my $elements	= '[';
			for (my $i=0 ; $i<$element_count ; $i++) {
				$elements		.= ', '		if $i > 0;
				my $element		= 'nil';
				my $element_ref	= pop @stack;
				$element		= %{ $element_ref }{value}	if defined $element_ref;
				$elements		.= $element;
			}
			$elements		.= ']';
			push @stack, {
				value		=> $elements,
				precedence	=> 14
			};
		}
		#Branching
		elsif	($opcode eq 0x16	# OPCRETURN			22
			||	 $opcode eq 0x17	# OPCRETVAL			23
			) {	# Returns from the function;
			my $text;
			#We suppress valueless returns that terminate the main loop
			$text	= 'return' unless $branching[$#branching]{type} eq 'MAIN';;
			if ($opcode eq 0x17) {
				my $value_ref	= pop @stack;
				my $value		= 'nil';
				$value			= %{ $value_ref }{value}	if defined $value_ref;
				$text			= "return $value";
			}
			# Push output to lines, with the reference to the first instruction that resulted in this text
			push @lines, {
				text	=> $text,
				label	=> $label,
				indent	=> $#branching
			};
			$label		= $next_label;
			my $type	= $branching[$#branching]{type};
			print $File_Log "\t\t$type RETURN at $pos/$label\n"	if $Option_Verbose;
			pop @branching	if $branching[$#branching]{type} eq 'MAIN';
		}
		elsif	($opcode eq 0x1A) {	# OPCJMP			26
			#Unconditional jump, can be used in different branching structures:
			#	WHILE	End		If destination is the start of WHILE branch
			#			Break	If destination is the end of first WHILE branch
			#	SWITCH	Break	If destination is the end of first SWITCH branch
			#	ELSIF	ELSE	If destination is the end of current ELSIF branch
			#	GOTO			Otherwise
			#Get destination from payload
			my $destination		= shift @payload;
			#The relevant branching levels
			my $branch_start	= $branching[$#branching]{start};
			my $branch_end		= $branching[$#branching]{end};
			my $branch_type		= $branching[$#branching]{type};
			my $switch_end;		# End of the first switch statement, if relevant
			my $switch_level;
			for (my $i=$#branching ; $i>=0 ; $i--){
				$switch_end			= $branching[$i]{end} if $branching[$i]{type} eq 'SWITCH';
				$switch_level		= $i;
			}
			my $while_end;		#End of the first while statement, if relevant
			my $while_level;
			for (my $i=$#branching ; $i>=0 ; $i--){
				$while_end			= $branching[$i]{end} if $branching[$i]{type} eq 'WHILE';
				$while_level		= $i;
			}
			#Only keep the topmost of the two
			undef $while_end		if defined $while_end && defined $switch_end && ($switch_end > $while_end);
			undef $switch_end		if defined $while_end && defined $switch_end && ($while_end > $switch_end);
			#Determine the corresponding branching construct
			if	  ($branch_type eq 'WHILE' && $branch_start eq $destination && $branch_end eq $next_label){
				#WHILE	Jump back to start of conditional jump
				#End branch and close brackets
				print $File_Log "\t\tWHILE-end at $pos/$label to $destination $branch_type($branch_start-$branch_end)\n"	if $Option_Verbose;
				pop @branching;
				push @lines, {
					text	=> '}',
					label	=> $label,
					indent	=> $#branching
				};
				$label		= $next_label;
			}
			elsif (defined $while_end && $while_end eq $destination){
				#WHILE	Jump to end of first while in stack
				#Write a break
				print $File_Log "\t\tWHILE-break at $pos/$label to $destination $branch_type($branch_start-$branch_end)\n"	if $Option_Verbose;
				push @lines, {
					text	=> 'break;',
					label	=> $label,
					indent	=> $#branching
				};
				$label		= $next_label;
			}
			elsif (defined $switch_end && $switch_end eq $destination){
				#SWITCH	Jump to end of first while in stack
				#Write a break
				print $File_Log "\t\tSWITCH-break at $pos/$label to $destination $branch_type($branch_start-$branch_end)\n"	if $Option_Verbose;
				push @lines, {
					text	=> 'break;',
					label	=> $label,
					indent	=> $#branching
				};
				$label		= $next_label;
			}
			elsif ($branch_type eq 'ELSIF' && $branch_end eq $destination){
				#ELSIF	The else part, with a possibility of an IF (0x1B) as next opcode
				#Keep the branch, and write an else.
				push @lines, {
					text	=> '} else {',
					label	=> $label,
					indent	=> $#branching
				};
				$label		= $next_label;
			}
			else {
				#GOTO
				#Insert a label mark at the destination instruction
				#Print a negated if condition and goto label
				print $File_Log "\t\tGOTO at $pos/$label to $destination $branch_type($branch_start-$branch_end)\n"	if $Option_Verbose;
				push @labels, $destination;
				push @lines, {
					text	=> 'goto label'.$destination.';',
					label	=> $label,
					indent	=> $#branching
				};
				$label		= $next_label;
			}
		}
		elsif	($opcode eq 0x1B) {	# OPCJF				27
			#Conditional jump, can indicate different branching structures:
			#	GOTO			If the jump is to outside the current structure
			#	WHILE	Start	If the last instruction before destination is an unconditional (26) jump back to label
			#	ELSIF	Append	If the destination or last instruction before destination is an unconditional (26) jump to the end of current ELSIF
			#			New		If the last instruction before destination is an unconditional jump forward inside current branch
			#	IF		New		Otherwise
			#Get destination from payload and condition from stack
			my $destination		= shift @payload;
			my $condition		= 'nil';
			my $condition_ref	= pop @stack;
			$condition			= %{ $condition_ref }{value}	if defined $condition_ref;
			#The relevant branching level
			my $branch_start	= $branching[$#branching]{start};
			my $branch_end		= $branching[$#branching]{end};
			my $branch_type		= $branching[$#branching]{type};
			#Find the last instruction in the branch, and see if it is a jump
			my $last_id;			# ID in instruction array for last instruction of branch
			my $last_opcode;		# Opcode of last intruction in branch
			my $last_destination;	# Destination of last jump, if it's unconditional jump
			for (my $branch_id=0 ; $branch_id<=$#instructions ; $branch_id++){
				$last_id		= ($branch_id - 1) if $destination eq $instructions[$branch_id]{pos};
			}
			$last_opcode		= $instructions[$last_id]{opcode};
			$last_destination	= $instructions[$last_id]{payload}[0] if $last_opcode eq 0x1A;
			my $end_destination	= $destination;
			$end_destination	= $last_destination if defined $last_destination;
			#Determine the corresponding branching construct
			if	  ($destination < $branch_start || $destination > $branch_end) {
				#GOTO	Jump to outside current branch
				#Insert a label mark at the destination instruction
				#Print a negated if condition and goto label
				print $File_Log "\t\tGOTO-unless at $pos/$label to $destination $branch_type($branch_start-$branch_end)\n"	if $Option_Verbose;
				push @labels, $destination;
				push @lines, {
					text	=> 'if (not '.$condition.') goto label'.$destination.';',
					label	=> $label,
					indent	=> $#branching
				};
				$label		= $next_label;
			}
			elsif (defined $last_destination && $last_destination eq $label) {
				#WHILE	Jump back to start of conditional jump
				#Print while condition and start a new branch
				print $File_Log "\t\tWHILE-start at $pos/$label to $destination $branch_type($branch_start-$branch_end)\n"	if $Option_Verbose;
				push @lines, {
					text	=> 'while ('.$condition.') {',
					label	=> $label,
					indent	=> $#branching
				};
				push @branching, {
					start	=> $label,
					end		=> $destination,
					type	=> 'WHILE'
				};
				$label		= $next_label;
			}
			elsif ($branch_type	eq 'ELSIF' && $branch_end eq $end_destination && substr($lines[$#lines]{text}, -8) eq '} else {') {
				#ELSIF	Jump to an unconditional jump to the end of the branch
				#Stay in the same branch, append condition to previously printed ELSE
				print $File_Log "\t\tELSIF-append at $pos/$label to $destination $branch_type($branch_start-$branch_end)\n"	if $Option_Verbose;
				$lines[$#lines]{text}	= substr($lines[$#lines]{text}, 0, length($lines[$#lines]{text}) -2)
										. ' if (' . $condition . ') {';
			}
			elsif (defined $last_destination && $last_destination > $pos && $last_destination <= $branch_end ){
				#ELSIF	Jump is to an unconditional forward jump inside same branch
				#Write a conditional if, and mark branch as having an else component
				print $File_Log "\t\tELSIF-new at $pos/$label to $destination $branch_type($branch_start-$branch_end)\n"	if $Option_Verbose;
				push @lines, {
					text	=> 'if ('.$condition.') {',
					label	=> $label,
					indent	=> $#branching
				};
				push @branching, {
					start	=> $label,
					end		=> $destination,
					type	=> 'ELSIF'
				};
				$label		= $next_label;
			}
			else {
				#IF		Simple conditional without else-clause
				print $File_Log "\t\tIF-new at $pos/$label to $destination $branch_type($branch_start-$branch_end)\n"	if $Option_Verbose;
				push @lines, {
					text	=> 'if ('.$condition.') {',
					label	=> $label,
					indent	=> $#branching
				};
				push @branching, {
					start	=> $label,
					end		=> $destination,
					type	=> 'IF'
				};
				$label		= $next_label;
			}
		}
		elsif	($opcode eq 0x44	# OPCJST			68
			||	 $opcode eq 0x45	# OPCJSF			69
			) {	# Logical short-circuited evaluation
			#We need to evaluate at the destination from payload
			my $branch_start	= $branching[$#branching]{start};
			my $branch_end		= $branching[$#branching]{end};
			my $branch_type		= $branching[$#branching]{type};
			my $destination		= shift @payload;
			print $File_Log "\t\tEVALUATION-start at $pos/$label to $destination $branch_type($branch_start-$branch_end)\n"	if $Option_Verbose;
			push @branching, {
				start	=> $label,
				end		=> $destination,
				type	=> 'EVALUATION',
				opcode	=> $opcode
			};
		}
		elsif	($opcode eq 0x4B) {	# OPCSWITCH			75
			#A table of switch cases is located at the position embedded in payload;
			#This has been unpacked to a list of opcodes with target stored in the payload.
			my $table_start		= $instructions[$instruction]{switch_start};
			my $table_end		= $instructions[$instruction]{switch_end};
			my @payload			= @{ $instructions[$instruction]{payload} };
			#The statement to execute the switch on is stored at top of stack
			my $statement_ref	= pop @stack;
			my $statement		= 'nil';
			$statement			= %{ $statement_ref }{value}	if defined $statement_ref;
			#Build the switch cases based on payload
			my @endpoints		= ();
			my @switch_cases	= ();
			for my $ref (@payload){
				my %entry	= %{ $ref };
				push @switch_cases, {
					text	=> $entry{payload}[0],
					start	=> $entry{target}
				};
				push @endpoints, $entry{target};
			}
			push @switch_cases, {
				text	=> 'default',
				start	=> $instructions[$instruction]{switch_default}
			};
			#Find the end points
			push @endpoints, $instructions[$instruction]{switch_default};
			push @endpoints, $table_start;
			push @endpoints, $table_end;
			@endpoints = sort {$a <=> $b} @endpoints;
			for (my $case=0 ; $case<=$#switch_cases ; $case++){
				for (my $end=0 ; $end<$#endpoints ; $end++){
					if ($endpoints[$end] eq $switch_cases[$case]{start}){
						$switch_cases[$case]{end}	= $endpoints[$end+1];
						last;
					}
				}
				die "No endpoint for switch case $case"  unless defined $switch_cases[$case]{end};
			}
			#Write the switch statement 
			push @lines, {
				text	=> "switch ($statement) {",
				label	=> $label,
				indent	=> $#branching
			};
			print $File_Log "\t\tSWITCH-start at $pos/$label to $endpoints[$#endpoints], ($table_start-$table_end)\n"if $Option_Verbose;
			print $File_Log "\t\tCASE-start at $pos/$label, $switch_cases[0]{start}-$switch_cases[0]{end}\n"	if $Option_Verbose;
			#Push the switch to branching, as well as the first case.
			#Changes between cases is handled by the end of branch code.
			push @branching, {
				type	=> 'SWITCH',
				start	=> $label,
				end		=> $endpoints[$#endpoints],
				cases	=> \@switch_cases,
				case	=> 0
			};
			push @branching, {
				type	=> 'CASE',
				start	=> $switch_cases[0]{start},
				end		=> $switch_cases[0]{end}
			};
			$label		= $next_label;
		}
		#Unhandled opcodes
		else{
			$fatal			= "Unknown OpCode $opcode for $print_id";
		}
		#Check for end of branches
		my $branch_end;
		$branch_end		= $branching[$#branching]{end}	unless $#branching eq -1;
		while(defined $branch_end && $branch_end eq $next_label){
			my $branch_type	= $branching[$#branching]{type};
			if    ($branch_type eq 'EVALUATION'){
				#Defered evaluation of shor-circuit logic operator
				#Operator and precedence are based on the opcode that started the branch
				my $operator;
				my $precedence;
				$operator	= 'or'	if $branching[$#branching]{opcode} eq 0x44;	# ||
				$precedence	= 2		if $branching[$#branching]{opcode} eq 0x44;
				$operator	= 'and'	if $branching[$#branching]{opcode} eq 0x45;	# &&
				$precedence	= 3		if $branching[$#branching]{opcode} eq 0x45;
				#Get arguments
				my $arg2_ref	= pop @stack;
				my $arg2		= 'nil';
				my $arg2_prec	= 14;
				$arg2			= %{ $arg2_ref }{value}	if defined $arg2_ref;
				$arg2_prec		= %{ $arg2_ref }{precedence}	if defined $arg2_ref;
				my $arg1_ref	= pop @stack;
				my $arg1		= 'nil';
				my $arg1_prec	= 14;
				$arg1			= %{ $arg1_ref }{value}	if defined $arg1_ref;
				$arg1_prec		= %{ $arg1_ref }{precedence}	if defined $arg1_ref;
				#Paranthesize as needed
				$arg2			= "($arg2)" if ($arg2_prec <= $precedence);
				$arg1			= "($arg1)" if ($arg1_prec < $precedence); # Note difference in prec comparison
				#Store the operation as the condition
				push @stack, {
					value		=> "$arg1 $operator $arg2",
					precedence	=> $precedence
				};
				pop @branching;
			}
			elsif ($branch_type eq 'CASE'){
				#End of switch case, try to find and start the next
				print $File_Log "\t\tCASE-end at $pos/$label\n"	if $Option_Verbose;
				pop @branching;
				my @cases		= @{ $branching[$#branching]{cases} };
				my $next_case	= $branching[$#branching]{case} + 1;
				my $next_pos;
				#See if there are more cases
				if ($next_case <= $#cases) {
					my $start	= $cases[$next_case]{start};
					my $end		= $cases[$next_case]{end};
					print $File_Log "\t\tCASE-start at $pos/$label, $start-$end\n"	if $Option_Verbose;
					$label	= $cases[$next_case]{start};
					$branching[$#branching]{case}++;
					#Write case line
					push @lines, {
						text	=> "case $cases[$next_case]{text}:",
						label	=> $label,
						indent	=> $#branching
					};
					#Push next case
					push @branching, {
						type	=> 'CASE',
						start	=> $start,
						end		=> $end
					};
					$next_pos	= $start;
				}
				else {
					#No more cases, close out the switch
					$next_pos	= $branching[$#branching]{end};
					print $File_Log "\t\tSWITCH-end at $pos/$label -> $next_pos\n"	if $Option_Verbose;
					pop @branching;
					push @lines, {
						text	=> "}",
						label	=> $label,
						indent	=> $#branching
					};
					$label	= $next_pos;
				}
				#Find the right instruction to continue at
#				print "$print_id from $instruction ";
				for (my $i=0 ; $i<=$#instructions ; $i++){
					$instruction = $i-1 if $instructions[$i]{pos} eq $next_pos;
				}
#				print "to $instruction\n";
			}
			elsif ($branch_type eq 'IF' || $branch_type eq 'ELSIF'){
				my $start	= $branching[$#branching]{start};
				my $end		= $branching[$#branching]{end};
				print $File_Log "\t\t$branch_type-end at $pos/$label ($start-$end)\n"	if $Option_Verbose;
				pop @branching;
				push @lines, {
					text	=> "}",
					label	=> $label,
					indent	=> $#branching
				};
				$label	= $next_label;
			}
			elsif ($branch_type eq 'MAIN'){
				#End of branch; ignore it as a return will catch it
				my $start	= $branching[$#branching]{start};
				my $end		= $branching[$#branching]{end};
				print $File_Log "\t\t$branch_type-end at $pos/$label ($start-$end)\n"	if $Option_Verbose;
				last;
			}
			else {
				warn "Unhandled end of branch $branch_type at $pos";
				pop @branching;
			}
			undef $branch_end;
			$branch_end		= $branching[$#branching]{end}	unless $#branching eq -1;
		}
		#Check for fatal errors
		if(defined $fatal){
			print $File_Log "\t$print_id\n"	unless $Option_Verbose;
			print $File_Log "\t\t$fatal\n";# . Dumper(@instructions);
			warn $fatal;
			last;
		}
		#Stop processing when the main loop is terminated
		last if $#branching eq -1;
	}
	#Calculate labels
	@labels		= sort {$a <=> $b} @labels;
	#Trim duplicates
	my $distinct = 1;
	while ($distinct < $#labels) {
		if ($labels[$distinct-1] eq $labels[$distinct]){
			splice @labels, $distinct, 1;
		}
		else {
			$distinct++;
		}
	}
	#Find the line corresponding to the position
	for my $l (0 .. $#labels){
		my $found;
		for my $i (0 .. $#lines) {
			last if $lines[$i]{label} > $labels[$l]; #We're past it..
			next if $lines[$i]{label} < $labels[$l]; #This is not the one
			$lines[$i]{print_label}	= 1;
			$found = 1;
		}
		#Label could be at the end..
		if ($lines[$#lines]{label} < $labels[$l]){
			push @lines, {
				text	=> "label$labels[$l];",
				label	=> $labels[$l],
				indent	=> 0
			};
			$found = 1;
		}
		unless (defined $found) {
#			print $File_Log Dumper @labels;
#			print $File_Log Dumper @lines;
#			print $File_Log Dumper @instructions;
			print $File_Log "\t$print_id\n"	unless $Option_Verbose;
			print $File_Log "\t\tUnable to insert label$labels[$l]\n";
		}
	}
	#Decide on arguments
	my $arguments = '';
	$arguments		= '('	if $function_arguments;
	for (my $i=1 ; $i<=$function_arguments ; $i++){
		$arguments	.= ', '	if $i > 1;
		$arguments	.= nameLocal($id, -$i);	# Arguments have negative indexes in bytecode
	}
	$arguments		.= ') '	if $function_arguments;
	#Print header
	print $File_Sourcecode nameObject(-$id) . ": function"	if $mode_obj;
	print $File_Sourcecode "\t".nameProperty($id)."\t= "	if $mode_prop;
	print $File_Sourcecode $arguments."{\n";
	#Print local definitions
	my $locals;
	$locals		= 'local '	if $function_locals;
	for (my $i=1 ; $i<=$function_locals ; $i++){
		$locals	.= ', '	if $i > 1;
		$locals	.= nameLocal($id, $i);
	}
	print $File_Sourcecode "\t"				if defined $locals && $mode_prop;
	print $File_Sourcecode "\t$locals;\n"	if defined $locals;
    for my $i (0 .. $#lines) {
		#Print label if needed
		print $File_Sourcecode "label$lines[$i]{label}:\n" 	if defined $lines[$i]{print_label};
		#Find the text
		my $text	= $lines[$i]{text};
		next unless defined $text;	# Returns sometimes don't leave a line
		#Indent properly before writing text
		my $indent	= $lines[$i]{indent};
		for my $t (0 .. $indent) { print $File_Sourcecode "\t"; }
		print $File_Sourcecode "\t"			if $mode_prop;
		print $File_Sourcecode "$text\n";
	}
	print $File_Sourcecode "\t"			if $mode_prop;
	print $File_Sourcecode "}\n";
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
	elsif($#ARGV >= 0 && $ARGV[0] eq '-a') {			# Aggressive naming
		$Option_Naming		= 1;
		splice(@ARGV, 0, 1);
	}
	elsif($#ARGV >= 0 && $ARGV[0] eq '-v') {			# Verbose
		$Option_Verbose		= 1;
		splice(@ARGV, 0, 1);
	}
	elsif($#ARGV >= 0 && $ARGV[0] eq '-m') {			# Minimalist mode
		$Option_Minimal		= 1;
		splice(@ARGV, 0, 1);
	}
	else { last }
}
$FileName_Bytecode	= $ARGV[0];	# There should be only one argument left, giving the name of the file to parse.
die "Use: tads2 [options] file.taf\n$Options" if ($#ARGV != 0);	# Too many unparsed arguments

#Determine names to use
$FileName_Path	= './';	# Default to no directory
if ($ARGV[0] =~ m/([\w\s]*)\.gam/i) {	# Use the name of the input file if possible
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
	|| die "$0: can't open $FileName_Path$FileName_Log for writing: $!";

print "Parsing $FileName_Bytecode\n";
open($File_Bytecode, "< :raw :bytes", $FileName_Bytecode)
	|| die("Couldn't open $FileName_Bytecode for reading.");
preloadConstants();								# Populate arrays with TADS2 constants
parseHeader();									# Read header and determine version/type of file
parseFile();									# Parse the input file into the local data structures
close($File_Bytecode);
preloadMapping();								# Load mapping defaults
parseMapping() if defined $FileName_Mapping;	# Read symbol file if called for
print "Analyzing...\n";
analyze();
generateMapping() if $Option_Generate;			# Generate symbol file if called for

open($File_Sourcecode, "> :raw :bytes", $FileName_Path . $FileName_Sourcecode)
	|| die "$0: can't open $FileName_Path$FileName_Sourcecode for writing: $!";
print "Writing results...\n";
printSource();									# Print TADS source based on bytecode

#Close file output
close($File_Sourcecode);
close($File_Log);
print "Decompiling completed in ".(time - $Time_Start)." seconds.\n";