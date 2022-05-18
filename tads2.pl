use strict;					# 'Safest' operation level
use warnings;				# Give warnings
use File::Basename;			# Interpreting embedded filenames
use File::Slurp;			# Read entire file at once
use File::Path 'make_path';	# Creating directories
use Data::Dumper;			# Dumping data structures
use Carp;					# For stack tracing at errors

my $Time_Start	= time();	# Epoch time for start of processing
##Version History
my $Decompiler_Version		= '0.13';
#v0.1:	Initial structure for flow and storage
#v0.2:	Parsing of data blocks (Headers + XSI/OBJ/RES)
#v0.3:	Generation and parsing of symbol file
#v0.4:	Verbose mode implementation, parsing of VOC/CMPD/FMTSTR
#v0.5:	Action analyzis and property decoding; working resource paths
#v0.6:	Basic source printing, vocabulary analysis
#v0.7:	Code analysis: instruction set parsing
#v0.8:	Code analysis: instruction printing
#v0.9:	Minor tweaks
#v0.10:	Various bugfixes
#v0.11:	New template
#v0.11a	Fixed string concatenation and empty switches
#v0.11b	Fixed a shift in all preloaded argument names
#v0.11c	Improved symbol loading
#v0.12a	Fixed proper headers and rewrote symbol handling for methods and functions
#v0.12b	Fixed argument-less method calls
#v0.13a	Count instances and subclasses

##Global Variables
#Story Settings
my $Container_Type;				# The type of TADS-2 file, determined by signature
my $Compiler_Version;			# The version used to compile the storyfile
my $Compiler_Time;				# Timestamp of compilation
my %Flags				= ();	# Flags from the signature
my %Encryption			= ();	# Store seed and increment value for XOR encryption

#Story Data
my @Objects 			= ( undef );	# Objects, starting from ID 1
my @Formats				= ( undef );	# Format strings, starting from ID 1
my @Compounds 			= ( undef );	# Compunded tokens, starting from ID 1
my %Property_Actions	= ();			# Mapping of which properties refer to which actions
my $Property_Max		= 0;			# Highest property ID used

#Symbol Translation Names
my @Symbol_Action				= ();	# Symbolic names for actions
my @Symbol_Builtin				= ();	# Symbolic names for builtin functions
my @Symbol_Object				= ();	# Symbolic names for objects
my %Symbol_Object_Argument		= ();	# Symbolic names for object arguments
my %Symbol_Object_Variable		= ();	# Symbolic names for object variables
my @Symbol_Property				= ();	# Symbolic names for properties
my %Symbol_Property_Argument	= ();	# Symbolic names for property arguments
my %Symbol_Property_Variable	= ();	# Symbolic names for property variables

#Statistics
my %Stat_Object_Count	= ();	# Number of object type found
my %Stat_Property_Count	= ();	# Number of each property type found
my %Stat_Opcode_Count	= ();	# Number of each opcode found

#File handling
my $FileName_Compiled;		# Filename for the compiled gamefile to decompile
my $FileName_Path	= './';	# Path to place output files in
my $FileName_Decompiled;	# Filename for decompiled sourcecode
my $FileName_Log;			# Filename for log file
my $FileName_PropMap;		# Filename for property map
my $FileName_Symbol;		# Filename for symbol mapping translation input file
my $FileName_Symbol_Gen;	# Filename for symbol mapping translation output file
my $FileName_XML;			# Filename for XML output
my $File_Compiled;			# File handle for input compiled gamefile
my $File_Log;				# File handle for logging output
my $File_Decompiled;		# File handle for output decompiled sourcecode
my $File_PropMap;			# File handle for property map
my $File_Symbol;			# File handle for symbol mapping translation (both input and output)
my $File_XML;				# File handle for XML output
my $Contents_Compiled;		# File contents

#Decompiling Options; see parseArguments()
my $Options	= "Decompiling Options:\n";
my $Option_Minimal;		# Skip output directory and embedded resources
$Options	.= "-m\t\tMinimalist mode, skipping output directory and resources\n";
my $Option_Verbose;		# Extra information dumped to story file
$Options	.= "-v\t\tVerbose loging output\n";
my $Option_Naming;		# Be extra aggressive on trying to determine names
						# TODO: This will create duplicate names, remake to avoid that
$Options	.= "-a\t\tAggressive naming of objects and properties\n";
my $Option_Generate;	# Generate a new symbol file
$Options	.= "+s\t\tGenerate symbol translation file in output directory\n";
$Options	.= "-s [file]:\tSymbol translation file\n";
my $Option_PragmaC;		# Use C-Pragma in code generation
$Options	.= "-c\t\tC-Pragma code style\n";

#TADS Constants
my @Constant_Property_Type	= ();		# Symbolic names for property types
my @Constant_Opcode			= ();		# Opcode names
my @Constant_Opcode_Operand	= ();		# List of operand types for each opcode
my $Null_Value				= 65535;	# Used to indicate no value in some places
$Encryption{Seed}			= 0x3f;
$Encryption{Increment}		= 0x40;

#Virtual Machine Properties
my @VM_Instructions		= ();	# The list of instructions currently being executed; needed for look-ahead
my @VM_Stack			= ();	# The current stack for the VM
my @VM_Lines			= ();	# The lines generated by executing the VM so far
my @VM_Branches			= ();	# The current branching level of the VM
my @VM_Labels			= ();	# Which positions need a label statement
my $VM_Arguments		= 0;	# The number of argument variables, determined by opcode execution
my $VM_Locals			= 0;	# The number of local variables, determined by opcode execution
my $VM_Fatal_Error;				# Indicates whether a fatal error has accured in the execution, and if so what went wrong
#Keep track of whether the label should or has been updated
my $VM_Label_Current	= 0;	# The position of the instruction that will result in the next line of text
my $VM_Label_Update		= 0;	# my $update_label
my $VM_Label_Updated	= 0;	# my $label_updated	= 0;
my $VM_Label_Next		= 0;	# What the current label should be updated to

##Initialization
sub initialize() {
	#Parse arguments;
	parseArguments();
	#There should be only one argument left, giving the name of the file to parse.
	die "Use: tads2 [options] file.gam\n$Options" unless ($#ARGV == 0);
	$FileName_Compiled	= $ARGV[0];
	if ($FileName_Compiled	=~ m/([-_\w\s]*)\.(gam|rs\d)/i) {
	#When input file has a recognized extension, use the name of the file
		$FileName_Path			= $1 . '/'	unless defined $Option_Minimal;
		$FileName_PropMap		= $1 . '.prop.map';
		$FileName_Log			= $1 . '.log';
		$FileName_Decompiled	= $1 . '.t';
		$FileName_XML			= $1 . '.xml';
		$FileName_Symbol_Gen	= $1 . '.sym'	if defined $Option_Generate;
	}
	else{
	#Otherwise decide on input agnostic file names
		$FileName_Path			= 'decompiled/'	unless defined $Option_Minimal;
		$FileName_PropMap		= 'prop.map';
		$FileName_Log			= 'story.log';
		$FileName_Decompiled	= 'story.t';
		$FileName_XML			= 'story.xml';
		$FileName_Symbol_Gen	= 'story.sym'	if defined $Option_Generate;
	}
	openFiles();
}
sub parseArguments() {
	while (defined $ARGV[0]) {
		if	 ($ARGV[0] eq '-m') {	# Minimalist mode
			$Option_Minimal	= 1;
			splice(@ARGV, 0, 1);
		}
		elsif($ARGV[0] eq '-v') {	#Verbose logging
			$Option_Verbose = 1;
			splice(@ARGV, 0, 1);
		}
		elsif($ARGV[0] eq '-a') {	#Aggressive naming search
			$Option_Naming	= 1;
			splice(@ARGV, 0, 1);
		}
		elsif($ARGV[0] eq '-s') {	#Read symbol mapping file
			$FileName_Symbol	= $ARGV[1];
			splice(@ARGV, 0, 2);
		}
		elsif($ARGV[0] eq '+s') {
			#Generate symbol mapping file template
			$Option_Generate	= 1;
			splice(@ARGV, 0, 1);
		}
		elsif($ARGV[0] eq '-c') {	#C-Pragma
			$Option_PragmaC = 1;
			splice(@ARGV, 0, 1);
		}
		else{ last }
	}
}
sub openFiles() {
	#Open file handles; Create path as needed
	mkdir $FileName_Path						unless -e $FileName_Path;
	die "$FileName_Path is not a valid path"	unless -d $FileName_Path;
	#Open log; use :unix to flush as we write to it
	open($File_Log, "> :raw :bytes :unix", $FileName_Path . $FileName_Log)
		or die "$0: can't open $FileName_Path$FileName_Log for writing: $!";
	#Open compiled file with some sanity checking
	die "$FileName_Compiled is not a valid file"	unless -f $FileName_Compiled;
	open($File_Compiled, "< :raw :bytes", $FileName_Compiled)
		or die("Couldn't open $FileName_Compiled for reading: $!");
	#Open symbol mapping file if defined
	open($File_Symbol, "< :raw :bytes", $FileName_Symbol)
		or die("Couldn't open $FileName_Symbol for reading.")
		if defined $FileName_Symbol;
	#Open generated output files
	open($File_Decompiled, "> :raw :bytes", $FileName_Path . $FileName_Decompiled)
		or die "$0: can't open $FileName_Path$FileName_Decompiled for writing: $!";
	open($File_XML, "> :raw :bytes", $FileName_Path . $FileName_XML)
		or die "$0: can't open $FileName_Path$FileName_XML for writing: $!";
	open($File_PropMap, "> :raw :bytes", $FileName_Path . $FileName_PropMap)
		or die "$0: can't open $FileName_Path$FileName_PropMap for writing: $!";
	#Open mapping file with some sanity checking
	die "Overwriting existing symbol file with autogenerated is not supported in minimal mode"
		if defined $FileName_Symbol_Gen && $Option_Minimal && -e $FileName_Symbol_Gen;
}
#Determine compiler version by reading the story header
sub determineVersion() {
	my $signature_story		= chr(84).chr(65).chr(68).chr(83).chr(50).chr(32).chr( 98).chr(105).chr(110).chr(10).chr(13);
	my $signature_resource	= chr(84).chr(65).chr(68).chr(83).chr(50).chr(32).chr(114).chr(115).chr( 99).chr(10).chr(13);
	#Read the signature (first 11 bytes) and compare to known signatures to determine the type of file we have
	my $signature;
	my $read = read ($File_Compiled, $signature, 11);
	die "Unable to read signature from $FileName_Compiled" unless $read == 11;
	#Store container type
	$Container_Type	= 'Story'		if $signature eq $signature_story;
	$Container_Type	= 'Resource'	if $signature eq $signature_resource;
	die "Unable to determine that $FileName_Compiled is a valid TADS-2 file" unless defined $Container_Type;
}
#Initialize constants that might depend on version
sub loadConstants() {
	{	#Property Types
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
	}
	{	#Property Names; sourced from detads by Daniel Schepler
		$Symbol_Property[1]		= 'doAction';
		$Symbol_Property[2]		= 'verb';
		$Symbol_Property[3]		= 'noun';
		$Symbol_Property[4]		= 'adjective';
		$Symbol_Property[5]		= 'preposition';
		$Symbol_Property[6]		= 'article';
		$Symbol_Property[7]		= 'plural';
		$Symbol_Property[8]		= 'sdesc';
		$Symbol_Property[9]		= 'thedesc';
		$Symbol_Property[10]	= 'doDefault';
#		$Symbol_Property_Argument{10} = [undef, 'actor', 'prep', 'iobj'];
		$Symbol_Property_Argument{10}{1}	= 'actor';
		$Symbol_Property_Argument{10}{2}	= 'prep';
		$Symbol_Property_Argument{10}{3}	= 'iobj';
		$Symbol_Property[11]	= 'ioDefault';
#		$Symbol_Property_Argument{11} = [undef, 'actor', 'prep'];
		$Symbol_Property_Argument{11}{1}	= 'actor';
		$Symbol_Property_Argument{11}{2}	= 'prep';
		$Symbol_Property[12]	= 'ioAction';
		$Symbol_Property[13]	= 'location';
		$Symbol_Property[14]	= 'value';
		$Symbol_Property[15]	= 'roomAction';
#		$Symbol_Property_Argument{15} = [undef, 'actor', 'verb', 'dobj', 'prep', 'iobj'];
		$Symbol_Property_Argument{15}{1}	= 'actor';
		$Symbol_Property_Argument{15}{2}	= 'verb';
		$Symbol_Property_Argument{15}{3}	= 'dobj';
		$Symbol_Property_Argument{15}{4}	= 'prep';
		$Symbol_Property_Argument{15}{5}	= 'iobj';
		$Symbol_Property[16]	= 'actorAction';
#		$Symbol_Property_Argument{16} = [undef, 'verb', 'dobj', 'prep', 'iobj'];
		$Symbol_Property_Argument{16}{1}	= 'verb';
		$Symbol_Property_Argument{16}{2}	= 'dobj';
		$Symbol_Property_Argument{16}{3}	= 'prep';
		$Symbol_Property_Argument{16}{4}	= 'iobj';
		$Symbol_Property[17]	= 'contents';
		$Symbol_Property[18]	= 'tpl';
		$Symbol_Property[19]	= 'prepDefault';
		$Symbol_Property[20]	= 'verActor';
		$Symbol_Property[21]	= 'validDo';
#		$Symbol_Property_Argument{21} = [undef, 'actor', 'obj', 'seqno'];
		$Symbol_Property_Argument{21}{1}	= 'actor';
		$Symbol_Property_Argument{21}{2}	= 'actor';
		$Symbol_Property_Argument{21}{3}	= 'actor';
		$Symbol_Property[22]	= 'validIo';
#		$Symbol_Property_Argument{22} = [undef, 'actor', 'obj', 'seqno'];
		$Symbol_Property_Argument{22}{1}	= 'actor';
		$Symbol_Property_Argument{22}{2}	= 'obj';
		$Symbol_Property_Argument{22}{3}	= 'seqno';
		$Symbol_Property[23]	= 'lookAround';
#		$Symbol_Property_Argument{23} = [undef, 'verbosity'];
		$Symbol_Property_Argument{23}{1}	= 'verbosity';
		$Symbol_Property[24]	= 'roomCheck';
#		$Symbol_Property_Argument{24} = [undef, 'verb'];
		$Symbol_Property_Argument{24}{1}	= 'verb';
		$Symbol_Property[25]	= 'statusLine';
		$Symbol_Property[26]	= 'locationOK';
		$Symbol_Property[27]	= 'isVisible';
#		$Symbol_Property_Argument{27} = [undef, 'vantage'];
		$Symbol_Property_Argument{27}{1}	= 'vantage';
		$Symbol_Property[28]	= 'cantReach';
#		$Symbol_Property_Argument{28} = [undef, 'actor', 'dolist', 'iolist', 'prep'];
		$Symbol_Property_Argument{28}{1}	= 'actor';
		$Symbol_Property_Argument{28}{2}	= 'dolist';
		$Symbol_Property_Argument{28}{3}	= 'iolist';
		$Symbol_Property_Argument{28}{4}	= 'prep';
		$Symbol_Property[29]	= 'isHim';
		$Symbol_Property[30]	= 'isHer';
		$Symbol_Property[31]	= 'action';
#		$Symbol_Property_Argument{31} = [undef, 'actor'];
		$Symbol_Property_Argument{31}{1}	= 'actor';
		$Symbol_Property[32]	= 'validDoList';
#		$Symbol_Property_Argument{32} = [undef, 'actor', 'prep', 'iobj'];
		$Symbol_Property_Argument{32}{1}	= 'actor';
		$Symbol_Property_Argument{32}{2}	= 'prep';
		$Symbol_Property_Argument{32}{3}	= 'iobj';
		$Symbol_Property[33]	= 'validIoList';
#		$Symbol_Property_Argument{33} = [undef, 'actor', 'prep', 'dobj'];
		$Symbol_Property_Argument{33}{1}	= 'actor';
		$Symbol_Property_Argument{33}{2}	= 'prep';
		$Symbol_Property_Argument{33}{3}	= 'dobj';
		$Symbol_Property[34]	= 'iobjGen';
#		$Symbol_Property_Argument{34} = [undef, 'actor', 'verb', 'dobj', 'prep'];
		$Symbol_Property_Argument{34}{1}	= 'actor';
		$Symbol_Property_Argument{34}{2}	= 'verb';
		$Symbol_Property_Argument{34}{3}	= 'dobj';
		$Symbol_Property_Argument{34}{4}	= 'prep';
		$Symbol_Property[35]	= 'dobjGen';
#		$Symbol_Property_Argument{35} = [undef, 'actor', 'verb', 'iobj', 'prep'];
		$Symbol_Property_Argument{35}{1}	= 'actor';
		$Symbol_Property_Argument{35}{2}	= 'verb';
		$Symbol_Property_Argument{35}{3}	= 'iobj';
		$Symbol_Property_Argument{35}{4}	= 'prep';
		$Symbol_Property[36]	= 'nilPrep';
		$Symbol_Property[37]	= 'rejectMultiDobj';
#		$Symbol_Property_Argument{37} = [undef, 'prep'];
		$Symbol_Property_Argument{37}{1}	= 'prep';
		$Symbol_Property[38]	= 'moveInto';
#		$Symbol_Property_Argument{38} = [undef, 'dest'];
		$Symbol_Property_Argument{38}{1}	= 'dest';
		$Symbol_Property[39]	= 'construct';
		$Symbol_Property[40]	= 'destruct';
		$Symbol_Property[41]	= 'validActor';
		$Symbol_Property[42]	= 'preferredActor';
		$Symbol_Property[43]	= 'isEquivalent';
		$Symbol_Property[44]	= 'adesc';
		$Symbol_Property[45]	= 'multisdesc';
		$Symbol_Property[46]	= 'tpl2';
		$Symbol_Property[47]	= 'anyvalue';
#		$Symbol_Property_Argument{47} = [undef, 'num'];
		$Symbol_Property_Argument{47}{1}	= 'num';
		$Symbol_Property[48]	= 'newNumbered';
#		$Symbol_Property_Argument{48} = [undef, 'actor', 'verb', 'num'];
		$Symbol_Property_Argument{48}{1}	= 'actor';
		$Symbol_Property_Argument{48}{2}	= 'verb';
		$Symbol_Property_Argument{48}{3}	= 'num';
#		$Symbol_Property[49]	= 'unknown';
		$Symbol_Property[50]	= 'parseUnknownDobj';
#		$Symbol_Property_Argument{50} = [undef, 'actor', 'prep', 'iobj', 'wordlist'];
		$Symbol_Property_Argument{50}{1}	= 'actor';
		$Symbol_Property_Argument{50}{2}	= 'prep';
		$Symbol_Property_Argument{50}{3}	= 'iobj';
		$Symbol_Property_Argument{50}{4}	= 'wordlist';
		$Symbol_Property[51]	= 'parseUnknownIobj';
#		$Symbol_Property_Argument{51} = [undef, 'actor', 'prep', 'iobj', 'wordlist'];
		$Symbol_Property_Argument{51}{1}	= 'actor';
		$Symbol_Property_Argument{51}{2}	= 'prep';
		$Symbol_Property_Argument{51}{3}	= 'iobj';
		$Symbol_Property_Argument{51}{4}	= 'wordlist';
		$Symbol_Property[52]	= 'dobjCheck';
#		$Symbol_Property_Argument{52} = [undef, 'actor', 'prep', 'iobj', 'prep'];
		$Symbol_Property_Argument{52}{1}	= 'actor';
		$Symbol_Property_Argument{52}{2}	= 'prep';
		$Symbol_Property_Argument{52}{3}	= 'iobj';
		$Symbol_Property_Argument{52}{4}	= 'wordlist';	# detads says this is second prep
		$Symbol_Property[53]	= 'iobjCheck';
#		$Symbol_Property_Argument{53} = [undef, 'actor', 'prep', 'iobj', 'prep'];
		$Symbol_Property_Argument{53}{1}	= 'actor';
		$Symbol_Property_Argument{53}{2}	= 'prep';
		$Symbol_Property_Argument{53}{3}	= 'iobj';
		$Symbol_Property_Argument{53}{4}	= 'wordlist';	# detads says this is second prep
		$Symbol_Property[54]	= 'verbAction';
#		$Symbol_Property_Argument{54} = [undef, 'actor', 'dobj', 'prep', 'iobj'];
		$Symbol_Property_Argument{51}{1}	= 'actor';
		$Symbol_Property_Argument{51}{2}	= 'dobj';
		$Symbol_Property_Argument{51}{3}	= 'prep';
		$Symbol_Property_Argument{51}{4}	= 'iobj';
		$Symbol_Property[55]	= 'disambigDobj';
#		$Symbol_Property_Argument{55} = [undef, 'actor', 'prep', 'iobj', 'verprop', 'wordlist', 'objlist', 'flaglist', 'numberWanted', 'isAmbiguous', 'silent'];
		$Symbol_Property_Argument{55}{1}	= 'actor';
		$Symbol_Property_Argument{55}{2}	= 'prep';
		$Symbol_Property_Argument{55}{3}	= 'iobj';
		$Symbol_Property_Argument{55}{4}	= 'verprop';
		$Symbol_Property_Argument{55}{5}	= 'wordlist';
		$Symbol_Property_Argument{55}{6}	= 'objlist';
		$Symbol_Property_Argument{55}{7}	= 'flaglist';
		$Symbol_Property_Argument{55}{8}	= 'numberWanted';
		$Symbol_Property_Argument{55}{9}	= 'isAmbiguous';
		$Symbol_Property_Argument{55}{10}	= 'silent';
		$Symbol_Property[56]	= 'disambigIobj';
#		$Symbol_Property_Argument{56} = [undef, 'actor', 'prep', 'dobj', 'verprop', 'wordlist', 'objlist', 'flaglist', 'numberWanted', 'isAmbiguous', 'silent'];
		$Symbol_Property_Argument{56}{1}	= 'actor';
		$Symbol_Property_Argument{56}{2}	= 'prep';
		$Symbol_Property_Argument{56}{3}	= 'iobj';
		$Symbol_Property_Argument{56}{4}	= 'verprop';
		$Symbol_Property_Argument{56}{5}	= 'wordlist';
		$Symbol_Property_Argument{56}{6}	= 'objlist';
		$Symbol_Property_Argument{56}{7}	= 'flaglist';
		$Symbol_Property_Argument{56}{8}	= 'numberWanted';
		$Symbol_Property_Argument{56}{9}	= 'isAmbiguous';
		$Symbol_Property_Argument{56}{10}	= 'silent';
		$Symbol_Property[57]	= 'prefixdesc';
#		$Symbol_Property_Argument{57} = [undef, 'show', 'current_index', 'count', 'multi_flags'];
		$Symbol_Property_Argument{57}{1}	= 'show';
		$Symbol_Property_Argument{57}{2}	= 'current_index';
		$Symbol_Property_Argument{57}{3}	= 'count';
		$Symbol_Property_Argument{57}{4}	= 'multi_flags';
		$Symbol_Property[58]	= 'isThem';
	}
	{	#Builtin functions; sourced from detads by Daniel Schepler
		$Symbol_Builtin[0]	= 'say';
		$Symbol_Builtin[1]	= 'car';
		$Symbol_Builtin[2]	= 'cdr';
		$Symbol_Builtin[3]	= 'length';
		$Symbol_Builtin[4]	= 'randomize';
		$Symbol_Builtin[5]	= 'rand';
		$Symbol_Builtin[6]	= 'substr';
		$Symbol_Builtin[7]	= 'cvtstr';
		$Symbol_Builtin[8]	= 'cvtnum';
		$Symbol_Builtin[9]	= 'upper';
		$Symbol_Builtin[10]	= 'lower';
		$Symbol_Builtin[11]	= 'caps';
		$Symbol_Builtin[12]	= 'find';
		$Symbol_Builtin[13]	= 'getarg';
		$Symbol_Builtin[14]	= 'datatype';
		$Symbol_Builtin[15]	= 'setdaemon';
		$Symbol_Builtin[16]	= 'setfuse';
		$Symbol_Builtin[17]	= 'setversion';
		$Symbol_Builtin[18]	= 'notify';
		$Symbol_Builtin[19]	= 'unnotify';
		$Symbol_Builtin[20]	= 'yorn';
		$Symbol_Builtin[21]	= 'remfuse';
		$Symbol_Builtin[22]	= 'remdaemon';
		$Symbol_Builtin[23]	= 'incturn';
		$Symbol_Builtin[24]	= 'quit';
		$Symbol_Builtin[25]	= 'save';
		$Symbol_Builtin[26]	= 'restore';
		$Symbol_Builtin[27]	= 'logging';
		$Symbol_Builtin[28]	= 'input';
		$Symbol_Builtin[29]	= 'setit';
		$Symbol_Builtin[30]	= 'askfile';
		$Symbol_Builtin[31]	= 'setscore';
		$Symbol_Builtin[32]	= 'firstobj';
		$Symbol_Builtin[33]	= 'nextobj';
		$Symbol_Builtin[34]	= 'isclass';
		$Symbol_Builtin[35]	= 'restart';
		$Symbol_Builtin[36]	= 'debugTrace';
		$Symbol_Builtin[37]	= 'undo';
		$Symbol_Builtin[38]	= 'defined';
		$Symbol_Builtin[39]	= 'proptype';
		$Symbol_Builtin[40]	= 'outhide';
		$Symbol_Builtin[41]	= 'runfuses';
		$Symbol_Builtin[42]	= 'rundaemons';
		$Symbol_Builtin[43]	= 'gettime';
		$Symbol_Builtin[44]	= 'getfuse';
		$Symbol_Builtin[45]	= 'intersect';
		$Symbol_Builtin[46]	= 'inputkey';
		$Symbol_Builtin[47]	= 'objwords';
		$Symbol_Builtin[48]	= 'addword';
		$Symbol_Builtin[49]	= 'delword';
		$Symbol_Builtin[50]	= 'getwords';
		$Symbol_Builtin[51]	= 'nocaps';
		$Symbol_Builtin[52]	= 'skipturn';
		$Symbol_Builtin[53]	= 'clearscreen';
		$Symbol_Builtin[54]	= 'firstsc';
		$Symbol_Builtin[55]	= 'verbinfo';
		$Symbol_Builtin[56]	= 'fopen';
		$Symbol_Builtin[57]	= 'fclose';
		$Symbol_Builtin[58]	= 'fwrite';
		$Symbol_Builtin[59]	= 'fread';
		$Symbol_Builtin[60]	= 'fseek';
		$Symbol_Builtin[61]	= 'fseekeof';
		$Symbol_Builtin[62]	= 'ftell';
		$Symbol_Builtin[63]	= 'outcapture';
		$Symbol_Builtin[64]	= 'systemInfo';
		$Symbol_Builtin[65]	= 'morePrompt';
		$Symbol_Builtin[66]	= 'parserSetMe';
		$Symbol_Builtin[67]	= 'parserGetMe';
		$Symbol_Builtin[68]	= 'reSearch';
		$Symbol_Builtin[69]	= 'reGetGroup';
		$Symbol_Builtin[70]	= 'inputevent';
		$Symbol_Builtin[71]	= 'timeDelay';
		$Symbol_Builtin[72]	= 'setOutputFilter';
		$Symbol_Builtin[73]	= 'execCommand';
		$Symbol_Builtin[74]	= 'parserGetObj';
		$Symbol_Builtin[75]	= 'parseNounList';
		$Symbol_Builtin[76]	= 'parserTokenize';
		$Symbol_Builtin[77]	= 'parserGetTokTypes';
		$Symbol_Builtin[78]	= 'parserDictLookup';
		$Symbol_Builtin[79]	= 'parserResolveObjects';
		$Symbol_Builtin[80]	= 'parserReplaceCommand';
		$Symbol_Builtin[81]	= 'exitobj';
		$Symbol_Builtin[82]	= 'inputdialog';
		$Symbol_Builtin[83]	= 'resourceExists';
	}
	{	#Opcodes; based on https://github.com/garglk/garglk/blob/master/tads/tads2/opc.h
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
	}
	{	#Opcode Operands; based on detads, naming convention, and trial and error
		$Constant_Opcode_Operand[0x01]	= ['INT32'];						# 1		OPCPUSHNUM
		$Constant_Opcode_Operand[0x02]	= ['OBJECT'];						# 2		OPCPUSHOBJ
		$Constant_Opcode_Operand[0x03]	= ['NONE'];							# 3		OPCNEG
		$Constant_Opcode_Operand[0x04]	= ['NONE'];							# 4		OPCNOT
		$Constant_Opcode_Operand[0x05]	= ['NONE'];							# 5		OPCADD
		$Constant_Opcode_Operand[0x06]	= ['NONE'];							# 6		OPCSUB
		$Constant_Opcode_Operand[0x07]	= ['NONE'];							# 7		OPCMUL
		$Constant_Opcode_Operand[0x08]	= ['NONE'];							# 8		OPCDIV
		$Constant_Opcode_Operand[0x09]	= ['NONE'];							# 9		OPCAND
		$Constant_Opcode_Operand[0x0A]	= ['NONE'];							# 10	OPCOR
		$Constant_Opcode_Operand[0x0B]	= ['NONE'];							# 11	OPCEQ
		$Constant_Opcode_Operand[0x0C]	= ['NONE'];							# 12	OPCNE
		$Constant_Opcode_Operand[0x0D]	= ['NONE'];							# 13	OPCGT
		$Constant_Opcode_Operand[0x0E]	= ['NONE'];							# 14	OPCGE
		$Constant_Opcode_Operand[0x0F]	= ['NONE'];							# 15	OPCLT
		$Constant_Opcode_Operand[0x10]	= ['NONE'];							# 16	OPCLE
		$Constant_Opcode_Operand[0x11]	= ['UINT8', 'OBJECT'];				# 17	OPCCALL
		$Constant_Opcode_Operand[0x12]	= ['UINT8', 'PROPERTY'];			# 18	OPCGETP
		$Constant_Opcode_Operand[0x13]	= ['UINT8', 'PROPERTY'];			# 19	OPCGETPDATA		Experimental based on 0x12
		$Constant_Opcode_Operand[0x14]	= ['LOCAL'];						# 20	OPCGETLCL
		$Constant_Opcode_Operand[0x15]	= ['UINT8'];						# 21	OPCPTRGETPDATA	Experimental based on 0x28
		$Constant_Opcode_Operand[0x16]	= ['UNKNOWN2'];						# 22	OPCRETURN
		$Constant_Opcode_Operand[0x17]	= ['UNKNOWN2'];						# 23	OPCRETVAL
		$Constant_Opcode_Operand[0x18]	= ['UINT16'];						# 24	OPCENTER
		$Constant_Opcode_Operand[0x19]	= ['NONE'];							# 25	OPCDISCARD
		$Constant_Opcode_Operand[0x1A]	= ['OFFSET'];						# 26	OPCJMP
		$Constant_Opcode_Operand[0x1B]	= ['OFFSET'];						# 27	OPCJF
		$Constant_Opcode_Operand[0x1C]	= ['NONE'];							# 28	OPCPUSHSELF
		$Constant_Opcode_Operand[0x1D]	= ['STRING'];						# 29	OPCSAY
		$Constant_Opcode_Operand[0x1E]	= ['UINT8', 'BUILTIN'];				# 30	OPCBUILTIN
		$Constant_Opcode_Operand[0x1F]	= ['STRING'];						# 31	OPCPUSHSTR
		$Constant_Opcode_Operand[0x20]	= ['LIST'];							# 32	OPCPUSHLST
		$Constant_Opcode_Operand[0x21]	= ['NONE'];							# 33	OPCPUSHNIL
		$Constant_Opcode_Operand[0x22]	= ['NONE'];							# 34	OPCPUSHTRUE
		$Constant_Opcode_Operand[0x23]	= ['FUNCTION'];						# 35	OPCPUSHFN
		$Constant_Opcode_Operand[0x24]	= ['UINT8', 'PROPERTY'];			# 36	OPCGETPSELFDATA		Experimental based on 0x3C
		#37 is unused
		$Constant_Opcode_Operand[0x26]	= ['UINT8'];						# 38	OPCPTRCALL
		$Constant_Opcode_Operand[0x27]	= ['UNKNOWN'];						# 39	OPCPTRINH
		$Constant_Opcode_Operand[0x28]	= ['UINT8'];						# 40	OPCPTRGETP
		$Constant_Opcode_Operand[0x29]	= ['PROPERTY'];						# 41	OPCPASS
		$Constant_Opcode_Operand[0x2A]	= ['NONE'];							# 42	OPCEXIT
		$Constant_Opcode_Operand[0x2B]	= ['NONE'];							# 43	OPCABORT
		$Constant_Opcode_Operand[0x2C]	= ['NONE'];							# 44	OPCASKDO
		$Constant_Opcode_Operand[0x2D]	= ['PROPERTY'];						# 45	OPCASKIO
		$Constant_Opcode_Operand[0x2E]	= ['UINT8', 'PROPERTY', 'OBJECT'];	# 46	OPCEXPINH
		$Constant_Opcode_Operand[0x2F]	= ['UNKNOWN'];						# 47	OPCEXPINHPTR
		$Constant_Opcode_Operand[0x30]	= ['UNKNOWN'];						# 48	OPCCALLD
		$Constant_Opcode_Operand[0x31]	= ['UNKNOWN'];						# 49	OPCGETPD
		$Constant_Opcode_Operand[0x32]	= ['UNKNOWN'];						# 50	OPCBUILTIND
		$Constant_Opcode_Operand[0x33]	= ['UNKNOWN'];						# 51	OPCJE
		$Constant_Opcode_Operand[0x34]	= ['UNKNOWN'];						# 52	OPCJNE
		$Constant_Opcode_Operand[0x35]	= ['UNKNOWN'];						# 53	OPCJGT
		$Constant_Opcode_Operand[0x36]	= ['UNKNOWN'];						# 54	OPCJGE
		$Constant_Opcode_Operand[0x37]	= ['UNKNOWN'];						# 55	OPCJLT
		$Constant_Opcode_Operand[0x38]	= ['UNKNOWN'];						# 56	OPCJLE
		$Constant_Opcode_Operand[0x39]	= ['UNKNOWN'];						# 57	OPCJNAND
		$Constant_Opcode_Operand[0x3A]	= ['UNKNOWN'];						# 58	OPCJNOR
		$Constant_Opcode_Operand[0x3B]	= ['OFFSET'];						# 59	OPCJT			Experimental
		$Constant_Opcode_Operand[0x3C]	= ['UINT8', 'PROPERTY'];			# 60	OPCGETPSELF
		$Constant_Opcode_Operand[0x3D]	= ['UINT8', 'PROPERTY'];			# 61	OPCGETPSLFD		Experimental based on 0x3C
		$Constant_Opcode_Operand[0x3E]	= ['UINT8', 'OBJECT', 'PROPERTY'];	# 62	OPCGETPOBJ
		$Constant_Opcode_Operand[0x3F]	= ['UINT8', 'OBJECT', 'PROPERTY'];	# 63	OPCGETPOBJD		Experimental based on 0x3E
		$Constant_Opcode_Operand[0x40]	= ['NONE'];							# 64	OPCINDEX
		#65-66 are unused
		$Constant_Opcode_Operand[0x43]	= ['POINTER'];						# 67	OPCPUSHPN
		$Constant_Opcode_Operand[0x44]	= ['OFFSET'];						# 68	OPCJST
		$Constant_Opcode_Operand[0x45]	= ['OFFSET'];						# 69	OPCJSF
		$Constant_Opcode_Operand[0x46]	= ['UNKNOWN'];						# 70	OPCJMPD
		$Constant_Opcode_Operand[0x47]	= ['UINT8', 'PROPERTY'];			# 71	OPCINHERIT
		$Constant_Opcode_Operand[0x48]	= ['UNKNOWN'];						# 72	OPCCALLEXT
		$Constant_Opcode_Operand[0x49]	= ['UNKNOWN'];						# 73	OPCDBGRET
		$Constant_Opcode_Operand[0x4A]	= ['UINT16'];						# 74	OPCCONS
		$Constant_Opcode_Operand[0x4B]	= ['SWITCH'];						# 75	OPCSWITCH
		$Constant_Opcode_Operand[0x4C]	= ['NONE'];							# 76	OPCARGC
		$Constant_Opcode_Operand[0x4D]	= ['UINT8'];						# 77	OPCCHKARGC
		$Constant_Opcode_Operand[0x4E]	= ['INT32', 'OBJECT', 'UINT16'];	# 78	OPCLINE			Experimental
		$Constant_Opcode_Operand[0x4F]	= ['FRAME'];						# 79	OPCFRAME
		$Constant_Opcode_Operand[0x50]	= ['UNKNOWN'];						# 80	OPCBP
		$Constant_Opcode_Operand[0x51]	= ['UNKNOWN'];						# 81	OPCGETDBLCL
		$Constant_Opcode_Operand[0x52]	= ['UINT8'];						# 82	OPCGETPPTRSELF	Experimental
		$Constant_Opcode_Operand[0x53]	= ['NONE'];							# 83	OPCMOD
		$Constant_Opcode_Operand[0x54]	= ['NONE'];							# 84	OPCBAND
		$Constant_Opcode_Operand[0x55]	= ['NONE'];							# 85	OPCBOR
		$Constant_Opcode_Operand[0x56]	= ['NONE'];							# 86	OPCXOR
		$Constant_Opcode_Operand[0x57]	= ['NONE'];							# 87	OPCBNOT
		$Constant_Opcode_Operand[0x58]	= ['NONE'];							# 88	OPCSHL
		$Constant_Opcode_Operand[0x59]	= ['NONE'];							# 89	OPCSHR
		$Constant_Opcode_Operand[0x5A]	= ['NONE'];							# 90	OPCNEW
		$Constant_Opcode_Operand[0x5B]	= ['NONE'];							# 91	OPCDELETE
	}
}
#Load symbol mapping translation from given file
sub loadSymbols() {
	return unless defined $FileName_Symbol;
	while (my $line = <$File_Symbol>) {
		#Pre-process the line
		chomp $line;
		$line	= (split('#', $line))[0];		# Remove comments
		#Skip ahead if the line doesn't contain anything
		next if($line =~ m/^\s*$/i );
		my $type;
		if($line =~ m/(Action|Act)(\d+)\s*=\s*['"](.*)['"]/i ) {
			$type	 			= $1;
			$Symbol_Action[$2]	= $3;
		}
		if($line =~ m/(Object|Obj)(\d+)\s*=\s*['"](.*)['"]/i ) {
			$type 				= $1;
			$Symbol_Object[$2]	= $3;
		}
		if($line =~ m/(Object|Obj)(\d+)[-_.]?(Arg|Argument)(\d+)\s*=\s*['"](.*)['"]/i ) {
			$type 							= $1 . $3;
			$Symbol_Object_Argument{$2}{$4}	= $5;
#			$Symbol_Object_Argument[$2][$4]	= $5;
		}
		if($line =~ m/(Object|Obj)(\d+)[-_.]?(Loc|Local|Var|Variable)(\d+)\s*=\s*['"](.*)['"]/i ) {
			$type 							= $1 . $3;
			$Symbol_Object_Variable{$2}{$4}	= $5;
#			$Symbol_Object_Variable[$2][$4]	= $5;
		}
		if($line =~ m/(Property|Prop)(\d+)\s*=\s*['"](.*)['"]/i ) {
			$type 					= $1;
			$Symbol_Property[$2]	= $3;
		}
		if($line =~ m/(Property|Prop)(\d+)[-_.]?(Arg|Argument)(\d+)\s*=\s*['"](.*)['"]/i ) {
			$type 								= $1 . $3;
			$Symbol_Property_Argument{$2}{$4}	= $5;
#			$Symbol_Property_Argument[$2][$4]	= $5;
		}
		if($line =~ m/(Object|Obj)(\d+)[-_.]?(Property|Prop)(\d+)[-_.]?(Loc|Local|Var|Variable)(\d+)\s*=\s*['"](.*)['"]/i ) {
			$type									= $1 . $3 . $5;
			$Symbol_Property_Variable{$2}{$4}{$6}	= $7;
#			$Symbol_Property_Variable[$2][$4][$6]	= $7;
		}
#		if($line =~ m/(Property|Prop)(\d+)[-_.]?(Loc|Local|Var|Variable)(\d+)\s*=\s*['"](.*)['"]/i ) {
#			$type 								= $1 . $3;
#			$Symbol_Property_Variable[$2][$4]	= $5;
#		}
#		print $File_Log "Parsed symbol of type $type\n" if defined $type;
		print "Unable to parse $line\n" unless defined $type;
	}
	close $File_Symbol;
}
sub loadFile() {
	$Contents_Compiled	= read_file ( $FileName_Compiled, binmode => ':raw' );
}
##Parsing each content type
sub parse() {
	#Parse header
	parseHeader();
	#The compiled file consists of several blocks of varying length.
	my $pos	= 48;
	for (;;) {
		#Block header of varying length
		my $header_size	= unpack('c', substr($Contents_Compiled, $pos, 1));
		$pos++;
		my $block_type	= substr($Contents_Compiled, $pos, $header_size);
		$pos+=$header_size;
		my $next_pos	= unpack('L', substr($Contents_Compiled, $pos, 4));
		$pos+=4;
		my $block_size	= $next_pos - $pos;
		unless ($block_size) {
			#Stop if size of next block is not positive; usually indicates $EOF block.
			print $File_Log "End-of-File: $block_type \@$next_pos\n";
			last;
		}
		#Log
		print $File_Log "$block_type ($block_size bytes)\n";
		#Parse each block
		my $block		= substr($Contents_Compiled, $pos, $block_size);
		if		($block_type eq '$EOF')		{ last }					# End of file marker; usually not reached due to negative size
		elsif	($block_type eq 'XSI')		{ parseXSI($block) }		# XOR Seed Information
		elsif	($block_type eq 'OBJ')		{ parseOBJ($block) }		# OBJects
		#FST	Fast load information; does not contain anything useful for decompilation
		#INH	Inheritances; not parsed
		elsif	($block_type eq 'FMTSTR')	{ parseFMTSTR($block) }		# ForMaT STRings
		elsif	($block_type eq 'REQ')		{ parseREQ($block) }		# REQuired (?)
		elsif	($block_type eq 'CMPD')		{ parseCMPD($block) }		# CoMPounD words
#TODO	elsif	($block_type eq 'SPECWORD')	{ parseSPECWORD($block) }	# SPECial WORDs
		elsif	($block_type eq 'VOC')		{ parseVOC($block) }		# VOCabulary
		elsif	($block_type eq 'HTMLRES')	{ parseRES($block) }		# Embedded (HTML) RESources
		else	{ print $File_Log "\tUnparsed\n" }
		$pos+=$block_size;
	}
}
sub parseHeader() {
	#The header is 48 bytes long:
	# 0-10	File header signature
	#11-12	Reserved but unused
	#13-18	Compiler version
	#19-20	Flags
	#   21	Unknown, unused?
	#22-45	Build date
	#46-47	Unknown, unused?
	$Compiler_Version	= substr($Contents_Compiled, 13, 6);
	my $flags			= unpack('n', substr($Contents_Compiled, 19, 2));	# Flags are stored as a bitmap, read in as big-endian UINT-16
	$Compiler_Time		= substr($Contents_Compiled, 22, 24);
	#Parse Flags
	$Flags{SymbolTable}		=	$flags & 2**0;
	$Flags{SourceTracking}	=	$flags & 2**1;
	$Flags{Preinit}			=	$flags & 2**2;
	$Flags{Encrypted}		=	$flags & 2**3;
	$Flags{Precompiled}		=	$flags & 2**4;
	$Flags{Fastload}		=	$flags & 2**5;
	$Flags{CaseFolding}		=	$flags & 2**6;
	$Flags{NewStyleLine}	=	$flags & 2**7;
	#Write results to log
	print $File_Log "Decompiler v$Decompiler_Version on $FileName_Compiled (TADS2-$Container_Type file)\n";
	print $File_Log "Compiled by $Compiler_Version at $Compiler_Time\n";
	print $File_Log "\tEnabled flags ($flags):\n";
	print $File_Log "\t\tSymbol table included\n"			if $Flags{SymbolTable};
	print $File_Log "\t\tSource file tracking included\n"	if $Flags{SourceTracking};
	print $File_Log "\t\tPreinit required\n"				if $Flags{Preinit};
	print $File_Log "\t\tEncrypted objects\n"				if $Flags{Encrypted};
	print $File_Log "\t\tHeader precompiled\n"				if $Flags{Precompiled};
	print $File_Log "\t\tFast-load records available\n"		if $Flags{Fastload};
	print $File_Log "\t\tCase folding was turned\n"			if $Flags{CaseFolding};
	print $File_Log "\t\tNew-style line records\n"			if $Flags{NewStyleLine};
}
sub parseXSI($) {
	#XSI blocks contains the XOR Seed Information for the compiled file.
	my $block = shift;
	my $length	= length($block);
	if ($length == 2) {
		#Read initial seed value and increment value
		$Encryption{Seed}		= unpack('C', substr($block, 0, 1));
		$Encryption{Increment}	= unpack('C', substr($block, 1, 1));
	}
	else {
		print $File_Log "ERROR: XSI block is size $length instead of 2; skipping\n";
	}
	print $File_Log "\t($Encryption{Seed}+$Encryption{Increment})\n";
}
sub parseOBJ($) {
	#OBJect blocks contain all the objects of the game
	my $block		= shift;
	my $length		= length($block);
	#Objects are stored sequentially with no count or dividers
	my $pos		= 0;
	while ($pos < $length) {
		#Object Header:
		# 0		Object type
		# 1-2	Object ID (UINT16)
		# 3-4	Unknown (often the same as size)	Object header size?
		# 5-6	Size (UINT16)
		my $type			= unpack('C', substr($block, $pos, 1));
		my $id				= unpack('S', substr($block, $pos + 1, 2));
		my $unknown			= unpack('S', substr($block, $pos + 3, 2));
		my $size			= unpack('S', substr($block, $pos + 5, 2));
		#Read object data, stored in encrypted form
		my $data			= decrypt(substr($block, $pos + 7, $size));
		$pos	+= 7 + $size;
		#Store according to type
		$Stat_Object_Count{$type}++;
		if		($type == 1) { # Function
			#Functions are just code, so we simply store it for later parsing
			print $File_Log "\tObj$id: function ($size bytes)\n"	if $Option_Verbose;
			print $File_Log "\t\tUnknown is $unknown\n"				if $Option_Verbose && $size != $unknown;
			$Objects[$id]	= {
				type		=> $type,
				code		=> $data
			};
		}
		elsif	($type == 2) { # Meta-Object
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
			print $File_Log "\tObj$id: object ($size bytes) in $workspace with $superclasses parents and $properties properties\n" if $Option_Verbose;
			#Read superclasses, a list of UINT16 object ids
			my @superclass;
			for (my $i=0 ; $i<$superclasses ; $i++) {
				push @superclass, unpack('S', substr($data, 14 + 2*$i, 2));
			}
			#Parse properties
			my %property	= ();
			my $pos_data	= 14 + 2 * $superclasses;			# Skip past header and super classes
			$pos_data 		+= 2 * $properties if $flags & 2;	# Skip past property index if needed
			for (my $i=0 ; $i<$properties ; $i++) {
				#Parse property header
				my $prop_id			= unpack('S',	substr($data, $pos_data + 0, 2));
				my $prop_type		= unpack('C',	substr($data, $pos_data + 2));
				my $prop_size		= unpack('S',	substr($data, $pos_data + 3, 2));
				#Flags: 1->Original, 2->Ignore (modified), 4->Deleted Permanently
				my $prop_flag		= unpack('C',	substr($data, $pos_data + 5));
				my $prop_data		= 				substr($data, $pos_data + 6, $prop_size);
				#Store the relevant data
				$property{$prop_id}	= {
					type	=> $prop_type,
					data	=> $prop_data
				} unless $Constant_Property_Type[$prop_type] eq 'demand'; # Demand properties are useless and skipped
				print $File_Log "\t\tProp$prop_id ($prop_size bytes): ".namePropertyType($prop_type)." ($prop_flag)\n" if $Option_Verbose;
				$pos_data += 6 + $prop_size;
				$Stat_Property_Count{$prop_type}++;
				$Property_Max	= $prop_id		if $Property_Max < $prop_id;
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
			print $File_Log "WARNING\tObject$id Unhandled type: $type\n";
		}
	}
	#Print statistics
	my $object_count	= $Stat_Object_Count{1} + $Stat_Object_Count{2};
	print $File_Log "\t$object_count objects in total:\n";
	print $File_Log "\t\t$Stat_Object_Count{1} functions\n";
	print $File_Log "\t\t$Stat_Object_Count{2} meta-objects\n";
	print $File_Log "\tProperty type breakdown:\n";
	for my $type ( sort {$a <=> $b} keys %Stat_Property_Count ) {
		print $File_Log "\t\t$type-$Constant_Property_Type[$type]: $Stat_Property_Count{$type}\n";
	}
}
sub parseFMTSTR($) {
	#ForMaT STRing block
	my $block	= shift;
	my $length	= length($block);
	#FMTSTR has a sub-header which contains the size of the block.
	my $size	= unpack('S', substr($block, 0, 2));
	$block		= decrypt(substr($block, 2));
	print $File_Log "WARNING\tFMTSTR block contains unparsed space" unless $size eq ($length - 2);
	#Format Strings are stored sequentially with no count or dividers
	my $pos		= 0;
	my $found	= 0;
	while ($pos < $size) {
		my $prop	= unpack('S',	substr($block, $pos, 2));
		my $size	= unpack('S',	substr($block, $pos + 2, 2));
		my $text	= 				substr($block, $pos + 4, $size - 2);
		#Generate a name for the property based on the linked text
		my $name_new			= uniformName('fmt '.$text);
		$Symbol_Property[$prop]	= $name_new	unless defined $Symbol_Property[$prop];
		my $prop_rename;
		$prop_rename			= 1				unless $name_new eq $Symbol_Property[$prop];
		#Log the name if we changed it
		print $File_Log	"\tProp$prop: $name_new"		if $prop_rename or $Option_Verbose;
		print $File_Log "\t -> ".nameProperty($prop)	if $prop_rename;
		print $File_Log	"\t($text)\n"					if $prop_rename or $Option_Verbose;
		#Store the format string
		my $format	= "'$text' " . nameProperty($prop);
		push @Formats, $format;
		#Increase and advance
		$found++;
		$pos	+= 2 + $size;
	}
	print $File_Log "\t$found formated strings found\n";
}
sub parseREQ($) {
	#REQuired Functionality block
	my $block	= shift;
	my $length	= length($block);
	#Required functions are stored as an array of UINT16 pointing to the ID of the implementing object; 65535 as null value
	#Exactly how many there are depends on the version of TADS; we currently know the names of 25.
	#Names and arguments for required functions are based on detads by Daniel Schepler and fio.c (from line 589)
	my @obj_names	= ();
	my @arg_names	= ();
	{	#Required function object names and arguments
		$obj_names[0]	= 'Me';
		$obj_names[1]	= 'takeVerb';
		$obj_names[2]	= 'strObj';
		$obj_names[3]	= 'numObj';
		$obj_names[4]	= 'pardon';
		$obj_names[5]	= 'againVerb';
		$obj_names[6]	= 'init';
		$obj_names[7]	= 'preparse';
		$arg_names[7]	= [undef, 'cmd'];
		$obj_names[8]	= 'parseError';
		$arg_names[8]	= [undef, 'num', 'str'];
		$obj_names[9]	= 'commandPrompt';
		$arg_names[9]	= [undef, 'type'];
		$obj_names[10]	= 'parseDisambig';
		$arg_names[10]	= [undef, 'nameString', 'objList'];
		$obj_names[11]	= 'parseError2';
		$arg_names[11]	= [undef, 'verb', 'dobj', 'prep', 'iobj'];
		$obj_names[12]	= 'parseDefault';
		$arg_names[12]	= [undef, 'obj', 'prep'];
		$obj_names[13]	= 'parseAskobj';
		$arg_names[13]	= [undef, 'verb'];
		$obj_names[14]	= 'preparseCmd';
		$arg_names[14]	= [undef, 'wordList'];
		$obj_names[15]	= 'parseAskobjActor';
		$arg_names[15]	= [undef, 'actor', 'verb'];
		$obj_names[16]	= 'parseErrorParam';
		$arg_names[16]	= [undef, 'num', 'str'];
		$obj_names[17]	= 'commandAfterRead';
		$arg_names[17]	= [undef, 'type'];
		$obj_names[18]	= 'initRestore';
		$obj_names[19]	= 'parseUnknownVerb';
		$arg_names[19]	= [undef, 'actor', 'wordlist', 'typelist', 'errnum'];
		$obj_names[20]	= 'parseNounPhrase';
		$arg_names[20]	= [undef, 'wordlist', 'typelist', 'currentIndex', 'complainOnNoMatch', 'isActorCheck'];
		$obj_names[21]	= 'postAction';
		$arg_names[21]	= [undef, 'actor', 'verb', 'dobj', 'prep', 'iobj', 'status'];
		$obj_names[22]	= 'endCommand';
		$arg_names[22]	= [undef, 'actor', 'verb', 'dobj_list', 'prep', 'iobj', 'status'];
		$obj_names[23]	= 'preCommand';
		$arg_names[23]	= [undef, 'actor', 'verb', 'dobj_list', 'prep', 'iobj'];
		$obj_names[24]	= 'parseAskobjIndirect';
		$arg_names[24]	= [undef, 'actor', 'verb', 'prep', 'objectList'];
		$obj_names[25]	= 'preparseExt';		# From fio.c
		$obj_names[26]	= 'parseDefaultExt';	# From fio.c
	}
	my $entries	= $length / 2;
	my $actual	= 0;
	#Try to name objects and arguments based on what functionality they implement
	for my $entry (0 .. $entries - 1) {
		my $obj	= unpack('S', substr($block, $entry * 2, 2));
		unless ($obj eq $Null_Value) {
			$actual++;
			#Update names for object, logging any changes
			if (defined $Symbol_Object[$obj] && $Symbol_Object[$obj] ne $obj_names[$entry]) {
				my $message = "Obj$obj renamed to $obj_names[$entry]\n";
				print $message;
				print $File_Log "INFO\t$message" 
			}
			$Symbol_Object[$obj]	= $obj_names[$entry];
			#Loop through all arguments, if defined
			my $arguments	= -1;
			$arguments		= @{ $arg_names[$entry] } if defined $arg_names[$entry];
			for my $arg(0 .. $arguments) {
				#Update names for argument, logging any changes
				if (defined $Symbol_Object_Argument{$obj}{$arg} && $Symbol_Object_Argument{$obj}{$arg} ne $arg_names[$entry][$arg]) {
					my $message = "Obj$obj-Arg$arg renamed to $arg_names[$entry][$arg]\n";
					print $message;
					print $File_Log "INFO\t$message" 
				}
				$Symbol_Object_Argument{$obj}{$arg} = $arg_names[$entry][$arg];
			}
		}
	}
	print $File_Log "\t$actual required functions implemented and renamed\n";
}
sub parseCMPD($) {
	#CoMPounD word blocks contains contractions for the token parser
	my $block	= shift;
	my $length	= length($block);
	#CMPD has a sub-header which contains the size of the block.
	my $size	= unpack('S', substr($block, 0, 2));
	$block		= decrypt(substr($block, 2));
	print $File_Log "WARNING: CMPD contains unparsed space" unless $size eq ($length - 2);
	#Compounds are stored sequentially with no count or dividers
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
		print $File_Log	"\t$found: $compound\n" if $Option_Verbose;
	}
	print $File_Log "\tFound $found compounds\n";
}
sub parseVOC($) {
	#VOCabulary blocks contain text properties that are used by the parser
	my $block	= shift;
	my $length	= length($block);
	#Compounds are stored sequentially with no count or dividers
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
		unless($flag & 2) {	# Inherited VOCabulary can be skipped
			$found++;
			# Decrypt and extract the text string(s)
			my $data	= decrypt(substr($block, $pos + 10, $size1+$size2));
			my $text	= substr($data, 0, $size1);
			$text		.= ' '.substr($data, $size1, $size2) if ($size2 > 0);
			$text		= cleanText($text, "'");
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
sub parseRES($) {
	#RESource blocks contain embedded files
	my $block	= shift;
	my $length	= length($block);
	#The block is divided into three distinct parts:
	#* Header, defining number of entries and start of data area
	#* ToC with metadata for each entry
	#* Embedded data for each entry
	# UINT32 Number of entries
	# UINT32 Data offset
	my $entries	= unpack('L', substr($block, 0, 4));
	my $offset	= unpack('L', substr($block, 4, 4));
	print $File_Log "\t$entries Resources\n";
	#Read metadata and embedded data for each entry in one pass
	print "Extracting $entries Resources...\n" unless $Option_Minimal or $entries == 0;
	my $pos		= 8;
	for my $i (1 .. $entries) {
		#Metadata
		my $data_pos	= unpack('L',	substr($block, $pos, 4));
		my $size		= unpack('L',	substr($block, $pos + 4, 4));
		my $name_size	= unpack('S',	substr($block, $pos + 8, 2));
		my $name		=				substr($block, $pos + 10, $name_size);
		$pos += $name_size + 10;
		print $File_Log "\t$name ($size bytes)\n";
		#Embedded data, only read when not in minimal mode
		unless ($Option_Minimal) {
			my $path = $FileName_Path.(dirname $name);
			make_path($path);
			my $file_resource;
			open($file_resource, "> :raw :bytes", $FileName_Path . $name)
				or die "$0: can't open $FileName_Path$name in write-open mode: $!";
			print $file_resource substr($block, $data_pos + $offset, $size);
			close $file_resource;
		}
	}
}
##Analyzing cross-type
sub analyze() {
	#Look for action definitions, and use those to name the related actions, objects and properties
	print $File_Log "Analyzing Actions\n";
	analyzeActions();
	#Look through the vocabulary and try to use that to name objects.
	#We do this after actions because the action naming often gives better results.
	print $File_Log "Analyzing Vocabulary\n";
	analyzeVocabulary();
	#Look through the function and property code, converting the bytecode into an array of instructions
	print $File_Log "Analyzing Code Blocks\n";
	analyzeCodeblocks();
	print $File_Log "\tOpcode breakdown:\n";
	for my $type ( sort {$a <=> $b} keys %Stat_Opcode_Count ) {
		print $File_Log "\t\t$type";
		print $File_Log "-$Constant_Opcode[$type]" if defined $Constant_Opcode[$type];
		print $File_Log ": $Stat_Opcode_Count{$type}\n";
	}
	#Analyze properties and generate map file
	analyzeProperties();
	#Analyze superclass inheritance
	analyzeInheritance();
}
#Look through all objects, trying to find actions and verbs
sub analyzeActions() {
	#Actions aren't explicitly numbered so we keep a running tally
	my $action	= 0;
	for my $obj (1 .. $#Objects) {
		#Not all Object ID's are actually used and not all objects have properties
		next unless defined $Objects[$obj] && defined $Objects[$obj]{properties};
		#Look through all properties
		for my $prop ( keys %{ $Objects[$obj]{properties} } ) {
			my $type	= $Objects[$obj]{properties}{$prop}{type};
			unless (defined $type) {
				print $File_Log "\tUnable to analyze $obj.$prop - Missing type";
				warn "Unable to analyze $obj.$prop - Missing type";
				next;
			}
			#TPL2 properties contains the action definitions we are looking for
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
			#Keep track of whether we need to print the object/property header
			my $header_needed			= 1;
			#Log action header if needed
			print $File_Log "\tAction$action \@Obj$obj\n"	if $Option_Verbose;
			undef $header_needed							if $Option_Verbose;
			#Get the existing action name
			my $action_name	= nameAction($action);
			#Try to use the short description (property 8) as name for action and object
			if (defined $Objects[$obj]{properties}{8}) {
				$action_name			= uniformName(propertyString($obj, 8));
				my $verb_name			= $action_name."Verb";
				#Store symbol for action & verb
				$Symbol_Action[$action]	= $action_name	unless defined $Symbol_Action[$action];
				$Symbol_Object[$obj]	= $verb_name	unless defined $Symbol_Object[$obj];
				#Check if updates took hold
				my $action_skipped		= 1;
				my $verb_skipped		= 1;
				undef $action_skipped	if $action_name	eq $Symbol_Action[$action];
				undef $verb_skipped		if $verb_name	eq $Symbol_Object[$obj];
				#Log action header if needed
				print $File_Log "\tAction$action \@Obj$obj\n"	if ($action_skipped or $verb_skipped) && $header_needed;
				undef $header_needed							if $action_skipped or $verb_skipped;
				#Log renamings if needed
				print $File_Log	"\t\tAction: $action_name"		if $action_skipped or $Option_Verbose;
				print $File_Log "\t <- ".nameAction($action)	if $action_skipped;
				print $File_Log	"\n"							if $action_skipped or $Option_Verbose;
				print $File_Log	"\t\tObject: $verb_name"		if $verb_skipped or $Option_Verbose;
				print $File_Log "\t <- ".nameObject($obj)		if $verb_skipped;
				print $File_Log	"\n"							if $verb_skipped or $Option_Verbose;
			}
			#An action defition contains a variable amount of templates, one for each valid preposition
			my $templates	= ord(substr($data, 0));
			for (my $i=0 ; $i < $templates ; $i++) {
				#Each template consists of an object reference (for the preposition) and four property references to call during action processing.
				#At the end there is 5 extra bytes, which seems to be at least in part flag data. UNKNOWN TODO
				my $prep_obj	= unpack('S', substr($data, $i * 16 + 1, 2));	# Preposition object reference
				my $ver_io_prop	= unpack('S', substr($data, $i * 16 + 3, 2));	# IndrectObject verify property reference
				my $exc_io_prop	= unpack('S', substr($data, $i * 16 + 5, 2));	# IndrectObject execute property reference
				my $ver_do_prop	= unpack('S', substr($data, $i * 16 + 7, 2));	# DirectObject verify property reference
				my $exc_do_prop	= unpack('S', substr($data, $i * 16 + 9, 2));	# DirectObject execute property reference
				#Keep track of whether we need to print a sub-header
				my $subheader_needed	= 1;
				#Try to rename the preposition object
				my $preposition			= '';
				unless ($prep_obj eq $Null_Value) { #No preposition
					#Generate a new object name based on the sdesc of the preposition object and store the preposition
					$preposition				= uniformName(propertyString($prep_obj, 8));
					my $new_name				= uniformName($preposition . ' Prep');
					#Rename object
					$Symbol_Object[$prep_obj]	= $new_name	unless defined $Symbol_Object[$prep_obj];
					#Check if updates took hold
					my $skipped					= 1;
					undef $skipped				if $new_name eq $Symbol_Object[$prep_obj];
					#Log action header if needed
					print $File_Log "\tAction$action \@Obj$obj\n"		if $skipped && $header_needed;
					undef $header_needed								if $skipped;
					#Log preposition subheader if needed
					print $File_Log	"\t\t$preposition(Obj$prep_obj):\n"	if $skipped or $Option_Verbose;
					undef $subheader_needed								if $skipped or $Option_Verbose;
					#Log renamings if needed
					print $File_Log	"\t\t\tObj$prep_obj: $new_name"		if $skipped or $Option_Verbose;
					print $File_Log "\t<- ".nameObject($prep_obj)		if $skipped;
					print $File_Log	"\n"								if $skipped or $Option_Verbose;
				}
				#Try to rename each of the four properties; these are similar but slightly different
				if ($ver_io_prop) { #Indirect Object Verification
					#Generate a property name 
					my $name	= uniformName('Ver IO '.$action_name.' '.$preposition);
					#Rename property and arguments, update property-action mapping
					$Property_Actions{$ver_io_prop}	= $action	unless defined $Property_Actions{$ver_io_prop};
					$Symbol_Property[$ver_io_prop]	= $name		unless defined $Symbol_Property[$ver_io_prop];
					$Symbol_Property_Argument{$ver_io_prop}	= {	1 => 'actor' };
					#Check if updates took hold
					my $skipped						= 1;
					my $unmapped					= 1;
					undef $skipped					if $name	eq $Symbol_Property[$ver_io_prop];
					undef $unmapped					if $action	eq $Property_Actions{$ver_io_prop};
					#Log action header if needed
					print $File_Log "\tAction$action \@Obj$obj\n"			if ($skipped or $unmapped) && $header_needed;
					undef $header_needed									if ($skipped or $unmapped);
					#Log preposition subheader if needed
					print $File_Log	"\t\t$preposition:\n"					if ($skipped or $unmapped) && $subheader_needed;
					undef $subheader_needed									if ($skipped or $unmapped);
					#Log renamings if needed
					print $File_Log	"\t\t\tVerIO\tProp$ver_io_prop: $name"	if $skipped or $Option_Verbose;
					print $File_Log "\t<- ".nameProperty($ver_io_prop)		if $skipped;
					print $File_Log "\t(Action $action->$Property_Actions{$ver_io_prop})"	if $unmapped;
					print $File_Log	"\n"									if $skipped or $Option_Verbose;
				}
				if ($exc_io_prop) { #Indirect Object Execution
					#Generate a property name 
					my $name	= uniformName('IO '.$action_name.' '.$preposition);
					#Rename property and arguments, update property-action mapping
					$Property_Actions{$exc_io_prop}	= $action	unless defined $Property_Actions{$exc_io_prop};
					$Symbol_Property[$exc_io_prop]	= $name		unless defined $Symbol_Property[$exc_io_prop];
					$Symbol_Property_Argument{$exc_io_prop}	= {	1 => 'actor', 2 => 'dobj' };
					#Check if updates took hold
					my $skipped						= 1;
					my $unmapped					= 1;
					undef $skipped					if $name	eq $Symbol_Property[$exc_io_prop];
					undef $unmapped					if $action	eq $Property_Actions{$exc_io_prop};
					#Log action header if needed
					print $File_Log "\tAction$action \@Obj$obj\n"			if ($skipped or $unmapped) && $header_needed;
					undef $header_needed									if ($skipped or $unmapped);
					#Log preposition subheader if needed
					print $File_Log	"\t\t$preposition:\n"					if ($skipped or $unmapped) && $subheader_needed;
					undef $subheader_needed									if ($skipped or $unmapped);
					#Log renamings if needed
					print $File_Log	"\t\t\tIO\tProp$exc_io_prop: $name"	if $skipped or $Option_Verbose;
					print $File_Log "\t<- ".nameProperty($exc_io_prop)		if $skipped;
					print $File_Log "\t(Action $action->$Property_Actions{$exc_io_prop})"	if $unmapped;
					print $File_Log	"\n"									if $skipped or $Option_Verbose;
				}
				if ($ver_do_prop) { #Direct Object Verification
					#Generate a property name 
					my $name	= uniformName('Ver DO '.$action_name.' '.$preposition);
					#Rename property and arguments, update property-action mapping
					$Property_Actions{$ver_do_prop}	= $action	unless defined $Property_Actions{$ver_do_prop};
					$Symbol_Property[$ver_do_prop]	= $name		unless defined $Symbol_Property[$ver_do_prop];
					$Symbol_Property_Argument{$ver_do_prop}	= {	1 => 'actor', 2=> 'iobj' }	if ($exc_io_prop);
					$Symbol_Property_Argument{$ver_do_prop}	= {	1 => 'actor' }			unless ($exc_io_prop);
					#Check if updates took hold
					my $skipped						= 1;
					my $unmapped					= 1;
					undef $skipped					if $name	eq $Symbol_Property[$ver_do_prop];
					undef $unmapped					if $action	eq $Property_Actions{$ver_do_prop};
					#Log action header if needed
					print $File_Log "\tAction$action \@Obj$obj\n"			if ($skipped or $unmapped) && $header_needed;
					undef $header_needed									if ($skipped or $unmapped);
					#Log preposition subheader if needed
					print $File_Log	"\t\t$preposition:\n"					if ($skipped or $unmapped) && $subheader_needed;
					undef $subheader_needed									if ($skipped or $unmapped);
					#Log renamings if needed
					print $File_Log	"\t\t\tVerDO\tProp$ver_do_prop: $name"	if $skipped or $Option_Verbose;
					print $File_Log "\t<- ".nameProperty($ver_do_prop)		if $skipped;
					print $File_Log "\t(Action $action->$Property_Actions{$ver_do_prop})"	if $unmapped;
					print $File_Log	"\n"									if $skipped or $Option_Verbose;
				}
				if ($exc_do_prop) { #Direct Object Execution
					#Generate a property name 
					my $name	= uniformName('DO '.$action_name.' '.$preposition);
					#Rename property and arguments, update property-action mapping
					$Property_Actions{$exc_do_prop}	= $action	unless defined $Property_Actions{$exc_do_prop};
					$Symbol_Property[$exc_do_prop]	= $name		unless defined $Symbol_Property[$exc_do_prop];
					$Symbol_Property_Argument{$exc_do_prop}	= {	1 => 'actor', 2=> 'iobj' }	if ($exc_io_prop);
					$Symbol_Property_Argument{$exc_do_prop}	= {	1 => 'actor' }			unless ($exc_io_prop);
					#Check if updates took hold
					my $skipped						= 1;
					my $unmapped					= 1;
					undef $skipped					if $name	eq $Symbol_Property[$exc_do_prop];
					undef $unmapped					if $action	eq $Property_Actions{$exc_do_prop};
					#Log action header if needed
					print $File_Log "\tAction$action \@Obj$obj\n"			if ($skipped or $unmapped) && $header_needed;
					undef $header_needed									if ($skipped or $unmapped);
					#Log preposition subheader if needed
					print $File_Log	"\t\t$preposition:\n"					if ($skipped or $unmapped) && $subheader_needed;
					undef $subheader_needed									if ($skipped or $unmapped);
					#Log renamings if needed
					print $File_Log	"\t\t\tDO\tProp$exc_do_prop: $name"	if $skipped or $Option_Verbose;
					print $File_Log "\t<- ".nameProperty($exc_do_prop)		if $skipped;
					print $File_Log "\t(Action $action->$Property_Actions{$exc_do_prop})"	if $unmapped;
					print $File_Log	"\n"									if $skipped or $Option_Verbose;
				}
			}
			$action++;
		}
	}
}
sub analyzeVocabulary() {
	#Look through the vocabulary of each object to see if we find a suitable name
	#There are four properties we use for naming:
	#2: Verb
	#3: Noun
	#4: Adjective
	#5: Preposition
	#Each can have several string tokens associated, so we take the longest one
	foreach my $obj (0 .. $#Objects) {
		#Not all Object ID's are actually used
		next unless defined $Objects[$obj];
		my $name;
		#First priority is to use the verb
		my $verb_token;
		$verb_token	= bestVocabularyToken($obj, 2, 1)		unless defined $name;
		$name		= uniformName($verb_token . " Verb")	if defined $verb_token;
		#Second priority is to use the preposition
		my $prep_token;
		$prep_token	= bestVocabularyToken($obj, 5, 1)		unless defined $name;
		$name		= uniformName($prep_token . " Prep")	if defined $prep_token;
		#Lastly we try to use the adjective and noun, if we are aggressive on name search
		if ($Option_Naming && not defined $name) {
			#Find the best available noun; stop if none are found
			my $token_noun;
			$token_noun		= bestVocabularyToken($obj, 3, 1);
			#Find the best available adjective
			my $token_adj;
			$token_adj		= bestVocabularyToken($obj, 4, 1);
			#Combine them
			$token_adj	= ''	unless defined $token_adj;
			$name	= uniformName($token_adj . ' ' . $token_noun)	if defined $token_noun;
		}
		#No naming alternatives available
		next unless defined $name;
		#Rename
		$Symbol_Object[$obj]	= $name unless defined $Symbol_Object[$obj];
		#Check if updates took hold
		my $skipped				= 1;
		undef $skipped			if $name eq $Symbol_Object[$obj];
		#Log renamings if needed
		print $File_Log	"\tObj$obj: $name"			if $skipped or $Option_Verbose;
		print $File_Log "\t<- ".nameObject($obj)	if $skipped;
		print $File_Log	"\n"						if $skipped or $Option_Verbose;
	}
}
sub analyzeCodeblocks() {
	#Look through all objects, analyzing the code segments of function objects
	for my $obj (0 .. $#Objects) {
		#Not all Object ID's are actually used
		next unless defined $Objects[$obj];
		#Decode function objects
		if ($Objects[$obj]{type} == 1) {
			unless (defined $Objects[$obj]{code}) {
				print $File_Log "ERROR\tObj$obj\tMissing codeblock; Unable to analyze function code\n";
				next;
			}
			print $File_Log "\tObj$obj: Function Code\n"	if $Option_Verbose;
			#Note the negative ID for object function code
			$Objects[$obj]{instructions}	= analyzeCodeblock(-$obj, $Objects[$obj]{code});
		}
		#Decode property functions
		elsif ($Objects[$obj]{type} == 2) {
			unless (defined $Objects[$obj]{properties}) {
				print $File_Log "ERROR\tObj$obj\tMissing properties; Unable to analyze property code\n";
				next;
			}
			#Loop through all properties
			for my $prop ( keys %{ $Objects[$obj]{properties} } ) {
				my $type	= $Objects[$obj]{properties}{$prop}{type};
				unless (defined $Objects[$obj]{properties}{$prop}{type}) {
					print $File_Log "ERROR\tObj$obj.Prop$prop\tMissing property type; Unable to analyze property code\n";
					next;
				}
				next unless $Constant_Property_Type[$type] eq 'code';
				unless (defined $Objects[$obj]{properties}{$prop}{data}) {
					print $File_Log "ERROR\tObj$obj.Prop$prop\tMissing property data; Unable to analyze property code\n";
					next;
				}
				print $File_Log "\tObj$obj.Prop$prop:\n"	if $Option_Verbose;
				# Note the positive ID for property code
				$Objects[$obj]{properties}{$prop}{instructions}	= analyzeCodeblock($prop, $Objects[$obj]{properties}{$prop}{data});	
			}
		}
		#Unknown object type
		else {
			print $File_Log "ERROR\tObj$obj\tUnknown object type; Unable to analyze property code\n";
			next;
		}
	}
}
sub analyzeCodeblock($$) {
	#Analyzes the given bytecode and returns the easier-to-handle opcodes, which can then be printed
	my $id					= shift;	# Negative for object functions, positive for property code
	my $codeblock			= shift;
	#We store the analyzed code as an array of hashes
	my @instructions		= ();
	#Bytecode has no stored structure and has to be parsed sequentially; size of each opcode is not constant
	my $pos					= 0;
	my $length				= length $codeblock;
	#Some areas shouldn't be parsed by the main parser; mainly switch tables
	my @exclusion_intervals	= ();
	my $exclusion_start		= $length;
	my $exclusion_end		= $length;
	#Parse the block sequentially
	while ($pos < $length) {
		#Read the opcode
		my %instruction	= %{ analyzeOpcode($id, $codeblock, $pos) };
		push @instructions, \%instruction;
		#Store the individual parts for easy access
		my $opcode	= $instruction{opcode};
		my $size	= $instruction{size};
		my $operand	= '';
		{	#Convert operand list to a string
			local $"	= ':';
			my @list	= @{ $instruction{operand} };
			$operand	= "[@list]" if $#list != -1;
		}
		#If we get an invalid opcode, we try to terminate gracefully:
		#All valid opcodes below 192 are defined in the Constant_Opcode list; opcodes above 192 are assignments
		unless (defined $Constant_Opcode[$opcode] or $opcode >= 192) {
			my $bytes = $length - ($pos + $size);
			print $File_Log	"\tObj".(-$id)."\n"	if $id < 0 && not defined $Option_Verbose;
			print $File_Log	"\tProp$id\n"		if $id > 0 && not defined $Option_Verbose;
			print $File_Log	"\t\tUnknown opcode $opcode \@ $pos: possible junk code ($bytes/$length left)\n";
#			debug($codeblock)					if defined $Option_Verbose;
			return \@instructions;
		}
		#Log statistics
		$Stat_Opcode_Count{$opcode}++;
		#If we got a switch table, remember to skip over it later on.
		if ($opcode == 0x4B) {
			my $start	= $instruction{switch_start};
			my $end		= $instruction{switch_end};
			push @exclusion_intervals, {
				start	=> $start,
				end		=> $end
			};
			if ($exclusion_start > $start) {
				$exclusion_start	= $start;
				$exclusion_end		= $end;
			}
			print $File_Log	"\t\t\t($start - $end)\n"	if $Option_Verbose;
		}
		#Print opcode decoding; for switches this has already been printed by analyzeOpcode
		elsif ($Option_Verbose) {
			print $File_Log	"\t\t$pos\t$opcode ($Constant_Opcode[$opcode]) ($size bytes):\t$operand\n"	if $opcode < 192;
			print $File_Log	"\t\t$pos\t$opcode - Assignment ($size bytes):\t$operand\n"					if $opcode >= 192;
		}
		#Increment position and check if we need to skip excluded areas
		$pos += $size;
		if ($pos >= $exclusion_start) {
			#Update position
			$pos	= $exclusion_end;
			#Update next exclusion interval
			my $next_exclusion_start	= $length;
			my $next_exclusion_end		= $length;
			foreach my $ref (@exclusion_intervals) {
				my %interval	= %{ $ref };
				if ($exclusion_start < $interval{start} && $interval{start} < $next_exclusion_start) {
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
sub analyzeOpcode($$$);
sub analyzeOpcode($$$) {
	#Analyzes a codeblock at a given position to find the resulting instruction
	#Called recursively for SWITCH statements.
	my $id			= shift;	# Negative for object functions, positive for property code
	my $codeblock	= shift;
	my $pos			= shift;
	my $length		= length($codeblock);
	#Read in opcode and assemble the instruction
	my $opcode		= unpack('C', substr($codeblock, $pos));
	my $size		= 1;	# The size of the current instruction including embedded operand
	my @operand		= ();
	my %instruction	= ();
	#Opcodes 192 and above are reserved for assignment, which is handled in a special way
	if ($opcode < 192) {
		$instruction{name}		= $Constant_Opcode[$opcode];
		my @templates	= ();
		@templates		= @{ $Constant_Opcode_Operand[$opcode] }	if defined $Constant_Opcode_Operand[$opcode];
#		die "Unknown operand template for opcode $opcode"			if $opcode != 0 and $#templates eq -1;
		foreach my $template (@templates) {
			#Some tads compilations contain unused "junk code" which is never run; If we find unknown opcodes we have to stop gracefully
			if	  ($template eq 'UNKNOWN') {
				#Operand is unknown for this opcode
				#We delay raising an error, as this might come from 'junk code' that is never called
				push @operand, 'UNKNOWN-OPERAND';
			}
			elsif ($template eq 'INT32') {
				#Number embedded as INT32
				my $value	= 'UNKNOWN-INT32';
				$value		= unpack('l', substr($codeblock, $pos + $size, 4))			if ($pos + $size + 4) < $length;
				$size+=4;
				push @operand, $value;
			}
			elsif ($template eq 'UINT16') {
				#Number embedded as UINT16
				my $value	= 'UNKNOWN-UINT16';
				$value		= unpack('S', substr($codeblock, $pos + $size, 2))			if ($pos + $size + 2) < $length;
				$size+=2;
				push @operand, $value;
			}
			elsif ($template eq 'UINT8') {
				#Number embedded as UINT8
				my $value	= 'UNKNOWN-UINT8';
				$value		= unpack('C', substr($codeblock, $pos + $size, 1))			if ($pos + $size + 1) < $length;
				$size++;
				push @operand, $value;
			}
			elsif ($template eq 'OBJECT') {
				#Object ID stored as UINT16
				my $value	= 'UNKNOWN-OBJECT';
				$value		= decodeProperty(2, substr($codeblock, $pos + $size, 2))	if ($pos + $size + 2) < $length;
				$size+=2;
				push @operand, $value;
			}
			elsif ($template eq 'FUNCTION') {
				#Object ID stored as UINT16
				my $value	= 'UNKNOWN-FUNCTION';
				$value		= decodeProperty(10, substr($codeblock, $pos + $size, 2))	if ($pos + $size + 2) < $length;
				$size+=2;
				push @operand, $value;
			}
			elsif ($template eq 'PROPERTY') {
				#Property ID stored as UINT16
				my $value	= 'UNKNOWN-PROPERTY';
				$value		= decodeProperty(13, substr($codeblock, $pos + $size, 2))	if ($pos + $size + 2) < $length;
				$size+=2;
				push @operand, $value;
			}
			elsif ($template eq 'POINTER') {
				#Property ID stored as UINT16
				my $value	= 'UNKNOWN-POINTER';
				$value		= '&'.decodeProperty(13, substr($codeblock, $pos + $size, 2))if ($pos + $size + 2) < $length;
				$size+=2;
				push @operand, $value;
			}
			elsif ($template eq 'LOCAL') {
				#Local variable ID stored as INT16
				my $value	= 'UNKNOWN-LOCAL';
				$value		= nameVariable($id, unpack('s', substr($codeblock, $pos + $size, 2)))	if ($pos + $size + 2) < $length;
				$size+=2;
				push @operand, $value;
			}
			elsif ($template eq 'BUILTIN') {
				#Builtin macro ID stored as UINT16
				my $value	= 'UNKNOWN-BUILTIN';
				$value		= nameBuiltin(unpack('S', substr($codeblock, $pos + $size, 2)))	if ($pos + $size + 2) < $length;;
				$size+=2;
				push @operand, $value;
			}
			elsif ($template eq 'OFFSET') {
				#Address in code block, stored as relative location in INT16
				my $value	= 'UNKNOWN-OFFSET';
				if (($pos + $size + 2) < $length) {
					$value		= unpack('s', substr($codeblock, $pos + $size, 2));
					$value		+= $pos + $size;
				}
				$size		+= 2;
				push @operand, $value;
			}
			elsif ($template eq 'STRING') {
				#String stored as a UINT16 denoting the total length
				my $length	= unpack('S', substr($codeblock, $pos + $size, 2));
				my $value	= 'UNKNOWN-STRING';
				$value		= decodeProperty(9, substr($codeblock, $pos + $size, $length)) if defined $length;
				$size+=$length if defined $length;
				push @operand, $value;
			}
			elsif ($template eq 'LIST') {
				#List stored as a UINT16 denoting the total length
				my $list_length	= unpack('S', substr($codeblock, $pos + $size, 2));
				#Code for handling junk code that's interpreted as OPCPUSHLST (0x20)
				my $value	= '[UNKNOWN-LIST]';
				$value		= decodeProperty(7, substr($codeblock, $pos + $size, $list_length)) if defined $list_length && ($pos + $size + $list_length) < $length;
				$size+=$list_length if defined $list_length;
				push @operand, $value;
			}
			elsif ($template eq 'FRAME') {
				#Debug frame, stored as UINT16 denoting the total length.
				#Skipped in full.
				my $length	= unpack('S', substr($codeblock, $pos + $size, 2));
				$size+=$length if defined $length;
			}
			elsif ($template eq 'SWITCH') {
				#Switch table at offset position
				my $offset	= unpack('S', substr($codeblock, $pos + $size, 2));
				next unless defined $offset;
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
				#Print opcode decoding
				print $File_Log	"\t\t$pos\t$opcode ($Constant_Opcode[$opcode]) ($size bytes):\t$entries entries \@$offset \n"	if $Option_Verbose;
				#Decode each case entry
				for my $case (1 .. $entries) {
					my %instruction		= %{ analyzeOpcode($id, $codeblock, $subpos) };
					$subpos				+= $instruction{size};
					$instruction{target}= $subpos + unpack('s', substr($codeblock, $subpos, 2));
					$subpos				+= 2;
					push @operand, \%instruction;
					#Print the case entry
					if ($Option_Verbose) {
						my $operand	= '';
						{
							local $"	= ':';
							my @list	= @{ $instruction{operand} };
							$operand	= "[@list]" if $#list != -1;
						}
						print $File_Log "\t\t\tCase$case: $operand -> $instruction{target} ($instruction{opcode})\n";
					}
				}
				#Decode switch default
				$instruction{switch_default}	= $subpos + unpack('s', substr($codeblock, $subpos, 2));
				print $File_Log "\t\t\tDefault -> $instruction{switch_default}\n" if $Option_Verbose;
				$subpos+=2;
				$instruction{switch_end}	= $subpos;
			}
			elsif ($template eq 'UNKNOWN2') {
				#Operand of known size but unknown function; skipped
#				my $value	= unpack('s', substr($codeblock, $pos + $size, 2));
				$size+=2;
			}
			else{
				#TODO: Make this more graceful
				die "Unhandled operand $template for opcode $opcode" unless $template eq 'NONE';
			}
		}
	}
	#Assignment opcodes are handled as a bitflag
	else {
		if    (($opcode & 0x03) == 0x00) {
			#Local var embedded as INT16
			my $value	= nameVariable($id, unpack('s', substr($codeblock, $pos + $size, 2)));
			$size+=2;
			push @operand, $value;
		}
		elsif (($opcode & 0x03) == 0x01) {
			#Property embedded as INT16, to be applied to object on stack
			my $value	= nameProperty(unpack('s', substr($codeblock, $pos + $size, 2)));
			$size+=2;
			push @operand, $value;
		}
		if    (($opcode & 0x03) == 0x1c) {
			#Extended opcode
			my $value	= ord(substr($codeblock, $pos + $size, 1));
			$size++;
			push @operand, $value;
		}
	}
	$instruction{pos}		= $pos;
	$instruction{opcode}	= $opcode;
	$instruction{size}		= $size;
	$instruction{operand}	= \@operand;
	return \%instruction;
}
sub analyzeProperties() {
	for my $prop (1 .. $Property_Max) {
		#Write property header
		my $prop_name	= '';
		$prop_name		= "\t'$Symbol_Property[$prop]'"					if defined $Symbol_Property[$prop];
		print $File_PropMap "prop$prop$prop_name\n";
		#Loop through objects to find usage
		for my $obj (0 .. $#Objects) {
			#Not all objects are used
			next unless defined $Objects[$obj];
			#Only meta objects have properties
			next unless $Objects[$obj]{type} == 2;
			#Retrieve type if property is defined for object
			my $prop_type;
			if (defined $Objects[$obj]{properties}{$prop}) {
				$prop_type	= $Objects[$obj]{properties}{$prop}{type}	if defined $Objects[$obj]{properties}{$prop}{type};
				$prop_type	= namePropertyType($prop_type)				if defined $prop_type;
			}
			$prop_type	= 'vocab'										if defined $Objects[$obj]{vocabulary}{$prop};
			if (defined $prop_type) {
				if (length $prop_type < 4) {
					$prop_type	= "$prop_type\t\t";
				}
				elsif (length $prop_type < 8) {
					$prop_type	= "$prop_type\t";
				}
				#Write object usage
				my $obj_name	= '';
				$obj_name		= "\t'$Symbol_Object[$obj]'"			if defined $Symbol_Object[$obj];
				print $File_PropMap "\t$prop_type\tobj$obj$obj_name\n";
			}
		}
	}
}
sub analyzeInheritance() {
	#Loop through objects to find inheritance
	for my $obj (0 .. $#Objects) {
		if (defined $Objects[$obj]{superclass}) {
			my @parents	= @{ $Objects[$obj]{superclass} };
#			print $File_Decompiled "object"		if $#parents == -1;
			foreach my $parent (0 .. $#parents) {
				my $parentObj	= $parents[$parent];
				push @{ $Objects[$parentObj]{children} }, $obj;
#				push @{ $Objects[$obj]{children} }, $parents[$parent];
			}
		}
	}
}
##Generate output
sub generate() {
	print $File_Log "Generating Source\n";
	print $File_Decompiled "//Generated by version $Decompiler_Version of tads2 decompiler by Fictitious Frode at ".localtime."\n";
	print $File_Decompiled "//Based on $FileName_Compiled (TADS2-$Container_Type file)\n";
	print $File_Decompiled "//Compiled by $Compiler_Version at $Compiler_Time\n";
	#TODO: formatstrings
	#generateFMTSTR();
	#TODO: compoundwords
	#generateCMPD();
	#TODO: specialwords
	#generateSPECWORD();
	#Generate object source, one type at a time
	generateOBJ();
}
sub generateOBJ() {
	print $File_Decompiled "\n\n//\t## Function Definitions ##\n";
	#Forward-declare all functions, with naming
	for my $obj (0 .. $#Objects) {
		#Not all objects are used
		next unless defined $Objects[$obj];
		#Only define functions
#		print "Unknown type: obj$obj\n"	unless defined $Objects[$obj]{type};
		next unless defined $Objects[$obj]{type} and $Objects[$obj]{type} == 1;
		#Generate function definitions
		print $File_Decompiled nameObject($obj) . ": function;\n";
	}
	print $File_Decompiled "\n\n//\t## Functions ##\n";
	for my $obj (0 .. $#Objects) {
		#Not all objects are used
		next unless defined $Objects[$obj];
		#Only generate functions
		next unless defined $Objects[$obj]{type} and $Objects[$obj]{type} == 1;
		#Generate function source
		generateOBJFunc($obj);
	}
	print $File_Decompiled "\n\n//\t## Meta-Objects ##\n";
	for my $obj (0 .. $#Objects) {
		#Not all objects are used
		next unless defined $Objects[$obj];
		#Only generate functions
		next unless defined $Objects[$obj]{type} and $Objects[$obj]{type} == 2;
		#Generate meta-object source
		generateOBJMeta($obj);
	}
}
sub generateOBJFunc($) {
	#Generate and print the source for a function
	my $obj	= shift;
	print $File_Log "\tObj$obj: Function\n"	if $Option_Verbose;
	#Include symbol mapping
	print $File_Decompiled	"\n//\tObj$obj\t= '".nameObject($obj)."'\n";
	#Print the instructions, which include the function header
	generateCode($obj, undef, $Objects[$obj]{instructions});

}
sub generateOBJMeta($) {
	#Generate and print the source for a meta-object
	my $obj	= shift;
	#Keep track of whether we need to print the object header
	my $header_needed	= 1;
	#Log object header if needed
	print $File_Log "\tObj$obj: Meta\n"			if $Option_Verbose;
	undef $header_needed						if $Option_Verbose;
	#Object header including symbol mapping
	print $File_Decompiled	"\n//\tObj$obj\t= '".nameObject($obj)."'\n";
	if ($Option_Verbose) {	# Print children/sub-classes
		my @children	= ();
		@children		= @{ $Objects[$obj]{children} }	if defined $Objects[$obj]{children};
		my $instances	= 0;
		my $subClasses	= 0;
		foreach my $child (@children) {
			if ($Objects[$child]{flags}{isClass}) { $subClasses++ }
			else { $instances++ }
		}
		print $File_Decompiled	"//\t$subClasses sub-classes, $instances instances\n";
	}
	print $File_Decompiled 'class ' if $Objects[$obj]{flags}{isClass};
	print $File_Decompiled nameObject($obj) . ': ';
	if (defined $Objects[$obj]{superclass}) {
		my @parents	= @{ $Objects[$obj]{superclass} };
		print $File_Decompiled "object"		if $#parents == -1;
		foreach my $parent (0 .. $#parents) {
			print $File_Decompiled ', ' if $parent > 0;
			print $File_Decompiled nameObject($parents[$parent]);
		}
		print $File_Decompiled "\n";
	}
#	else { print $File_Decompiled "object\n" }
	#Vocabulary properties
	if (defined $Objects[$obj]{vocabulary}) {
		my $count = keys %{ $Objects[$obj]{vocabulary} };
		print $File_Decompiled "\t// $count vocabulary properties\n"		if $count;
		for my $voc ( sort {$a <=> $b} keys %{ $Objects[$obj]{vocabulary} } ) {
			my $name	= nameProperty($voc);
			my $tokens;
			{	#Convert token list to a string
				local $"	= "' '";
				my @list	= @{ $Objects[$obj]{vocabulary}{$voc} };
				$tokens	= "'@list'" if $#list != -1;
			}
			print $File_Decompiled "\t$name\t= $tokens\n";
		}
	}
	#Data properties
	if (defined $Objects[$obj]{properties}) {
		my $count = keys %{ $Objects[$obj]{properties} };
		print $File_Decompiled "\t// $count data properties\n";
		for my $prop ( sort {$a <=> $b} keys %{ $Objects[$obj]{properties} } ) {
			my $prop_type	= $Objects[$obj]{properties}{$prop}{type};
			my $prop_data	= $Objects[$obj]{properties}{$prop}{data};
			unless (defined $prop_type ) {
				#Log object header if needed
				print $File_Log "\tObj$obj Generation:\n"	if $header_needed;
				undef $header_needed;
				print $File_Log "ERROR\tObj$obj.Prop$prop Undefined property type\n";
				next;
			}
			unless (defined $prop_data ) {
				#Log object header if needed
				print $File_Log "\tObj$obj Generation:\n"	if $header_needed;
				undef $header_needed;
				print $File_Log "ERROR\tObj$obj.Prop$prop Undefined property data\n";
				next;
			}
			#Demand - SKIP
			if		($Constant_Property_Type[$prop_type] eq 'demand') {
				next;
			}
			#Action definition (tpl2)
			elsif	($Constant_Property_Type[$prop_type] eq 'tpl2') {
				my $templates	= ord(substr($prop_data, 0));
				for (my $i=0 ; $i<$templates ; $i++) {
					#Determine relevant identifiers from template
					my $prep_obj	= unpack('S', substr($prop_data, $i * 16 + 1, 2)); # Preposition Object
					my $exc_io		= unpack('S', substr($prop_data, $i * 16 + 5, 2)); # Execute IndrectObject Property
					my $exc_do		= unpack('S', substr($prop_data, $i * 16 + 9, 2)); # Property for DirectObject execute
					#Write default preposition
					my $prep_name	= nameObject($prep_obj);
					print $File_Decompiled "\tprepDefault\t= $prep_name\n" if $i == 0 && $prep_obj != $Null_Value;
					#Write action reference
					my $act_name		= nameAction($Objects[$obj]{properties}{$prop}{action});
					my $act_type	= 'doAction';
					my $prep		= '';
					$act_type 		= 'ioAction' 		unless $exc_io eq $Null_Value;
					$prep			= "($prep_name)"	unless $prep_obj eq $Null_Value;
					print $File_Decompiled "\t$act_type$prep\t= '$act_name'\n";
				}
			}
			#Synonym action reference
			elsif	($Constant_Property_Type[$prop_type] eq 'synonym') {
				my $property_target	= unpack('S', $prop_data);
				if (defined $Property_Actions{$prop} && defined $Property_Actions{$property_target}) {
					my $action_target	= nameAction($Property_Actions{$property_target});
					my $action_this		= nameAction($Property_Actions{$prop});
					my $action_type		= nameProperty($prop);
					if ($action_type =~ m/^([id]o)Action/i) {
						print $File_Decompiled "\t$1Synonym('$action_target')\t= '$action_this'\n";
					}
				}
				else {
					print $File_Log "WARNING\tObj$obj.Prop$prop\tSynonym to undefined action at Prop$property_target\n";
				}
			}
			#Action redirect
			elsif	($Constant_Property_Type[$prop_type] eq 'redir') {
				my $object_target	= nameObject(unpack('S', $prop_data));
				my $prop_name		= nameProperty($prop);
				if ($prop_name =~ m/^([id]o)Action/i) {
					print $File_Decompiled "\t$prop_name\t= $object_target\n";
				}
			}
			#Codeblock
			elsif	($Constant_Property_Type[$prop_type] eq 'code') {
				print $File_Log "\t\tObj$obj.Prop$prop Code:\n"	if $Option_Verbose;
				generateCode($obj, $prop, $Objects[$obj]{properties}{$prop}{instructions});
			}
			#Raw value
			else {
				#Works for NUMBER, SSTRING, DSTRING, OBJECT, PROPNUM, FNADDR, NIL, TRUE, DAT_LIST
				#Also covers BASEPTR and TPL which we don't know what to print for
				my $name	= nameProperty($prop);
				my $value	= propertyString($obj, $prop);
				print $File_Decompiled "\t$name\t= $value\n";
			}
		}
	}
}
sub generateCode($) {
	my $obj					= shift;
	my $prop				= shift;
	my $instructions_ref	= shift;
	#Determine if we're generating a property or function source 
	my $print_id	= "Obj$obj";
	my $tab		= '';
	my $mode;
	if (defined $prop) {	#PropID defined, must be property method
		$mode		= 'method';
		$tab		= "\t";
		$print_id	.= ".Prop$prop";
	}
	else {					# Only ObjID defined, must be function
		$mode		= 'function';
	}
#	if ($id < 0) { #Object Function
#		$mode_obj	= 1;
#		$print_id	= "Obj".(-$id);
#	}
#	if ($id > 0) { #Property Method
#		$mode_prop	= 1;
#		$print_id	= "Prop$id";
#	}
	#Restart the VM
	VMinit();
	#Initiate the main branch and decode instructions
	@VM_Instructions	= @{ $instructions_ref };
	VMbranchStart('MAIN', 0, $VM_Instructions[$#VM_Instructions]{pos});
	foreach my $instruction (0 .. $#VM_Instructions) {
		VMexecute($VM_Instructions[$instruction]);
		my $pos			= $VM_Instructions[$instruction]{pos};
		my $location	= "\@$pos/$VM_Label_Next";
		#Check for end of branches
		my ($type, $start, $end)	= VMbranchGet();
		while($end && $end eq $VM_Label_Next) {
#			print $File_Log "Checking Ending for $type: ($start - $end): Labels \@ $VM_Label_Current/$VM_Label_Next\n";
			if ($type eq 'OR') {	
				#Defered evaluation of short-circuited OR
				my $operator		= $Option_PragmaC ? '||' : 'or';
				my $precedence		= 2;
				my ($arg2, $prec2)	= VMstackPop();
				my ($arg1, $prec1)	= VMstackPop();
				#Assemble the operation and push to stack; Note difference in prec comparison
				$arg1				= "($arg1)" if ($prec1 < $precedence);
				$arg2				= "($arg2)" if ($prec2 <= $precedence);
				VMstackPush("$arg1 $operator $arg2", $precedence);
				#End the branch and log branch manipulation for debugging
				VMbranchEnd();
				print $File_Log "OR(END)\t$location ($start-$end)\n"		if $Option_Verbose;
				next;
			}
			if ($type eq 'AND') {
				#Defered evaluation of short-circuited AND
				my $operator		= $Option_PragmaC ? '&&' : 'and';
				my $precedence		= 3;
				my ($arg2, $prec2)	= VMstackPop();
				my ($arg1, $prec1)	= VMstackPop();
				#Assemble the operation and push to stack; Note difference in prec comparison
				$arg1				= "($arg1)" if ($prec1 < $precedence);
				$arg2				= "($arg2)" if ($prec2 <= $precedence);
				VMstackPush("$arg1 $operator $arg2", $precedence);
				#End the branch and log branch manipulation for debugging
				VMbranchEnd();
				print $File_Log "AND(END)\t$location ($start-$end)\n"		if $Option_Verbose;
				next;
			}
			if ($type eq 'CASE') {
				#End of switch case; End the branch and log branch manipulation for debugging
				VMbranchEnd();
				print $File_Log "CASE(END)\t$location\n"	if $Option_Verbose;
				#See if there is a next case to start:
				my @cases		= @{ $VM_Branches[$#VM_Branches]{cases} };
				my $case_next	= $VM_Branches[$#VM_Branches]{case} + 1;
				my $next_pos;
				if ($case_next <= $#cases) {
#				if ($next_case <= $#cases && not $cases[$#cases]{start} eq $cases[$#cases]{end}) {
					my $case_start	= $cases[$case_next]{start};
					my $case_end	= $cases[$case_next]{end};
					$next_pos		= $case_start;
					#Start the next case branch
					$VM_Branches[$#VM_Branches]{case}++;
					warn "ERROR: Case-less switch at $print_id" unless defined $cases[$case_next];
					VMprint("case $cases[$case_next]{text}:");
					VMbranchStart('CASE', $case_start, $case_end);
					#Log branch manipulation for debugging
					print $File_Log "CASE(BEGIN)\t$location, $case_start-$case_end\n"	if $Option_Verbose;
				}
				else {
					#No more cases, continue after the cases
					$next_pos	= $VM_Branches[$#VM_Branches]{end};
					#Close out the SWITCH branch and 'print' a closing bracket
					VMbranchEnd();
					VMprint('}');
					#Log branch manipulation for debugging
					print $File_Log "SWITCH(END)\t$location -> $next_pos  ($start-$end)\n"	if $Option_Verbose;
				}
				#Continue from the correct instruction
				$VM_Label_Current	= $next_pos;
				$VM_Label_Updated++;
				for (my $i=0 ; $i<=$#VM_Instructions ; $i++) {
					if ($VM_Instructions[$i]{pos} eq $next_pos) {
						$instruction = $i-1;
						last;
					}
				}
				next;
			}
			if ($type eq 'IF' or $type eq 'ELSIF') {
				#End of IF branch, with potential ELSE clause; close branch and print closing bracket
				VMbranchEnd();
				VMprint('}');
				#Log branch manipulation for debugging
				print $File_Log "$type(END)\t$location ($start-$end)\n"	if $Option_Verbose;
				next;
			}
			if ($type eq 'MAIN') {
				#End of main branch; ignore it as a return will catch it
				print $File_Log "MAIN(END)\t$location ($start-$end)\n"	if $Option_Verbose;
				last;
			}
			{	#Warn of any unhandled endings
				my $message	= "Unhandled end of branch $type at $pos";
				print $File_Log "\t$print_id\n"	unless $Option_Verbose;
				print $File_Log "ERROR\t$message\n";
				warn "$message for $print_id";
				print $File_Log Dumper(@VM_Branches);
				VMbranchEnd();
				next;
			}
		}
		continue {
			#Update flow control
			($type, $start, $end)	= VMbranchGet();
			#Update labels as needed
			$VM_Label_Current	= $VM_Label_Next if $VM_Label_Update && not $VM_Label_Updated;
		}
		#Check for fatal errors
		if(defined $VM_Fatal_Error) {
			print $File_Log "\t$print_id\n"	unless $Option_Verbose;
			print $File_Log "ERROR\t$VM_Fatal_Error\n";
			warn $VM_Fatal_Error;
			last;
		}
		#Update labels as needed
		$VM_Label_Current	= $VM_Label_Next if $VM_Label_Update && not $VM_Label_Updated;
		#Stop processing when the main loop is terminated
		last if $#VM_Branches eq -1;
	}
	{	#Calculate where labels should be inserted
		@VM_Labels		= sort {$a <=> $b} @VM_Labels;
		#Trim duplicates
		my $distinct = 1;
		while ($distinct < $#VM_Labels) {
			if ($VM_Labels[$distinct-1] eq $VM_Labels[$distinct]) { splice @VM_Labels, $distinct, 1 }
			else { $distinct++ }
		}
		#Find the line corresponding to the position
		for my $label (0 .. $#VM_Labels) {
			my $found;
			#Label could be past the end of the lines
			if ($VM_Lines[$#VM_Lines]{label} < $VM_Labels[$label]) {
				push @VM_Lines, {
					text	=> "label$VM_Labels[$label];",
					label	=> $VM_Labels[$label],
					indent	=> 0
				};
				$found++;
			}
			#Scan through lines in reverse order
			else {
				for (my $line = $#VM_Lines ; $line >= 0 ; $line--) {
					last if $VM_Lines[$line]{label} < $VM_Labels[$label]; #We're past it..
					next if $VM_Lines[$line]{label} > $VM_Labels[$label]; #This is not the one
					$VM_Lines[$line]{print_label}	= 1;
					$found++;
					last;
				}
			}
			unless (defined $found) {
				print $File_Log "\t$print_id\n"	unless $Option_Verbose;
				print $File_Log "ERROR\tUnable to insert label$VM_Labels[$label]\n";
			}
		}
	}
	{	#Assemble header w/ arguments
		my $arguments	= '';
		if ($VM_Arguments) {
			$arguments		= '(';
			foreach my $arg (1 .. $VM_Arguments & 127) {
				$arguments	.= ', '	if $arg > 1;
				$arguments	.= nameFunctionArgument($obj, $arg)	if $mode eq 'function';
				$arguments	.= nameMethodArgument($prop, $arg)	if $mode eq 'method';
				#$arguments	.= nameVariable(-$obj, -$arg);
			}
			$arguments	.= ')';
		}
		my $header;
		$header	= nameObject($obj) . ": function$arguments"		if $mode eq 'function';
		$header	= "\t".nameProperty($prop)."$arguments\t="		if $mode eq 'method';
		print $File_Decompiled "$header\n$tab\{\n";
	}
	{	#Define local variables
		if ($VM_Locals) {
			my $locals	= "\tlocal ";
			$locals		= "\t$locals"	if $mode eq 'method';
			foreach my $var (1 .. $VM_Locals) {
				$locals	.= ', '	if $var > 1;
				$locals	.= nameFunctionVariable($obj, $var)			if $mode eq 'function';
				$locals	.= nameMethodVariable($obj, $prop, $var)	if $mode eq 'method';
			}
			print $File_Decompiled "$locals;\n";
		}
		#Initial values for local variables are often left on stack
		#TODO: Try to fit this into local variable declarations
		print $File_Decompiled "//\tWARNING: Orphaned values left on stack:\n" unless $#VM_Stack eq -1;
		while ($#VM_Stack != -1) {
			my ($value)	= VMstackPop();
			print $File_Decompiled "//\t\t$value\n";
		}
	}
	{	#Print lines
		for (my $line=0 ; $line<=$#VM_Lines ; $line++) {
			my $text;
			my $indent	= $VM_Lines[$line]{indent};
			#Print label if needed
			print $File_Decompiled "label$VM_Lines[$line]{label}:\n" 	if defined $VM_Lines[$line]{print_label};
			#Concatenate subsequent string outputs
			if (defined $VM_Lines[$line]{text} && $VM_Lines[$line]{text} =~ m/^"(.*)";$/m) {
				$text	= '"' . $1;
				my $nextline = $line +1;
				#Ensure are no intervening labels and everything is on the same indentation
				while($nextline <= $#VM_Lines && $VM_Lines[$nextline]{indent} eq $indent && not $VM_Lines[$nextline]{print_label}) {
					if ($VM_Lines[$nextline]{text} =~ m/^"(.*)";$/m) {
						$text	.= $1;
						$nextline++;
					}
					else {	last; }
				}
				$text	.= '";';
				#Skip ahead; subtract 1 for the for-loop increment
				$line = $nextline - 1;
			}
			else {
				#All other output is printed as is
				$text	= $VM_Lines[$line]{text};
			}
			#Indent properly before writing text
			for my $t (0 .. $indent) { print $File_Decompiled "\t"; }
			print $File_Decompiled "$tab$text\n";
		}
		print $File_Decompiled "$tab}\n";
	}
}
##Virtual Machine Simulator
sub VMinit() {
	#Reset everything related to the VM
	@VM_Instructions	= ();
	@VM_Stack			= ();
	@VM_Lines			= ();
	@VM_Branches		= ();
	@VM_Labels			= ();
	$VM_Arguments		= 0;
	$VM_Locals			= 0;
	$VM_Label_Current	= 0;
}
sub VMexecute($;$);
sub VMexecute($;$) {
	#Execute the given instruction on the current state of the VM
	my $instruction_ref	= shift;
	my $location		= shift;
	die "Attempting to execute non-existing instruction" unless defined $instruction_ref;
	#Decode instruction
	my %instruction		= %{ $instruction_ref };
	my $opcode			= $instruction{opcode};
	my $pos				= $instruction{pos};
	my @operand			= @{ $instruction{operand} };
	#Reset execution variables
	undef $VM_Fatal_Error;
	$VM_Label_Update	= 0;
	$VM_Label_Updated	= 0;
	$VM_Label_Next		= $instruction{size} + $instruction{pos};
	$location	 		= "\@$pos/$VM_Label_Next"		unless defined $location;
	#Property Assignments
	if	($opcode >= 192) {	# Bitflag encoded assignment
		my $variable;
		my $operator;
		my $discard;
		my $assignment;
		my $precedence;
		{	#0-1	Variable type	0x03
			my $variable_mask	= $opcode & 0x03;
			#	00	LOCAL	embedded(UINT16)
			#	01	PROP	embedded(UINT16) applied to object from stack
			#	10	(index, list)	from stack
			#	11	(prop, obj)		from stack
			if		($variable_mask == 0x00) {
				#Local variable, stored in operand
				$variable				= shift @operand;
			}
			elsif	($variable_mask == 0x01) {
				#Property from operand applied to object from stack
				my $property			= shift @operand;
				my ($object, $prec)		= VMstackPop();
				$object					= "($object)" if $prec < 13;
				#Assemble variable
				$variable				= "$object.$property";
			}
			elsif	($variable_mask == 0x02) {
				#Index from stack applied to list from stack
				my ($index)				= VMstackPop();
				my ($list, $prec)		= VMstackPop();
				$list			= "($list)" if $prec < 13;
				#Assemble variable
				$variable		= $list . '[' . $index . ']';
			}
			elsif	($variable_mask == 0x03) {
				#Property from stack applied to object from stack
				my ($property)			= VMstackPop();
				my ($object, $prec)		= VMstackPop();
				$object					= "($object)" if ($prec < 13);
				#Assemble variable
				$variable				= $object . '(' . $property . ')';
			}
		}
		{	#2-4	Operation type	0x1c
			my $operator_mask		= $opcode & 0x1C;
			#	000		:=	direct assignment
			#	001		+=	add tos to variable
			#	010		-=	subtract tos from variable
			#	011		*=	multiply variable by tos
			#	100		/=	divide variable by tos
			#	101		++	increment tos
			#	110		--	decrement tos
			#	111			extension flag
			$operator	= ':='	if $operator_mask == 0x00;
			$operator	= '+='	if $operator_mask == 0x04;
			$operator	= '-='	if $operator_mask == 0x08;
			$operator	= '*='	if $operator_mask == 0x0C;
			$operator	= '/='	if $operator_mask == 0x10;
			$operator	= '++'	if $operator_mask == 0x14;
			$operator	= '--'	if $operator_mask == 0x18;
			#If extension flag is set, contains an extra byte in operand:
			#	1	%=	modulo and assign
			#	2	&=	binary AND and assign
			#	3	|=	binary OR and assign
			#	4	^=	binary XOR and assign
			#	5	<<=	shift left and assign
			#	6	>>=	shift right and assign
			if ($operator_mask == 0x1c) {
				my $extended	= shift @operand;
				$operator	= '%='	if $extended == 1;
				$operator	= '&='	if $extended == 2;
				$operator	= '|='	if $extended == 3;
				$operator	= '^='	if $extended == 4;
				$operator	= '<<='	if $extended == 5;
				$operator	= '>>='	if $extended == 6;
			}
		}
		{	#5	Destinationtype
			#	0	leave on stack	implies pre increment/decrement
			#	1	discard 		implies post increment/decrement
			$discard	= $opcode & 0x20;
		}
		{	#Get the value to modify by and build the assignment
			if ($operator eq '++' or $operator eq '--') {
				#Implied value operator; Discard flag indicates post or pre assignment
				$assignment		= "$operator$variable" if $discard;
				$assignment		= "$variable$operator" unless $discard;
				$precedence		= 12;
			}
			else {
				#Get value from stack
				my ($value)		= VMstackPop();
				#Assemble assignment
				$assignment		= "$variable\t$operator $value";
				$precedence		= 0;
			}
		}
		#Perform the assignment based on destination
		if ($discard)	{ VMprint("$assignment;") }				#Treat as discard opcode; add to lines
		else			{ VMstackPush($assignment,$precedence) }#Push back on stack
		return;
	}
	{	#Push value to stack
		if	($opcode == 0x01) {	# OPCPUSHNUM		01
			#Push number from operator to stack
			my $value	= shift @operand;
			VMstackPush($value, 14);
			return;
		}
		if	($opcode == 0x02) {	# OPCPUSHOBJ		02
			#Push object from operator to stack
			my $value	= shift @operand;
			VMstackPush($value, 14);
			return;
		}
		if	($opcode == 0x14) {	# OPCGETLCL			20
			#Push local variable from operator to stack
			my $value	= shift @operand;
			VMstackPush($value, 14);
			return;
		}
		if	($opcode == 0x1F) {	# OPCPUSHSTR		31
			#Push string from operator to stack
			my $value	= shift @operand;
			VMstackPush($value, 14);
			return;
		}
		if	($opcode == 0x20) {	# OPCPUSHLST		32
			#Push list from operator to stack
			my $value	= shift @operand;
			VMstackPush($value, 14);
			return;
		}
		if	($opcode == 0x23) {	# OPCPUSHFN			35
			#Push function reference from operator to stack
			my $value	= shift @operand;
			VMstackPush($value, 14);
			return;
		}
		if	($opcode == 0x43) {	# OPCPUSHPN			67
			#Push pointer from operator to stack
			my $value	= shift @operand;
			VMstackPush($value, 14);
			return;
		}
		if	($opcode == 0x1C) {	# OPCPUSHSELF		28
			#Push static word to stack
			VMstackPush('self', 14);
			return;
		}
		if	($opcode == 0x21) {	# OPCPUSHNIL		33
			#Push static word to stack
			VMstackPush('nil', 14);
			return;
		}
		if	($opcode == 0x22) {	# OPCPUSHTRUE		34
			#Push static word to stack
			VMstackPush('true', 14);
			return;
		}
	}
	{	#Unary operators
		if	($opcode == 0x03) {	# OPCNEG			03
			#Perform unary operation on the top argument from stack, pushing the result back
			my $precedence		= 11;
			my $operator		= '-';
			#Retrieve argument from stack
			my ($arg, $prec)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg				= "($arg)" if ($prec < $precedence);
			VMstackPush("$operator$arg", $precedence);
			return;
		}
		if	($opcode == 0x04) {	# OPCNOT			04
			#Perform unary operation on the top argument from stack, pushing the result back
			my $precedence		= 11;
			my $operator		= 'not ';
			#Retrieve argument from stack
			my ($arg, $prec)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg				= "($arg)" if ($prec < $precedence);
			VMstackPush("$operator$arg", $precedence);
			return;
		}
		if	($opcode == 0x57) {	# OPCBNOT			87
			#Perform unary operation on the top argument from stack, pushing the result back
			my $precedence		= 11;
			my $operator		= '~';
			#Retrieve argument from stack
			my ($arg, $prec)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg				= "($arg)" if ($prec < $precedence);
			VMstackPush("$operator$arg", $precedence);
			return;
		}
		if	($opcode == 0x5A) {	# OPCNEW			90
			#Perform unary operation on the top argument from stack, pushing the result back
			my $precedence		= 11;
			my $operator		= 'new ';
			#Retrieve argument from stack
			my ($arg, $prec)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg				= "($arg)" if ($prec < $precedence);
			VMstackPush("$operator$arg", $precedence);
			return;
		}
		if	($opcode == 0x5B) {	# OPCDELETE			91
			#Perform unary operation on the top argument from stack, pushing the result back
			my $precedence		= 11;
			my $operator		= 'delete ';
			#Retrieve argument from stack
			my ($arg, $prec)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg				= "($arg)" if ($prec < $precedence);
			VMstackPush("$operator$arg", $precedence);
			return;
		}
	}
	{	#Binary operators
		if	($opcode == 0x05) {	# OPCADD			05
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 9;
			my $operator		= '+';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x06) {	# OPCSUB			06
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 9;
			my $operator		= '-';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x07) {	# OPCMUL			07
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 10;
			my $operator		= '*';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x08) {	# OPCDIV			08
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 10;
			my $operator		= '/';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x09) {	# OPCAND			09
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 3;
			my $operator		= $Option_PragmaC ? '&&' : 'and';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x0A) {	# OPCOR				10
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 2;
			my $operator		= $Option_PragmaC ? '||' : 'or';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x0B) {	# OPCEQ				11
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 7;
			my $operator		= $Option_PragmaC ? '==' : '=';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x0C) {	# OPCNE				12
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 7;
			my $operator		= $Option_PragmaC ? '!=' : '<>';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x0D) {	# OPCGT				13
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 7;
			my $operator		= '>';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x0E) {	# OPCGE				14
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 7;
			my $operator		= '>=';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x0F) {	# OPCLT				15
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 7;
			my $operator		= '<';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x10) {	# OPCLE				16
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 7;
			my $operator		= '<=';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x53) {	# OPCMOD			83
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 10;
			my $operator		= '%';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x54) {	# OPCBAND			84
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 6;
			my $operator		= '&';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x55) {	# OPCBOR			85
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 4;
			my $operator		= '|';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x56) {	# OPCXOR			86
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 5;
			my $operator		= '^';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x58) {	# OPCSHL			88
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 8;
			my $operator		= '<<';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
		if	($opcode == 0x59) {	# OPCSHR			89
			#Perform binary operation on top two arguments from stack, pushing the result back
			my $precedence		= 8;
			my $operator		= '>>';
			#Retrieve arguments from stack
			my ($arg2, $prec2)	= VMstackPop();
			my ($arg1, $prec1)	= VMstackPop();
			#Assemble operation and push result to stack
			$arg2		= "($arg2)" if ($prec2 <= $precedence);
			$arg1		= "($arg1)" if ($prec1 < $precedence); # Note difference in prec comparison
			VMstackPush("$arg1 $operator $arg2", $precedence);
			return;
		}
	}
	{	#List operators
		if	($opcode == 0x40) {	# OPCINDEX			64
			#Index from stack applied to list from stack
			my $precedence		= 13;
			my ($index)			= VMstackPop();
			my ($list, $prec)	= VMstackPop();
			#Assemble operation and push result to stack
			$list				= "($list)"	if ($prec < $precedence);
			VMstackPush($list .'['. $index . ']', $precedence);
			return;
		}
		if	($opcode == 0x4A) {	# OPCCONS			74
			#Construct a new list with number of elements from operand, retrieved from stack
			my $precedence		= 14;
			my $element_count	= shift @operand;
			#Assemble list
			my $list		= '[';
			foreach my $elm (0..$element_count) {
				$list			.= ' '		if $elm > 0;	# NOTE: TADS does not use a list separator
				#Retrieve element from stack
				my ($element)	= VMstackPop();
				$list			.= $element;
			}
			$list			.= ']';
			#Push list to stack
			VMstackPush($list, $precedence);
			return;
		}
	}
	{	#Function calls
		if	($opcode == 0x11) {	# OPCCALL			17
			#Perform a function call to object in operand and push result to stack
			my $precedence		= 13;
			my $argument_count	= shift @operand;
			my $function		= shift @operand;
			#Extract arguments from stack
			my $arguments	= VMstackArguments($argument_count);
			#Push assembled function call with arguments back to stack
			VMstackPush("$function$arguments", $precedence);
			return;
		}
		if	($opcode == 0x12) {	# OPCGETP			18
			#Perform a call to property in operand on object from stack and push result to stack
			my $precedence		= 13;
			my $argument_count	= shift @operand;
			my $property		= shift @operand;
			my ($object, $prec)	= VMstackPop();
			#Extract arguments from stack
			my $arguments	= VMstackArguments($argument_count);
			#Push assembled function call with arguments back to stack
			$object			= "($object)" if $prec < $precedence;
			VMstackPush("$object.$property$arguments", $precedence);
			return;
		}
		if	($opcode == 0x13) {	# OPCGETPDATA		19	EXPERIMENTAL
			#Perform a call to property in operand on object from stack and push result to stack
			#EXPERIMENTAL: Assumed to be functionally identical to 0x12
			my $precedence		= 13;
			my $argument_count	= shift @operand;
			my $property		= shift @operand;
			my ($object, $prec)	= VMstackPop();
			#Extract arguments from stack
			my $arguments	= VMstackArguments($argument_count);
			#Push assembled function call with arguments back to stack
			$object			= "($object)" if $prec < $precedence;
			VMstackPush("$object.$property$arguments", $precedence);
			return;
		}
		if	($opcode == 0x15) {	# OPCPTRGETPDATA	21	EXPERIMENTAL
			#Perform a call to property from stack on object from stack and push result to stack
			#EXPERIMENTAL: Assumed to be functionally identical to 0x28
			my $precedence		= 13;
			my $argument_count	= shift @operand;
			my ($property)		= VMstackPop();
			my ($object, $prec)	= VMstackPop();
			#Extract arguments from stack
			my $arguments	= VMstackArguments($argument_count);
			#Push assembled function call with arguments back to stack
			$property		= "($property)";	# Always need paranthesis?
			$object			= "($object)" if $prec < $precedence;
			VMstackPush("$object.$property$arguments", $precedence);
			return;
		}
		if	($opcode == 0x24) {	# OPCGETPSELFDATA	36	EXPERIMENTAL
			#Perform a call to property in operand on self and push result to stack
			#EXPERIMENTAL: Assumed to be functionally identical to 0x3C
			my $precedence		= 13;
			my $argument_count	= shift @operand;
			my $property		= shift @operand;
			#Extract arguments from stack
			my $arguments	= VMstackArguments($argument_count);
			#Push assembled function call with arguments back to stack
			VMstackPush("self.$property$arguments", $precedence);
			return;
		}
		if	($opcode == 0x26) {	# OPCPTRCALL		38
			#Perform a call to property in operand and push result to stack
			my $precedence		= 13;
			my $argument_count	= shift @operand;
			my ($property)		= VMstackPop();
			#Extract arguments from stack
			my $arguments	= VMstackArguments($argument_count);
			#Push assembled function call with arguments back to stack
			$property		= "($property)";	# Always need paranthesis?
			VMstackPush("$property$arguments", $precedence);
			return;
		}
		if	($opcode == 0x28) {	# OPCPTRGETP		40
			#Perform a call to property from stack on object from stack and push result to stack
			my $precedence		= 13;
			my $argument_count	= shift @operand;
			my ($property)		= VMstackPop();
			my ($object, $prec)	= VMstackPop();
			#Extract arguments from stack
			my $arguments	= VMstackArguments($argument_count);
			#Push assembled function call with arguments back to stack
			$property		= "($property)";	# Always need paranthesis?
			$object			= "($object)" if $prec < $precedence;
			VMstackPush("$object.$property$arguments", $precedence);
			return;
		}
		if	($opcode == 0x2E) {	# OPCEXPINH			46
			#Perform an inherited call to property in operand on object in operand and push result to stack
			my $precedence		= 13;
			my $argument_count	= shift @operand;
			my $property		= shift @operand;
			my $object			= shift @operand;
			#Extract arguments from stack
			my $arguments	= VMstackArguments($argument_count);
			#Push assembled function call with arguments back to stack
			VMstackPush("inherited $object.$property$arguments", $precedence);
			return;
		}
		if	($opcode == 0x3C) {	# OPCGETPSELF		60
			#Perform a call to property in operand on self and push result to stack
			my $precedence		= 13;
			my $argument_count	= shift @operand;
			my $property		= shift @operand;
			#Extract arguments from stack
			my $arguments	= VMstackArguments($argument_count);
			#Push assembled function call with arguments back to stack
			VMstackPush("self.$property$arguments", $precedence);
			return;
		}
		if	($opcode == 0x3D) {	# OPCGETPSLFD		61	EXPERIMENTAL
			#Perform a call to property in operand on self and push result to stack
			#EXPERIMENTAL: Assumed to be functionally identical to 0x3C
			my $precedence		= 13;
			my $argument_count	= shift @operand;
			my $property		= shift @operand;
			#Extract arguments from stack
			my $arguments	= VMstackArguments($argument_count);
			#Push assembled function call with arguments back to stack
			VMstackPush("self.$property$arguments", $precedence);
			return;
		}
		if	($opcode == 0x3E) {	# OPCGETPOBJ		62
			#Perform a call to property in operand on object in operand and push result to stack
			my $precedence		= 13;
			my $argument_count	= shift @operand;
			my $object			= shift @operand;
			my $property		= shift @operand;
			#Extract arguments from stack
			my $arguments	= VMstackArguments($argument_count);
			#Push assembled function call with arguments back to stack
			VMstackPush("$object.$property$arguments", $precedence);
			return;
		}
		if	($opcode == 0x3F) {	# OPCGETPOBJD		63	EXPERIMENTAL
			#Perform a call to property in operand on object in operand and push result to stack
			#EXPERIMENTAL: Assumed to be functionally identical to 0x3F
			my $precedence		= 13;
			my $argument_count	= shift @operand;
			my $object			= shift @operand;
			my $property		= shift @operand;
			#Extract arguments from stack
			my $arguments	= VMstackArguments($argument_count);
			#Push assembled function call with arguments back to stack
			VMstackPush("$object.$property$arguments", $precedence);
			return;
		}
		if	($opcode == 0x47) {	# OPCINHERIT		71
			#Perform a call to inherited property in operand and push result to stack
			my $precedence		= 13;
			my $argument_count	= shift @operand;
			my $property		= shift @operand;
			#Extract arguments from stack
			my $arguments	= VMstackArguments($argument_count);
			#Push assembled function call with arguments back to stack
			VMstackPush("inherited $property$arguments", $precedence);
			return;
		}
		if	($opcode == 0x52) {	# OPCGETPPTRSELF	82	EXPERIMENTAL
			#Perform a call to property from stack on self and push result to stack
			my $precedence		= 13;
			my $argument_count	= shift @operand;
			my ($property)		= VMstackPop();
			#Extract arguments from stack
			my $arguments	= VMstackArguments($argument_count);
			#Push assembled function call with arguments back to stack
			VMstackPush("self.$property$arguments", $precedence);
			return;
		}
		if	($opcode == 0x1E) {	# OPCBUILTIN		30
			#Call to builtin function as defined in operand
			my $precedence		= 13;
			my $argument_count	= shift @operand;
			my $type 			= shift @operand;
			#Say (type0) with 2 arguments is a special case
			if ($type eq $Symbol_Builtin[0] && $argument_count == 2) {
				#Inline text substitution: "<< expr >>"
				my $line;
				my ($expr)	= VMstackPop();
				my ($call)	= VMstackPop();
				#The second argument is the object to call on, which is usually nil
				$line		= "\"<<$expr>>\""			if $call eq 'nil';
				$line		= "\"<<$call.$expr>>\""	unless $call eq 'nil';
				#'Print' the substituted line as we discard the value
				VMprint("$line;");
			}
			else{
				#Extract arguments from stack
				my $arguments	= VMstackArguments($argument_count);
				#Push assembled function call with arguments back to stack
				VMstackPush("$type$arguments", $precedence);
			}
			return;
		}
	}
	{	#Output
		if	($opcode == 0x19) {	# OPCDISCARD		25
			#Discard the top element of the stack, which implies a print
			my ($line)		= VMstackPop();
			#'Print' the line
			VMprint("$line;");
			return;
		}
		if	($opcode == 0x1D) {	# OPCSAY			29
			#Say the string in operand
			my $text	= shift @operand;
			VMprint("$text;");
			return;
		}
		if	($opcode == 0x29) {	# OPCPASS			41
			#Pass the property in operand
			my $property	= shift @operand;
			VMprint("pass ($property);");
			return;
		}
		if	($opcode == 0x2A) {	# OPCEXIT			42
			#Signal an Exit
			VMprint("exit;");
			return;
		}
		if	($opcode == 0x2B) {	# OPCABORT			43
			#Signal an Abort
			VMprint("abort;");
			return;
		}
		if	($opcode == 0x2C) {	# OPCASKDO			44
			#Signal an DO verification
			VMprint("askdo;");
			return;
		}
		if	($opcode == 0x2D) {	# OPCASKIO			45
			#Signal an IO verification with property from operand
			my $property	= shift @operand;
			VMprint("askdo($property);");
			return;
		}
	}
	{	#Branch manipulation
		if	($opcode == 0x16) {	# OPCRETURN			22
			#Return from function without any value
			my ($type, $start, $end)	= VMbranchGet();
			#'Print' the line, Suppress valueless returns that terminate the main loop
			VMprint('return;')	unless $type eq 'MAIN';
			#Terminate processing when returning from main branch; other branches are handled in post processing
			VMbranchEnd()		if $type eq 'MAIN';
			#Log branch manipulation for debugging
			print $File_Log "RETURN\t$location\tduring $type($start-$end)\n"	if $Option_Verbose;
			return;
		}
		if	($opcode == 0x17) {	# OPCRETVAL			23
			#Return from function with the top stack value
			my ($value)				= VMstackPop();
			my ($type, $start, $end)= VMbranchGet();
			#'Print' the line
			VMprint("return $value;");
			#Terminate processing when returning from main branch; other branches are handled in post processing
			VMbranchEnd()		if $type eq 'MAIN';
			#Log branch manipulation for debugging
			print $File_Log "RETURN\t$location\tduring $type($start-$end)\n"	if $Option_Verbose;
			return;
		}
		if	($opcode == 0x1A) {	# OPCJMP			26
			#Unconditional jump, can be used in different branching structures:
			#	WHILE	END		Destination is the start of current WHILE branch
			#			BREAK	Destination is the end of topmost WHILE branch
			#	SWITCH	BREAK	Destination is the end of topmost SWITCH branch
			#	ELSIF	ELSE	Destination is the end of current ELSIF branch
			#	GOTO			Otherwise
			my $destination		= shift @operand;	#Jump destination from operand
			#The relevant variables
			my ($type, $start, $end)	= VMbranchGet();
			my $switch_end;
			my $while_end;
			my $jump_type;
			{	#Calculate relevant determination variables
				my $switch_level;
				my $while_level;
				#Find the end of the topmost switch branch
				for (my $lvl = $#VM_Branches ; $lvl >= 0 ; $lvl--) {
					if ($VM_Branches[$lvl]{type} eq 'SWITCH') {
						$switch_end			= $VM_Branches[$lvl]{end};
						$switch_level		= $lvl;
						last;
					}
				}
				#Find the end of the topmost while branch
				for (my $lvl = $#VM_Branches ; $lvl >= 0 ; $lvl--) {
					if ($VM_Branches[$lvl]{type} eq 'WHILE') {
						$while_end			= $VM_Branches[$lvl]{end};
						$while_level		= $lvl;
						last;
					}
				}
				#Only the topmost of the two is relevent to keep
				if (defined $while_end && defined $switch_end) {
					undef $while_end		if $switch_level > $while_level;
					undef $switch_end		if $switch_level < $while_level;
				}
			}
			#Determine the corresponding branching construct
#			{	#DEBUG
#				print $File_Log "JUMP (0x1A) to $destination during $type ($start-$end): $VM_Label_Next\n";
#				print $File_Log "\tLabel:\t $VM_Label_Current\n";
#				print $File_Log "\tDest:\t $destination\n";
#				print $File_Log "\tSwitch\t$switch_end\n"	if defined $switch_end;
#				print $File_Log "\tWhile\t$while_end\n"		if defined $while_end;
#			}
			if	  ($type eq 'WHILE' && $start eq $destination && $end eq $VM_Label_Next) {	# WHILE-END
				$jump_type	= 'WHILE(END)';
				#Close the while branch
				VMbranchEnd();
				#'Print' closing bracket
				VMprint('}');
			}
			elsif (defined $while_end && $while_end eq $destination) {						# WHILE-BREAK
				$jump_type	= 'WHILE(BREAK)';
				#'Print' a break statement
				VMprint('break;');
			}
			elsif (defined $switch_end && $switch_end eq $destination) {					# SWITCH-BREAK
				$jump_type	= 'SWITCH(BREAK)';
				#'Print' a break statement
				VMprint('break;');
			}
			elsif ($type eq 'ELSIF' && $end eq $destination) {								# ELSIF-ELSE
				$jump_type	= 'ELSIF(ELSE)';
				#'Print' an else on the next level down; this can be appended by an IF (0x1B) as next opcode
				VMprint('}', -1);
				VMprint('else {', -1);
			}
			else {																			# GOTO
				$jump_type	= 'GOTO(JMP)';
				#Flag that we need a label at the destination instruction
				push @VM_Labels, $destination;
				#'Print' goto statement
				VMprint("goto label$destination;");
			}
			#Log branch manipulation for debugging
			print $File_Log "$jump_type\t$location to $destination\tduring $type($start-$end)\n"	if $Option_Verbose;
			return;
		}
		if	($opcode == 0x1B) {	# OPCJF				27
			#Conditional jump, can indicate different branching structures:
			#	GOTO			Destination is outside the current branch
			#	WHILE	BEGIN	Destination is just past the an unconditional (26) jump back to label
			#	ELSIF	IF		Destination or (last instruction before it) is an unconditional (26) jump to the end of current ELSIF
			#			BEGIN	Destination is just past an unconditional jump forward inside current branch (1)
			#	IF		BEGIN	Otherwise
			#	(1)	BUG: If the jump just before is a while-break, we detect the wrong kind of loop here
			my $destination		= shift @operand;
			my ($condition)		= VMstackPop();
			#The relevant variables
			my ($type, $start, $end)	= VMbranchGet();
			my $destination_last;				#Destination of last jump, if it's unconditional (0x1A) jump
			my $destination_end	= $destination;	#The final destination if the jump is chained
			my $jump_type;
			#Find the last instruction in the branch, and see if it is a jump
			my $last_opcode;					# Opcode of last intruction in branch
			for (my $destination_id = 0 ; $destination_id <= $#VM_Instructions ; $destination_id++) {
				if ($destination eq $VM_Instructions[$destination_id]{pos}) {
					my $last_id			= ($destination_id - 1);
					$last_opcode		= $VM_Instructions[$last_id]{opcode};
					#Retrieve jump destination if it's an unconditional jump
					$destination_last	= $VM_Instructions[$last_id]{operand}[0] if $last_opcode == 0x1A;
					#Update the final destination if needed
					$destination_end	= $destination_last if defined $destination_last;
					last;
				}
			}
			#Determine the corresponding branching construct
#			{	#DEBUG
#				print $File_Log "JUMP-UNLESS ($condition) (0x1B) during $type ($start-$end)\n";
#				print $File_Log "\tLabel:\t $VM_Label_Current\n";
#				print $File_Log "\tDest:\t $destination\n";
#				print $File_Log "\tLast:\t $destination_last\n"	if defined $destination_last;
#				print $File_Log "\tEnd:\t $destination_end\n"	if defined $destination_end;
#				print $File_Log "\tPrevious Line: $VM_Lines[$#VM_Lines]{text}\n" if $#VM_Lines >= 0;
#			}
			die unless defined $end;
			if	  ($destination < $start or $end < $destination) {												# GOTO
				$jump_type		= 'GOTO(UNLESS)';
				#Flag that we need a label at the destination instruction
				push @VM_Labels, $destination;
				#'Print' goto statement
				VMprint("goto label$destination;");
			}
			elsif (defined $destination_last && $destination_last eq $VM_Label_Current) {						# WHILE(BEGIN)
				$jump_type		= 'WHILE(BEGIN)';
				#'Print' while condition
				VMprint("while ($condition) {");
				#Start new branch
				VMbranchStart('WHILE', $VM_Label_Current, $destination);
			}
			elsif ($type eq 'ELSIF' && $end eq $destination_end && $VM_Lines[$#VM_Lines]{text} eq 'else {') {	#ELSIF(IF)
				$jump_type		= 'ELSIF(IF)';
				#Splice an IF CONDITION into the previous ELSE
				substr ($VM_Lines[$#VM_Lines]{text}, -2, 2, " if ($condition) {");
			}
			elsif (defined $destination_last && $pos < $destination_last && $destination_last <= $end ) {		#ELSIF(BEGIN)
				$jump_type		= 'ELSIF(BEGIN)';
				#'Print' a conditional if
				VMprint("if ($condition) {");
				#Start a new 'else-if' branch
				VMbranchStart('ELSIF', $VM_Label_Current, $destination_last);
			}
			else {																								#IF(BEGIN)
				$jump_type		= 'IF(BEGIN)';
				#'Print' a conditional if
				VMprint("if ($condition) {");
				#Start a new 'else-if' branch
				VMbranchStart('IF', $VM_Label_Current, $destination);
			}
			#Log branch manipulation for debugging
			print $File_Log "$jump_type\t$location to $destination\tduring $type($start-$end)\n"	if $Option_Verbose;
			return;
		}
#		if	($opcode == 0x3B) {	# OPCJT				59
			#Conditional jump, can indicate different branching structures:
			#
#		}
		if	($opcode == 0x44) {	# OPCJST			68
			#Logical short-circuited OR evaluation
			my $destination		= shift @operand;
			#Log branch manipulation for debugging
			my $branch_start	= $VM_Branches[$#VM_Branches]{start};
			my $branch_end		= $VM_Branches[$#VM_Branches]{end};
			my $branch_type		= $VM_Branches[$#VM_Branches]{type};
			print $File_Log "OR(BEGIN)\t$location to $destination\tduring $branch_type($branch_start-$branch_end)\n"	if $Option_Verbose;
			#Add a new branch to execute at ending
			VMbranchStart('OR', $VM_Label_Current, $destination);
			return;
		}
		if	($opcode == 0x45) {	# OPCJSF			69
			#Logical short-circuited AND evaluation
			my $destination		= shift @operand;
			#Log branch manipulation for debugging
			my $branch_start	= $VM_Branches[$#VM_Branches]{start};
			my $branch_end		= $VM_Branches[$#VM_Branches]{end};
			my $branch_type		= $VM_Branches[$#VM_Branches]{type};
			print $File_Log "AND(BEGIN)\t$location to $destination\tduring $branch_type($branch_start-$branch_end)\n"	if $Option_Verbose;
			#Add a new branch to execute at ending
			VMbranchStart('AND', $VM_Label_Current, $destination);
			return;
		}
		if	($opcode == 0x4B) {	# OPCSWITCH			75
			#Switch on the statement from stack according to switching table
			my ($statement)		= VMstackPop();
			my $table_start		= $instruction{switch_start};
			my $table_end		= $instruction{switch_end};
			my @switch_cases	= ();
			{	#Build the switch cases
				#The operand contains a list of instructions to execute in order to get the case value from stack
				foreach my $case_ref (@operand) {
					#Execute case instruction and retrieve value from stack
					VMexecute($case_ref, $location);
					my ($case_text)	= VMstackPop();
					my $target		= %{ $case_ref }{target};
					#Assemble switch case
					push @switch_cases, {
						text	=> $case_text,
						start	=> $target
					};
					#Reset the next label property TODO make sure this is needed
					$VM_Label_Next		= $instruction{size} + $pos;
				}
				#Add the default case
				unless ($instruction{switch_default} eq $table_end) {
					push @switch_cases, {
						text	=> 'default',
						start	=> $instruction{switch_default}
					};
				}
				#Calculate the endpoints for each switch case
				@switch_cases = sort { %{$a}{start} <=> %{$b}{start} } @switch_cases;
				foreach my $case(0..$#switch_cases) {
					my $start		= $switch_cases[$case]{start};
					#Sanity check: Case should never start inside switch table
					if ($table_start <= $start && $start < $table_end) {
						$VM_Fatal_Error	= "Case$case located inside switch table: $start ($table_start-$table_end)";
						return;
					}
					#NOTE: We assume that all cases are before the switch table; might have to redo this
					my $next_start	= $table_start;
					$next_start		= $switch_cases[$case+1]{start} unless $case eq $#switch_cases;
					$switch_cases[$case]{end}	= $next_start;
				}
			}
			#TADS *will* compile games without any cases
			if ($#switch_cases eq -1) {
				print $File_Log "SWITCH(EMPTY)\t$location ($table_start-$table_end)\n"					if $Option_Verbose;
				return;
			}
			#'Print' the switch statement
			VMprint("switch ($statement) {");
			#Start the main switch branch and add switch-specific data
			VMbranchStart('SWITCH', $VM_Label_Current, $table_end);
			$VM_Branches[$#VM_Branches]{cases}	= \@switch_cases;
			$VM_Branches[$#VM_Branches]{case}	= 0;
			#Start the first case branch; Changes between cases is handled by the end of branch code.
			$VM_Label_Current	= $switch_cases[0]{start};
			$VM_Label_Updated++;
			VMprint("case $switch_cases[0]{text}:");
			VMbranchStart('CASE', $switch_cases[0]{start}, $switch_cases[0]{end});
			#Log branch manipulation for debugging
			print $File_Log "SWITCH(BEGIN)\t$location ($table_start-$table_end)\n"						if $Option_Verbose;
			print $File_Log "CASE(BEGIN)\t$location, $switch_cases[0]{start}-$switch_cases[0]{end}\n"	if $Option_Verbose;
			return;
		}
	}
	{	#Function headers
		if	($opcode == 0x18) {	# OPCENTER			24
			#States how many local variables to allocate, and should only apply once per codeblock
			$VM_Fatal_Error			= "Duplicate OPCENTER" if $VM_Locals;
			$VM_Locals				= shift @operand;
			#Update the start of the main codeblock and first label
			$VM_Branches[0]{start}	= $VM_Label_Current;
			$VM_Label_Update++;
			return;
		}
		if	($opcode == 0x4D) {	# OPCCHKARGC		77
			#States how many arguments to take in, and should only apply once per codeblock
			$VM_Fatal_Error			= "Duplicate OPCCHKARGC" if $VM_Arguments;
			$VM_Arguments			= shift @operand;
			#Update the start of the main codeblock and first label
			$VM_Branches[0]{start}	= $VM_Label_Current;
			$VM_Label_Update++;
			return;
		}
		if	($opcode == 0x4E) {	# OPCLINE			78
			#Debug line info; Skipped for now
			return;
		}
		if	($opcode == 0x4F) {	# OPCFRAME			79
			#Debug frame info; Skipped for now
			return;
		}
	}
	#Unhandled opcodes
	$VM_Fatal_Error		= "Unhandled OpCode $opcode";
}
sub VMprint($;$) {
	#'Print' a line with optional indent modifier
	my $line	= shift;
	my $indent	= shift;
	$line		= 'nil;'	unless defined $line;
	$indent		= 0			unless defined $indent;
	push @VM_Lines, {
		text	=> $line,
		label	=> $VM_Label_Current,
		indent	=> $#VM_Branches + $indent
	} unless $line eq 'nil;';
	$VM_Label_Update++;
}
sub VMstackPop() {
	#Retrieve value from stack
	my $value		= 'nil';
	my $precedence	= 14;
	my $reference	= pop @VM_Stack;
	$value			= %{ $reference }{value}		if defined $reference;
	$precedence		= %{ $reference }{precedence}	if defined $reference;
	return ($value, $precedence);
}
sub VMstackPush($$) {
	#Place value on stack
	my $value		= shift;
	my $precedence	= shift;
	$value			= 'nil'	unless defined $value;
	$precedence		= 14	unless defined $precedence;
	push @VM_Stack, {
		value		=> $value,
		precedence	=> $precedence
	};
}
sub VMstackArguments($) {
	my $argument_count	= shift;
	return	''	unless defined $argument_count;
	return	''	if $argument_count == 0;	# NOTE: The TADS-compiler can't handle empty argument list ()
	#Extract arguments from stack
	my $arguments	= '(';
	foreach my $arg (1..$argument_count) {
		$arguments		.= ', '		if $arg > 1;
		my ($argument)	= VMstackPop();
		$arguments		.= $argument;
	}
	$arguments		.= ')';
	return $arguments;
}
sub VMbranchStart($$$) {
	#Start a branch of a given type and interval
	my $type	= shift;
	my $start	= shift;
	my $end		= shift;
	push @VM_Branches, {
		type	=> $type,
		start	=> $start,
		end		=> $end
	};
}
sub VMbranchEnd() {
	#End the top branch
	pop @VM_Branches;
}
sub VMbranchGet() {
	#Returning the type and interval of the top branch
	return ('NONE', 0, 0) if $#VM_Branches eq -1;
	my %branch	= %{ $VM_Branches[$#VM_Branches] };
	return $branch{type}, $branch{start}, $branch{end};
}
##Utility
sub decrypt($) {
	my $block	= shift;
	return $block unless $Flags{Encrypted};
	my $size	= length($block);
	my $mask	= $Encryption{Seed};
	my $block_mask;
	for my $i (1 .. $size) {
		use integer;
		$block_mask	.= chr($mask);
		$mask		= ($mask + $Encryption{Increment}) % 256;
	}
	return $block ^ $block_mask;
}
sub uniformName($) {
	my $text	= lc(shift);				# Lower case
	$text		=~ s/[-_'\"\/\\]//g;		# Trim all unwanted characters
	$text		=~ s/\s+/ /g;				# Convert all whitespace to spaces, and trim multiples
	$text		=~ s/^\s+|\s+$//g;			# Trim leading/trailing whitespace
	$text		=~ s/ (.)/uc($1)/ge;		# Remove spaces, capitalizing the next letter
	return $text;
}
sub cleanText($$) {
	#Cleans a text-string, setting escapes for quotes.
	my $text	= shift;
	my $wrapper	= shift;
	croak "Can't clean without text"	unless defined $text;
#	$text	=~ s/[\\]/\\\\/g;	#Fore-slash
	$text	=~ s/[']/\\'/g		if $wrapper eq "'";		#Single-quote
	$text	=~ s/["]/\\"/g		if $wrapper eq '"';		#Double-quote
	$text	=~ s/<</\\<<'/g;	#Embedded expression safety
	return $text;
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
#Value Lookups
sub propertyString($$) {
	#Stringify the contents of a given property for a given object
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
sub decodeProperty($$);
sub decodeProperty($$) {
	#Decode the contents of a property given it's type; lists need to be interpreted recursively
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
	if ($text eq 'number')		{ $text	= unpack('l', $data) }					# 1
	if ($text eq 'object')		{ $text	= nameObject(unpack('S', $data)) }		# 2
	if ($text eq 's-string')	{ $text	= "'".cleanText(substr($data, 2), "'")."'" }	# 3
	if ($text eq 'd-string')	{ $text	= '"'.cleanText(substr($data, 2), '"').'"' }	# 9
	if ($text eq 'fnaddr')		{ $text	= '&'.nameObject(unpack('S', $data)) }	# 10
	if ($text eq 'property')	{ $text	= nameProperty(unpack('S', $data)) }	# 13
	#Lists (7) require some special handling, as they can be recursive
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
				or	$Constant_Property_Type[$entry_type] eq 'fnaddr'
				or	$Constant_Property_Type[$entry_type] eq 'property') {
				#Fixed 1 + 2 byte size
				$entry_data	= substr($data, $pos, 2);
				$entry_size	= 2;
			}
			elsif (	$Constant_Property_Type[$entry_type] eq 'nil'
				or	$Constant_Property_Type[$entry_type] eq 'true') {
				#Fixed 1 + 0 byte size
				$entry_size	= 0;
				$entry_data	= '';
			}
			elsif (	$Constant_Property_Type[$entry_type] eq 's-string'
				or	$Constant_Property_Type[$entry_type] eq 'd-string'
				or	$Constant_Property_Type[$entry_type] eq 'list') {
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
		{	#Convert the list to a scalar context
			local $" = ', ';
			$text = "[@entries]";
		}
	}
	return $text;
}
sub bestVocabularyToken($$;$);
sub bestVocabularyToken($$;$) {
	#Find the best (longest) vocabulary token for an object, with optional recursion to parents
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

#Symbolic Name Lookups
sub nameAction($) {
	my $action	= shift;
	return 'actionX'				unless defined $action;
	return $Symbol_Action[$action]		if defined $Symbol_Action[$action];
	return "action$action";
}
sub nameBuiltin($) {
	my $builtin	= shift;
	return 'builtinX'				unless defined $builtin;
	return $Symbol_Builtin[$builtin]	if defined $Symbol_Builtin[$builtin];
	return "builtin$builtin";
}
sub nameObject($) {
	my $obj	= shift;
	return 'objX'				unless defined $obj;
	return 'nullObj'				if $obj eq $Null_Value;
	return $Symbol_Object[$obj]		if defined $Symbol_Object[$obj];
	return "obj$obj";
}
sub nameProperty($) {
	my $prop	= shift;
	return 'propX'				unless defined $prop;
	return $Symbol_Property[$prop]	if defined $Symbol_Property[$prop];
	return "prop$prop";
}
sub namePropertyType($) {
	my $propType	= shift;
	return 'propTypeX'							unless defined $propType;
	return $Constant_Property_Type[$propType]		if defined $Constant_Property_Type[$propType];
	return "propType$propType";
}
sub nameFunctionArgument($$) {
	my $obj	= shift;
	my $arg	= shift;
	return "argX"	unless defined $obj;
	return "argX"	unless defined $arg;
	return $Symbol_Object_Argument{$obj}{$arg}	if defined $Symbol_Object_Argument{$obj}{$arg};
	return "arg$arg";
}
sub nameFunctionVariable($$) {
	my $obj	= shift;
	my $var	= shift;
	return "varX"	unless defined $obj;
	return "varX"	unless defined $var;
	return $Symbol_Object_Variable{$obj}{$var}	if defined $Symbol_Object_Variable{$obj}{$var};
	return "var$var";
}
sub nameMethodArgument($$) {
	my $prop= shift;
	my $arg	= shift;
	return "argX"	unless defined $prop;
	return "argX"	unless defined $arg;
	return $Symbol_Property_Argument{$prop}{$arg}	if defined $Symbol_Property_Argument{$prop}{$arg};
	return "arg$arg";
}
sub nameMethodVariable($$$) {
	my $obj	= shift;
	my $prop= shift;
	my $var	= shift;
	return "varX"	unless defined $obj;
	return "varX"	unless defined $prop;
	return "varX"	unless defined $var;
	return $Symbol_Property_Variable{$obj}{$prop}{$var}	if defined $Symbol_Property_Variable{$obj}{$prop}{$var};
	return "var$var";
}
sub nameVariable($$) {
	#TODO DEPRECATED
	#Variable names are split on property/object and argument/local
	my $type	= shift;	# Negative for object functions, positive for properties
	my $id		= shift;	# Negative for arguments, positive for local variables.
	return "UnknownVar"	unless defined $type;
	return "UnknownVar"	unless defined $id;
	#Local variables
	if ($id > 0) {
		if ($type > 0) {	# Properties
			return nameMethodVariable(0, $type, $id);
#			return $Symbol_Property_Variable[0][$type][$id]	if defined $Symbol_Property_Variable[0][$type][$id];
		}
		else {				# Functions
			return nameFunctionVariable(-$type, $id);
#			return $Symbol_Object_Variable[-$type][$id]		if defined $Symbol_Object_Variable[-$type][$id];
		}
		return "var$id";
	}
	#Arguments
	else {
#		$id		= -$id;
		if ($type > 0) {	# Properties
			return nameMethodArgument($type, -$id);
#			return $Symbol_Property_Argument[$type][-$id]	if defined $Symbol_Property_Argument[$type][-$id];
		}
		else {				# Functions
			return nameFunctionArgument(-$type, -$id);
#			return $Symbol_Object_Argument[-$type][-$id]	if defined $Symbol_Object_Argument[-$type][-$id];
		}
		return "arg".-$id;
	}
}
sub dumpSymbols($) {
	my $obj			= shift;
	#Determine if we're generating a property or function source 
	print $File_Log	"Symbol tables for Obj$obj";
	print $File_Log "($Symbol_Object[$obj])"		if defined $Symbol_Object[$obj];
	print $File_Log	"\n";
	print $File_Log	"obj$obj\t= '".nameObject($obj)."'\n";
	{	# Function Arguments
		my @keys	= sort keys %{ $Symbol_Object_Argument{$obj} };
		#my $size	= @keys;
		#print $File_Log "$size Function Arguments:\n";
		foreach my $arg (@keys) {
			#print $File_Log "arg$arg\t$Symbol_Object_Argument{$obj}{$arg}\n";
			print $File_Log "obj$obj-arg$arg\t= '".nameFunctionArgument($obj, $arg)."'\n";
		}
	}
	{	# Function Variables
		my @keys	= sort keys %{ $Symbol_Object_Variable{$obj} };
		#my $size	= @keys;
		#print $File_Log "$size Function Variables:\n";
		foreach my $var (@keys) {
			#print $File_Log "var$var\t$Symbol_Object_Variable{$obj}{$var}\n";
			print $File_Log "obj$obj-var$var\t= '".nameFunctionVariable($obj, $var)."'\n";
		}
	}
	my @properties	= sort keys %{ $Objects[$obj]{properties} }; 
	foreach my $prop (@properties) {
		#print $File_Log	"\tSymbol tables for Obj$obj.Prop$prop";
		#print $File_Log "($Symbol_Property[$prop])"		if defined $Symbol_Property[$prop];
		#print $File_Log	"\n";
		print $File_Log "prop$prop\t= '".nameProperty($prop)."'\n";
		{	# Method Arguments
			my @keys	= sort keys %{ $Symbol_Property_Argument{$prop} };
			#my $size	= @keys;
			#print $File_Log "\t$size Method Arguments:\n";
			foreach my $arg (@keys) {
				#print $File_Log "\targ$arg\t$Symbol_Property_Argument{$prop}{$arg}\n";
				print $File_Log "prop$prop-arg$arg\t= '".nameMethodArgument($prop, $arg)."'\n";
			}
		}
		{	# Method Default Variables
			my @keys	= sort keys %{ $Symbol_Property_Variable{0}{$prop} };
			#my $size	= @keys;
			#print $File_Log "\t$size Method Variables:\n";
			foreach my $var (@keys) {
				#print $File_Log "\tvar$var\t$Symbol_Property_Variable{0}{$prop}{$var}\n";
				print $File_Log "obj$obj-prop$prop-arg$var\t= '".nameMethodVariable(0, $prop, $var)."'\n";
			}
		}
		{	# Method Variables
			my @keys	= sort keys %{ $Symbol_Property_Variable{$obj}{$prop} };
			#my $size	= @keys;
			#print $File_Log "\t$size Method Variables:\n";
			foreach my $var (@keys) {
				#print $File_Log "\tvar$var\t$Symbol_Property_Variable{$obj}{$prop}{$var}\n";
				print $File_Log "obj$obj-prop$prop-arg$var\t= '".nameMethodVariable($obj, $prop, $var)."'\n";
			}
		}
	}
}

##Main Program Loop
initialize();		# Parse command line arguments for options and filename
print "Preparing to read $FileName_Compiled\n";
openFiles();		# Open file handles
determineVersion();	# Read the header to determine version
print "Reading...\n";
loadFile();			# Read the compiled file into memory and close input files
loadConstants();	# Initialize version dependant constants
loadSymbols();		# Parse the translation mapping file
print "Parsing...\n";
parse();			# Parse the compiled file into memory structure
print "Analyzing...\n";
analyze();			# Deeper analysis that depends on the entire story being parsed
print "Generating output...\n";
generate();			# Generate output and close the files
print "Decompiling completed in ".(time - $Time_Start)." seconds.\n";
#dumpSymbols(745);
