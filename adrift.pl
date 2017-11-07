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
my $Decompiler_Version		= '0.14';
#v0.1:	Initial structure for flow and storage
#v0.2:	Signature parsing, inflation/decryption of source
#v0.3:	Raw dump
#v0.4:	Parse header
#v0.5:	Parse rooms with basic XML output
#v0.6:	Parse objects with basic XML output
#v0.7:	Parse tasks
#v0.8:	Parse events, persons and roomgroups
#v0.9:	Parse synonyms, variables and ALRs
#v0.10: Improved output to XML and Inform
#v0.11:	Improved parsing of actions and restrictions
#v0.12:	Code restructuring
#v0.13: Symbol generation
#v0.14: Improved references
#v0.15: Expanded XML output

##Global Variables
#Story Settings
my $Container_Version;				# The version used to contain the storyfile

#Story Data
my %Story;
my @Rooms 			= ( undef );	# Contains the room objects for the story, starting from ID 1
my @Objects 		= ( undef );	# Contains the 'object' objects for the story, starting from ID 1
my @Tasks	 		= ( undef );	# Contains the task objects for the story, starting from ID 1
my @Events	 		= ( undef );	# Contains the event objects for the story, starting from ID 1
my @Persons	 		= ( undef );	# Contains the person objects for the story, starting from ID 1
my @Groups	 		= ( undef );	# Contains the room group objects for the story, starting from ID 1
my @Synonyms 		= ( undef );	# Contains the synonym objects for the story, starting from ID 1
my @Variables 		= ( undef );	# Contains the variable objects for the story, starting from ID 1
my @ALRs 			= ( undef );	# Contains the ALR objects for the story, starting from ID 1

#Object mappings
my @ObjectStatic		= ( 0 );	# Mapping from static object ID to actual object ID
my @ObjectPortable		= ( 0 );	# Mapping from non-static object ID to actual object ID
my @ObjectOpenable		= ( 0 );	# Mapping from openable object ID to actual object ID
my @ObjectStateful		= ( 0 );	# Mapping from stateful object ID to actual object ID
my @ObjectContainer		= ( 0 );	# Mapping from container object ID to actual object ID
my @ObjectSurface		= ( 0 );	# Mapping from surface object ID to actual object ID
my @ObjectHolder		= ( 0 );	# Mapping from holder/parent object ID to actual object ID
my @ObjectLieable		= ( 0 );	# Mapping from lieable object ID to actual object ID
my @ObjectSitStandable	= ( 0 );	# Mapping from sit/standable object ID to actual object ID

#Symbol Translation Names
my @Symbol_Room;					# Translation names for rooms
my @Symbol_Object;					# Translation names for 'objects'
my @Symbol_Task;					# Translation names for tasks
my @Symbol_Event;					# Translation names for event
my @Symbol_Person;					# Translation names for persons
my @Symbol_Group;					# Translation names for room groups
my @Symbol_Variable;				# Translation names for variables

#Static Symbol Names
my @Symbol_Compass_Direction;		# Symbolic names for compass directions
my @Symbol_Compass_Reversed;		# Symbolic names for reversed compass directions
my @Symbol_Gender;					# Symbolic names for genders

#Constants
my @Versions		= ();			# Printable names for each compiler version, ascending order
my @Signatures		= ();			# Header signatures for each compiler version, corresponsing to @Versions
my %PRNG			= ();
$PRNG{Constant1} 	= 0x43fd43fd;
$PRNG{Constant2} 	= 0x00c39ec3;
$PRNG{Constant3} 	= 0x00ffffff;
$PRNG{Initial}		= 0x00a09e86;
$PRNG{State}		= $PRNG{Initial};

#File handling
my $FileName_Compiled;		# Filename for the compiled gamefile to decompile
my $FileName_Path	= './';	# Path to place output files in
my $FileName_Decompiled;	# Filename for the decompiled sourcecode
my $FileName_Log;			# Filename for the log
my $FileName_Symbol_In;		# Filename for the symbol mapping translation input file
my $FileName_Symbol_Out;	# Filename for the symbol mapping translation output file
my $FileName_I7;			# Filename for the Inform output
my $FileName_XML;			# Filename for the XML output
my $File_Compiled;			# File handle for input compiled gamefile
my $File_Log;				# File handle for logging output
my $File_Decompiled;		# File handle for output decompiled sourcecode
my $File_Symbol_In;			# File handle for symbol mapping translation input
my $File_Symbol_Out;		# File handle for symbol mapping translation output
my $File_I7;				# File handle for Inform output
my $File_XML;				# File handle for XML output
my $File_XML_Indent	= -1;	# Storing the indentation level of the XML file
my $Contents_Compiled;		# File contents

#Decompiling Options; see parseArguments()
my $Options	= "Decompiling Options:\n";
my $Option_Minimal;		# Skip output directory and embedded resources
$Options	.= "-m\t\tMinimalist mode, skipping output directory and resources\n";
my $Option_Verbose;		# Extra information dumped to story file
$Options	.= "-v\t\tVerbose loging output\n";
my $Option_Naming;		# Be extra aggressive on trying to determine names
						# TODO: This will create duplicate names, remake to avoid that
$Options	.= "-a\t\tAggressive search for symbol names\n";
my $Option_Rawdump;		# Dump raw decompiled source
$Options	.= "+r\t\tRaw dump of decompiled source\n";
my $Option_Generate;	# Generate a new symbol file
$Options	.= "+s\t\tGenerate symbol translation file in output directory\n";
$Options	.= "-s [file]:\tSymbol translation file\n";

#Utility functions to access ADRIFTs line-oriented structure
my @Lines;					# Stores the lines which form the basis of ADRIFT files
my $Lines_Next;				# Index of next entry in @Lines
my $Terminator;				# String indicating end of multi-line value
#Next single-line value
sub nextLine(){
	die "Tried to access line $Lines_Next, $#Lines defined"	unless defined $Lines[$Lines_Next];
	return $Lines[$Lines_Next++];
}
#Next multi-line value
sub nextMulti(){
	my $multi;
	do {
		$multi		.= "\n"		if defined $multi;
		$multi		.=  nextLine();
	} until $Terminator eq substr ($multi, - length($Terminator));
	return $multi;
}
#Generate the next value of the PRNG
sub nextRandom(){
	$PRNG{State} = ($PRNG{State} * $PRNG{Constant1} + $PRNG{Constant2}) & $PRNG{Constant3};
	return (255 * $PRNG{State}) / ($PRNG{Constant3} + 1);
}
##Initialization
sub initialize(){
	#Parse arguments;
	parseArguments();
	#There should be only one argument left, giving the name of the file to parse.
	die "Use: adrift [options] story.taf\n$Options" unless ($#ARGV eq 0);
	$FileName_Compiled	= $ARGV[0];
	if ($FileName_Compiled	=~ m/([-_\w\s]*)\.(taf)/i) {
	#When input file has a recognized extension, use the name of the file
		$FileName_Path			= $1 . '/'	unless defined $Option_Minimal;
		$FileName_Log			= $1 . '.log';
		$FileName_Decompiled	= $1 . '.src';
		$FileName_XML			= $1 . '.xml';
		$FileName_I7			= $1 . '.ni';
		$FileName_Symbol_Out	= $1 . '.sym'	if defined $Option_Generate;
	}
	else{
	#Otherwise decide on input agnostic file names
		$FileName_Path			= 'decompiled/'	unless defined $Option_Minimal;
		$FileName_Log			= 'story.log';
		$FileName_Decompiled	= 'story.src';
		$FileName_XML			= 'story.xml';
		$FileName_I7			= 'story.ni';
		$FileName_Symbol_Out	= 'story.sym'	if defined $Option_Generate;
	}
	openFiles();
}
sub parseArguments(){	# Interpret command line arguments
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
			$FileName_Symbol_In	= $ARGV[1];
			splice(@ARGV, 0, 2);
		}
		elsif($ARGV[0] eq '+s') {	#Generate symbol mapping file template
			$Option_Generate	= 1;
			splice(@ARGV, 0, 1);
		}
		elsif($#ARGV >= 0 && $ARGV[0] eq '-a') {		
			$Option_Naming		= 1;
			splice(@ARGV, 0, 1);
		}
		elsif($#ARGV >= 0 && $ARGV[0] eq '+r') {		# Rawdump mode
			$Option_Rawdump		= 1;
			splice(@ARGV, 0, 1);
		}
		else{ last }
	}
}
sub openFiles(){		# Open file handles
	#Determine filenames to use
	#Create path as needed
	mkdir $FileName_Path						unless -e $FileName_Path;
	die "$FileName_Path is not a valid path"	unless -d $FileName_Path;
	#Open log; use :unix to flush as we write to it
	open($File_Log, "> :raw :bytes :unix", $FileName_Path . $FileName_Log)
		or die "$0: can't open $FileName_Path$FileName_Log for writing: $!";
	#Open compiled file with some sanity checking
	die "$FileName_Compiled is not a valid file"	unless -f $FileName_Compiled;
	open($File_Compiled, "< :raw :bytes", $FileName_Compiled)
		or die("Couldn't open $FileName_Compiled for reading: $!");
	#Open symbol mapping input file if defined
	open($File_Symbol_In, "< :raw :bytes", $FileName_Symbol_In)
		or die("Couldn't open $FileName_Symbol_In for reading.")
		if defined $FileName_Symbol_In;
	#Open symbol mapping output file if defined
	open($File_Symbol_Out, "> :raw :bytes", $FileName_Path . $FileName_Symbol_Out)
		or die "$0: can't open $FileName_Path$FileName_Symbol_Out for writing: $!"
		if defined $FileName_Symbol_Out;
	#Open generated output files
	open($File_Decompiled, "> :raw :bytes", $FileName_Path . $FileName_Decompiled)
		or die "$0: can't open $FileName_Path$FileName_Decompiled for writing: $!";
	open($File_I7, "> :raw :bytes", $FileName_Path . $FileName_I7)
		or die "$0: can't open $FileName_Path$FileName_I7 for writing: $!";
	open($File_XML, "> :raw :bytes", $FileName_Path . $FileName_XML)
		or die "$0: can't open $FileName_Path$FileName_XML for writing: $!";
	#Open mapping file with some sanity checking
	die "Overwriting existing symbol file with autogenerated is not supported in minimal mode"
		if defined $FileName_Symbol_In 
				&& $Option_Minimal 
				&& -e $FileName_Symbol_In;
}
sub determineVersion(){	# Determine container version by reading the story header
	#Load signature constants
#	$Signature{Size}	= 14;
#	$Signature{Extra}	= 8;
	my $base	= chr(0x3c).chr(0x42).chr(0x3f).chr(0xc9).chr(0x6a).chr(0x87).chr(0xc2).chr(0xcf);
	#Load known signatures
	{	# v3.80
		my $v380			= 0;
		$Versions[$v380]	= '3.80';
		$Signatures[$v380]	= $base.chr(0x94).chr(0x45).chr(0x36).chr(0x61).chr(0x39).chr(0xfa);
	}
	{	# v3.90
		my $v390			= 1;
		$Versions[$v390]	= '3.90';
		$Signatures[$v390]	= $base.chr(0x94).chr(0x45).chr(0x37).chr(0x61).chr(0x39).chr(0xfa);
	}
	{	# v4.00
		my $v400			= 2;
		$Versions[$v400]	= '4.00';
		$Signatures[$v400]	= $base.chr(0x93).chr(0x45).chr(0x3e).chr(0x61).chr(0x39).chr(0xfa);
	}
	{	# v5.00
		my $v500			= 3;
		$Versions[$v500]	= '5.00';
		$Signatures[$v500]	= $base.chr(0x92).chr(0x45).chr(0x3e).chr(0x61).chr(0x30).chr(0x32);
	}
	#Read signature from file
	my $signature_file;
	my $bytes_read = read ($File_Compiled, $signature_file, 14);
	die 'Unable to read file signature'	unless $bytes_read eq 14;
	#Check file signature against known signatures
	for my $v (0..$#Signatures) { $Container_Version	= $Versions[$v] if ($signature_file eq $Signatures[$v]) }
	unless (defined $Container_Version){
		my $mask			= '';
		for (1 .. length($signature_file)) { $mask .= chr(nextRandom()) }
		#Decrypt; don't bother reseting PRNG
		my $decrypted	= $signature_file ^ $mask;
		#Print and die
		print $File_Log "Unknown or unhandled version: $decrypted:\n";
		debugDump($signature_file);
		die 'Unable to determine version';
	}
	#Set some version dependant constants
	$Terminator		= chr(189).chr(208)	if $Container_Version eq '4.00' or $Container_Version eq '5.00';
	$Terminator		= chr( 42).chr( 42)	if $Container_Version eq '3.90' or $Container_Version eq '3.80';
}
sub loadConstants(){	# Initialize constants that might depend on version
	{	#Null-values
		$Symbol_Room[0]		= 'nowhere';
		$Symbol_Object[0]	= 'nothing';
		$Symbol_Person[0]	= 'player';
	}
	{	#Compass directions; dependant on the ExpandedCompass global
		$Symbol_Compass_Direction[0]	= 'North';
		$Symbol_Compass_Direction[1]	= 'East';
		$Symbol_Compass_Direction[2]	= 'South';
		$Symbol_Compass_Direction[3]	= 'West';
		$Symbol_Compass_Direction[4]	= 'Up';
		$Symbol_Compass_Direction[5]	= 'Down';
		$Symbol_Compass_Direction[6]	= 'Inside';
		$Symbol_Compass_Direction[7]	= 'Outside';
		$Symbol_Compass_Direction[8]	= 'Northeast'		if $Story{ExpandedCompass};
		$Symbol_Compass_Direction[9]	= 'Southeast'		if $Story{ExpandedCompass};
		$Symbol_Compass_Direction[10]	= 'Southwest'		if $Story{ExpandedCompass};
		$Symbol_Compass_Direction[11]	= 'Northwest'		if $Story{ExpandedCompass};
	}
	{	#Reversed Compass directions; dependant on the ExpandedCompass global
		$Symbol_Compass_Reversed[0]		= 'south of';
		$Symbol_Compass_Reversed[1]		= 'west of';
		$Symbol_Compass_Reversed[2]		= 'north of';
		$Symbol_Compass_Reversed[3]		= 'east of';
		$Symbol_Compass_Reversed[4]		= 'down from';
		$Symbol_Compass_Reversed[5]		= 'up from';
		$Symbol_Compass_Reversed[6]		= 'outside from';
		$Symbol_Compass_Reversed[7]		= 'inside from';
		$Symbol_Compass_Reversed[8]		= 'southwest of'	if $Story{ExpandedCompass};
		$Symbol_Compass_Reversed[9]		= 'northwest of'	if $Story{ExpandedCompass};
		$Symbol_Compass_Reversed[10]	= 'northeast of'	if $Story{ExpandedCompass};
		$Symbol_Compass_Reversed[11]	= 'southeast of'	if $Story{ExpandedCompass};
	}
	{	#Gender names
		$Symbol_Gender[0]	= 'male';
		$Symbol_Gender[1]	= 'female';
		$Symbol_Gender[2]	= 'neuter';
	}
}
sub loadSymbols(){		# Read symbol mapping translation from given file
	return unless defined $FileName_Symbol_In;
	while (my $line = <$File_Symbol_In>) {
		#Pre-process the line
		chomp $line;
		$line	= (split('#', $line))[0];		# Remove comments
		#Skip ahead if the line doesn't contain anything
#		next unless length $line;
		next if($line =~ m/^\s*$/i );
		my $parsed;
#TODO: This could be improved
		if ($line =~ m/(Room)s?\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 			= $3;
			$Symbol_Room[$2]	= $parsed;
		}
		if ($line =~ m/(Object|Obj)s?\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 			= $3;
			$Symbol_Object[$2]	= $parsed;
		}
		if ($line =~ m/(Task)s?\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 			= $3;
			$Symbol_Task[$2]	= $parsed;
		}
		if ($line =~ m/(Event)s?\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 			= $3;
			$Symbol_Event[$2]	= $parsed;
		}
		if ($line =~ m/(Person|NPC)s?\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 			= $3;
			$Symbol_Person[$2]	= $parsed;
		}
		if ($line =~ m/(Group|RoomGroup)s?\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 			= $3;
			$Symbol_Group[$2]	= $parsed;
		}
		if ($line =~ m/(Variable|Var)s?\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 			= $3;
			$Symbol_Variable[$2]	= $parsed;
		}
		print "Unable to parse $line (".length($line).")\n" unless defined $parsed;
	}
}
sub loadFile(){
	#Read in the raw file
	my $buffer			= read_file ( $FileName_Compiled, binmode => ':raw' );
	#V3 is stored as encrypted text
	if ($Container_Version	eq '3.90' or $Container_Version	eq '3.80'){
		#Generate decryption mask
		my $size			= length($buffer);
		my $mask			= '';
		for (1 .. $size) { $mask .= chr(nextRandom()) }
		#Decrypt
		$Contents_Compiled	= $buffer ^ $mask;
	}
	#V4 is stored as a deflated zlib after an extended header
	if ($Container_Version	eq '4.00' or $Container_Version	eq '5.00'){
		#Skip file signature and header
		$buffer				= substr($buffer, 14+8);
		#Initiate inflation stream
		my $stream 			= inflateInit() or die 'Cannot create inflation stream';
		#Inflate and store in Contents_Compiled
		my $status;
		($Contents_Compiled, $status)	= $stream->inflate($buffer);
		#TODO: Check status
	}
	#V5 is stored as a deflated zlib
	if ($Container_Version	eq '5.00'){
		#Skip file signature and header
		my $skip			= index($buffer, '</ifindex>')+10	if $Container_Version eq '5.00';
		print $skip;
		debugDump(substr($buffer, $skip, 30));
		$buffer				= substr($buffer, $skip);
		die "v5.00 containeris not yet supported";
		#Initiate inflation stream
		my $stream 			= inflateInit() or die 'Cannot create inflation stream';
		#Inflate and store in Contents_Compiled
		my $status;
		($Contents_Compiled, $status)	= $stream->inflate($buffer);
		#TODO: Check status
	}
	#Sanity check
	die "V$Container_Version not supported, unable to load file"	unless defined $Contents_Compiled;
	#Dump raw file if called for
	print $File_Decompiled $Contents_Compiled if defined $Option_Rawdump;
	#Split and store lines
	$Lines_Next	= 0;
	@Lines		= split(chr(13).chr(10), $Contents_Compiled);
	print $File_Log "Decompiler v$Decompiler_Version on $FileName_Compiled";
}
##Parsing file into memory structure
sub parse(){
	#Parse header, printing the most important settings
	parseHeader();
	print $File_Log " $Story{Title} by $Story{Author} (ADRIFT v$Container_Version)\n";
	print $File_Log "\tBattles\n"			if $Story{EnableBattle};
	print $File_Log "\t8-point compass\n"	if $Story{ExpandedCompass};
	print $File_Log "\tGraphics\n"			if $Story{EnableGraphics};
	print $File_Log "\tSound\n"				if $Story{EnableSound};
	#Load constants based on header
	loadConstants();
	$Story{Directions}		= 8;
	$Story{Directions}		= 12	if $Story{ExpandedCompass};
	#Parse rooms
	my $rooms		= nextLine();
	print $File_Log "$rooms rooms\n";
	for (1 .. $rooms)		{ push @Rooms, parseRoom() }
	#Parse objects
	my $objects		= nextLine();
	print $File_Log "$objects objects\n";
	for (1 .. $objects) 	{ push @Objects, parseObject() }
	#Parse tasks
	my $tasks		= nextLine();
	print $File_Log "$tasks tasks\n";
	for (1 .. $tasks)		{ push @Tasks, parseTask() }
	#Parse timed events
	my $events		= nextLine();
	print $File_Log "$events events\n";
	for (1 .. $events)		{ push @Events, parseEvent() }
	#Parse persons
	my $persons		= nextLine();
	print $File_Log "$persons persons\n";
	for (1 .. $persons)		{ push @Persons, parsePerson(); }
	#Parse room-groups
	my $groups		= nextLine();
	print $File_Log "$groups groups\n";
	for (1 .. $groups)		{ push @Groups, parseGroup(); }
	#Parse parser-synonyms
	my $synonyms	= nextLine();
	print $File_Log "$synonyms synonyms\n";
	for (1 .. $synonyms)	{ push @Synonyms, parseSynonym(); }
	#Parse variables
	my $variables	= 0;
	$variables		= nextLine()	if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	print $File_Log "$variables variables\n";
	for (1 .. $variables)	{ push @Variables, parseVariable(); }
	#Parse alternate-language resources
	my $alrs		= 0;
	$alrs			= nextLine() if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	print $File_Log "$alrs ALRs\n";
	for (1 .. $alrs)		{ push @ALRs, parseALR(); }
	#Parse footer
	parseFooter();
	print $File_Log "Parsed  $Lines_Next of ". ($#Lines + 1) ." lines\n";
}
sub parseHeader(){
	#Intro Text
	$Story{Intro}			= nextMulti();
	$Story{Start}			= nextLine() + 1;
	$Story{Ending}			= nextMulti();
	#text	GameName
	$Story{Title}			= nextLine();
	#text	GameAuthor
	$Story{Author}			= nextLine();
	#number	MaxCarried		TODO postprocessing into MaxSize and MaxWeight
	my $max_carried			= nextLine()		if $Container_Version eq '3.80';
	#text	DontUnderstand
	$Story{Error}			= nextLine();
	#number	Perspective
	$Story{Perspective}		= nextLine();
	#truth	ShowExits
	$Story{ShowExits}		= nextLine();
	#number	WaitTurns
	$Story{WaitTurns}		= nextLine();
	#truth	DispFirstRoom
	$Story{InitialLook}		= 0					if $Container_Version eq '3.80';
	$Story{InitialLook}		= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#truth	BattleSystem
	$Story{EnableBattle}	= 0					if $Container_Version eq '3.80';
	$Story{EnableBattle}	= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#number	MaxScore
	$Story{MaxScore}		= 0					if $Container_Version eq '3.80';
	$Story{MaxScore}		= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#text	PlayerName
	$Story{PlayerName}		= ''				if $Container_Version eq '3.80';
	$Story{PlayerName}		= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#truth	PromptName
	$Story{PromptName}		= 0					if $Container_Version eq '3.80';
	$Story{PromptName}		= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#text	PlayerDesc
	$Story{PlayerDesc}		= ''				if $Container_Version eq '3.80';
	$Story{PlayerDesc}		= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#number	Task
	$Story{AltDescTask}		= 0					if $Container_Version eq '3.80';
	$Story{AltDescTask}		= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#text	AltDesc
	$Story{AltDesc}			= nextLine()		if $Story{AltDescTask};
	#number	Position
	$Story{Position}		= 0					if $Container_Version eq '3.80';
	$Story{Position}		= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#number	ParentObject
	$Story{ParentObject}	= 0					if $Container_Version eq '3.80';
	$Story{ParentObject}	= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#number	PlayerGender
	$Story{PlayerGender}	= 0					if $Container_Version eq '3.80';
	$Story{PlayerGender}	= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#number	MaxSize
	$Story{MaxSize}			= 0					if $Container_Version eq '3.80';	#TODO Process $max_carried into this
	$Story{MaxSize}			= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#number	MaxWeight
	$Story{MaxWeight}		= 0					if $Container_Version eq '3.80';	#TODO Process $max_carried into this
	$Story{MaxWeight}		= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#battle	PlayerStats
	$Story{PlayerStats}		= parseBattle()		if $Story{EnableBattle};
	#truth	EightPointCompass
	$Story{ExpandedCompass}	= 0					if $Container_Version eq '3.80';
	$Story{ExpandedCompass}	= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#truth	NoDebug			SKIP
	nextLine()									if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#truth	NoScoreNotify
	$Story{NoScoreNotify}	= 1					if $Container_Version eq '3.80';
	$Story{NoScoreNotify}	= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#truth	DisableMap
	$Story{DisableMap}		= 0					if $Container_Version eq '3.80';
	$Story{DisableMap}		= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#truth	NoAutoComplete	SKIP
	nextLine()									if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#truth	NoControlPanel	SKIP
	nextLine()									if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#truth	NoMouse			SKIP
	nextLine()									if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#truth	Sound
	$Story{EnableSound}		= 0					if $Container_Version eq '3.80';
	$Story{EnableSound}		= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#truth	Graphics
	$Story{EnableGraphics}	= 0					if $Container_Version eq '3.80';
	$Story{EnableGraphics}	= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#resource	IntroRes
	$Story{IntroRes}		= parseResource()	if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#resource	WinRes
	$Story{WinRes}			= parseResource()	if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#truth	StatusBox
	$Story{EnableStatusBox}	= 0					if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	$Story{EnableStatusBox}	= nextLine()		if $Container_Version eq '4.00';
	#text	StatusBoxText
	$Story{StatusBoxText}	= ''				if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	$Story{StatusBoxText}	= nextLine()		if $Container_Version eq '4.00';
	#2x	Unknown				SKIP
	nextLine()									if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	nextLine()									if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#truth	Embedded
	$Story{Embedded}		= 0					if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	$Story{Embedded}		= nextLine()		if $Container_Version eq '4.00';
}
sub parseFooter(){
	#truth	CustomFont
	$Story{CustomFont}		= 0					if $Container_Version eq '3.80';
	$Story{CustomFont}		= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#text	FontNameSize
	$Story{FontNameSize}	= nextLine()		if $Story{CustomFont};
	#text	CompileDate
	$Story{CompileDate}		= nextLine();
	#text	Password		SKIP
	nextLine()	if $Container_Version eq '3.80' or $Container_Version eq '3.90';
}
#Routines for parsing major objects
sub parseRoom(){
	my $id		= @Rooms;
	my %room	= ();
	#References
	$room{RoomReferences}		= [];
	$room{ObjectReferences}		= [];
	$room{TaskReferences}		= [];
	$room{EventReferences}		= [];
	$room{PersonReferences}		= [];
	$room{GroupReferences}		= [];
	$room{SynonymReferences}	= [];
	$room{VariableReferences}	= [];
	$room{ALRReferences}		= [];
	#text	Short
	$room{Short}			= nextLine();
	print $File_Log "\t\t$id: $room{Short}\n"	if defined $Option_Verbose;
	#text	Long
	$room{Description}		= nextLine();
	#text	LastDesc
	$room{LastDesc}			= nextLine()		if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	#exit	RoomExits
	my $exit_count			= 0;
	$room{Exits}			= [];
	for my $dir (1 .. $Story{Directions}) { 
		push @{ $room{Exits} }, parseExit();
		$exit_count++	unless $room{Exits}[$dir - 1]{Destination} eq 0;
	}
	print $File_Log "\t\t\t$exit_count exit(s)\n"	if defined $Option_Verbose;
	#text	AddDesc1
	$room{AltDesc1}			= nextLine()		if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	#number	AddDesc1Task
	$room{AltDesc1Task}		= nextLine()		if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	#text	AddDesc2
	$room{AltDesc2}			= nextLine()		if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	#number	AddDesc2Task
	$room{AltDesc2Task}		= nextLine()		if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	#number	Obj
	$room{AltDesc3Obj}		= nextLine()		if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	#text	AltDesc
	$room{AltDesc3}			= nextLine()		if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	#number	TypeHideObjects
	$room{TypeHideObjects}	= nextLine()		if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	#resource	Res
	$room{Resource}			= parseResource()	if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#resource	LastRes
	$room{LastDescResource}	= parseResource()	if $Container_Version eq '3.90';
	#resource	Task1Res
	$room{AltDesc1Resource}	= parseResource()	if $Container_Version eq '3.90';
	#resource	Task2Res
	$room{AltDesc2Resource}	= parseResource()	if $Container_Version eq '3.90';
	#resource	AltRes
	$room{AltDesc3Resource}	= parseResource()	if $Container_Version eq '3.90';
	#RoomAlt	Alternates
	my $alternate_count	= 0;
	my @alternates		= ();
	$alternate_count		= nextLine()		if $Container_Version eq '4.00';
	for (1 .. $alternate_count){ push @alternates, parseRoomAlt() }
	$room{Alternates}		= \@alternates;
	print $File_Log "\t\t\t$alternate_count alternate(s)\n"	if defined $Option_Verbose && $alternate_count;
	#truth	HideOnMap
	$room{Hidden}			= nextLine()		if ($Container_Version eq '3.90' or $Container_Version eq '4.00') && not $Story{DisableMap};
	return \%room;
}
sub parseObject(){
	my $id	= @Objects;
	my %object	= ();
	#References
	$object{RoomReferences}		= [];
	$object{ObjectReferences}	= [];
	$object{TaskReferences}		= [];
	$object{EventReferences}	= [];
	$object{PersonReferences}	= [];
	$object{GroupReferences}	= [];
	$object{SynonymReferences}	= [];
	$object{VariableReferences}	= [];
	$object{ALRReferences}		= [];
	#text	Prefix
	$object{Prefix}			= nextLine();
	#text	Short
	$object{Short}			= nextLine();
	print $File_Log "\t\t$id: ($object{Prefix}) $object{Short}\n"	if defined $Option_Verbose;
	#text	Alias
	my $alias				= 1;
	$alias					= nextLine()		if $Container_Version eq '4.00';
	$object{Alias}			= ();
	for (1 .. $alias) { push @{ $object{Alias} }, nextLine(); }
	#truth	Static
	$object{Static}			= nextLine();
	#text	Description
	$object{Description}	= nextLine();
	#number	InitialPosition
	$object{InitialPosition}= nextLine();
	#number	Task
	$object{AltDescTask}	= nextLine();
	#truth	TaskNotDone
	$object{AltDescType}	= nextLine();
	#text	AltDesc
	$object{AltDesc}		= nextLine();
	#RoomList	Where
	$object{WhereType}		= 9;
	$object{WhereType}		= nextLine()		if $object{Static};
#	0: NO_ROOMS
#	1: ONE_ROOM
#	2: SOME_ROOMS
#	3: ALL_ROOMS
#	4: NPC_PART
#	9: NULL/Off-stage
	$object{Where}			= [];
	if ($object{WhereType} eq 1) {
		my $roomID	= nextLine() + 1;
		push @{	$object{Where} }, $roomID;
	}
	if($object{WhereType} eq 2){
		for my $room (0 .. $#Rooms){ push @{ $object{Where} }, $room if nextLine(); }
	}
	my $surfaceContainer	= 0;
	$surfaceContainer		= nextLine()		if $Container_Version eq '3.80';
	#truth	Container
	$object{Container}		= 0					unless $surfaceContainer eq 1;
	$object{Container}		= 1					if $surfaceContainer eq 1;
	$object{Container}		= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#truth	Surface
	$object{Surface}		= 0					unless $surfaceContainer eq 2;
	$object{Surface}		= 1					if $surfaceContainer eq 2;
	$object{Surface}		= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#number	Capacity
	$object{Capacity}		= nextLine();
	$object{Capacity}		= $object{Capacity} * 10 + 2	if $Container_Version eq '3.80';
	#truth	Wearable
	$object{Wearable}		= 0;
	$object{Wearable}		= nextLine()		unless $object{Static};
	#number	SizeWeight
	$object{SizeWeight}		= 0;
	$object{SizeWeight}		= nextLine()		unless $object{Static};
	#number	Parent
	$object{Parent}			= 0;
	$object{Parent}			= nextLine()		unless $object{Static};
	$object{Parent}			= nextLine()		if $object{Static} && $object{WhereType} eq 4;
	#number	Openable
	my $openable			= nextLine();
#	0: UNOPENABLE
#	5: OPEN
#	6: CLOSED
#	7: LOCKED
	$object{Openable}		= $openable;
	#Code 5 and 6 are reversed in v3.XX
	if($Container_Version eq '3.80' or $Container_Version eq '3.90'){
		$object{Openable}		= 6 if $openable eq 5;
		$object{Openable}		= 5 if $openable eq 6;
	}
	#number	Key
	$object{Key}			= nextLine()		if $Container_Version eq '4.00' && $object{Openable};
	#number	SitLie
	my $enterableType		= nextLine();
	$object{EnterableType}	= $enterableType;
	$object{SitStandable}	= 1 if $enterableType eq 1 || $enterableType eq 3;
	$object{Lieable}		= 1 if $enterableType eq 2 || $enterableType eq 3;
	#truth	Edible
	$object{Edible}			= nextLine()		unless $object{Static};
	#truth	Readable
	$object{Readable}		= nextLine();
	#truth	ReadText
	$object{ReadText}		= nextLine()		if $object{Readable};
	#truth	Weapon
	$object{Weapon}			= nextLine()		unless $object{Static};
	#number	CurrentState
	$object{CurrentState}	= 0					if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	$object{CurrentState}	= nextLine()		if $Container_Version eq '4.00';
	#number	States
	$object{States}			= 0;
	$object{States}			= nextLine()		if $object{CurrentState};
	#truth	StateListed
	$object{StateListed}	= 0;
	$object{StateListed}	= nextLine()		if $object{CurrentState};
	#truth	ListFlag
	$object{ListFlag}		= 0					if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	$object{ListFlag}		= nextLine()		if $Container_Version eq '4.00';
	#resource	Res1
	$object{Resource1}		= parseResource()	if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#resource	Res2
	$object{Resource2}		= parseResource()	if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#battle	Battle
	$object{BattleStats}	= parseBattle()		if $Story{EnableBattle};
	#text	InRoomDesc
	$object{InRoomDesc}		= ''				if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	$object{InRoomDesc}		= nextLine()		if $Container_Version eq '4.00';
	#number	OnlyWhenNotMoved
	$object{InRoomDescType}	= 0					if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	$object{InRoomDescType}	= nextLine()		if $Container_Version eq '4.00';
	#Update the Object mapping references:
	push @ObjectPortable, $id		unless $object{Static};
	push @ObjectStatic,	$id			if $object{Static};
	push @ObjectOpenable, $id		if $object{Openable};
	push @ObjectStateful, $id		if $object{Openable} or $object{CurrentState};
	push @ObjectContainer, $id		if $object{Container};
	push @ObjectSurface, $id		if $object{Surface};
	push @ObjectHolder,	$id			if $object{Container} or $object{Surface};
	push @ObjectLieable, $id		if $object{Lieable};
	push @ObjectSitStandable, $id	if $object{SitStandable};
	return \%object;
}
sub parseTask(){
	my $id		= @Tasks;
	my %task	= ();
	#References
	$task{RoomReferences}		= [];
	$task{ObjectReferences}		= [];
	$task{TaskReferences}		= [];
	$task{EventReferences}		= [];
	$task{PersonReferences}		= [];
	$task{GroupReferences}		= [];
	$task{SynonymReferences}	= [];
	$task{VariableReferences}	= [];
	$task{ALRReferences}		= [];
	#text	Command
	my $commands			= nextLine();
	$commands++				if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	$task{Commands}			= ();
	for (1 .. $commands) { push @{ $task{Commands} }, nextLine(); }
	print $File_Log "\t\t$id: $task{Commands}[0] ($commands)\n"	if defined $Option_Verbose;
	#text	CompleteText
	$task{CompleteText}			= nextLine();
	#text	ReverseMessage
	$task{ReverseText}			= nextLine();
	#text	RepeatText
	$task{RepeatText}			= nextLine();
	#text	AdditionalMessage
	$task{AdditionalText}		= nextLine();
	#number	ShowRoomDesc
	$task{ShowRoomDesc}			= nextLine();
	#Some 3.80 variables
	if ($Container_Version eq '3.80'){
		#number	Score
		$task{Score}			= nextLine();
		#number	SingleScore
		$task{BSingleScore}		= nextLine();
		#TaskMove	Movements
		$task{Movements}		= ();
		for (1 .. 6) {
			my %movement	= ();
			$movement{Var1}		= nextLine();
			$movement{Var2}		= nextLine();
			$movement{Var3}		= nextLine();
			push @{ $task{Movements} },  \%movement;
		}
	}
	#truth	Repeatable
	$task{Repeatable}			= nextLine();
	#truth	Reversible
	$task{Reversible}			= nextLine();
	#text	ReverseCommand
	my $commands_reverse		= nextLine();
	$commands_reverse++			if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	print $File_Log "\t\t\t$commands_reverse reversion(s)\n"	if defined $Option_Verbose;
	$task{CommandsReverse}		= [];
	for (1 .. $commands_reverse) { push @{ $task{CommandsReverse} }, nextLine(); }
	#Some 3.80 variables
	if ($Container_Version eq '3.80'){
		#number	WearObj1
		$task{WearObj1}			= nextLine();
		#number	WearObj2
		$task{WearObj2}			= nextLine();
		#number	HoldObj1
		$task{HoldObj1}			= nextLine();
		#number	HoldObj2
		$task{HoldObj2}			= nextLine();
		#number	HoldObj3
		$task{HoldObj3}			= nextLine();
		#number	Obj1
		$task{Obj1}				= nextLine();
		#number	Task
		$task{Task}				= nextLine();
		#truth	TaskNotDone
		$task{TaskNotDone}		= nextLine();
		#text	TaskMsg
		$task{TaskMsg}			= nextLine();
		#text	HoldMsg
		$task{HoldMsg}			= nextLine();
		#text	WearMsg
		$task{WearMsg}			= nextLine();
		#text	CompanyMsg
		$task{CompanyMsg}		= nextLine();
		#truth	NotInSameRoom
		$task{NotInSameRoom}	= nextLine();
		#number	NPC
		$task{NPC}				= nextLine();
		#text	Obj1Msg
		$task{Obj1Msg}			= nextLine();
		#number	Obj1Room
		$task{Obj1Room}			= nextLine();
	}
	#RoomList	Where
	$task{WhereType}			= 9;
	$task{WhereType}			= nextLine();
#	0: NO_ROOMS
#	1: ONE_ROOM
#	2: SOME_ROOMS
#	3: ALL_ROOMS
#	4: NPC_PART
#	9: NULL/Off-stage
	$task{Where}				= [];
	if ($task{WhereType} eq 1) {
		my $roomID	= nextLine() + 1;
		push @{	$task{Where} }, $roomID;
	}
	if($task{WhereType} eq 2){
		for my $room (1 .. $#Rooms){ push @{ $task{Where} }, $room if nextLine(); }
	}
	#Some 3.80 variables
	if ($Container_Version eq '3.80'){
		#truth	KillsPlayer
		$task{KillsPlayer}		= nextLine();
		#truth	HoldingSameRoom
		$task{HoldingSameRoom}	= nextLine();
	}
#	$Question ?$Question:$Hint1,$Hint2
	#text	Question
	$task{Question}				= nextLine();
	#text	Hint1
	$task{Hint1}				= nextLine()		if length $task{Question};
	#text	Hint2
	$task{Hint2}				= nextLine()		if length $task{Question};
	#Some 3.80 variables
	if ($Container_Version eq '3.80'){
		#number	Obj2
		$task{Obj2}				= nextLine();
		#number	Obj2Var1
		$task{Obj2Var1}			= nextLine()		if $task{Obj2};
		#number	Obj2Var2
		$task{Obj2Var2}			= nextLine()		if $task{Obj2};
		#text	Obj2Msg
		$task{Obj2Msg}			= nextLine()		if $task{Obj2};
		#truth	WinGame
		$task{WinGame}			= nextLine();
	}
	#Restrictions	Restrictions
	$task{Restrictions}			= [];
	my $restrictions			= 0;
	$restrictions				= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	print $File_Log "\t\t\t$restrictions restriction(s)\n"	if defined $Option_Verbose;
	for (1 .. $restrictions) { push @{ $task{Restrictions} }, parseRestriction(); }
	#Actions	Actions
	$task{Actions}				= [];
	my $actions					= 0;
	$actions					= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	print $File_Log "\t\t\t$actions action(s)\n"	if defined $Option_Verbose;
	for (1 .. $actions) { push @{ $task{Actions} }, parseAction(); }
	#text	RestrMask
	$task{RestrMask}			= nextLine()		if $Container_Version eq '4.00';
	#resource Res
	$task{Resource}				= parseResource()	if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	return \%task;
}
sub parseEvent(){
	my $id		= @Events;
	my %event	= ();
	#References
	$event{RoomReferences}		= [];
	$event{ObjectReferences}	= [];
	$event{TaskReferences}		= [];
	$event{EventReferences}		= [];
	$event{PersonReferences}	= [];
	$event{GroupReferences}		= [];
	$event{SynonymReferences}	= [];
	$event{VariableReferences}	= [];
	$event{ALRReferences}		= [];
	#text	Short
	$event{Short}			= nextLine();
	print $File_Log "\t\t$id: $event{Short}\n"	if defined $Option_Verbose;
	#number	StarterType
	$event{StarterType}		= nextLine();
	#number	StartTime
	$event{StartTime}		= nextLine()		if $event{StarterType} eq 2;
	#number	EndTime
	$event{EndTime}			= nextLine()		if $event{StarterType} eq 2;
	#number	TaskNum
	$event{TaskNum}			= nextLine()		if $event{StarterType} eq 3;
	#number	RestartType
	$event{RestartType}		= nextLine();
	#truth	TaskFinished
	$event{TaskFinished}	= nextLine();
	#number	Time1
	$event{Time1}			= nextLine();
	#number	Time2
	$event{Time2}			= nextLine();
	#text	StartText
	$event{StartText}		= nextLine();
	#text	LookText
	$event{LookText}		= nextLine();
	#text	FinishText
	$event{FinishText}		= nextLine();
	#RoomList	Where
	$event{WhereType}		= 9;
	$event{WhereType}		= nextLine();
#	0: NO_ROOMS
#	1: ONE_ROOM
#	2: SOME_ROOMS
#	3: ALL_ROOMS
#	4: NPC_PART
#	9: NULL/Off-stage
	$event{Where}			= ();
	if ($event{WhereType} eq 1) {
		my $roomID	= nextLine() + 1;
		push @{	$event{Where} }, $roomID;
	}
	if($event{WhereType} eq 2){
		for my $room (1 .. $#Rooms){ push @{ $event{Where} }, $room if nextLine(); }
	}
	#number	PauseTask
	$event{PauseTask}		= nextLine();
	#truth	PauserCompleted
	$event{PauserCompleted}	= nextLine();
	#number	PrefTime1
	$event{PrefTime1}		= nextLine();
	#text	PrefText1
	$event{PrefText1}		= nextLine();
	#number	ResumeTask
	$event{ResumeTask}		= nextLine();
	#truth	ResumerCompleted
	$event{ResumerCompleted}= nextLine();
	#number	PrefTime2
	$event{PrefTime2}		= nextLine();
	#text	PrefText2
	$event{PrefText2}		= nextLine();
	#number	Obj2
	$event{Obj2}			= nextLine();
	#number	Obj2Dest
	$event{Obj2Dest}		= nextLine();
	#number	Obj3
	$event{Obj3}			= nextLine();
	#number	Obj3Dest
	$event{Obj3Dest}		= nextLine();
	#number	Obj1
	$event{Obj1}			= nextLine();
	#number	Obj1Dest
	$event{Obj1Dest}		= nextLine();
	#number	TaskAffected
	$event{TaskAffected}	= nextLine();
	#Resources
	$event{Res1}			= parseResource()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	$event{Res2}			= parseResource()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	$event{Res3}			= parseResource()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	$event{Res4}			= parseResource()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	$event{Res5}			= parseResource()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	return \%event;
}
sub parsePerson(){
	my $id		= @Persons;
	my %person	= ();
	#References
	$person{RoomReferences}		= [];
	$person{ObjectReferences}	= [];
	$person{TaskReferences}		= [];
	$person{EventReferences}	= [];
	$person{PersonReferences}	= [];
	$person{GroupReferences}	= [];
	$person{SynonymReferences}	= [];
	$person{VariableReferences}	= [];
	$person{ALRReferences}		= [];
	#text	Name
	$person{Name}			= nextLine();
	print $File_Log "\t\t$id: $person{Name}\n"	if defined $Option_Verbose;
	#text	Prefix
	$person{Prefix}			= nextLine();
	#text	Alias
	my $alias				= 1;
	$alias					= nextLine()		if $Container_Version eq '4.00';
	$person{Alias}			= ();
	for (1 .. $alias) { push @{ $person{Alias} }, nextLine(); }
	#text	Descr
	$person{Description}	= nextLine();
	#number	StartRoom
	$person{StartRoom}		= nextLine();
	#text	AltText
	$person{AltDesc}		= nextLine();
	#text	Task
	$person{AltDescTask}	= nextLine();
	#text	Topics
	my $topics				= nextLine();
	$person{Topics}			= ();
	print $File_Log "\t\t\t$topics topics(s)\n"	if defined $Option_Verbose;
	for (1 .. $topics) { push @{ $person{Topics} }, parseTopic(); }
	#text	Walks
	my $walks				= nextLine();
	$person{Walks}			= ();
	print $File_Log "\t\t\t$walks walks(s)\n"	if defined $Option_Verbose;
	for (1 .. $walks) { push @{ $person{Walks} }, parseWalk(); }
	#truth	ShowEnterExit
	$person{ShowEnterExit}	= nextLine();
	#text	EnterText
	$person{EnterText}		= nextLine()		if $person{ShowEnterExit};
	#text	ExitText
	$person{ExitText}		= nextLine()		if $person{ShowEnterExit};
	#text	InRoomText
	$person{InRoomText}		= nextLine();
	#number	Gender
	$person{Gender}			= 0					if $Container_Version eq '3.80';
	$person{Gender}			= nextLine()		if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#Resources
	$person{Res1}			= parseResource()	if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	$person{Res2}			= parseResource()	if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	$person{Res3}			= parseResource()	if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	$person{Res4}			= parseResource()	if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#battle	Battle
	$person{BattleStats}	= parseBattle()		if $Story{EnableBattle};
	return \%person;
}
sub parseGroup(){
	my $id		= @Groups;
	my %group	= ();
	#References
	$group{RoomReferences}		= [];
	$group{ObjectReferences}	= [];
	$group{TaskReferences}		= [];
	$group{EventReferences}		= [];
	$group{PersonReferences}	= [];
	$group{GroupReferences}		= [];
	$group{SynonymReferences}	= [];
	$group{VariableReferences}	= [];
	$group{ALRReferences}		= [];
	#text	Name
	$group{Name}			= nextLine();
	print $File_Log "\t\t$id: $group{Name}\n"	if defined $Option_Verbose;
	#		Rooms
	$group{Rooms}			= ();
	for my $room (1 .. $#Rooms){ push @{ $group{Rooms} }, $room if nextLine(); }
	return \%group;
}
sub parseSynonym(){
	my $id		= @Synonyms;
	my %synonym	= ();
	#References
	$synonym{RoomReferences}		= [];
	$synonym{ObjectReferences}		= [];
	$synonym{TaskReferences}		= [];
	$synonym{EventReferences}		= [];
	$synonym{PersonReferences}		= [];
	$synonym{GroupReferences}		= [];
	$synonym{SynonymReferences}		= [];
	$synonym{VariableReferences}	= [];
	$synonym{ALRReferences}			= [];
	#text	Original
	$synonym{Original}			= nextLine();
	#text	Replacement
	$synonym{Replacement}		= nextLine();
	print $File_Log "\t\t$id: $synonym{Replacement} -> $synonym{Original}\n"	if defined $Option_Verbose;
	return \%synonym;
}
sub parseVariable(){
	my $id			= @Variables;
	my %variable	= ();
	#References
	$variable{RoomReferences}		= [];
	$variable{ObjectReferences}		= [];
	$variable{TaskReferences}		= [];
	$variable{EventReferences}		= [];
	$variable{PersonReferences}		= [];
	$variable{GroupReferences}		= [];
	$variable{SynonymReferences}	= [];
	$variable{VariableReferences}	= [];
	$variable{ALRReferences}		= [];
	#text	Name
	$variable{Name}			= nextLine();
	#number	Type
	$variable{Type}			= 0					if $Container_Version eq '3.90';
	$variable{Type}			= nextLine()		if $Container_Version eq '4.00';
	#text	Value
	$variable{Value}		= nextLine();
	print $File_Log "\t\t$id: $variable{Name} ($variable{Type}) = $variable{Value}\n"	if defined $Option_Verbose;
	return \%variable;
}
sub parseALR(){
	my $id	= @ALRs;
	my %alr	= ();
	#References
	$alr{RoomReferences}		= [];
	$alr{ObjectReferences}		= [];
	$alr{TaskReferences}		= [];
	$alr{EventReferences}		= [];
	$alr{PersonReferences}		= [];
	$alr{GroupReferences}		= [];
	$alr{SynonymReferences}		= [];
	$alr{VariableReferences}	= [];
	$alr{ALRReferences}			= [];
	#text	Original
	$alr{Original}			= nextLine();
	#text	Replacement
	$alr{Replacement}		= nextLine();
	print $File_Log "\t\t$id: $alr{Original} -> $alr{Replacement}\n"	if defined $Option_Verbose;
	return \%alr;
}
#Routines for parsing sub-objects
sub parseBattle(){
	die 'Fatal error: Stories using the battle system are not supported';
}
sub parseResource(){
	my %resource	= ();
	if($Story{EnableSound}){
		#text	SoundFile
		$resource{SoundFile}	= nextLine();
		#number	SoundLen
		$resource{SoundSize}	= 0				if $Container_Version eq '3.90';
		$resource{SoundSize}	= nextLine()	if $Container_Version eq '4.00';
	}
	if($Story{EnableGraphics}){
		#text	GraphicFile
		$resource{GraphicFile}	= nextLine();
		#number	GraphicLen
		$resource{GraphicSize}	= 0				if $Container_Version eq '3.90';
		$resource{GraphicSize}	= nextLine()	if $Container_Version eq '4.00';
	}
	return \%resource;
}
sub parseRoomAlt(){
	my %alt				= ();
	#	$M1
	$alt{M1}			= nextLine();
	#	#Type
	$alt{Type}			= nextLine();
	#	<RESOURCE>Res1
	$alt{Resource1}		= parseResource();
	#	$M2
	$alt{M2}			= nextLine();
	#	#Var2
	$alt{Var2}			= nextLine();
	#	<RESOURCE>Res2
	$alt{Resource2}		= parseResource();
	#	#HideObjects
	$alt{HideObjects}	= nextLine();
	#	$Changed
	$alt{Changed}		= nextLine();
	#	#Var3
	$alt{Var3}			= nextLine();
	#	#DisplayRoom
	$alt{DisplayRoom}	= nextLine();
	return \%alt;
}
sub parseExit(){
	my %exit		= ();
	#destination
	$exit{Destination}	= nextLine();
	if ($exit{Destination}){
		$exit{Var1}		= nextLine();
		$exit{Var2}		= nextLine();
		$exit{Var3}		= 0;
		$exit{Var3}		= nextLine()			if $Container_Version eq '4.00';
	}
	return \%exit;
}
sub parseRestriction(){
	my %restriction		= ();
	#number	Type
	$restriction{Type}		= nextLine();
	if($restriction{Type} eq 0){
		$restriction{Var1}	= nextLine();
		$restriction{Var2}	= nextLine();
		$restriction{Var3}	= nextLine();
	}
	if($restriction{Type} eq 1){
		$restriction{Var1}	= nextLine();
		$restriction{Var2}	= nextLine();
	}
	if($restriction{Type} eq 2){
		$restriction{Var1}	= nextLine();
		$restriction{Var2}	= nextLine();
	}
	if($restriction{Type} eq 3){
		$restriction{Var1}	= nextLine();
		$restriction{Var2}	= nextLine();
		$restriction{Var3}	= nextLine();
	}
	if($restriction{Type} eq 4){
		$restriction{Var1}	= nextLine();
		$restriction{Var1}++				if $Container_Version eq '3.90' && $restriction{Var1};
		$restriction{Var2}	= nextLine();
		$restriction{Var3}	= nextLine();
		$restriction{Var4}	= '';
		$restriction{Var4}	= nextLine()	if $Container_Version eq '4.00';
	}
	$restriction{FailureText}	= nextLine();
	return \%restriction;
}
sub parseAction(){
	my %action;
	#number	Type
	$action{Type}		= nextLine();
	$action{Type}++		if $action{Type} > 4 && $Container_Version eq '3.90';
	if($action{Type} eq 0){
		$action{Var1}	= nextLine();
		$action{Var2}	= nextLine();
		$action{Var3}	= nextLine();
	}
	if($action{Type} eq 1){
		$action{Var1}	= nextLine();
		$action{Var2}	= nextLine();
		$action{Var3}	= nextLine();
	}
	if($action{Type} eq 2){
		$action{Var1}	= nextLine();
		$action{Var2}	= nextLine();
	}
	if($action{Type} eq 3){
		$action{Var1}	= nextLine();
		$action{Var2}	= nextLine();
		$action{Var3}	= nextLine();
		$action{Expr}	= nextLine()	if $Container_Version eq '4.00';
		$action{Expr}	= nextLine()	if $Container_Version eq '3.90' && $action{Var2} eq 5;
		$action{Expr}	= ''			if $Container_Version eq '3.90' && $action{Var2} != 5;
		$action{Var5}	= nextLine()	if $Container_Version eq '4.00';
		$action{Var5}	= nextLine()	if $Container_Version eq '3.90' && $action{Var2} != 5;
		$action{Var5}	= 0				if $Container_Version eq '3.90' && $action{Var2} eq 5;
	}
	if($action{Type} eq 4){
		$action{Var1}	= nextLine();
	}
	if($action{Type} eq 5){
		$action{Var1}	= nextLine();
		$action{Var2}	= nextLine();
	}
	if($action{Type} eq 6){
		$action{Var1}	= nextLine();
		$action{Var2}	= 0				if $Container_Version eq '3.90';
		$action{Var2}	= nextLine()	if $Container_Version eq '4.00';
		$action{Var3}	= 0				if $Container_Version eq '3.90';
		$action{Var3}	= nextLine()	if $Container_Version eq '4.00';
	}
	if($action{Type} eq 7){
		$action{Var1}	= nextLine();
		$action{Var2}	= nextLine();
		$action{Var3}	= nextLine();
	}
	return \%action;
}
sub parseTopic(){
	my %topic;
	#text	Subject
	$topic{Subject}			= nextLine();
	#text	Reply
	$topic{Reply}			= nextLine();
	#number	Task
	$topic{AltReplyTask}	= nextLine();
	#text	AltReply
	$topic{AltReply}		= nextLine();
	return \%topic;
}
sub parseWalk(){
	my %walk;
	#number	NumStops
	my $stops				= nextLine();
	print $File_Log "\t\t\t\t$stops stops(s)\n"	if defined $Option_Verbose;
	$walk{NumStops}			= $stops;
	#truth	Loop
	$walk{Loop}				= nextLine();
	#number	StartTask
	$walk{StartTask}		= nextLine();
	#number	CharTask
	$walk{CharTask		}	= nextLine();
	#number	MeetObject
	$walk{MeetObject}		= nextLine();
#TODO: ?!#MeetObject=0:|V380_WALK:_MeetObject_|
	#number	ObjectTask
	$walk{ObjectTask}		= nextLine();
	#number	StoppingTask
	$walk{StoppingTask}		= 0				if $Container_Version eq '3.80';
	$walk{StoppingTask}		= nextLine()	if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#number	MeetChar
	$walk{MeetChar}			= 0				if $Container_Version eq '3.80' or $Container_Version eq '3.90';
	$walk{MeetChar}			= nextLine()	if $Container_Version eq '4.00';
	#text	ChangedDesc
	$walk{ChangedDesc}		= ''			if $Container_Version eq '3.80';
	$walk{ChangedDesc}		= nextLine()	if $Container_Version eq '3.90' or $Container_Version eq '4.00';
	#	{WALK:#Rooms_#Times}
	$walk{Stops}				= ();
	for (1 .. $stops){
		my %stop		= ();
		$stop{Room}		= nextLine();
		$stop{Times}	= nextLine();
		push @{ $walk{Stops} }, \%stop;
	}
	return \%walk;
}
##Generate symbolic names, printing to mapping file if called for
sub generateSymbols(){
	{	#Rooms
		print $File_Symbol_Out "#\t$#Rooms Rooms\n"	if defined $Option_Generate;
		for my $room (1 .. $#Rooms){
			#Find a symbolic name
			my $name			= symbolic($Rooms[$room]{Short});
			#Write to mapping file if called for
			if (defined $Option_Generate){
				print $File_Symbol_Out	'#'						unless	defined $Symbol_Room[$room];
				print $File_Symbol_Out "Room$room\t = ";
				print $File_Symbol_Out "'TODO'"				unless	defined $Symbol_Room[$room];
				print $File_Symbol_Out "'$Symbol_Room[$room]'"	if		defined $Symbol_Room[$room];
				print $File_Symbol_Out "\t# $name\n";
			}
			#Store the calculated symbolic name
			$Symbol_Room[$room]	= $name		unless defined $Symbol_Room[$room];
		}
	}
	{	#Objects
		print $File_Symbol_Out "#\t$#Objects Objects\n"	if defined $Option_Generate;
		for my $object (1 .. $#Objects){
			#Find a symbolic name
			#TODO: When aggressive naming is in use, also consider aliases
			my $name			= symbolic($Objects[$object]{Prefix}.' '.$Objects[$object]{Short});
			#Write to mapping file if called for
			if (defined $Option_Generate){
				print $File_Symbol_Out	'#'							unless	defined $Symbol_Object[$object];
				print $File_Symbol_Out "Object$object\t = ";
				print $File_Symbol_Out "'TODO'"					unless	defined $Symbol_Object[$object];
				print $File_Symbol_Out "'$Symbol_Object[$object]'"	if		defined $Symbol_Object[$object];
				print $File_Symbol_Out "\t# $name\n";
			}
			#Store the calculated symbolic name
			$Symbol_Object[$object]	= $name		unless defined $Symbol_Object[$object];
		}
	}
	{	#Tasks
		print $File_Symbol_Out "#\t$#Tasks Tasks\n"	if defined $Option_Generate;
		for my $task (1 .. $#Tasks){
			#Find a symbolic name
			my @commands		= @{ $Tasks[$task]{Commands} };
			my $name			= '';
			foreach my $command (@commands){
				$command	= symbolic($command);
				$name		= $command	if length($command) > length($name);
			}
			#Write to mapping file if called for
			if (defined $Option_Generate){
				print $File_Symbol_Out	'#'						unless	defined $Symbol_Task[$task];
				print $File_Symbol_Out "Task$task\t = ";
				print $File_Symbol_Out "'TODO'"				unless	defined $Symbol_Task[$task];
				print $File_Symbol_Out "'$Symbol_Task[$task]'"	if		defined $Symbol_Task[$task];
				print $File_Symbol_Out "\t# $name\n";
			}
			#Store the calculated symbolic name
			$Symbol_Task[$task]	= $name		unless defined $Symbol_Task[$task];
		}
	}
	{	#Events
		print $File_Symbol_Out "#\t$#Events Events\n"	if defined $Option_Generate;
		for my $event (1 .. $#Events){
			#Find a symbolic name
			my $name			= symbolic($Events[$event]{Short});
			#Write to mapping file if called for
			if (defined $Option_Generate){
				print $File_Symbol_Out	'#'							unless	defined $Symbol_Event[$event];
				print $File_Symbol_Out "Event$event\t = ";
				print $File_Symbol_Out "'TODO'"						unless	defined $Symbol_Event[$event];
				print $File_Symbol_Out "'$Symbol_Event[$event]'"	if		defined $Symbol_Event[$event];
				print $File_Symbol_Out "\t# $name\n";
			}
			#Store the calculated symbolic name
			$Symbol_Event[$event]	= $name		unless defined $Symbol_Event[$event];
		}
	
	}
	{	#Persons
		print $File_Symbol_Out "#\t$#Persons Persons\n"	if defined $Option_Generate;
		for my $person (1 .. $#Persons){
			#Find a symbolic name
			#TODO: When aggressive naming is in use, also consider aliases
			my $name			= symbolic($Persons[$person]{Prefix}.' '.$Persons[$person]{Name});
			#Write to mapping file if called for
			if (defined $Option_Generate){
				print $File_Symbol_Out	'#'							unless	defined $Symbol_Person[$person];
				print $File_Symbol_Out "Person$person\t = ";
				print $File_Symbol_Out "'TODO'"					unless	defined $Symbol_Person[$person];
				print $File_Symbol_Out "'$Symbol_Person[$person]'"	if		defined $Symbol_Person[$person];
				print $File_Symbol_Out "\t# $name\n";
			}
			#Store the calculated symbolic name
			$Symbol_Person[$person]	= $name		unless defined $Symbol_Person[$person];
		}
	}
	{	#RoomGroups
		print $File_Symbol_Out "#\t$#Groups Groups\n"	if defined $Option_Generate;
		for my $group (1 .. $#Groups){
			#Find a symbolic name
			my $name			= symbolic($Groups[$group]{Name});
			#Write to mapping file if called for
			if (defined $Option_Generate){
				print $File_Symbol_Out	'#'							unless	defined $Symbol_Group[$group];
				print $File_Symbol_Out "Group$group\t = ";
				print $File_Symbol_Out "'TODO'"						unless	defined $Symbol_Group[$group];
				print $File_Symbol_Out "'$Symbol_Group[$group]'"	if		defined $Symbol_Group[$group];
				print $File_Symbol_Out "\t# $name\n";
			}
			#Store the calculated symbolic name
			$Symbol_Group[$group]	= $name		unless defined $Symbol_Group[$group];
		}
	}
	{	#Variables
		print $File_Symbol_Out "#\t$#Variables Variables\n"	if defined $Option_Generate;
		for my $variable (1 .. $#Variables){
			#Find a symbolic name
			my $name			= symbolic($Variables[$variable]{Name});
			#Write to mapping file if called for
			if (defined $Option_Generate){
				print $File_Symbol_Out	'#'								unless	defined $Symbol_Variable[$variable];
				print $File_Symbol_Out "Variable$variable\t = ";
				print $File_Symbol_Out "'TODO'"						unless	defined $Symbol_Variable[$variable];
				print $File_Symbol_Out "'$Symbol_Variable[$variable]'"	if		defined $Symbol_Variable[$variable];
				print $File_Symbol_Out "\t# $name\n";
			}
			#Store the calculated symbolic name
			$Symbol_Variable[$variable]	= $name		unless defined $Symbol_Variable[$variable];
		}
	}
}
sub symbolic($){
	my $text	= shift;
	return ''	unless defined $text;
#	$text		=~ s/[-_\"\[\]\\%]//g;		# Trim all unwanted characters
	$text		=~ s/[^a-z0-9\s]//ig;		# Remove any non-alphanumeric characters
	$text		=~ s/\s+/ /g;				# Convert all whitespace to spaces, and trim multiples
	$text		=~ s/^\s+|\s+$//g;			# Trim leading/trailing whitespace
	return $text;
}
##Analyzing cross-type
sub analyze(){
	#Analyze rooms
	print $File_Log "Analyzing rooms:\n";
	for my $room (1 .. $#Rooms){ analyzeRoom($room) }
	#Analyze objects
	print $File_Log "Analyzing objects:\n";
	for my $object (1 .. $#Objects){ analyzeObject($object) }
	#Analyze tasks
	print $File_Log "Analyzing tasks:\n";
	for my $task (1 .. $#Tasks){ analyzeTask($task) }
	#Analyze events
	print $File_Log "Analyzing events:\n";
	for my $event (1 .. $#Events){ analyzeEvent($event) }
	#TODO: Analyze persons
	#TODO: Analyze room groups
	#TODO: Analyze synonyms
	#TODO: Analyze variables
	#TODO: Analyze ALRs
	#Mapping tables
	if ($Option_Verbose){
		print $File_Log "Static Object IDs:\n";
		for my $id (1 .. $#ObjectStatic){
			print $File_Log "\t$id -> $ObjectStatic[$id] (".nameObject($ObjectStatic[$id]).")\n";
		}
		print $File_Log "Portable Object IDs:\n";
		for my $id (1 .. $#ObjectPortable){
			print $File_Log "\t$id -> $ObjectPortable[$id] (".nameObject($ObjectPortable[$id]).")\n";
		}
		print $File_Log "Openable Object IDs:\n";
		for my $id (1 .. $#ObjectOpenable){
			print $File_Log "\t$id -> $ObjectOpenable[$id] (".nameObject($ObjectOpenable[$id]).")\n";
		}
		print $File_Log "Stateful Object IDs:\n";
		for my $id (1 .. $#ObjectStateful){
			print $File_Log "\t$id -> $ObjectStateful[$id] (".nameObject($ObjectStateful[$id]).")\n";
		}
		print $File_Log "Holder Object IDs:\n";
		for my $id (1 .. $#ObjectHolder){
			print $File_Log "\t$id -> $ObjectHolder[$id] (".nameObject($ObjectHolder[$id]).")\n";
		}
		print $File_Log "Container Object IDs:\n";
		for my $id (1 .. $#ObjectContainer){
			print $File_Log "\t$id -> $ObjectContainer[$id] (".nameObject($ObjectContainer[$id]).")\n";
		}
		print $File_Log "Supporter Object IDs:\n";
		for my $id (1 .. $#ObjectSurface){
			print $File_Log "\t$id -> $ObjectSurface[$id] (".nameObject($ObjectSurface[$id]).")\n";
		}
	}
}
sub analyzeRoom($){
	my $room		= shift;
	my $exits		= @{ $Rooms[$room]{Exits} };
	#Interpret the exit restrictions; sclibrar.lib_can_go
	for my $direction (0 .. $Story{Directions}-1){
		my %exit = %{ $Rooms[$room]{Exits}[$direction] };
		# Destination; 0 indicates no exit
		my $destination	= $exit{Destination};
		next unless $destination;
		my $var1		= $exit{Var1};	#	ID; 0 indicates no restriction
		my $var2		= $exit{Var2};	#	ExpectedState
		my $var3		= $exit{Var3};	#	Type
		my $text		= "UNKNOWN RESTRICTION $var1 $var2 $var3";
		# Restriction ID: 0 indicates no restriction
		next unless $var1;
		#Type determines the restriction
		# 0: Task
		if($var3 eq 0) {
			# TaskID
			my $task		= "UNKNOWN TASK $var1";
			$task			= nameTask($var1)	if $var1 < @Tasks;
			#Record reference between room and task
			push @{ $Rooms[$room]{TaskReferences} },
				{ id => $var1,		type => 'RestrainedBy'};
			push @{ $Tasks[$var1]{RoomReferences} }, 
				{ id => $room,	type => 'Restraining'};
			# ExpectedState determines condition
			my $condition	= "UNKNOWN TASK-CONDITION $var2";
			$condition		= 'if'		if $var2 eq 0;
			$condition		= 'unless'	if $var2 eq 1;
			#Assemble full text
			$text	= "$condition $task is performed";
		}
		# 1: ObjectState
		if($var3 eq 1) {
			# ObjectID
			my $objectID	= $ObjectStateful[$var1];
			my $object		= nameObject($objectID);
			#Record reference between room and object
			push @{ $Rooms[$room]{ObjectReferences} },
				{ id => $objectID,		type => 'RestrainedBy'};
			push @{ $Objects[$objectID]{RoomReferences} }, 
				{ id => $room,	type => 'Restraining'};
			# ExpectedState		TODO
			my $state		= "UNKNOWN STATE $var2";
			#Assemble full text
			$text	= "if $object is $state";
		}
		$Rooms[$room]{Exits}[$direction]{Restriction}	= $text if defined $text;
	}
}
sub analyzeObject($){
	my $object			= shift;
	{	# Determine object class based on properties	TODO
		my $class;
		#If object is in multiple rooms, it must be a backdrop (even if it is a container in ADRIFT)
		if		($Objects[$object]{WhereType} eq 2
			or	 $Objects[$object]{WhereType} eq 3){
			$class	= 'backdrop';
		}
		#If object is classified as a body part, then we go with that
		elsif	($Objects[$object]{WhereType} eq 4){
			$class	= 'body part';
		}
		#Store what we've calculated
		$Objects[$object]{Class}		= $class	if defined $class;
	}
}
sub analyzeTask($){
	my $task			= shift;
	my $locations		= @{ $Tasks[$task]{Where} };
	my $restrictions	= @{ $Tasks[$task]{Restrictions} };
	my $actions			= @{ $Tasks[$task]{Actions} };
	my @commands		= @{ $Tasks[$task]{Commands} };
	#Interpret the restrictions of the task; screstrs.restr_pass_task_restriction (pp21-22)
	for my $id (0 .. $restrictions - 1){
		my %restriction	= %{ $Tasks[$task]{Restrictions}[$id] };
		my $type		= $restriction{Type};
		my $text;
		#ObjectLocation: ObjectID, Condition, Location;
		if($type eq 0){
			my $var1	= $restriction{Var1};
			my $var2	= $restriction{Var2};
			my $var3	= $restriction{Var3};
			#ObjectID
			my $object		= "UNKNOWN OBJECT $var1";
			# 0=Nothing
			$object			= 'nothing'				if $var1 eq 0;
			# 1=Anything
			$object			= 'anything'			if $var1 eq 1;
			# 2=Referenced
			$object			= 'referenced object'	if $var1 eq 2;
			# 3+: Portable Object
			if (3 <= $var1 && $var1 <= @ObjectPortable + 2) {
				my $objectID	= $ObjectPortable[$var1-2];
				$object			= nameObject($objectID);
				#Record reference between task and object
				push @{ $Objects[$objectID]{TaskReferences} },
					{ id => $task,		type => 'Restraining'};
				push @{ $Tasks[$task]{ObjectReferences} },
					{ id => $objectID,	type => 'RestrainedBy'};
			}
			#Log warning
			print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3) unhandled object (v1)\n" unless 0 <= $var1 && $var1 <= @ObjectPortable+2;
			#ConditionType
			my $condition	= "UNKNOWN CONDITION $var2";
			# 0& 6=In Room
			$condition		= 'located in'			if $var2 eq 0;
			$condition		= 'not located in'		if $var2 eq 6;
			# 1& 7=Carried by person
			$condition		= 'carried by'			if $var2 eq 1;
			$condition		= 'not carried by'		if $var2 eq 7;
			# 2& 8=Worn by person
			$condition		= 'worn by'				if $var2 eq 2;
			$condition		= 'not worn by'			if $var2 eq 8;
			# 3& 9=Visible to person
			$condition		= 'visible to'			if $var2 eq 3;
			$condition		= 'not visible to'		if $var2 eq 9;
			# 4&10=Inside container
			$condition		= 'inside'				if $var2 eq 4;
			$condition		= 'not inside'			if $var2 eq 10;
			# 5&11=On surface
			$condition		= 'on top of'			if $var2 eq 5;
			$condition		= 'not on top of'		if $var2 eq 11;
			#Log warning
			print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3) unhandled condition (v2)\n" unless 0 <= $var2 && $var2 <= 11;
			#Location; depending on condition
			my $location	= "UNKNOWN LOCATION $var3";
			# 0: Room
			if ($var2 % 6 eq 0) {
				if (0 <= $var3 && $var3 < @Rooms){
					my $roomID		= $var3 + 1;
					$location		= nameRoom($roomID);
					#Record reference between task and room
					push @{ $Rooms[$roomID]{TaskReferences} },
						{ id => $task,		type => 'Restraining'};
					push @{ $Tasks[$task]{RoomReferences} }, 
						{ id => $roomID,	type => 'RestrainedBy'};
				}
				#Log warning
				print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3) unhandled room (v3)\n" unless 1 <= $var3 && $var3 <= @Rooms;
			}
			# 1-3: Person
			if (1 <= $var2 % 6 && $var2 % 6 <= 3) {
				# 0: The player
				$location		= 'the player'		if $var3 eq 0;
				# 1: The referenced person
				$location		= 'referenced'		if $var3 eq 1;
				# 2+: PersonID
				if (1 < $var3 && $var3 <= @Persons + 1){
					my $personID	= $var3-1;
					$location		= 'by '.namePerson($personID);
					#Record reference between task and person
					push @{ $Persons[$personID]{TaskReferences} },
						{ id => $task,		type => 'Restraining'};
					push @{ $Tasks[$task]{PersonReferences} }, 
						{ id => $personID,	type => 'RestrainedBy'};
				}
				#Log warning
				print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3) unhandled person (v3)\n" unless 0 <= $var3 && $var3 <= @Persons+1;
			}
			#4: Container
			if ($var2 % 6 eq 4) {
				my $objectID	= $ObjectContainer[$var3];
				$location		= nameObject($objectID);
				#Record reference between task and object
				push @{ $Objects[$objectID]{TaskReferences} },
					{ id => $task,		type => 'Restraining'};
				push @{ $Tasks[$task]{ObjectReferences} },
					{ id => $objectID,	type => 'RestrainedBy'};
				#Log warning
				print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3) unhandled container (v3)\n" unless 1 <= $var3 && $var3 <= @ObjectContainer;
			}
			#5: Supporter
			if ($var2 % 6 eq 5) {
				my $objectID	= $ObjectSurface[$var3];
				$location		= nameObject($objectID);
				#Record reference between task and object
				push @{ $Objects[$objectID]{TaskReferences} },
					{ id => $task,		type => 'Restraining'};
				push @{ $Tasks[$task]{ObjectReferences} },
					{ id => $objectID,	type => 'RestrainedBy'};
				#Log warning
				print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3) unhandled surface (v3)\n" unless 1 <= $var3 && $var3 <= @ObjectSurface;
			}
			#Assemble the full text
			$text	= "Unless $object is $condition $location";
		}
		#ObjectState:	ObjectID, State		TODO
		if($type eq 1){
			my $var1	= $restriction{Var1};
			my $var2	= $restriction{Var2};
			#ObjectID
			my $object		= "UNKNOWN OBJECT $var1";
			# 0: Referenced
			$object			= 'referenced object'		if $var1 eq 0;
			# 1+: Stateful ObjectID
			if (1 <= $var1 && $var1 <= @ObjectStateful) {
				my $objectID	= $ObjectStateful[$var1];
				$object			= nameObject($objectID);
				#Record reference between task and object
				push @{ $Objects[$objectID]{TaskReferences} },
					{ id => $task,		type => 'Restraining'};
				push @{ $Tasks[$task]{ObjectReferences} },
					{ id => $objectID,	type => 'RestrainedBy'};
			}
			#State
			my $state		= "UNKNOWN STATE $var2";
			#Assemble the full text and log warning
			$text	= "Unless $object is $state";
			print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2) unhandled object (v1)\n" unless 0 <= $var1 && $var1 <= @ObjectStateful;
			print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2) unhandled state (v2)\n";
		}
		#TaskState:		Task, State
		if($type eq 2){
			my $var1	= $restriction{Var1};
			my $var2	= $restriction{Var2};
			#TaskID
			my $restrictor	= "UNKNOWN TASK $var1";
			# 0: Referenced
			$restrictor			= 'all tasks'		if $var1 eq 0;
			# 1+: TaskID
			if ($var1 > 0 && $var1 <= @Tasks) {
				my $taskID	= $var1;
				$restrictor	= nameTask($taskID);
				#Record reference between task and task
				push @{ $Tasks[$taskID]{TaskReferences} },
					{ id => $task,		type => 'Restraining'};
				push @{ $Tasks[$task]{TaskReferences} },
					{ id => $taskID,	type => 'RestrainedBy'};
			}
			#State
			my $state		= "UNKNOWN STATE $var2";
			# 0: Performed
			$state			= 'performed'		if $var2 eq 0;
			# 1: Not Performed
			$state			= 'not performed'	if $var2 eq 1;
			#Assemble the full text and log warning
			$text	= "Unless $restrictor is $state";
			print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2) unhandled task (v1)\n"		unless 0 <= $var1 && $var1 <= @Tasks;
			print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2) unhandled state (v2)\n"	unless 0 <= $var2 && $var2 <= 1;
		}
		#Person:		PersonID, Condition, Location
		if($type eq 3){
			my $var1	= $restriction{Var1};
			my $var2	= $restriction{Var2};
			my $var3	= $restriction{Var3};
			#PersonID
			my $person		= "UNKNOWN PERSON $var1";
			# 0: Player
			$person			= 'the player'				if $var1 eq 0;
			# 1: Referenced
			$person			= 'referenced person'		if $var1 eq 1;
			# 2+: PersonID
			if (2 <= $var1 && $var1 <= @Persons + 1){
				my $personID	= $var1-1;
				$person			= namePerson($personID);
				#Record reference between task and person
				push @{ $Persons[$personID]{TaskReferences} },
					{ id => $task,		type => 'Restraining'};
				push @{ $Tasks[$task]{PersonReferences} }, 
					{ id => $personID,	type => 'RestrainedBy'};
			}
			#Log warning
			print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3) unhandled person (v1)\n" unless 0 <= $var1 && $var1 <= @Persons+1;
			#Condition
			my $condition	= "UNKNOWN CONDITION $var2";
			# 0=In same room as
			$condition		= 'in the presence of'		if $var2 eq 0;
			# 1=Not in same room as
			$condition		= 'not in the presence of'	if $var2 eq 1;
			# 2=Alone
			$condition		= 'alone'					if $var2 eq 2;
			# 3=Not Alone
			$condition		= 'not alone'				if $var2 eq 3;
			# 4=Standing on
			$condition		= 'standing on'				if $var2 eq 4;
			# 5=Sitting on
			$condition		= 'sitting on'				if $var2 eq 5;
			# 6=Lying on
			$condition		= 'lying on'				if $var2 eq 6;
			# 7=Gender
			$condition		= ''						if $var2 eq 7;
			#Log warning
			print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3) unhandled condition (v2)\n" unless 0 <= $var2 && $var2 <= 7;
			#Location; depending on condition
			my $location	= "UNKNOWN LOCATION $var3";
			#0-1: Person
			if (0 <= $var2 && $var2 <= 1) {
				# 0=Player
				$location		= 'the player'			if $var3 eq 0;
				# 1=Referenced
				$location		= 'referenced'			if $var3 eq 1;
				# 2+: PersonID
				if (2 <= $var3 && $var3 <= @Persons + 1) {
					my $personID	= $var3-1;
					$location		= namePerson($personID);
					#Record reference between task and person
					push @{ $Persons[$personID]{TaskReferences} },
						{ id => $task,		type => 'Restraining'};
					push @{ $Tasks[$task]{PersonReferences} }, 
						{ id => $personID,	type => 'RestrainedBy'};
				}
				#Log warning
				print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3) unhandled person (v3)\n" unless 0 <= $var3 && $var3 <= @Persons+1;
			}
			#2-3: Blank
			if (2 <= $var2 && $var2 <= 3) {
				$location		= '';
			}
			#4-5: Sit/Standable
			if (4 <= $var2 && $var2 <= 5) {
				# 0: ground (ie nothing)
				$location		= 'the ground'	if $var3 eq 0;
				# 1+: Object
				if (1 <= $var3 && $var3 <= @ObjectSitStandable) {
					my $objectID	= $ObjectSitStandable[$var3];
					$location		= nameObject($objectID);
					#Record reference between task and object
					push @{ $Objects[$objectID]{TaskReferences} },
						{ id => $task,		type => 'Restraining'};
					push @{ $Tasks[$task]{ObjectReferences} },
						{ id => $objectID,	type => 'RestrainedBy'};
				}
				#Log warning
				print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3) unhandled sitstandable (v3)\n" unless 0 <= $var3 && $var3 <= @ObjectSitStandable;
			}
			#6: Lieable
			if ($var2 eq 6) {
				my $objectID	= $ObjectLieable[$var3];
				$location		= nameObject($objectID);
				#Record reference between task and object
				push @{ $Objects[$objectID]{TaskReferences} },
					{ id => $task,		type => 'Restraining'};
				push @{ $Tasks[$task]{ObjectReferences} },
					{ id => $objectID,	type => 'RestrainedBy'};
				#Log warning
				print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3) unhandled lieable (v3)\n" unless 1 <= $var3 && $var3 <= @ObjectLieable;
			}
			#7: Gender
			if ($var2 eq 7) {
				$location		= nameGender($var3);
				#Log warning
				print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3) unhandled gender (v3)\n" unless 0 <= $var3 && $var3 <= @Symbol_Gender;
			}
			#Assemble the full text
			$text	= "Unless $person is $condition $location";
		}
		#Variable:		VariableID, Operator, Number, Text
		if($type eq 4){
			my $var1	= $restriction{Var1};
			my $var2	= $restriction{Var2};
			my $var3	= $restriction{Var3};
			my $var4	= $restriction{Var4};
			#Variable
			my $variable	= "UNKNOWN VARIABLE $var1";
			my $numeric		= 0;
			# 0: Referenced Number
			if ($var1 eq 0) {
				$variable		= 'referenced number';
				$numeric		= 1;
			}
			# 1: Referenced String
			if ($var1 eq 1) {
				$variable		= 'referenced text';
				$numeric		= 0;
			}
			# 2+: Variable
			if (2 <= $var1 && $var1 <= (1 + @Variables)) {
				my $variableID	= $var1-1;
				$variable		= nameVariable($variableID);
				$numeric		= 1 if $Variables[$variableID]{Type} eq 0;
				#Record reference between task and variable
				push @{ $Variables[$variableID]{TaskReferences} },
					{ id => $task,		type => 'Restraining'};
				push @{ $Tasks[$task]{VariableReferences} },
					{ id => $variableID,	type => 'RestrainedBy'};
			}
			#Log warning
			print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3:$var4) unhandled variable (v1)\n" unless 0 <= $var1 && $var1 <= @Variables+1;
			#Operator determines comparator
			my $operator	= "UNKNOWN OPERATOR $var2";
			my $comparator	= "UNKNOWN COMPARATOR $var2";
			#Numeric variables:
			if ($numeric) {
				# 0,10: <
				$operator		= 'less than'			if $var2 % 10 eq 0;
				# 1,11: <
				$operator		= 'less or equal than'	if $var2 % 10 eq 1;
				# 2,12: ==
				$operator		= 'equal to'			if $var2 % 10 eq 2;
				# 3,13: >=
				$operator		= 'greater or equal to'	if $var2 % 10 eq 3;
				# 4,14: >
				$operator		= 'greater than'		if $var2 % 10 eq 4;
				# 5,15: !=
				$operator		= 'different to'		if $var2 % 10 eq 5;
				#Log warning
				print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3:$var4) unhandled operator (v2)\n" unless (0 <= $var2 && $var2 <= 5) or (10 <= $var2 && $var2 <= 15);
				#Direct value comparison
				if ($var2 < 10){
					$comparator		= $var3;
				}
				#Reference comparison
				else {
					#0: Referenced number
					$comparator		= 'referenced number'	if $var3 eq 0;
					#1: Variable
					if (1 <= $var3 && $var3 <= @Variables) {
						my $variableID	= $var3;
						$comparator		= nameVariable($variableID);
						#Record reference between task and variable
						push @{ $Variables[$variableID]{TaskReferences} },
							{ id => $task,		type => 'Restraining'};
						push @{ $Tasks[$task]{VariableReferences} },
							{ id => $variableID,	type => 'RestrainedBy'};
					}
					#Log warning
					print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3:$var4) unhandled variable (v3)\n" unless 0 <= $var3 && $var3 <= @Variables;
				}
			}
			#String variables
			else {
				$comparator	= $var4;
				# 0: ==
				$operator	= 'equal to'		if $var2 eq 0;
				# 1: !=
				$operator	= 'different to'	if $var2 eq 1;
				#Log warning
				print $File_Log "WARNING\tTask$task\tType=$type ($var1:$var2:$var3:$var4) unhandled operator (v2)\n" unless 0 <= $var2 && $var2 <= 1;
			}
			#Assemble the full text
			$text	= "Unless $variable is $operator $comparator";
		}
		#Store and log warning
		$Tasks[$task]{Restrictions}[$id]{Condition}		= $text if defined $text;
		print $File_Log "WARNING\tTask$task\tRestrictionType=$type unhandled\n" unless 0 <= $type && $type <= 4;
	}
	#Interpret the actions of the task
	for my $id (0 .. $actions - 1){
		my %action	= %{ $Tasks[$task]{Actions}[$id] };
		my $type	= $action{Type};
		my $text;
		#MoveObject:	ObjectID, DestinationType, Location
		if($type eq 0){
			my $var1	= $action{Var1};
			my $var2	= $action{Var2};
			my $var3	= $action{Var3};
			#ObjectID
			my $object		= "UNKNOWN PERSON $var1";
			# 0: All Carried
			$object			= 'all held objects'	if $var1 eq 0;
			# 1: All Worn
			$object			= 'all worn objects'	if $var1 eq 1;
			# 2: Referenced
			$object			= 'referenced object'	if $var1 eq 2;
			# 3+: Portable Object
			if (3 <= $var1 && $var1 <= @ObjectPortable + 2) {
				my $objectID	= $ObjectPortable[$var1-2];
				$object			= nameObject($objectID);
				#Record reference between task and object
				push @{ $Objects[$objectID]{TaskReferences} },
					{ id => $task,		type => 'MovedBy'};
				push @{ $Tasks[$task]{ObjectReferences} },
					{ id => $objectID,	type => 'Moving'};
			}
			#DestinationType determines the value of the Location
			my $destination	= "UNKNOWN DESTINATION $var2 TO $var3";
			# 0: Room
			if ($var2 eq 0) {
				# 0+: RoomID
				if (0 <= $var3 && $var3 <= @Rooms - 1) {
					my $roomID		= $var3 +1;
					$destination	= 'to '.nameRoom($roomID);
					#Record reference between task and room
					push @{ $Rooms[$roomID]{TaskReferences} },
						{ id => $task,		type => 'TargetedBy'};
					push @{ $Tasks[$task]{RoomReferences} },
						{ id => $roomID,	type => 'Targeting'};
				}
				#Log warning
				print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3) unhandled room (v3)\n" unless 0 <= $var3 && $var3 <= @Rooms-1;
			}
			# 1: RoomGroup
			if ($var2 eq 1) {
				# 0+: RoomGroupID
				if (0 <= $var3 && $var3 <= @Groups - 1) {
					my $groupID		= $var3+1;
					$destination	= 'to random room in '.nameGroup($groupID);
					#Record reference between task and roomgroup
					push @{ $Groups[$groupID]{TaskReferences} },
						{ id => $task,		type => 'TargetedBy'};
					push @{ $Tasks[$task]{GroupReferences} },
						{ id => $groupID,	type => 'Targeting'};
				}
				#Log warning
				print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3) unhandled roomgroup (v3)\n" unless 1 <= $var3 && $var3 <= @Groups-1;
			}
			# 2: Container
			if ($var2 eq 2) {
				# 0+: ContainerID
				if (0 <= $var3 && $var3 <= @ObjectContainer - 1) {
					my $objectID	= $ObjectContainer[$var3+1];
					$destination	= 'inside '.nameObject($objectID);
					#Record reference between task and object
					push @{ $Objects[$objectID]{TaskReferences} },
						{ id => $task,		type => 'TargetedBy'};
					push @{ $Tasks[$task]{ObjectReferences} },
						{ id => $objectID,	type => 'Targeting'};
				}
				#Log warning
				print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3) unhandled container (v3)\n" unless 0 <= $var3 && $var3 <= @ObjectContainer-1;
			}				
			# 3: Supporter
			if ($var2 eq 3) {
				# 0+: SupporterID
				if (0 <= $var3 && $var3 <= @ObjectSurface - 1) {
					my $objectID	= $ObjectSurface[$var3+1];
					$destination	= 'on top of '.nameObject($objectID);
					#Record reference between task and object
					push @{ $Objects[$objectID]{TaskReferences} },
						{ id => $task,		type => 'TargetedBy'};
					push @{ $Tasks[$task]{ObjectReferences} },
						{ id => $objectID,	type => 'Targeting'};
				}
				#Log warning
				print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3) unhandled supporter (v3)\n" unless 0 <= $var3 && $var3 <= @ObjectSurface-1;
			}
			# 4-6: Person (carried by, worn by, location of)
			if (4 <= $var2 && $var2 <= 6) {
				my $target	= "UNKNOWN TARGET $var3";
				# 0: The player
				$target		= 'the player'			if $var3 eq 0;
				# 1: Referenced Person
				$target		= 'referenced person'	if $var3 eq 1;
				# 2+: Person
				if (2 <= $var3 && $var3 <= @Persons + 1) {
					my $personID	= $var3 - 1;
					$target			= namePerson($personID);
					#Record reference between task and person
					push @{ $Persons[$personID]{TaskReferences} },
						{ id => $task,		type => 'TargetedBy'};
					push @{ $Tasks[$task]{PersonReferences} },
						{ id => $personID,	type => 'Targeting'};
				}
				#Assemble and log warning
				$destination	= "to $target (carried)"	if $var2 eq 4;
				$destination	= "to $target (worn)"		if $var2 eq 5;
				$destination	= "to location of $target"	if $var2 eq 6;
				print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3) unhandled person (v3)\n" unless 0 <= $var3 && $var3 <= @Persons + 1;
			}
			#Assemble the full text and log warning
			$text	= "Move $object $destination";
			print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3) unhandled Object (v1)\n" unless 0 <= $var1 && $var1 <= @ObjectPortable+2;
			print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3) unhandled destination (v2)\n" unless 0 <= $var2 && $var2 <= 6;
		}
		#MovePerson:	PersonID, DestinationType, Location
		if($type eq 1){
			my $var1	= $action{Var1};
			my $var2	= $action{Var2};
			my $var3	= $action{Var3};
			#PersonID
			my $person		= "UNKNOWN PERSON $var1";
			# 0: Player
			$person			= 'the player'			if $var1 eq 0;
			# 1: Referenced
			$person			= 'referenced person'	if $var1 eq 1;
			# 2+: Person
			if (2 <= $var1 && $var1 <= @Persons + 1) {
				my $personID	= $var1-1;
				$person			= namePerson($personID);
				#Record reference between task and person
				push @{ $Persons[$personID]{TaskReferences} },
					{ id => $task,		type => 'MovedBy'};
				push @{ $Tasks[$task]{PersonReferences} },
					{ id => $personID,	type => 'Moving'};
			}
			#DestinationType determines the value of the Location
			my $destination	= "UNKNOWN DESTINATION $var2 TO $var3";
			# 0: Room
			if ($var2 eq 0) {
				# 0+: Room/Nowhere
				if (0 <= $var3 && $var3 < @Rooms) {
					my $roomID		= $var3;
					$destination	= 'to '.nameRoom($roomID);
					#Record reference between task and room
					push @{ $Rooms[$roomID]{TaskReferences} },
						{ id => $task,		type => 'TargetedBy'};
					push @{ $Tasks[$task]{RoomReferences} },
						{ id => $roomID,	type => 'Targeting'};
				}
				#Log warning
				print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3) unhandled room (v3)\n" unless 0 <= $var3 && $var3 <= @Rooms-1;
			}
			# 1: RoomGroup
			if ($var2 eq 1) {
				# 0+: RoomGroup
				if (0 <= $var3 && $var3 <= @Groups-1) {
					my $groupID		= $var3-1;
					$destination	= 'to random room in '.nameGroup($groupID);
					#Record reference between task and roomgroup
					push @{ $Groups[$groupID]{TaskReferences} },
						{ id => $task,		type => 'TargetedBy'};
					push @{ $Tasks[$task]{GroupReferences} },
						{ id => $groupID,	type => 'Targeting'};
				}
				#Log warning
				print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3) unhandled roomgroup (v3)\n" unless 0 <= $var3 && $var3 <= @Groups-1;
			}
			# 2: Location of Person
			if ($var2 eq 2) {
				my $target	= "UNKNOWN TARGET $var3";
				# 0: The player
				$target		= 'the player'			if $var3 eq 0;
				# 1: Referenced Person
				$target		= 'referenced person'	if $var3 eq 1;
				# 2+: Person
				if (2 <= $var3 && $var3 <= @Persons + 1) {
					my $personID	= $var3 - 1;
					$target			= namePerson($personID);
					#Record reference between task and person
					push @{ $Persons[$personID]{TaskReferences} },
						{ id => $task,		type => 'TargetedBy'};
					push @{ $Tasks[$task]{PersonReferences} },
						{ id => $personID,	type => 'Targeting'};
				}
				#Assemble and log warning
				$destination	= "to location of $target";
				print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3) unhandled person (v3)\n" unless 0 <= $var3 && $var3 <= @Persons+1;
			}
			# 3: Standing on
			if ($var2 eq 3) {
				# 0+: Object
				if (0 <= $var3 && $var3 <= @ObjectSitStandable) {
					my $objectID	= $ObjectSitStandable[$var3];
					$destination	= 'standing on '.nameObject($objectID);
					#Record reference between task and object
					push @{ $Objects[$objectID]{TaskReferences} },
						{ id => $task,		type => 'TargetedBy'};
					push @{ $Tasks[$task]{ObjectReferences} },
						{ id => $objectID,	type => 'Targeting'};
				}
				#Log warning
				print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3) unhandled object (v3)\n" unless 0 <= $var3 && $var3 <= @ObjectSitStandable;
			}
			# 4: Sitting on
			if ($var2 eq 4) {
				# 0+: Object
				if (0 <= $var3 && $var3 <= @ObjectSitStandable) {
					my $objectID	= $ObjectSitStandable[$var3];
					$destination	= 'sitting on '.nameObject($objectID);
					#Record reference between task and object
					push @{ $Objects[$objectID]{TaskReferences} },
						{ id => $task,		type => 'TargetedBy'};
					push @{ $Tasks[$task]{ObjectReferences} },
						{ id => $objectID,	type => 'Targeting'};
				}
				#Log warning
				print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3) unhandled object (v3)\n" unless 0 <= $var3 && $var3 <= @ObjectSitStandable;
			}
			# 5: Lying on
			if ($var2 eq 5) {
				# 0+: Object
				if (0 <= $var3 && $var3 <= @ObjectLieable) {
					my $objectID	= $ObjectLieable[$var3];
					$destination	= 'lying on '.nameObject($objectID);
					#Record reference between task and object
					push @{ $Objects[$objectID]{TaskReferences} },
						{ id => $task,		type => 'TargetedBy'};
					push @{ $Tasks[$task]{ObjectReferences} },
						{ id => $objectID,	type => 'Targeting'};
				}
				#Log warning
				print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3) unhandled object (v3)\n" unless 0 <= $var3 && $var3 <= @ObjectLieable;
			}			
			#Assemble the full text and log warning
			$text	= "Move $person $destination";
			print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3) unhandled person (v1)\n" unless 0 <= $var1 && $var1 <= @Persons+1;
			print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3) unhandled destination (v2)\n" unless 0 <= $var2 && $var2 <= 5;
		}
		#ObjectState:	ObjectID, State		TODO
		if($type eq 2){
			my $var1	= $action{Var1};
			my $var2	= $action{Var2};
			#ObjectID
			my $object		= "UNKNOWN OBJECT $var1";
			# 0: Referenced
			$object			= 'referenced object'		if $var1 eq 0;
			# 1+: Stateful ObjectID
			if (1 <= $var1 && $var1 <= @ObjectStateful) {
				my $objectID	= $ObjectStateful[$var1];
				$object			= nameObject($objectID);
				#Record reference between task and object
				push @{ $Objects[$objectID]{TaskReferences} },
					{ id => $task,		type => 'AlteredBy'};
				push @{ $Tasks[$task]{ObjectReferences} },
					{ id => $objectID,	type => 'Altering'};
			}
			#State
			my $state		= "UNKNOWN STATE $var2";
			#TODO VERIFY 0=open 1=closed?
			#Assemble the full text and log warnings
			$text	= "Now $object is $state";
			print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2) unhandled object (v1)\n" unless 0 <= $var1 && $var1 <= @ObjectStateful;
			print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2) unhandled state (v2)\n";
		}
		#Variable:		VariableID, Operator, Min
		if($type eq 3){
			my $var1	= $action{Var1};
			my $var2	= $action{Var2};
			my $var3	= $action{Var3};
			my $expr	= $action{Expr};
			my $var5	= $action{Var5};
			#Variable
			my $variable	= "UNKNOWN VARIABLE $var1";
			my $numeric		= 0;
			# 0+: Variable
			if (0 <= $var1 && $var1 <= @Variables-1) {
				my $variableID	= $var1+1;
				$variable		= nameVariable($variableID);
				$numeric		= 1 if $Variables[$variableID]{Type} eq 0;
				#Record reference between task and variable
				push @{ $Variables[$variableID]{TaskReferences} },
					{ id => $task,		type => 'AlteredBy'};
				push @{ $Tasks[$task]{VariableReferences} },
					{ id => $variableID,	type => 'Altering'};
			}
			#Log warning
			print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3:$var5) unhandled variable (v1)\n" unless 0 <= $var1 && $var1 <= @Variables-1;
			#Operator determines value
			my $operator	= "UNKNOWN OPERATOR $var2";
			my $value		= "UNKNOWN VALUE $var3:$var5:$expr";
			#Numeric variable
			if ($numeric) {
				# 0: assign
				if ($var2 eq 0){
					$operator	= 'to';
					$value		= $var3;
				}
				# 1: increase
				if ($var2 eq 1){
					$operator	= 'by';
					$value		= $var3;
				}
				# 2: assign range
				if ($var2 eq 2){
					$operator	= 'to';
					$value		= "between $var3 and $var5";
				}
				# 3: increase range
				if ($var2 eq 3){
					$operator	= 'by';
					$value		= "between $var3 and $var5";
				}
				# 4: Referenced value
				if ($var2 eq 4){
					$operator	= 'to';
					$value		= 'referenced value';
				}
				# 5: to formula
				if ($var2 eq 5){
					$operator	= 'to';
					$value		= $expr;
#TODO: Evalue formula for variable references
				}
				#Log warning
				print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3:$var5) unhandled operator (v2)\n" unless 0 <= $var2 && $var2 <=5;
			}
			#String variable
			else {
				# 0: assign
				if ($var2 eq 0){
					$operator	= 'to';
					$value		= "'$expr'";
				}
				# 1: Referenced value
				if ($var2 eq 1){
					$operator	= 'to';
					$value		= 'referenced value';
				}
				# 2: to formula
				if ($var2 eq 2){
					$operator	= 'to';
					$value		= "'$expr'";
#TODO: Evalue formula for variable references
				}
				#Log warning
				print $File_Log "WARNING\tTask$task\tActionType=$type ($var1:$var2:$var3:$var5) unhandled operator (v2)\n" unless 0 <= $var2 && $var2 <=2;
			}
			$text		= "Change $variable $operator $value";
		}
		#Score:			Modifier
		if($type eq 4){
			my $var1	= $action{Var1};
			$text		= "Modify score by $var1";
		}
		#Task:			Direction, Task
		if($type eq 5){
			my $var1	= $action{Var1};
			my $var2	= $action{Var2};
			#Direction
			my $direction	= "UNKNOWN DIRECTION $var1";
			# 0: Run
			$direction		= 'Run'		if $var1 eq 0;
			# 1: Undo
			$direction		= 'Undo'	if $var1 eq 1;
			#Task
			my $executable	= "UNKNOWN TASK $var2";
			#0+: Task ID
			if (0 <= $var2 && $var2 <= @Tasks - 1) {
				my $taskID	= $var2+1;
				$executable	= nameTask($taskID);
				#Record reference between task and task
				push @{ $Tasks[$taskID]{TaskReferences} },
					{ id => $task,		type => 'ExecutedBy'};
				push @{ $Tasks[$task]{TaskReferences} },
					{ id => $taskID,	type => 'Executing'};
			}
			#Assemble the full text and log warning
			$text		= "$direction $executable";
			print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2) unhandled direction (v1)\n" unless 0 <= $var1 && $var1 <= 1;
			print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2) unhandled task (v2)\n" unless 0 <= $var2 && $var2 <= @Tasks-1;
		}
		#End Game:		Ending
		if($type eq 6){
			my $var1	= $action{Var1};
			my $var2	= $action{Var2};
			#Ending:
			my $ending	= "UNKNOWN ENDING $var1 $var2";
			# 0: Win
			$ending		= 'victory'	if $var1 eq 0;
			# 1: Failure
			$ending		= 'failure'	if $var1 eq 1;
			# 2: Death
			$ending		= 'death'	if $var1 eq 2;
			#Assemble the full text and log warning
			$text		= "End the game in $ending";
			print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2) unhandled ending (v1)\n" unless 0 <= $var1 && $var1 <= 2;
			print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2) unhandled ending (v2)\n";
		}
		#Battle:		TODO
		if($type eq 7){
			my $var1	= $action{Var1};
			my $var2	= $action{Var2};
			my $var3	= $action{Var3};
			#Assemble the full text and log warning
			$text		= "UNKNOWN BATTLE $var1 $var2 $var3";
			print $File_Log "WARNING\tTask$task\tRestrictionType=$type ($var1:$var2:$var3) unhandled battle\n";
		}
		$Tasks[$task]{Actions}[$id]{Text}	= $text if defined $text;
	}
	#TODO Classify task by interpreting task name or commands
}	
sub analyzeEvent($){
	#TODO: Analyze texts for references to variables and ALRs
	#TODO: Add location references
	my $event			= shift;
	{	#Start Condition
		my $type	= $Events[$event]{StarterType};
		my $start		= "UNKNOWN EVENT START $type";
		# 1: Immediate
		if ($type eq 1){
			$start		= 'immediately';
		}
		# 2: Timed
		if ($type eq 2){
			my $lower	= $Events[$event]{StartTime};
			my $upper	= $Events[$event]{EndTime};
			$start		= "after $lower to $upper turns";
			$start		= "after $lower turns"	if $lower eq $upper;
		}
		# 3: Triggered by task
		if ($type eq 3){
			my $taskID	= $Events[$event]{TaskNum};
			my $trigger	= "UNKNOWN TRIGGER $taskID";
			# 0: Any task
			$trigger	= 'any task'	if $taskID eq 0;
			# 1+: Task ID
			if (0 < $taskID && $taskID <= @Tasks) {
				$trigger	= nameTask($taskID);
				#Record reference between event and task
				push @{ $Events[$event]{TaskReferences} }, 
					{ id => $taskID,	type => 'TriggeredBy'};
				push @{ $Tasks[$taskID]{EventReferences} },
					{ id => $event,		type => 'Triggering'};
			}
			#Assemble and log warning
			$start	= "when $trigger is performed";
			print $File_Log "WARNING\tEvent$event\tTaskNum=$taskID unhandled (Start)\n" unless 0 <= $taskID && $taskID <= @Tasks;
		}
		#Store and log warning
		$Events[$event]{Start}	= $start;
		print $File_Log "WARNING\tEvent$event\tStarterType=$type unhandled (Start)\n" unless 1 <= $type && $type <= 3;
	}
	{	#Duration
		my $lower	= $Events[$event]{Time1};
		my $upper	= $Events[$event]{Time2};
		my $duration;
		$duration	= "lasts $lower to $upper turns";
		$duration	= "lasts $lower turns"	if $lower eq $upper;
		#Store
		$Events[$event]{Duration}	= $duration;
	}
	{	#Restart
		my $type	= $Events[$event]{RestartType};
		my $restart	= "UNKNOWN RESTART $type";
		# 0: No restart
		$restart	= 'final'		if $type eq 0;
		# 1: Immediate restart, looping
		$restart	= 'looping'		if $type eq 1;
		# 2: Conditional
		$restart	= 'recurring'	if $type eq 2;
		#Store and log warning
		$Events[$event]{Type}		= $restart;
		print $File_Log "WARNING\tEvent$event\tRestartType=$type unhandled (Restart)\n" unless 0 <= $type && $type <= 2;
	}
	{	#Pause
		my $pause;
		my $taskID		= $Events[$event]{PauseTask};
		my $trigger		= "UNKNOWN PAUSE $taskID";
		# 0: No pause
		last if $taskID eq 0;
		# 1+: Task ID
		if (0 < $taskID && $taskID <= @Tasks) {
			$trigger	= nameTask($taskID);
			#Record reference between event and task
			push @{ $Events[$event]{TaskReferences} }, 
				{ id => $taskID,	type => 'PausedBy'};
			push @{ $Tasks[$taskID]{EventReferences} },
				{ id => $event,		type => 'Pausing'};
		}
		my $condition	= $Events[$event]{PauserCompleted};
		# 0: Task completed
		$pause		= "when $trigger is completed"	if $condition eq 0;
		#Store and log warning
		$Events[$event]{Pause}		= $pause;
		print $File_Log "WARNING\tEvent$event\tPauseTask=$taskID unhandled\n" unless 0 <= $taskID && $taskID <= @Tasks;
		print $File_Log "WARNING\tEvent$event\tPauserCompleted=$condition unhandled\n" unless 0 <= $condition && $condition <= 0;
	}
	{	#Resume
		my $resume;
		my $taskID		= $Events[$event]{ResumeTask};
		my $trigger		= "UNKNOWN PAUSE $taskID";
		# 0: No resume
		last if $taskID eq 0;
		# 1+: Task ID
		if (0 < $taskID && $taskID <= @Tasks) {
			$trigger	= nameTask($taskID);
			#Record reference between event and task
			push @{ $Events[$event]{TaskReferences} }, 
				{ id => $taskID,	type => 'ResumedBy'};
			push @{ $Tasks[$taskID]{EventReferences} },
				{ id => $event,		type => 'Resuming'};
		}
		my $condition	= $Events[$event]{ResumerCompleted};
		# 0: Task completed
		$resume		= "when $trigger is completed"	if $condition eq 0;
		#Store and log warning
		$Events[$event]{Resume}		= $resume;
		print $File_Log "WARNING\tEvent$event\tResumeTask=$taskID unhandled\n" unless 0 <= $taskID && $taskID <= @Tasks;
		print $File_Log "WARNING\tEvent$event\tResumerCompleted=$condition unhandled\n" unless 0 <= $condition && $condition <= 0;
	}
	{	#Midpoints
		my $turn1		= $Events[$event]{PrefTime1};
		my $turn2		= $Events[$event]{PrefTime2};
		#Store
		$Events[$event]{Midpoint1}		= "$turn1 turns before ending"	if $turn1;
		$Events[$event]{Midpoint2}		= "$turn2 turns before ending"	if $turn2;
	}
	{	#Start Effect
		#Object:
		my $objectID		= $Events[$event]{Obj1};
		my $object			= "UNKNOWN OBJECT $objectID";
		# 0: nothing
		last if $objectID eq 0;
		# 1+: Object
		if (0 < $objectID && $objectID <= @Objects){
			$object				= nameObject($objectID);
			#Record reference between event and object
			push @{ $Objects[$objectID]{EventReferences} },
				{ id => $event,		type => 'MovedBy'};
			push @{ $Events[$event]{ObjectReferences} },
				{ id => $objectID,	type => 'Moving'};
		}
		#Destination:
		my $destinationID	= $Events[$event]{Obj1Dest};
		my $destination		= "UNKNOWN DESTINATION $destinationID";
		# 0: Nowhere
		$destination		= 'nowhere'				if $destinationID eq 0;
		# 1: Player
		$destination		= 'the player'			if $destinationID eq 1;
		# 2: Location of player
		$destination		= 'location of player'	if $destinationID eq 2;
		# 3+: Room
		if (2 < $destinationID && $destinationID <= @Rooms+2){
			my $roomID		= $destinationID - 2;
			$destination	= nameRoom($roomID);
			#Record reference between event and Room
			push @{ $Rooms[$roomID]{EventReferences} },
				{ id => $event,		type => 'TargetedBy'};
			push @{ $Events[$event]{RoomReferences} },
				{ id => $roomID,	type => 'Targeting'};
		}
		# X+: RoomGroup
		if (@Rooms+2 < $destinationID && $destinationID <= @Groups+@Rooms+2){
			my $groupID		= $destinationID - @Rooms - 2;
			$destination	= nameGroup($groupID);
			#Record reference between event and Room
			push @{ $Groups[$groupID]{EventReferences} },
				{ id => $event,		type => 'TargetedBy'};
			push @{ $Events[$event]{GroupReferences} },
				{ id => $groupID,	type => 'Targeting'};
		}
		#Store and log warning
		$Events[$event]{StartEffect}		= "move $object to $destination";
		print $File_Log "WARNING\tEvent$event\tObj1=$objectID unhandled\n" unless 0 <= $objectID && $objectID <= @Objects;
		print $File_Log "WARNING\tEvent$event\tObj1Dest=$destinationID unhandled\n" unless 0 <= $destinationID && $destinationID <= @Groups+@Rooms+2;
	}
	{	#End Effect 1
		#Object:
		my $objectID		= $Events[$event]{Obj2};
		my $object			= "UNKNOWN OBJECT $objectID";
		# 0: nothing
		last if $objectID eq 0;
		# 1+: Object
		if (0 < $objectID && $objectID <= @Objects){
			$object				= nameObject($objectID);
			#Record reference between event and object
			push @{ $Objects[$objectID]{EventReferences} },
				{ id => $event,		type => 'MovedBy'};
			push @{ $Events[$event]{ObjectReferences} },
				{ id => $objectID,	type => 'Moving'};
		}
		#Destination:
		my $destinationID	= $Events[$event]{Obj2Dest};
		my $destination		= "UNKNOWN DESTINATION $destinationID";
		# 0: Nowhere
		$destination		= 'nowhere'				if $destinationID eq 0;
		# 1: Player
		$destination		= 'the player'			if $destinationID eq 1;
		# 2: Location of player
		$destination		= 'location of player'	if $destinationID eq 2;
		# 3+: Room
		if (2 < $destinationID && $destinationID <= @Rooms+2){
			my $roomID		= $destinationID - 2;
			$destination	= nameRoom($roomID);
			#Record reference between event and Room
			push @{ $Rooms[$roomID]{EventReferences} },
				{ id => $event,		type => 'TargetedBy'};
			push @{ $Events[$event]{RoomReferences} },
				{ id => $roomID,	type => 'Targeting'};
		}
		# X+: RoomGroup
		if (@Rooms+2 < $destinationID && $destinationID <= @Groups+@Rooms+2){
			my $groupID		= $destinationID - @Rooms - 2;
			$destination	= nameGroup($groupID);
			#Record reference between event and Room
			push @{ $Groups[$groupID]{EventReferences} },
				{ id => $event,		type => 'TargetedBy'};
			push @{ $Events[$event]{GroupReferences} },
				{ id => $groupID,	type => 'Targeting'};
		}
		#Store and log warning
		$Events[$event]{EndEffect1}		= "move $object to $destination";
		print $File_Log "WARNING\tEvent$event\tObj2=$objectID unhandled\n" unless 0 <= $objectID && $objectID <= @Objects;
		print $File_Log "WARNING\tEvent$event\tObj2Dest=$destinationID unhandled\n" unless 0 <= $destinationID && $destinationID <= @Groups+@Rooms+2;
	}
	{	#End Effect 2
		#Object:
		my $objectID		= $Events[$event]{Obj3};
		my $object			= "UNKNOWN OBJECT $objectID";
		# 0: nothing
		last if $objectID eq 0;
		# 1+: Object
		if (0 < $objectID && $objectID <= @Objects){
			$object				= nameObject($objectID);
			#Record reference between event and object
			push @{ $Objects[$objectID]{EventReferences} },
				{ id => $event,		type => 'MovedBy'};
			push @{ $Events[$event]{ObjectReferences} },
				{ id => $objectID,	type => 'Moving'};
		}
		#Destination:
		my $destinationID	= $Events[$event]{Obj3Dest};
		my $destination		= "UNKNOWN DESTINATION $destinationID";
		# 0: Nowhere
		$destination		= 'nowhere'				if $destinationID eq 0;
		# 1: Player
		$destination		= 'the player'			if $destinationID eq 1;
		# 2: Location of player
		$destination		= 'location of player'	if $destinationID eq 2;
		# 3+: Room
		if (2 < $destinationID && $destinationID <= @Rooms+2){
			my $roomID		= $destinationID - 2;
			$destination	= nameRoom($roomID);
			#Record reference between event and Room
			push @{ $Rooms[$roomID]{EventReferences} },
				{ id => $event,		type => 'TargetedBy'};
			push @{ $Events[$event]{RoomReferences} },
				{ id => $roomID,	type => 'Targeting'};
		}
		# X+: RoomGroup
		if (@Rooms+2 < $destinationID && $destinationID <= @Groups+@Rooms+2){
			my $groupID		= $destinationID - @Rooms - 2;
			$destination	= nameGroup($groupID);
			#Record reference between event and Room
			push @{ $Groups[$groupID]{EventReferences} },
				{ id => $event,		type => 'TargetedBy'};
			push @{ $Events[$event]{GroupReferences} },
				{ id => $groupID,	type => 'Targeting'};
		}
		#Store and log warning
		$Events[$event]{EndEffect1}		= "move $object to $destination";
		print $File_Log "WARNING\tEvent$event\tObj3=$objectID unhandled\n" unless 0 <= $objectID && $objectID <= @Objects;
		print $File_Log "WARNING\tEvent$event\tObj3Dest=$destinationID unhandled\n" unless 0 <= $destinationID && $destinationID <= @Groups+@Rooms+2;
	}
	{	#End Execute
		my $taskID	= $Events[$event]{TaskAffected};
		my $execute	= "UNKNOWN EXECUTE $taskID";
		# 0: No task
		last if $taskID eq 0;
		# 1+: Task ID
		if (0 < $taskID && $taskID <= @Tasks) {
			$execute	= nameTask($taskID);
			#Record reference between event and task
			push @{ $Events[$event]{TaskReferences} }, 
				{ id => $taskID,	type => 'Triggering'};
			push @{ $Tasks[$taskID]{EventReferences} },
				{ id => $event,		type => 'TriggeredBy'};
		}
		#Store and log warning
		$Events[$event]{EndExecute}	= $execute;
		print $File_Log "WARNING\tEvent$event\tTaskAffected=$taskID unhandled\n" unless 0 <= $taskID && $taskID <= @Tasks;
	}
}
##Generate output
sub generate(){
	generateXML();
#TODO	generateInform();	
}
#Generate XML Output
sub generateXML(){
	print $File_Log "Generating XML File\n";
	print $File_XML "<!-- Decompiled by $Decompiler_Version at ".localtime." -->";
	writeXMLElementOpen('Story');
	generateXMLHeader();
	generateXMLRooms();
	generateXMLObjects();
	generateXMLTasks();
	generateXMLEvents();
	#generateXMLGroup();
	generateXMLPersons();
	generateXMLVariables();
	writeXMLElementClose('Story');
}
sub generateXMLHeader(){
	writeXMLElementOpen('Header');
	writeXMLElement('Title',			$Story{Title});
	writeXMLElement('Author',			$Story{Author});
	writeXMLElement('Compiled',			$Story{CompileDate});
	writeXMLElement('StartLocation',	$Story{Start});
	writeXMLElement('WaitingTurns',		$Story{WaitTurns});
	writeXMLElement('Perspective',		$Story{Perspective});
	{	#Options
		writeXMLElementOpen('Options');
		writeXMLElement('Battles')			if $Story{EnableBattle};
		writeXMLElement('NoMap')			if $Story{DisableMap};
		writeXMLElement('Sound')			if $Story{EnableSound};
		writeXMLElement('Graphics')			if $Story{EnableGraphics};
		writeXMLElement('ExpandedCompass')	if $Story{ExpandedCompass};
		writeXMLElement('InitialLook')		if $Story{InitialLook};
		writeXMLElement('ShowExits')		if $Story{ShowExits};
		writeXMLElementClose('Options');
	}
	writeXMLElementClose('Header');
}
sub generateXMLRooms(){
	print $File_XML "\n<!-- $#Rooms rooms -->";
	writeXMLElementOpen('Rooms')	if $#Rooms;
	for my $room (1 .. $#Rooms){
		writeXMLElementOpen('Room');
		if ($Option_Verbose){	#Verbose ID and name
			print $File_XML "\t<!-- $room";
			print $File_XML " ($Symbol_Room[$room])"	if defined $Symbol_Room[$room];
			print $File_XML " -->";
		}
		{	#Properties
			writeXMLElementOpen('Properties');
			writeXMLElement('ID', 			$room);
			writeXMLElement('SymbolicName', nameRoom($room));
			writeXMLElement('PrintedName', 	$Rooms[$room]{Short});
			writeXMLElement('Hidden')		if $Rooms[$room]{Hidden};
			writeXMLElementClose('Properties');
		}
		{	#Descriptions	TODO Resources
			writeXMLElementOpen('Descriptions');
			#Default
			writeXMLElementOpen('Description');
			writeXMLElement('Text',	$Rooms[$room]{Description});
			writeXMLElementClose('Description');
			#v3 style alternate descriptions
			if($Rooms[$room]{AltDesc1Task}){
				writeXMLElementOpen('Description');
				writeXMLElement('Text',		$Rooms[$room]{AltDesc1});
				writeXMLElement('TaskID',	$Rooms[$room]{AltDesc1Task});
				writeXMLElement('Task',		nameTask($Rooms[$room]{AltDesc1Task}));
				writeXMLElementClose('Description');
			}
			if($Rooms[$room]{AltDesc2Task}){
				writeXMLElementOpen('Description');
				writeXMLElement('Text',		$Rooms[$room]{AltDesc2});
				writeXMLElement('TaskID',	$Rooms[$room]{AltDesc2Task});
				writeXMLElement('Task',		nameTask($Rooms[$room]{AltDesc2Task}));
				writeXMLElementClose('Description');
			}
			if($Rooms[$room]{AltDesc3Obj}){
				writeXMLElementOpen('Description');
				writeXMLElement('Text',		$Rooms[$room]{AltDesc3});
				writeXMLElement('ObjectID',	$Rooms[$room]{AltDesc3Obj});
				writeXMLElement('Object',	nameObject( $ObjectPortable[ $Rooms[$room]{AltDesc3Obj}] ) );
				writeXMLElementClose('Description');
			}
			#v4 style alternate descriptions
			my @alternates	= ();
			@alternates		= @{ $Rooms[$room]{Alternates} } if defined $Rooms[$room]{Alternates};
			foreach my $alternate (0..$#alternates){
				writeXMLElementOpen('Description');
				writeXMLElement('M1',			$alternates[$alternate]{M1});
				writeXMLElement('Type',			$alternates[$alternate]{Type});
				writeXMLElement('M2',			$alternates[$alternate]{M2});
				writeXMLElement('Var2',			$alternates[$alternate]{Var2});
				writeXMLElement('HideObjects',	$alternates[$alternate]{HideObjects});
				writeXMLElement('Changed',		$alternates[$alternate]{Changed});
				writeXMLElement('Var3',			$alternates[$alternate]{Var3});
				writeXMLElement('DisplayRoom',	$alternates[$alternate]{DisplayRoom});
				writeXMLElementClose('Description');
			}
			writeXMLElementClose('Descriptions');
		}
		{	#Exits
			writeXMLElementOpen('Exits');
			foreach my $direction (0..$Story{Directions}-1){
				my $destination	= $Rooms[$room]{Exits}[$direction]{Destination};
				if ($destination){
					writeXMLElementOpen('Exit');
					writeXMLElement('Direction',		$Symbol_Compass_Direction[$direction]);
					writeXMLElement('DestinationID',	$destination);
					writeXMLElement('Destination',		nameRoom($destination));
					writeXMLElement('Restriction',		$Rooms[$room]{Exits}[$direction]{Restriction}) if defined $Rooms[$room]{Exits}[$direction]{Restriction};
					writeXMLElementClose('Exit');
				}
			}
			writeXMLElementClose('Exits');
		}
		{	#Relations
			my @rooms		= @{ $Rooms[$room]{RoomReferences} };
			my @objects		= @{ $Rooms[$room]{ObjectReferences} };
			my @tasks		= @{ $Rooms[$room]{TaskReferences} };
			my @events		= @{ $Rooms[$room]{EventReferences} };
			my @persons		= @{ $Rooms[$room]{PersonReferences} };
			my @groups		= @{ $Rooms[$room]{GroupReferences} };
			my @synonyms	= @{ $Rooms[$room]{SynonymReferences} };
			my @variables	= @{ $Rooms[$room]{VariableReferences} };
			my @alrs		= @{ $Rooms[$room]{ALRReferences} };
			my $relations	= @rooms + @objects + @tasks + @events + @persons + @groups + @synonyms + @variables + @alrs;
			writeXMLElementOpen('Relations')	if $relations;
			{	#Rooms
				writeXMLElementOpen('Rooms')	if @rooms;
				for my $i (0..$#rooms){
					my $type	= $rooms[$i]{type};
					my $id		= $rooms[$i]{id};
					writeXMLElement($type, "Room$id (".nameRoom($id).")");
				}
				writeXMLElementClose('Rooms')	if @rooms;
			}
			{	#Objects
				writeXMLElementOpen('Objects')	if @objects;
				for my $i (0..$#objects){
					my $type	= $objects[$i]{type};
					my $id		= $objects[$i]{id};
					writeXMLElement($type, "Object$id (".nameObject($id).")");
				}
				writeXMLElementClose('Objects')	if @objects;
			}
			{	#Tasks
				writeXMLElementOpen('Tasks')	if @tasks;
				for my $i (0..$#tasks){
					my $type	= $tasks[$i]{type};
					my $id		= $tasks[$i]{id};
					writeXMLElement($type, "Task$id (".nameTask($id).")");
				}
				writeXMLElementClose('Tasks')	if @tasks;
			}
			{	#Events
				writeXMLElementOpen('Events')	if @events;
				for my $i (0..$#events){
					my $type	= $events[$i]{type};
					my $id		= $events[$i]{id};
					writeXMLElement($type, "Event$id (".nameEvent($id).")");
				}
				writeXMLElementClose('Events')	if @events;
			}
			{	#Persons
				writeXMLElementOpen('Persons')	if @persons;
				for my $i (0..$#persons){
					my $type	= $persons[$i]{type};
					my $id		= $persons[$i]{id};
					writeXMLElement($type, "Person$id (".namePerson($id).")");
				}
				writeXMLElementClose('Persons')	if @persons;
			}
			{	#Groups
				writeXMLElementOpen('Groups')	if @groups;
				for my $i (0..$#groups){
					my $type	= $groups[$i]{type};
					my $id		= $groups[$i]{id};
					writeXMLElement($type, "Group$id (".nameGroup($id).")");
				}
				writeXMLElementClose('Groups')	if @groups;
			}
			{	#Synonyms
				writeXMLElementOpen('Synonyms')		if @synonyms;
				for my $i (0..$#synonyms){
					my $type	= $synonyms[$i]{type};
					my $id		= $synonyms[$i]{id};
					writeXMLElement($type, "Synonym$id (".nameSynonym($id).")");
				}
				writeXMLElementClose('Synonyms')	if @synonyms;
			}
			{	#Variables
				writeXMLElementOpen('Variables')	if @variables;
				for my $i (0..$#variables){
					my $type	= $variables[$i]{type};
					my $id		= $variables[$i]{id};
					writeXMLElement($type, "Variable$id (".nameVariable($id).")");
				}
				writeXMLElementClose('Variables')	if @variables;
			}
			{	#ALRs
				writeXMLElementOpen('ALRs')		if @alrs;
				for my $i (0..$#alrs){
					my $type	= $alrs[$i]{type};
					my $id		= $alrs[$i]{id};
					writeXMLElement($type, "ALR$id (".nameALR($id).")");
				}
				writeXMLElementClose('ALRs')	if @alrs;
			}
			writeXMLElementClose('Relations')	if $relations;
		}
		writeXMLElementClose('Room');
	}
	writeXMLElementClose('Rooms')	if $#Rooms;
}
sub generateXMLObjects(){
	print $File_XML "\n<!-- $#Objects objects -->";
	writeXMLElementOpen('Objects') if $#Objects;
	for my $object (1 .. $#Objects){
		writeXMLElementOpen('Object');
		if ($Option_Verbose){	#Verbose ID and name
			print $File_XML "\t<!-- $object";
			print $File_XML " ($Symbol_Object[$object])"	if defined $Symbol_Object[$object];
			print $File_XML " -->";
		}
		{	#Properties
			writeXMLElementOpen('Properties');
			writeXMLElement('ID',			$object);
			writeXMLElement('SymbolicName',	nameObject($object));
			writeXMLElement('ShortName',	$Objects[$object]{Short});
			writeXMLElement('Prefix',		$Objects[$object]{Prefix});
			foreach my $alias ( @{$Objects[$object]{Alias} } ){
				writeXMLElement('Alias',	$alias) unless $alias eq '';
			}
			writeXMLElement('Class',		$Objects[$object]{Class})		if defined $Objects[$object]{Class};
			writeXMLElementClose('Properties');
		}
		{	#Attributes
			writeXMLElementOpen('Attributes');
			writeXMLElement('Static')		if $Objects[$object]{Static};
			writeXMLElement('Portable')		unless $Objects[$object]{Static};
			writeXMLElement('Container')	if $Objects[$object]{Container};
			writeXMLElement('Surface')		if $Objects[$object]{Surface};
			writeXMLElement('Wearable')		if $Objects[$object]{Wearable};
			writeXMLElement('SitStandable')	if $Objects[$object]{SitStandable};
			writeXMLElement('Lieable')		if $Objects[$object]{Lieable};
			writeXMLElement('Weapon')		if $Objects[$object]{Weapon};
			writeXMLElement('Edible')		if $Objects[$object]{Edible};
			writeXMLElement('Readable')		if $Objects[$object]{Readable};
			writeXMLElement('ReadText',		$Objects[$object]{ReadText})	if defined $Objects[$object]{ReadText};
			writeXMLElement('InitialPosition',	$Objects[$object]{InitialPosition});	#VERIFY
			writeXMLElement('Capacity',		$Objects[$object]{Capacity});
			writeXMLElement('SizeWeight',	$Objects[$object]{SizeWeight});
			writeXMLElement('Openable',		$Objects[$object]{Openable});	#TODO: Translate
			writeXMLElement('KeyID',		$Objects[$object]{Key})			if defined $Objects[$object]{Key};
			writeXMLElement('InRoomDesc',	$Objects[$object]{InRoomDesc})	unless $Objects[$object]{InRoomDesc} eq '';
			writeXMLElement('OnlyWhenNotMoved')		if $Objects[$object]{OnlyWhenNotMoved};
#TODO: Resources, BattleStats
#TODO: CurrentState, States, StateListed, ListFlag
			writeXMLElementClose('Attributes');
		}
		{	#Location
			writeXMLElementOpen('Location');
			#0: No Rooms
			writeXMLElement('Nowhere')	if $Objects[$object]{WhereType} eq 0;
			#1-2: Specific Rooms
			if( $Objects[$object]{WhereType} eq 1 or $Objects[$object]{WhereType} eq 2){
				my @rooms = @{ $Objects[$object]{Where} };
				foreach my $room (@rooms){ writeXMLElement('Room', nameRoom($room)) }
			}
			#3: All Rooms
			writeXMLElement('Everywhere') if $Objects[$object]{WhereType} eq 3;
			#4: Bodypart
			writeXMLElement('Person', namePerson( $Objects[$object]{Parent} )) if $Objects[$object]{WhereType} eq 4;
			#9: Portable
			if($Objects[$object]{WhereType} eq 9){
				if ($Objects[$object]{Parent} eq '-1') {
					writeXMLElement('Nowhere');
				}
				else{
					writeXMLElement('Holder', nameObject( $ObjectHolder[ $Objects[$object]{Parent} ]));
				}
			}
			writeXMLElementClose('Location');
		}
		{	#Descriptions
			writeXMLElementOpen('Descriptions');
			writeXMLElementOpen('Description');
			writeXMLElement('Text',	$Objects[$object]{Description});
			writeXMLElementClose('Description');
			if($Objects[$object]{AltDescTask}){
				writeXMLElementOpen('Description');
				writeXMLElement('Text',	$Objects[$object]{AltDesc});
				writeXMLElement('Type',	$Objects[$object]{AltDescType});
				writeXMLElement('Task',	$Objects[$object]{AltDescTask});
				writeXMLElement('Name',	nameTask($Objects[$object]{AltDescTask}));
				writeXMLElementClose('Description');
			}
			writeXMLElementClose('Descriptions');
		}
		{	#Relations
			my @rooms		= @{ $Objects[$object]{RoomReferences} };
			my @objects		= @{ $Objects[$object]{ObjectReferences} };
			my @tasks		= @{ $Objects[$object]{TaskReferences} };
			my @events		= @{ $Objects[$object]{EventReferences} };
			my @persons		= @{ $Objects[$object]{PersonReferences} };
			my @groups		= @{ $Objects[$object]{GroupReferences} };
			my @synonyms	= @{ $Objects[$object]{SynonymReferences} };
			my @variables	= @{ $Objects[$object]{VariableReferences} };
			my @alrs		= @{ $Objects[$object]{ALRReferences} };
			my $relations	= @rooms + @objects + @tasks + @events + @persons + @groups + @synonyms + @variables + @alrs;
			writeXMLElementOpen('Relations')	if $relations;
			{	#Rooms
				writeXMLElementOpen('Rooms')	if @rooms;
				for my $i (0..$#rooms){
					my $type	= $rooms[$i]{type};
					my $id		= $rooms[$i]{id};
					writeXMLElement($type, "Room$id (".nameRoom($id).")");
				}
				writeXMLElementClose('Rooms')	if @rooms;
			}
			{	#Objects
				writeXMLElementOpen('Objects')	if @objects;
				for my $i (0..$#objects){
					my $type	= $objects[$i]{type};
					my $id		= $objects[$i]{id};
					writeXMLElement($type, "Object$id (".nameObject($id).")");
				}
				writeXMLElementClose('Objects')	if @objects;
			}
			{	#Tasks
				writeXMLElementOpen('Tasks')	if @tasks;
				for my $i (0..$#tasks){
					my $type	= $tasks[$i]{type};
					my $id		= $tasks[$i]{id};
					writeXMLElement($type, "Task$id (".nameTask($id).")");
				}
				writeXMLElementClose('Tasks')	if @tasks;
			}
			{	#Events
				writeXMLElementOpen('Events')	if @events;
				for my $i (0..$#events){
					my $type	= $events[$i]{type};
					my $id		= $events[$i]{id};
					writeXMLElement($type, "Event$id (".nameEvent($id).")");
				}
				writeXMLElementClose('Events')	if @events;
			}
			{	#Persons
				writeXMLElementOpen('Persons')	if @persons;
				for my $i (0..$#persons){
					my $type	= $persons[$i]{type};
					my $id		= $persons[$i]{id};
					writeXMLElement($type, "Person$id (".namePerson($id).")");
				}
				writeXMLElementClose('Persons')	if @persons;
			}
			{	#Groups
				writeXMLElementOpen('Groups')	if @groups;
				for my $i (0..$#groups){
					my $type	= $groups[$i]{type};
					my $id		= $groups[$i]{id};
					writeXMLElement($type, "Group$id (".nameGroup($id).")");
				}
				writeXMLElementClose('Groups')	if @groups;
			}
			{	#Synonyms
				writeXMLElementOpen('Synonyms')		if @synonyms;
				for my $i (0..$#synonyms){
					my $type	= $synonyms[$i]{type};
					my $id		= $synonyms[$i]{id};
					writeXMLElement($type, "Synonym$id (".nameSynonym($id).")");
				}
				writeXMLElementClose('Synonyms')	if @synonyms;
			}
			{	#Variables
				writeXMLElementOpen('Variables')	if @variables;
				for my $i (0..$#variables){
					my $type	= $variables[$i]{type};
					my $id		= $variables[$i]{id};
					writeXMLElement($type, "Variable$id (".nameVariable($id).")");
				}
				writeXMLElementClose('Variables')	if @variables;
			}
			{	#ALRs
				writeXMLElementOpen('ALRs')		if @alrs;
				for my $i (0..$#alrs){
					my $type	= $alrs[$i]{type};
					my $id		= $alrs[$i]{id};
					writeXMLElement($type, "ALR$id (".nameALR($id).")");
				}
				writeXMLElementClose('ALRs')	if @alrs;
			}
			writeXMLElementClose('Relations')	if $relations;
		}
		writeXMLElementClose('Object');
	}
	writeXMLElementClose('Objects') if $#Objects;
}
sub generateXMLTasks(){
	print $File_XML "\n<!-- $#Tasks tasks -->";
	writeXMLElementOpen('Tasks') if $#Tasks;
	for my $task (1 .. $#Tasks){
		writeXMLElementOpen('Task');
		if ($Option_Verbose){	#Verbose ID and name
			print $File_XML "\t<!-- $task";
			print $File_XML " ($Symbol_Task[$task])"	if defined $Symbol_Task[$task];
			print $File_XML " -->";
		}
		{	#Properties
			writeXMLElementOpen('Properties');
			writeXMLElement('ID',			$task);
			writeXMLElement('SymbolicName',	nameTask($task));
			writeXMLElement('Class',		$Tasks[$task]{Class})		if defined $Tasks[$task]{Class};
			writeXMLElement('Repeatable')	if $Tasks[$task]{Repeatable};
			writeXMLElement('Reversible')	if $Tasks[$task]{Reversible};
			writeXMLElement('ShowRoomDesc',	nameRoom($Tasks[$task]{ShowRoomDesc})) unless $Tasks[$task]{ShowRoomDesc} eq 0;
			writeXMLElementClose('Properties');
		}
		{	#Commands
			my @commands = @{ $Tasks[$task]{Commands} };
			my @commandsReverse = @{ $Tasks[$task]{CommandsReverse} };
			writeXMLElementOpen('Commands');
			foreach my $command (@commands) { writeXMLElement('Command', $command) }
			foreach my $command (@commandsReverse) { writeXMLElement('Reverse', $command) }
			writeXMLElementClose('Commands');
		}
		{	#Messages
			writeXMLElementOpen('Messages');
			writeXMLElement('CompleteText',	$Tasks[$task]{CompleteText})	unless $Tasks[$task]{CompleteText} eq '';
			writeXMLElement('RepeatText',	$Tasks[$task]{RepeatText})		unless $Tasks[$task]{RepeatText} eq '';
			writeXMLElement('ReverseText',	$Tasks[$task]{ReverseText})		unless $Tasks[$task]{ReverseText} eq '';
			writeXMLElement('ExtraText',	$Tasks[$task]{AdditionalText})	unless $Tasks[$task]{AdditionalText} eq '';
			writeXMLElementClose('Messages');
		}
		{	#Location
			writeXMLElementOpen('Location');
			#0: No Rooms
			writeXMLElement('Nowhere')	if $Tasks[$task]{WhereType} eq 0;
			#1-2: Specific Roomlist
			if( $Tasks[$task]{WhereType} eq 1 or $Tasks[$task]{WhereType} eq 2){
				my @rooms = @{ $Tasks[$task]{Where} };
				foreach my $room (@rooms){ writeXMLElement('Room', nameRoom($room)) }
			}
			#3: All Rooms
			writeXMLElement('Everywhere')	if $Tasks[$task]{WhereType} eq 3;
			writeXMLElementClose('Location');
		}
		{	#Help
			unless ($Tasks[$task]{Question} eq ''){
				writeXMLElementOpen('Help');
				writeXMLElement('Question',		$Tasks[$task]{Question});
				writeXMLElement('Hint1',		$Tasks[$task]{Hint1});
				writeXMLElement('Hint2',		$Tasks[$task]{Hint2});
				writeXMLElementClose('Help');
			}
		}
		{	#Restrictions
			my @restrictions = @{ $Tasks[$task]{Restrictions} };
			unless ($#restrictions eq -1){
				writeXMLElementOpen('Restrictions');
				foreach my $reference (@restrictions) {
					my %restriction = %{ $reference };
					writeXMLElementOpen('Restriction');
					writeXMLElement('Condition',	$restriction{Condition})if defined $restriction{Condition};
					writeXMLElement('FailureText',	$restriction{FailureText});
					writeXMLElementClose('Restriction');
				}
				writeXMLElementClose('Restrictions');
			}
		}
		{	#Actions
			my @actions = @{ $Tasks[$task]{Actions} };
			if (@actions){
				writeXMLElementOpen('Actions');
				foreach my $reference (@actions) {
					my %action = %{ $reference };
					writeXMLElement('Action',	$action{Text});
				}
				writeXMLElementClose('Actions');
			}
		}
		{	#Relations
			my @rooms		= @{ $Tasks[$task]{RoomReferences} };
			my @objects		= @{ $Tasks[$task]{ObjectReferences} };
			my @tasks		= @{ $Tasks[$task]{TaskReferences} };
			my @events		= @{ $Tasks[$task]{EventReferences} };
			my @persons		= @{ $Tasks[$task]{PersonReferences} };
			my @groups		= @{ $Tasks[$task]{GroupReferences} };
			my @synonyms	= @{ $Tasks[$task]{SynonymReferences} };
			my @variables	= @{ $Tasks[$task]{VariableReferences} };
			my @alrs		= @{ $Tasks[$task]{ALRReferences} };
			my $relations	= @rooms + @objects + @tasks + @events + @persons + @groups + @synonyms + @variables + @alrs;
			writeXMLElementOpen('Relations')	if $relations;
			{	#Rooms
				writeXMLElementOpen('Rooms')	if @rooms;
				for my $i (0..$#rooms){
					my $type	= $rooms[$i]{type};
					my $id		= $rooms[$i]{id};
					writeXMLElement($type, "Room$id (".nameRoom($id).")");
				}
				writeXMLElementClose('Rooms')	if @rooms;
			}
			{	#Objects
				writeXMLElementOpen('Objects')	if @objects;
				for my $i (0..$#objects){
					my $type	= $objects[$i]{type};
					my $id		= $objects[$i]{id};
					writeXMLElement($type, "Object$id (".nameObject($id).")");
				}
				writeXMLElementClose('Objects')	if @objects;
			}
			{	#Tasks
				writeXMLElementOpen('Tasks')	if @tasks;
				for my $i (0..$#tasks){
					my $type	= $tasks[$i]{type};
					my $id		= $tasks[$i]{id};
					writeXMLElement($type, "Task$id (".nameTask($id).")");
				}
				writeXMLElementClose('Tasks')	if @tasks;
			}
			{	#Events
				writeXMLElementOpen('Events')	if @events;
				for my $i (0..$#events){
					my $type	= $events[$i]{type};
					my $id		= $events[$i]{id};
					writeXMLElement($type, "Event$id (".nameEvent($id).")");
				}
				writeXMLElementClose('Events')	if @events;
			}
			{	#Persons
				writeXMLElementOpen('Persons')	if @persons;
				for my $i (0..$#persons){
					my $type	= $persons[$i]{type};
					my $id		= $persons[$i]{id};
					writeXMLElement($type, "Person$id (".namePerson($id).")");
				}
				writeXMLElementClose('Persons')	if @persons;
			}
			{	#Groups
				writeXMLElementOpen('Groups')	if @groups;
				for my $i (0..$#groups){
					my $type	= $groups[$i]{type};
					my $id		= $groups[$i]{id};
					writeXMLElement($type, "Group$id (".nameGroup($id).")");
				}
				writeXMLElementClose('Groups')	if @groups;
			}
			{	#Synonyms
				writeXMLElementOpen('Synonyms')		if @synonyms;
				for my $i (0..$#synonyms){
					my $type	= $synonyms[$i]{type};
					my $id		= $synonyms[$i]{id};
					writeXMLElement($type, "Synonym$id (".nameSynonym($id).")");
				}
				writeXMLElementClose('Synonyms')	if @synonyms;
			}
			{	#Variables
				writeXMLElementOpen('Variables')	if @variables;
				for my $i (0..$#variables){
					my $type	= $variables[$i]{type};
					my $id		= $variables[$i]{id};
					writeXMLElement($type, "Variable$id (".nameVariable($id).")");
				}
				writeXMLElementClose('Variables')	if @variables;
			}
			{	#ALRs
				writeXMLElementOpen('ALRs')		if @alrs;
				for my $i (0..$#alrs){
					my $type	= $alrs[$i]{type};
					my $id		= $alrs[$i]{id};
					writeXMLElement($type, "ALR$id (".nameALR($id).")");
				}
				writeXMLElementClose('ALRs')	if @alrs;
			}
			writeXMLElementClose('Relations')	if $relations;
		}
		writeXMLElementClose('Task');
	}
	writeXMLElementClose('Tasks') if $#Tasks;
}
sub generateXMLEvents(){
	print $File_XML "\n<!-- $#Events events -->";
	writeXMLElementOpen('Events') if $#Events;
	for my $event (1 .. $#Events){
		writeXMLElementOpen('Event');
		if ($Option_Verbose){	#Verbose ID and name
			print $File_XML "\t<!-- $event";
			print $File_XML " ($Symbol_Event[$event])"	if defined $Symbol_Event[$event];
			print $File_XML " -->";
		}
		{	#Properties
			writeXMLElementOpen('Properties');
			writeXMLElement('ID',			$event);
			writeXMLElement('SymbolicName',	nameEvent($event));
			writeXMLElement('ShortName',	$Events[$event]{Short});
			writeXMLElement('Type',			$Events[$event]{Type});
			writeXMLElementClose('Properties');
		}
		{	#Starting
			writeXMLElementOpen('Starting');
			writeXMLElement('Condition',	$Events[$event]{Start});
			writeXMLElement('Description',	$Events[$event]{StartText})		unless $Events[$event]{StartText} eq '';
			writeXMLElement('Effect',		$Events[$event]{StartEffect})	if defined $Events[$event]{StartEffect};
			writeXMLElementClose('Starting');
		}
		{	#During
			writeXMLElementOpen('During');
			writeXMLElement('Description',	$Events[$event]{LookText})	unless $Events[$event]{LookText} eq '';
			writeXMLElement('Pause',		$Events[$event]{Pause})		if defined $Events[$event]{Pause};
			writeXMLElement('Resume',		$Events[$event]{Resume})	if defined $Events[$event]{Resume};
			writeXMLElement('Midpoint1',	$Events[$event]{Midpoint1})	if $Events[$event]{PrefTime1};
			writeXMLElement('Message1',		$Events[$event]{PrefText1})	if $Events[$event]{PrefTime1};
			writeXMLElement('Midpoint2',	$Events[$event]{Midpoint2})	if $Events[$event]{PrefTime2};
			writeXMLElement('Message2',		$Events[$event]{PrefText2})	if $Events[$event]{PrefTime2};
			writeXMLElementClose('During');
		}
		{	#Ending
			writeXMLElementOpen('Ending');
			writeXMLElement('Duration',		$Events[$event]{Duration});
			writeXMLElement('Description',	$Events[$event]{FinishText})	if defined $Events[$event]{FinishText};
			writeXMLElement('Effect',		$Events[$event]{EndEffect1})	if defined $Events[$event]{EndEffect1};
			writeXMLElement('Effect',		$Events[$event]{EndEffect2})	if defined $Events[$event]{EndEffect2};
			writeXMLElement('Execute',		$Events[$event]{EndExecute})	if defined $Events[$event]{EndExecute};
			writeXMLElementClose('Ending');
		}
		{	#Location
			writeXMLElementOpen('Location');
			#0: No Rooms
			writeXMLElement('Nowhere')	if $Events[$event]{WhereType} eq 0;
			#1-2: Specific Roomlist
			if( $Events[$event]{WhereType} eq 1 or $Events[$event]{WhereType} eq 2){
				my @rooms = @{ $Events[$event]{Where} };
				foreach my $room (@rooms){ writeXMLElement('Room', nameRoom($room)) }
			}
			#3: All Rooms
			writeXMLElement('Everywhere')	if $Events[$event]{WhereType} eq 3;
			writeXMLElementClose('Location');
		}
			#Resources	TODO
		{	#Relations
			my @rooms		= @{ $Events[$event]{RoomReferences} };
			my @objects		= @{ $Events[$event]{ObjectReferences} };
			my @tasks		= @{ $Events[$event]{TaskReferences} };
			my @events		= @{ $Events[$event]{EventReferences} };
			my @persons		= @{ $Events[$event]{PersonReferences} };
			my @groups		= @{ $Events[$event]{GroupReferences} };
			my @synonyms	= @{ $Events[$event]{SynonymReferences} };
			my @variables	= @{ $Events[$event]{VariableReferences} };
			my @alrs		= @{ $Events[$event]{ALRReferences} };
			my $relations	= @rooms + @objects + @tasks + @events + @persons + @groups + @synonyms + @variables + @alrs;
			writeXMLElementOpen('Relations')	if $relations;
			{	#Rooms
				writeXMLElementOpen('Rooms')	if @rooms;
				for my $i (0..$#rooms){
					my $type	= $rooms[$i]{type};
					my $id		= $rooms[$i]{id};
					writeXMLElement($type, "Room$id (".nameRoom($id).")");
				}
				writeXMLElementClose('Rooms')	if @rooms;
			}
			{	#Objects
				writeXMLElementOpen('Objects')	if @objects;
				for my $i (0..$#objects){
					my $type	= $objects[$i]{type};
					my $id		= $objects[$i]{id};
					writeXMLElement($type, "Object$id (".nameObject($id).")");
				}
				writeXMLElementClose('Objects')	if @objects;
			}
			{	#Tasks
				writeXMLElementOpen('Tasks')	if @tasks;
				for my $i (0..$#tasks){
					my $type	= $tasks[$i]{type};
					my $id		= $tasks[$i]{id};
					writeXMLElement($type, "Task$id (".nameTask($id).")");
				}
				writeXMLElementClose('Tasks')	if @tasks;
			}
			{	#Events
				writeXMLElementOpen('Events')	if @events;
				for my $i (0..$#events){
					my $type	= $events[$i]{type};
					my $id		= $events[$i]{id};
					writeXMLElement($type, "Event$id (".nameEvent($id).")");
				}
				writeXMLElementClose('Events')	if @events;
			}
			{	#Persons
				writeXMLElementOpen('Persons')	if @persons;
				for my $i (0..$#persons){
					my $type	= $persons[$i]{type};
					my $id		= $persons[$i]{id};
					writeXMLElement($type, "Person$id (".namePerson($id).")");
				}
				writeXMLElementClose('Persons')	if @persons;
			}
			{	#Groups
				writeXMLElementOpen('Groups')	if @groups;
				for my $i (0..$#groups){
					my $type	= $groups[$i]{type};
					my $id		= $groups[$i]{id};
					writeXMLElement($type, "Group$id (".nameGroup($id).")");
				}
				writeXMLElementClose('Groups')	if @groups;
			}
			{	#Synonyms
				writeXMLElementOpen('Synonyms')		if @synonyms;
				for my $i (0..$#synonyms){
					my $type	= $synonyms[$i]{type};
					my $id		= $synonyms[$i]{id};
					writeXMLElement($type, "Synonym$id (".nameSynonym($id).")");
				}
				writeXMLElementClose('Synonyms')	if @synonyms;
			}
			{	#Variables
				writeXMLElementOpen('Variables')	if @variables;
				for my $i (0..$#variables){
					my $type	= $variables[$i]{type};
					my $id		= $variables[$i]{id};
					writeXMLElement($type, "Variable$id (".nameVariable($id).")");
				}
				writeXMLElementClose('Variables')	if @variables;
			}
			{	#ALRs
				writeXMLElementOpen('ALRs')		if @alrs;
				for my $i (0..$#alrs){
					my $type	= $alrs[$i]{type};
					my $id		= $alrs[$i]{id};
					writeXMLElement($type, "ALR$id (".nameALR($id).")");
				}
				writeXMLElementClose('ALRs')	if @alrs;
			}
			writeXMLElementClose('Relations')	if $relations;
		}
		writeXMLElementClose('Event');
	}
	writeXMLElementClose('Events') if $#Events;
}
sub generateXMLPersons(){
	print $File_XML "\n<!-- $#Persons non-player persons -->";
	writeXMLElementOpen('Persons') if $#Persons;
	#TODO: Add the player
	for my $person (1 .. $#Persons){
		writeXMLElementOpen('Person');
		if ($Option_Verbose){	#Verbose ID and name
			print $File_XML "\t<!-- $person";
			print $File_XML " ($Symbol_Person[$person])"	if defined $Symbol_Person[$person];
			print $File_XML " -->";
		}
		{	#Properties
			writeXMLElementOpen('Properties');
			writeXMLElement('ID',			$person);
			writeXMLElement('SymbolicName',	namePerson($person));
			writeXMLElement('PrintedName',	$Persons[$person]{Name});
			writeXMLElement('Prefix',		$Persons[$person]{Prefix});
			foreach my $alias ( @{$Persons[$person]{Alias} } ){
				writeXMLElement('Alias',	$alias) unless $alias eq '';
			}
			writeXMLElement('Gender',		nameGender($Persons[$person]{Gender}));
			writeXMLElementClose('Properties');
		}
		{	#Location
			writeXMLElementOpen('Location');
			writeXMLElement('RoomID',		$Persons[$person]{StartRoom});
			writeXMLElement('Room',			nameRoom($Persons[$person]{StartRoom}));
			writeXMLElement('Presence',		$Persons[$person]{InRoomText});
			writeXMLElement('Entering',		$Persons[$person]{EnterText});
			writeXMLElement('Leaving',		$Persons[$person]{ExitText});
			writeXMLElementClose('Location');
		}
		#TODO: BattleStats
		{	#Descriptions	TODO Resource
			writeXMLElementOpen('Descriptions');
			writeXMLElementOpen('Description');
			writeXMLElement('Text',	$Persons[$person]{Description});
			writeXMLElementClose('Description');
			if($Persons[$person]{AltDescTask}){
				writeXMLElementOpen('Description');
				writeXMLElement('Text',		$Persons[$person]{AltDesc});
				writeXMLElement('TaskID',	$Persons[$person]{AltDescTask});
				writeXMLElement('TaskName',	nameTask($Persons[$person]{AltDescTask}));
				writeXMLElementClose('Description');
			}
			writeXMLElementClose('Descriptions');
		}
		{	#Topics
			writeXMLElementOpen('Topics');
			foreach my $topic ( @{$Persons[$person]{Topics} } ){
				writeXMLElementOpen('Topic');
				writeXMLElement('Subject',		$topic->{Subject});
				writeXMLElement('Reply',		$topic->{Reply});
				writeXMLElement('Reply_Alt',	$topic->{AltReply})			if $topic->{Task};
				writeXMLElement('Task',			$topic->{Task})				if $topic->{Task};
				writeXMLElement('Task_Name',	nameTask($topic->{Task}))	if $topic->{Task};
				writeXMLElementClose('Topic');
			}
			writeXMLElementClose('Topics');
		}
		#TODO: Walks
		{	#Relations
			my @rooms		= @{ $Persons[$person]{RoomReferences} };
			my @objects		= @{ $Persons[$person]{ObjectReferences} };
			my @tasks		= @{ $Persons[$person]{TaskReferences} };
			my @events		= @{ $Persons[$person]{EventReferences} };
			my @persons		= @{ $Persons[$person]{PersonReferences} };
			my @groups		= @{ $Persons[$person]{GroupReferences} };
			my @synonyms	= @{ $Persons[$person]{SynonymReferences} };
			my @variables	= @{ $Persons[$person]{VariableReferences} };
			my @alrs		= @{ $Persons[$person]{ALRReferences} };
			my $relations	= @rooms + @objects + @tasks + @events + @persons + @groups + @synonyms + @variables + @alrs;
			writeXMLElementOpen('Relations')	if $relations;
			{	#Rooms
				writeXMLElementOpen('Rooms')	if @rooms;
				for my $i (0..$#rooms){
					my $type	= $rooms[$i]{type};
					my $id		= $rooms[$i]{id};
					writeXMLElement($type, "Room$id (".nameRoom($id).")");
				}
				writeXMLElementClose('Rooms')	if @rooms;
			}
			{	#Objects
				writeXMLElementOpen('Objects')	if @objects;
				for my $i (0..$#objects){
					my $type	= $objects[$i]{type};
					my $id		= $objects[$i]{id};
					writeXMLElement($type, "Object$id (".nameObject($id).")");
				}
				writeXMLElementClose('Objects')	if @objects;
			}
			{	#Tasks
				writeXMLElementOpen('Tasks')	if @tasks;
				for my $i (0..$#tasks){
					my $type	= $tasks[$i]{type};
					my $id		= $tasks[$i]{id};
					writeXMLElement($type, "Task$id (".nameTask($id).")");
				}
				writeXMLElementClose('Tasks')	if @tasks;
			}
			{	#Events
				writeXMLElementOpen('Events')	if @events;
				for my $i (0..$#events){
					my $type	= $events[$i]{type};
					my $id		= $events[$i]{id};
					writeXMLElement($type, "Event$id (".nameEvent($id).")");
				}
				writeXMLElementClose('Events')	if @events;
			}
			{	#Persons
				writeXMLElementOpen('Persons')	if @persons;
				for my $i (0..$#persons){
					my $type	= $persons[$i]{type};
					my $id		= $persons[$i]{id};
					writeXMLElement($type, "Person$id (".namePerson($id).")");
				}
				writeXMLElementClose('Persons')	if @persons;
			}
			{	#Groups
				writeXMLElementOpen('Groups')	if @groups;
				for my $i (0..$#groups){
					my $type	= $groups[$i]{type};
					my $id		= $groups[$i]{id};
					writeXMLElement($type, "Group$id (".nameGroup($id).")");
				}
				writeXMLElementClose('Groups')	if @groups;
			}
			{	#Synonyms
				writeXMLElementOpen('Synonyms')		if @synonyms;
				for my $i (0..$#synonyms){
					my $type	= $synonyms[$i]{type};
					my $id		= $synonyms[$i]{id};
					writeXMLElement($type, "Synonym$id (".nameSynonym($id).")");
				}
				writeXMLElementClose('Synonyms')	if @synonyms;
			}
			{	#Variables
				writeXMLElementOpen('Variables')	if @variables;
				for my $i (0..$#variables){
					my $type	= $variables[$i]{type};
					my $id		= $variables[$i]{id};
					writeXMLElement($type, "Variable$id (".nameVariable($id).")");
				}
				writeXMLElementClose('Variables')	if @variables;
			}
			{	#ALRs
				writeXMLElementOpen('ALRs')		if @alrs;
				for my $i (0..$#alrs){
					my $type	= $alrs[$i]{type};
					my $id		= $alrs[$i]{id};
					writeXMLElement($type, "ALR$id (".nameALR($id).")");
				}
				writeXMLElementClose('ALRs')	if @alrs;
			}
			writeXMLElementClose('Relations')	if $relations;
		}
		writeXMLElementClose('Person');
	}
	writeXMLElementClose('Persons')	if $#Persons;
}
sub generateXMLVariables(){
	print $File_XML "\n<!-- $#Variables variables -->";
	writeXMLElementOpen('Variables') if $#Variables;
	for my $variable (1 .. $#Variables){
		writeXMLElementOpen('Variable');
		if ($Option_Verbose){	#Verbose ID and name
			print $File_XML "\t<!-- $variable";
			print $File_XML " ($Symbol_Variable[$variable])"	if defined $Symbol_Variable[$variable];
			print $File_XML " -->";
		}
		{	#Properties
			writeXMLElementOpen('Properties');
			writeXMLElement('ID',			$variable);
			writeXMLElement('SymbolicName',	nameVariable($variable));
			writeXMLElement('PrintedName',	$Variables[$variable]{Name});
			writeXMLElement('Type',			$Variables[$variable]{Type});
			writeXMLElement('Value',		$Variables[$variable]{Value});
			writeXMLElementClose('Properties');
		}
		{	#Relations
			my @rooms		= @{ $Variables[$variable]{RoomReferences} };
			my @objects		= @{ $Variables[$variable]{ObjectReferences} };
			my @tasks		= @{ $Variables[$variable]{TaskReferences} };
			my @events		= @{ $Variables[$variable]{EventReferences} };
			my @persons		= @{ $Variables[$variable]{PersonReferences} };
			my @groups		= @{ $Variables[$variable]{GroupReferences} };
			my @synonyms	= @{ $Variables[$variable]{SynonymReferences} };
			my @variables	= @{ $Variables[$variable]{VariableReferences} };
			my @alrs		= @{ $Variables[$variable]{ALRReferences} };
			my $relations	= @rooms + @objects + @tasks + @events + @persons + @groups + @synonyms + @variables + @alrs;
			writeXMLElementOpen('Relations')	if $relations;
			{	#Rooms
				writeXMLElementOpen('Rooms')	if @rooms;
				for my $i (0..$#rooms){
					my $type	= $rooms[$i]{type};
					my $id		= $rooms[$i]{id};
					writeXMLElement($type, "Room$id (".nameRoom($id).")");
				}
				writeXMLElementClose('Rooms')	if @rooms;
			}
			{	#Objects
				writeXMLElementOpen('Objects')	if @objects;
				for my $i (0..$#objects){
					my $type	= $objects[$i]{type};
					my $id		= $objects[$i]{id};
					writeXMLElement($type, "Object$id (".nameObject($id).")");
				}
				writeXMLElementClose('Objects')	if @objects;
			}
			{	#Tasks
				writeXMLElementOpen('Tasks')	if @tasks;
				for my $i (0..$#tasks){
					my $type	= $tasks[$i]{type};
					my $id		= $tasks[$i]{id};
					writeXMLElement($type, "Task$id (".nameTask($id).")");
				}
				writeXMLElementClose('Tasks')	if @tasks;
			}
			{	#Events
				writeXMLElementOpen('Events')	if @events;
				for my $i (0..$#events){
					my $type	= $events[$i]{type};
					my $id		= $events[$i]{id};
					writeXMLElement($type, "Event$id (".nameEvent($id).")");
				}
				writeXMLElementClose('Events')	if @events;
			}
			{	#Persons
				writeXMLElementOpen('Persons')	if @persons;
				for my $i (0..$#persons){
					my $type	= $persons[$i]{type};
					my $id		= $persons[$i]{id};
					writeXMLElement($type, "Person$id (".namePerson($id).")");
				}
				writeXMLElementClose('Persons')	if @persons;
			}
			{	#Groups
				writeXMLElementOpen('Groups')	if @groups;
				for my $i (0..$#groups){
					my $type	= $groups[$i]{type};
					my $id		= $groups[$i]{id};
					writeXMLElement($type, "Group$id (".nameGroup($id).")");
				}
				writeXMLElementClose('Groups')	if @groups;
			}
			{	#Synonyms
				writeXMLElementOpen('Synonyms')		if @synonyms;
				for my $i (0..$#synonyms){
					my $type	= $synonyms[$i]{type};
					my $id		= $synonyms[$i]{id};
					writeXMLElement($type, "Synonym$id (".nameSynonym($id).")");
				}
				writeXMLElementClose('Synonyms')	if @synonyms;
			}
			{	#Variables
				writeXMLElementOpen('Variables')	if @variables;
				for my $i (0..$#variables){
					my $type	= $variables[$i]{type};
					my $id		= $variables[$i]{id};
					writeXMLElement($type, "Variable$id (".nameVariable($id).")");
				}
				writeXMLElementClose('Variables')	if @variables;
			}
			{	#ALRs
				writeXMLElementOpen('ALRs')		if @alrs;
				for my $i (0..$#alrs){
					my $type	= $alrs[$i]{type};
					my $id		= $alrs[$i]{id};
					writeXMLElement($type, "ALR$id (".nameALR($id).")");
				}
				writeXMLElementClose('ALRs')	if @alrs;
			}
			writeXMLElementClose('Relations')	if $relations;
		}
		writeXMLElementClose('Variable');
	}
	writeXMLElementClose('Variables');
}
##Utility
sub debugDump($;$) {
	my $block	= shift;
	my $id		= shift;
	my $size	= length $block;
	print $File_Log "Debug dump for $id\n"	if defined $id;
	for my $i (1..$size){
		my $value	= ord substr($block, $i-1, 1);
		my $line	= sprintf('%08d: %03d (0x%2$02x) %2$c', $i, $value);
		print $File_Log "\t$line\n"
	}
}
#Symbolic Name Lookups
sub nameRoom($){
	my $id	= shift;
	return 'UnknownRoom'			unless defined $id;
	return $Symbol_Room[$id]		if defined $Symbol_Room[$id];
	return "Room$id";
}
sub nameObject($){
	my $id	= shift;
	return 'UnknownObject'			unless defined $id;
	return $Symbol_Object[$id]		if defined $Symbol_Object[$id];
	return "Object$id";
}
sub nameTask($){
	my $id	= shift;
	return 'UnknownTask'			unless defined $id;
	return $Symbol_Task[$id]		if defined $Symbol_Task[$id];
	return "Task$id";
}
sub nameEvent($){
	my $id	= shift;
	return 'UnknownEvent'			unless defined $id;
	return $Symbol_Event[$id]		if defined $Symbol_Event[$id];
	return "Event$id";
}
sub namePerson($){
	my $id	= shift;
	return 'UnknownPerson'			unless defined $id;
	return $Symbol_Person[$id]		if defined $Symbol_Person[$id];
	return "Person$id";
}
sub nameGroup($){
	my $id	= shift;
	return 'UnknownGroup'			unless defined $id;
	return $Symbol_Group[$id]		if defined $Symbol_Group[$id];
	return "Group$id";
}
sub nameVariable($){
	my $id	= shift;
	return 'UnknownVariable'		unless defined $id;
	return $Symbol_Variable[$id]	if defined $Symbol_Variable[$id];
	return "Variable$id";
}
sub nameGender($){
	my $id	= shift;
	return 'UnknownGender'			unless defined $id;
	return $Symbol_Gender[$id]		if defined $Symbol_Gender[$id];
	print $File_Log "WARNING: Unknown gender ID$id\n";
	return "person";
}
#XML Handling
sub writeXMLElement($;$){
	#Write a single-line XML element with content
	my $element	= shift;
	my $content	= shift;
	undef $content	if defined $content && $content eq '';
	if (defined $content){
		#Convert brackets
		$content =~ s/</\[/g;
		$content =~ s/>/\]/g;
		#New line and indentation
		print $File_XML "\n";
		$File_XML_Indent++;
		foreach (1..$File_XML_Indent) { print $File_XML "\t" }
		#Write content wrapped in element
		print $File_XML "<$element>";
		print $File_XML $content;
		print $File_XML "</$element>";
		$File_XML_Indent--;
	}
	else{
		writeXMLElementEmpty($element);
	}
}
sub writeXMLElementEmpty($){
	#Write an empty single-line XML element
	my $element	= shift;
	#New line and indentation
	print $File_XML "\n";
	$File_XML_Indent++;
	foreach (1..$File_XML_Indent) { print $File_XML "\t" }
	#Write element
	print $File_XML "<$element />";
	$File_XML_Indent--;
}
sub writeXMLElementOpen($){
	my $element	= shift;
	#New line and indentation
	print $File_XML "\n";
	$File_XML_Indent++;
	foreach (1..$File_XML_Indent) { print $File_XML "\t" }
	print $File_XML "<$element>";
}
sub writeXMLElementClose($;$){
	my $element	= shift;
	#New line and indentation
	print $File_XML "\n";
	foreach (1..$File_XML_Indent) { print $File_XML "\t" }
	print $File_XML "</$element>";
	$File_XML_Indent--;
}
##Main Program Loop
initialize();		# Parse command line arguments for options and filename
print "Preparing to read $FileName_Compiled\n";
openFiles();		# Open file handles
determineVersion();	# Read the header to determine version
print "Reading...\n";
loadFile();			# Read the compiled file into memory and close input files
loadSymbols();		# Parse the translation mapping file
print "Parsing...\n";
parse();			# Parse the compiled file into memory structure
print "Analyzing...\n";
generateSymbols();	# Generate (and print) symbol names
analyze();			# Deeper analysis that depends on the entire story being parsed
print "Generating output...\n";
generate();			# Generate output and close the files
print "Decompiling completed in ".(time - $Time_Start)." seconds.\n";
