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
my $Decompiler_Version		= '0.11';
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


##Global variables##
#File handling
my $FileName_Compiled;		# Filename for the compiled gamefile to decompile
my $FileName_Path;			# Path to place output files in
my $FileName_Log;			# Filename for the log
my $FileName_Mapping;		# Filename for the mapping/translation file, if any.
my $FileName_Generate;		# Filename for the generated mapping file
my $FileName_Decompiled;	# Filename for the decompiled sourcecode
my $FileName_Inform;		# Filename for the Inform output
my $FileName_XML;			# Filename for the XML output
my $File_Compiled;			# File handle for input compiled gamefile
my $File_Log;				# File handle for logging output
my $File_Mapping;			# File handle for name mapping
my $File_Decompiled;		# File handle for output decompiled sourcecode
my $File_Inform;			# File handle for Inform output
my $File_XML;				# File handle for XML output
my $File_XML_Indent	= -1;	# Storing the indentation level of the XML file

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
my @Rooms 			= ( undef );	# Contains the room objects from the game, starting from ID 1
my @Objects 		= ( undef );	# Contains the 'object' objects from the game, starting from ID 1
my @Tasks	 		= ( undef );	# Contains the task objects from the game, starting from ID 1
my @Events	 		= ( undef );	# Contains the event objects from the game, starting from ID 1
my @Persons	 		= ( undef );	# Contains the person objects from the game, starting from ID 1
my @Groups	 		= ( undef );	# Contains the room group objects from the game, starting from ID 1
my @Synonyms 		= ( undef );	# Contains the synonym objects from the game, starting from ID 1
my @Variables 		= ( undef );	# Contains the variable objects from the game, starting from ID 1
my @ALRs 			= ( undef );	# Contains the ALR objects from the game, starting from ID 1
#Relationships
my @RoomTasks		= ();
my @ObjectTasks		= ();
my @TaskPersons		= ();
my @TaskGroups		= ();
my @TaskVariables	= ();

##Translation
#Translation Mappings
my @Translate_Room;					# Translation names for rooms
my @Translate_Object;				# Translation names for 'objects'
my @Translate_Task;					# Translation names for tasks
my @Translate_Event;				# Translation names for event
my @Translate_Person;				# Translation names for persons
my @Translate_Group;				# Translation names for room groups
my @Translate_Variable;				# Translation names for variables
#Object mappings - VERIFY if some of these start at 0
my @ObjectStatic		= ( 0 );	# Mapping from static object ID to actual object ID
my @ObjectPortable		= ( 0 );	# Mapping from non-static object ID to actual object ID
my @ObjectOpenable		= ( 0 );	# Mapping from openable object ID to actual object ID; VERIFY Starts at 0.
my @ObjectContainer		= ( 0 );	# Mapping from container object ID to actual object ID; VERIFY Starts at 0 
my @ObjectSurface		= ( 0 );	# Mapping from surface object ID to actual object ID; VERIFY Starts at 0.
my @ObjectHolder		= ( 0 );	# Mapping from holder/parent object ID to actual object ID; VERIFY Starts at 0.
my @ObjectLieable		= ( 0 );	# Mapping from lieable object ID to actual object ID
my @ObjectSitStandable	= ( 0 );	# Mapping from sit/standable object ID to actual object ID
#Static mappings
my @Compass_Direction;				# Names of the compass directions, populated by loadCompass
my @Compass_Reversed;				# Names of the reversed compass directions, populated by loadCompass
my @Gender;

#Namings
sub nameRoom($){
	my $id	= shift;
	return 'UnknownRoom'			unless defined $id;
	return $Translate_Room[$id]		if defined $Translate_Room[$id];
	return "Room$id";
}
sub nameObject($){
	my $id	= shift;
	return 'UnknownObject'			unless defined $id;
	return $Translate_Object[$id]	if defined $Translate_Object[$id];
	return "Object$id";
}
sub nameTask($){
	my $id	= shift;
	return 'UnknownTask'			unless defined $id;
	return $Translate_Task[$id]		if defined $Translate_Task[$id];
	return "Task$id";
}
sub nameEvent($){
	my $id	= shift;
	return 'UnknownEvent'			unless defined $id;
	return $Translate_Event[$id]	if defined $Translate_Event[$id];
	return "Event$id";
}
sub namePerson($){
	my $id	= shift;
	return 'UnknownPerson'			unless defined $id;
	return $Translate_Person[$id]	if defined $Translate_Person[$id];
	return "Person$id";
}
sub nameGroup($){
	my $id	= shift;
	return 'UnknownGroup'			unless defined $id;
	return $Translate_Group[$id]	if defined $Translate_Group[$id];
	return "Group$id";
}
sub nameVariable($){
	my $id	= shift;
	return 'UnknownVariable'			unless defined $id;
	return $Translate_Variable[$id]	if defined $Translate_Variable[$id];
	return "Variable$id";
}
sub nameGender($){
	my $id	= shift;
	return 'UnknownGender'			unless defined $id;
	return $Gender[$id]				if defined $Gender[$id];
	print $File_Log "WARNING: Unknown gender ID=$id\n";
	return "person";
}
#Mapping File Handling

#Constants
sub loadConstants(){
	#Compass directions; dependant on the ExpandedCompass global
	$Compass_Direction[0]	= 'North';
	$Compass_Direction[1]	= 'East';
	$Compass_Direction[2]	= 'South';
	$Compass_Direction[3]	= 'West';
	$Compass_Direction[4]	= 'Up';
	$Compass_Direction[5]	= 'Down';
	$Compass_Direction[6]	= 'Inside';
	$Compass_Direction[7]	= 'Outside';
	$Compass_Direction[8]	= 'Northeast'		if $Game{ExpandedCompass};
	$Compass_Direction[9]	= 'Southeast'		if $Game{ExpandedCompass};
	$Compass_Direction[10]	= 'Southwest'		if $Game{ExpandedCompass};
	$Compass_Direction[11]	= 'Northwest'		if $Game{ExpandedCompass};
	$Compass_Reversed[0]	= 'south of';
	$Compass_Reversed[1]	= 'west of';
	$Compass_Reversed[2]	= 'north of';
	$Compass_Reversed[3]	= 'east of';
	$Compass_Reversed[4]	= 'down from';
	$Compass_Reversed[5]	= 'up from';
	$Compass_Reversed[6]	= 'outside from';
	$Compass_Reversed[7]	= 'inside from';
	$Compass_Reversed[8]	= 'southwest of'	if $Game{ExpandedCompass};
	$Compass_Reversed[9]	= 'northwest of'	if $Game{ExpandedCompass};
	$Compass_Reversed[10]	= 'northeast of'	if $Game{ExpandedCompass};
	$Compass_Reversed[11]	= 'southeast of'	if $Game{ExpandedCompass};
	#Gender names
	$Gender[0]	= 'man';
	$Gender[1]	= 'woman';
}

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
	for (1 .. $size) { $mask .= chr(nextPRNG()) }
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
#Convert text into uniform naming without spaces or quotes
sub parseFile(){
	#Parse header, printing the most important settings
	print $File_Log "Decompiler v$Decompiler_Version on $FileName_Compiled";
	parseHeader();
	print $File_Log ", $Game{Title} by $Game{Author} (ADRIFT v$Gamefile_Version)\n";
	print $File_Log "\tBattles\n"			if $Game{EnableBattle};
	print $File_Log "\t8-point compass\n"	if $Game{ExpandedCompass};
	print $File_Log "\tGraphics\n"			if $Game{EnableGraphics};
	print $File_Log "\tSound\n"				if $Game{EnableSound};
	#Load constants based on header
	loadConstants();
	#Parse rooms
	my $rooms		= nextSLV();
	print $File_Log "$rooms rooms\n";
	for my $room	(1 .. $rooms)	{ push @Rooms, parseRoom($room); }
	#Parse objects
	my $objects		= nextSLV();
	print $File_Log "$objects objects\n";
	for my $object	(1 .. $objects)	{ push @Objects, parseObject($object); }
	#Parse tasks
	my $tasks		= nextSLV();
	print $File_Log "$tasks tasks\n";
	for my $task	(1 .. $tasks)	{ push @Tasks, parseTask($task); }
	#Parse timed events
	my $events		= nextSLV();
	print $File_Log "$events events\n";
	for my $event	(1 .. $events)	{ push @Events, parseEvent($event); }
	#Parse persons
	my $persons		= nextSLV();
	print $File_Log "$persons persons\n";
	for my $person	(1 .. $persons)	{ push @Persons, parsePerson($person); }
	#Parse room-groups
	my $groups		= nextSLV();
	print $File_Log "$groups groups\n";
	for my $group	(1 .. $groups)	{ push @Groups, parseGroup($group); }
	#Parse parser-synonyms
	my $synonyms	= nextSLV();
	print $File_Log "$synonyms synonyms\n";
	for my $synonym	(1 .. $synonyms)	{ push @Synonyms, parseSynonym($synonym); }
	#Parse variables
	my $variables	= 0;
	$variables		= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	print $File_Log "$variables variables\n";
	for my $variable	(1 .. $variables)	{ push @Variables, parseVariable($variable); }
	#Parse alternate-language resources
	my $alrs		= 0;
	$alrs			= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	print $File_Log "$alrs ALRs\n";
	for my $alr	(1 .. $alrs)	{ push @ALRs, parseALR($alr); }
	#Parse footer
	parseFooter();
	print $File_Log "Parsed  $Lines_Next of ". ($#Lines + 1) ." lines\n";
}
sub parseHeader(){
	#Intro Text
	$Game{Intro}			= nextMLV();
	$Game{Start}			= nextSLV() + 1;	# The only place rooms are indexed from 0
	$Game{Ending}			= nextMLV();
	#text	GameName
	$Game{Title}			= nextSLV();
	#text	GameAuthor
	$Game{Author}			= nextSLV();
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
	nextSLV()							if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	nextSLV()							if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#truth	Embedded
	$Game{Embedded}			= 0			if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	$Game{Embedded}			= nextSLV()	if $Gamefile_Version eq '4.00';
}
sub parseFooter(){
	#truth	CustomFont
	$Game{CustomFont}		= 0			if $Gamefile_Version eq '3.80';
	$Game{CustomFont}		= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#text	FontNameSize
	$Game{FontNameSize}		= nextSLV()	if $Game{CustomFont};
	#text	CompileDate
	$Game{CompileDate}		= nextSLV();
	#text	Password		SKIP
	nextSLV()	if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
}
#Routines for parsing major objects
sub parseRoom($){
	my $id		= shift;
	my %room	= ();
	#text	Short
	$room{Title}			= nextSLV();
	print $File_Log "\t\t$id: $room{Title}\n"	if defined $Option_Verbose;
	#text	Long
	$room{Description}		= nextSLV();
	#text	LastDesc
	$room{LastDesc}			= nextSLV()	if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	#exit	RoomExits
	my $exit_count			= 0;
	$room{Exits}			= [];
	for my $dir (0 .. $#Compass_Direction) { 
		push @{ $room{Exits} }, parseExit();
		$exit_count++	unless $room{Exits}[$dir]{Destination} eq 0;
	}
	print $File_Log "\t\t\t$exit_count exit(s)\n"	if defined $Option_Verbose;
	#text	AddDesc1
	$room{AltDesc1}			= nextSLV()	if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	#number	AddDesc1Task
	$room{AltDesc1Task}		= nextSLV()	if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	#text	AddDesc2
	$room{AltDesc2}			= nextSLV()	if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	#number	AddDesc2Task
	$room{AltDesc2Task}		= nextSLV()	if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	#number	Obj
	$room{AltDesc3Obj}		= nextSLV()	if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	#text	AltDesc
	$room{AltDesc3}			= nextSLV()	if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	#number	TypeHideObjects
	$room{TypeHideObjects}	= nextSLV()	if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	#resource	Res
	$room{Resource}			= parseResource()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#resource	LastRes
	$room{LastDescResource}	= parseResource()	if $Gamefile_Version eq '3.90';
	#resource	Task1Res
	$room{AltDesc1Resource}	= parseResource()	if $Gamefile_Version eq '3.90';
	#resource	Task2Res
	$room{AltDesc2Resource}	= parseResource()	if $Gamefile_Version eq '3.90';
	#resource	AltRes
	$room{AltDesc3Resource}	= parseResource()	if $Gamefile_Version eq '3.90';
	#RoomAlt	Alternates
	my $alt_count	= 0;
	my @alternates	= ();
	$alt_count		= nextSLV()	if $Gamefile_Version eq '4.00';
	for (1 .. $alt_count){ push @alternates, parseRoomAlt() }
	$room{Alternates}		= \@alternates;
	print $File_Log "\t\t\t$alt_count alternate(s)\n"	if defined $Option_Verbose && $alt_count;
	#truth	HideOnMap
	$room{Hidden}		= nextSLV()		if ($Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00') && not $Game{DisableMap};
	return \%room;
}
sub parseObject($){
	my $id		= shift;
	my %object	= ();
	#text	Prefix
	$object{Prefix}				= nextSLV();
	#text	Short
	$object{Short}				= nextSLV();
	print $File_Log "\t\t$id: ($object{Prefix}) $object{Short}\n"	if defined $Option_Verbose;
	#text	Alias
	my $alias					= 1;
	$alias						= nextSLV()	if $Gamefile_Version eq '4.00';
	$object{Alias}				= ();
	for (1 .. $alias) { push @{ $object{Alias} }, nextSLV(); }
	#truth	Static
	$object{Static}				= nextSLV();
	#text	Description
	$object{Description}		= nextSLV();
	#number	InitialPosition
	$object{InitialPosition}	= nextSLV();
	#number	Task
	$object{AltDescTask}		= nextSLV();
	#truth	TaskNotDone
	my $altdesctype				= nextSLV();
	$object{AltDescType}		= 'if';
	$object{AltDescType}		= 'unless'	if $altdesctype;
	#text	AltDesc
	$object{AltDesc}			= nextSLV();
	#RoomList	Where
	$object{WhereType}			= 9;
	$object{WhereType}			= nextSLV()	if $object{Static};
#	0: NO_ROOMS
#	1: ONE_ROOM
#	2: SOME_ROOMS
#	3: ALL_ROOMS
#	4: NPC_PART
#	9: NULL/Off-stage
	$object{Where}				= [];
	push @{	$object{Where} }, nextSLV if $object{WhereType} eq 1;
	if($object{WhereType} eq 2){
		for my $room (0 .. $#Rooms){ push @{	$object{Where} }, $room if nextSLV(); }
	}
	my $surfaceContainer		= 0;
	$surfaceContainer			= nextSLV()	if $Gamefile_Version eq '3.80';
	#truth	Container
	$object{Container}			= 0			unless $surfaceContainer eq 1;
	$object{Container}			= 1			if $surfaceContainer eq 1;
	$object{Container}			= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#truth	Surface
	$object{Surface}			= 0			unless $surfaceContainer eq 2;
	$object{Surface}			= 1			if $surfaceContainer eq 2;
	$object{Surface}			= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#number	Capacity
	$object{Capacity}			= nextSLV();
	$object{Capacity}			= $object{Capacity} * 10 + 2	if $Gamefile_Version eq '3.80';
	#truth	Wearable
	$object{Wearable}			= 0;
	$object{Wearable}			= nextSLV()	unless $object{Static};
	#number	SizeWeight
	$object{SizeWeight}			= 0;
	$object{SizeWeight}			= nextSLV()	unless $object{Static};
	#number	Parent
	$object{Parent}				= 0;
	$object{Parent}				= nextSLV()	unless $object{Static};
	$object{Parent}				= nextSLV()	if $object{Static} && $object{WhereType} eq 4;
	#number	Openable
	my $openable				= nextSLV();
#	0: UNOPENABLE
#	5: OPEN
#	6: CLOSED
#	7: LOCKED
	$object{Openable}			= $openable;
	#Code 5 and 6 are reversed in v3.XX
	if($Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90'){
		$object{Openable}			= 6 if $openable eq 5;
		$object{Openable}			= 5 if $openable eq 6;
	}
	#number	Key
	$object{Key}				= nextSLV()	if $Gamefile_Version eq '4.00' && $object{Openable};
	#number	SitLie
	my $enterableType			= nextSLV();
	$object{EnterableType}		= $enterableType;
	$object{SitStandable}		= 1 if $enterableType eq 1 || $enterableType eq 3;
	$object{Lieable}			= 1 if $enterableType eq 2 || $enterableType eq 3;
	#truth	Edible
	$object{Edible}				= nextSLV()	unless $object{Static};
	#truth	Readable
	$object{Readable}			= nextSLV();
	#truth	ReadText
	$object{ReadText}			= nextSLV()	if $object{Readable};
	#truth	Weapon
	$object{Weapon}				= nextSLV()	unless $object{Static};
	#number	CurrentState
	$object{CurrentState}		= 0			if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	$object{CurrentState}		= nextSLV() if $Gamefile_Version eq '4.00';
	#number	States
	$object{States}				= 0;
	$object{States}				= nextSLV()	if $object{CurrentState};
	#truth	StateListed
	$object{StateListed}		= 0;
	$object{StateListed}		= nextSLV()	if $object{CurrentState};
	#truth	ListFlag
	$object{ListFlag}			= 0			if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	$object{ListFlag}			= nextSLV() if $Gamefile_Version eq '4.00';
	#resource	Res1
	$object{Resource1}			= parseResource()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#resource	Res2
	$object{Resource2}			= parseResource()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#battle	Battle
	$object{BattleStats}		= parseBattle()	if $Game{EnableBattle};
	#text	InRoomDesc
	$object{InRoomDesc}			= ''		if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	$object{InRoomDesc}			= nextSLV() if $Gamefile_Version eq '4.00';
	#number	OnlyWhenNotMoved
	$object{InRoomDescType}		= 0			if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	$object{InRoomDescType}		= nextSLV() if $Gamefile_Version eq '4.00';
	#Update the Object mapping references:
	push @ObjectStatic,	$id		if $object{Static};
	push @ObjectPortable, $id	unless $object{Static};
	push @ObjectOpenable, $id	if $object{Openable};
	push @ObjectContainer, $id	if $object{Container};
	push @ObjectSurface, $id	if $object{Surface};
	push @ObjectHolder,	$id		if $object{Container} || $object{Surface};
	push @ObjectLieable, $id	if $object{Lieable};
	push @ObjectSitStandable, $id	if $object{SitStandable};
	return \%object;
}
sub parseTask($){
	my $id		= shift;
	my %task	= ();
	#text	Command
	my $commands				= nextSLV();
	$commands++					if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	$task{Commands}				= ();
	for (1 .. $commands) { push @{ $task{Commands} }, nextSLV(); }
	print $File_Log "\t\t$id: $task{Commands}[0] ($commands)\n"	if defined $Option_Verbose;
	#text	CompleteText
	$task{CompleteText}				= nextSLV();
	#text	ReverseMessage
	$task{ReverseText}				= nextSLV();
	#text	RepeatText
	$task{RepeatText}				= nextSLV();
	#text	AdditionalMessage
	$task{AdditionalText}			= nextSLV();
	#number	ShowRoomDesc
	$task{ShowRoomDesc}				= nextSLV();
	#Some 3.80 variables
	if ($Gamefile_Version eq '3.80'){
		#number	Score
		$task{Score}				= nextSLV();
		#number	SingleScore
		$task{BSingleScore}			= nextSLV();
		#TaskMove	Movements
		$task{Movements}			= ();
		for (1 .. 6) {
			my %movement	= ();
			$movement{Var1}		= nextSLV();
			$movement{Var2}		= nextSLV();
			$movement{Var3}		= nextSLV();
			push @{ $task{Movements} },  \%movement;
		}
	}
	#truth	Repeatable
	$task{Repeatable}				= nextSLV();
	#truth	Reversible
	$task{Reversible}				= nextSLV();
	#text	ReverseCommand
	my $commands_reverse			= nextSLV();
	$commands_reverse++				if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	print $File_Log "\t\t\t$commands_reverse reversion(s)\n"	if defined $Option_Verbose;
	$task{CommandsReverse}			= [];
	for (1 .. $commands_reverse) { push @{ $task{CommandsReverse} }, nextSLV(); }
	#Some 3.80 variables
	if ($Gamefile_Version eq '3.80'){
		#number	WearObj1
		$task{WearObj1}				= nextSLV();
		#number	WearObj2
		$task{WearObj2}				= nextSLV();
		#number	HoldObj1
		$task{HoldObj1}				= nextSLV();
		#number	HoldObj2
		$task{HoldObj2}				= nextSLV();
		#number	HoldObj3
		$task{HoldObj3}				= nextSLV();
		#number	Obj1
		$task{Obj1}					= nextSLV();
		#number	Task
		$task{Task}					= nextSLV();
		#truth	TaskNotDone
		$task{TaskNotDone}			= nextSLV();
		#text	TaskMsg
		$task{TaskMsg}				= nextSLV();
		#text	HoldMsg
		$task{HoldMsg}				= nextSLV();
		#text	WearMsg
		$task{WearMsg}				= nextSLV();
		#text	CompanyMsg
		$task{CompanyMsg}			= nextSLV();
		#truth	NotInSameRoom
		$task{NotInSameRoom}		= nextSLV();
		#number	NPC
		$task{NPC}					= nextSLV();
		#text	Obj1Msg
		$task{Obj1Msg}				= nextSLV();
		#number	Obj1Room
		$task{Obj1Room}				= nextSLV();
	}
	#RoomList	Where
	$task{WhereType}				= 9;
	$task{WhereType}				= nextSLV();
#	0: NO_ROOMS
#	1: ONE_ROOM
#	2: SOME_ROOMS
#	3: ALL_ROOMS
#	4: NPC_PART
#	9: NULL/Off-stage
	$task{Where}					= [];
	push @{	$task{Where} }, nextSLV if $task{WhereType} eq 1;
	if($task{WhereType} eq 2){
		for my $room (1 .. $#Rooms){ push @{ $task{Where} }, $room if nextSLV(); }
	}
	#Some 3.80 variables
	if ($Gamefile_Version eq '3.80'){
		#truth	KillsPlayer
		$task{KillsPlayer}			= nextSLV();
		#truth	HoldingSameRoom
		$task{HoldingSameRoom}		= nextSLV();
	}
#	$Question ?$Question:$Hint1,$Hint2
	#text	Question
	$task{Question}					= nextSLV();
	#text	Hint1
	$task{Hint1}					= nextSLV()	if length $task{Question} != 0;
	#text	Hint2
	$task{Hint2}					= nextSLV()	if length $task{Question} != 0;
	#Some 3.80 variables
	if ($Gamefile_Version eq '3.80'){
		#number	Obj2
		$task{Obj2}				= nextSLV();
		#number	Obj2Var1
		$task{Obj2Var1}			= nextSLV()	if $task{Obj2};
		#number	Obj2Var2
		$task{Obj2Var2}			= nextSLV()	if $task{Obj2};
		#text	Obj2Msg
		$task{Obj2Msg}			= nextSLV()	if $task{Obj2};
		#truth	WinGame
		$task{WinGame}			= nextSLV();
	}
	#Restrictions	Restrictions
	$task{Restrictions}				= [];
	my $restrictions				= 0;
	$restrictions					= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	print $File_Log "\t\t\t$restrictions restriction(s)\n"	if defined $Option_Verbose;
	for (1 .. $restrictions) { push @{ $task{Restrictions} }, parseRestriction(); }
	#Actions	Actions
	$task{Actions}					= [];
	my $actions						= 0;
	$actions						= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	print $File_Log "\t\t\t$actions action(s)\n"	if defined $Option_Verbose;
	for (1 .. $actions) { push @{ $task{Actions} }, parseAction(); }
	#text	RestrMask
	$task{RestrMask}				= nextSLV()	if $Gamefile_Version eq '4.00';
	#resource Res
	$task{Resource}					= parseResource()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	return \%task;
}
sub parseEvent($){
	my $id		= shift;
	my %event	= ();
	#text	Short
	$event{Short}				= nextSLV();
	print $File_Log "\t\t$id: $event{Short}\n"	if defined $Option_Verbose;
	#number	StarterType
	$event{StarterType}			= nextSLV();
	#number	StartTime
	$event{StartTime}			= nextSLV()	if $event{StarterType} eq 2;
	#number	EndTime
	$event{EndTime}				= nextSLV()	if $event{StarterType} eq 2;
	#number	TaskNum
	$event{TaskNum}				= nextSLV()	if $event{StarterType} eq 3;
	#number	RestartType
	$event{RestartType}			= nextSLV();
	#truth	TaskFinished
	$event{TaskFinished}		= nextSLV();
	#number	Time1
	$event{Time1}				= nextSLV();
	#number	Time2
	$event{Time2}				= nextSLV();
	#text	StartText
	$event{StartText}			= nextSLV();
	#text	LookText
	$event{LookText}			= nextSLV();
	#text	FinishText
	$event{FinishText}			= nextSLV();
	#RoomList	Where
	$event{WhereType}			= 9;
	$event{WhereType}			= nextSLV();
#	0: NO_ROOMS
#	1: ONE_ROOM
#	2: SOME_ROOMS
#	3: ALL_ROOMS
#	4: NPC_PART
#	9: NULL/Off-stage
	$event{Where}				= ();
	push @{	$event{Where} }, nextSLV if $event{WhereType} eq 1;
	if($event{WhereType} eq 2){
		for my $room (1 .. $#Rooms){ push @{ $event{Where} }, $room if nextSLV(); }
	}
	#number	PauseTask
	$event{PauseTask}			= nextSLV();
	#truth	PauserCompleted
	$event{PauserCompleted}		= nextSLV();
	#number	PrefTime1
	$event{PrefTime1}			= nextSLV();
	#text	PrefText1
	$event{PrefText1}			= nextSLV();
	#number	ResumeTask
	$event{ResumeTask}			= nextSLV();
	#truth	ResumerCompleted
	$event{ResumerCompleted}	= nextSLV();
	#number	PrefTime2
	$event{PrefTime2}			= nextSLV();
	#text	PrefText2
	$event{PrefText2}			= nextSLV();
	#number	Obj2
	$event{Obj2}				= nextSLV();
	#number	Obj2Dest
	$event{Obj2Dest}			= nextSLV();
	#number	Obj3
	$event{Obj3}				= nextSLV();
	#number	Obj3Dest
	$event{Obj3Dest}			= nextSLV();
	#number	Obj1
	$event{Obj1}				= nextSLV();
	#number	Obj1Dest
	$event{Obj1Dest}			= nextSLV();
	#number	TaskAffected
	$event{TaskAffected}		= nextSLV();
	#Resources
	$event{Res1}				= parseResource()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	$event{Res2}				= parseResource()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	$event{Res3}				= parseResource()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	$event{Res4}				= parseResource()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	$event{Res5}				= parseResource()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	return \%event;
#v4.00
#	$Short #StarterType
#	?#StarterType=2:#StartTime,#EndTime ?#StarterType=3:#TaskNum
#	#RestartType BTaskFinished #Time1 #Time2 $StartText $LookText $FinishText
#	<ROOM_LIST0>Where #PauseTask
#	BPauserCompleted #PrefTime1 $PrefText1 #ResumeTask BResumerCompleted
#	#PrefTime2 $PrefText2 #Obj2 #Obj2Dest #Obj3 #Obj3Dest #Obj1 #Obj1Dest
#	#TaskAffected [5]<RESOURCE>Res
#v3.90
#	$Short #StarterType
#	?#StarterType=2:#StartTime,#EndTime ?#StarterType=3:#TaskNum
#	#RestartType BTaskFinished #Time1 #Time2 $StartText $LookText $FinishText
#	<ROOM_LIST0>Where #PauseTask
#	BPauserCompleted #PrefTime1 $PrefText1 #ResumeTask BResumerCompleted
#	#PrefTime2 $PrefText2 #Obj2 #Obj2Dest #Obj3 #Obj3Dest #Obj1 #Obj1Dest
#	#TaskAffected [5]<RESOURCE>Res
#v3.80
#   $Short #StarterType
#	?#StarterType=2:#StartTime,#EndTime ?#StarterType=3:#TaskNum
#	#RestartType BTaskFinished #Time1 #Time2 $StartText $LookText $FinishText
#	<ROOM_LIST0>Where #PauseTask
#	BPauserCompleted #PrefTime1 $PrefText1 #ResumeTask BResumerCompleted
#	#PrefTime2 $PrefText2 #Obj2 #Obj2Dest #Obj3 #Obj3Dest #Obj1 #Obj1Dest
#	#TaskAffected
}
sub parsePerson($){
	my $id		= shift;
	my %person	= ();
	#text	Name
	$person{Name}				= nextSLV();
	print $File_Log "\t\t$id: $person{Name}\n"	if defined $Option_Verbose;
	#text	Prefix
	$person{Prefix}				= nextSLV();
	#text	Alias
	my $alias					= 1;
	$alias						= nextSLV()	if $Gamefile_Version eq '4.00';
	$person{Alias}				= ();
	for (1 .. $alias) { push @{ $person{Alias} }, nextSLV(); }
	#text	Descr
	$person{Description}		= nextSLV();
	#number	StartRoom
	$person{StartRoom}			= nextSLV();
	#text	AltText
	$person{AltDesc}			= nextSLV();
	#text	Task
	$person{AltDescTask}		= nextSLV();
	#text	Topics
	my $topics					= nextSLV();
	$person{Topics}				= ();
	print $File_Log "\t\t\t$topics topics(s)\n"	if defined $Option_Verbose;
	for (1 .. $topics) { push @{ $person{Topics} }, parseTopic(); }
	#text	Walks
	my $walks					= nextSLV();
	$person{Walks}				= ();
	print $File_Log "\t\t\t$walks walks(s)\n"	if defined $Option_Verbose;
	for (1 .. $walks) { push @{ $person{Walks} }, parseWalk(); }
	#truth	ShowEnterExit
	$person{ShowEnterExit}		= nextSLV();
	#text	EnterText
	$person{EnterText}			= nextSLV()	if $person{ShowEnterExit};
	#text	ExitText
	$person{ExitText}			= nextSLV()	if $person{ShowEnterExit};
	#text	InRoomText
	$person{InRoomText}			= nextSLV();
	#number	Gender
	$person{Gender}	= 0				if $Gamefile_Version eq '3.80';
	$person{Gender}	= nextSLV()		if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#Resources
	$person{Res1}				= parseResource()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	$person{Res2}				= parseResource()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	$person{Res3}				= parseResource()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	$person{Res4}				= parseResource()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#battle	Battle
	$person{BattleStats}		= parseBattle()	if $Game{EnableBattle};
	return \%person;
#v4.00
#	$Name $Prefix V$Alias $Descr #StartRoom $AltText #Task V<TOPIC>Topics
#	V<WALK>Walks BShowEnterExit ?BShowEnterExit:$EnterText,$ExitText
#	$InRoomText #Gender [4]<RESOURCE>Res ?GBattleSystem:<NPC_BATTLE>Battle
#v3.90
#	$Name $Prefix [1]$Alias $Descr #StartRoom $AltText #Task V<TOPIC>Topics
#	V<WALK>Walks BShowEnterExit ?BShowEnterExit:$EnterText,$ExitText
#	$InRoomText #Gender [4]<RESOURCE>Res ?GBattleSystem:<NPC_BATTLE>Battle
#v3.80
#	$Name $Prefix [1]$Alias $Descr #StartRoom $AltText #Task V<TOPIC>Topics
#	V<WALK>Walks BShowEnterExit ?BShowEnterExit:$EnterText,$ExitText
#	$InRoomText ZGender
}
sub parseGroup($){
	my $id		= shift;
	my %group	= ();
	#text	Name
	$group{Name}				= nextSLV();
	print $File_Log "\t\t$id: $group{Name}\n"	if defined $Option_Verbose;
	#		Rooms
	$group{Rooms}				= ();
	for my $room (1 .. $#Rooms){ push @{ $group{Rooms} }, $room if nextSLV(); }
	return \%group;
}
sub parseSynonym($){
	my $id		= shift;
	my %synonym	= ();
	#text	Original
	$synonym{Original}				= nextSLV();
	#text	Replacement
	$synonym{Replacement}			= nextSLV();
	print $File_Log "\t\t$id: $synonym{Replacement} -> $synonym{Original}\n"	if defined $Option_Verbose;
	return \%synonym;
}
sub parseVariable($){
	my $id			= shift;
	my %variable	= ();
	#text	Name
	$variable{Name}				= nextSLV();
	#number	Type
	$variable{Type}				= 0			if $Gamefile_Version eq '3.90';
	$variable{Type}				= nextSLV()	if $Gamefile_Version eq '4.00';
	#text	Value
	$variable{Value}			= nextSLV();
	print $File_Log "\t\t$id: $variable{Name} ($variable{Type}) = $variable{Value}\n"	if defined $Option_Verbose;
	return \%variable;
}
sub parseALR($){
	my $id		= shift;
	my %alr	= ();
	#text	Original
	$alr{Original}				= nextSLV();
	#text	Replacement
	$alr{Replacement}			= nextSLV();
	print $File_Log "\t\t$id: $alr{Original} -> $alr{Replacement}\n"	if defined $Option_Verbose;
	return \%alr;
}
#Routines for parsing sub-objects
sub parseBattle(){
	die 'Fatal error: Battle system is not implemented';
}
sub parseResource(){
	my %resource	= ();
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
sub parseRoomAlt(){
	my %alt				= ();
	#	$M1
	$alt{M1}			= nextSLV();
	#	#Type
	$alt{Type}			= nextSLV();
	#	<RESOURCE>Res1
	$alt{Resource1}		= parseResource();
	#	$M2
	$alt{M2}			= nextSLV();
	#	#Var2
	$alt{Var2}			= nextSLV();
	#	<RESOURCE>Res2
	$alt{Resource2}		= parseResource();
	#	#HideObjects
	$alt{HideObjects}	= nextSLV();
	#	$Changed
	$alt{Changed}		= nextSLV();
	#	#Var3
	$alt{Var3}			= nextSLV();
	#	#DisplayRoom
	$alt{DisplayRoom}	= nextSLV();
	return \%alt;
}
sub parseExit(){
	my %exit		= ();
	#destination
	$exit{Destination}	= nextSLV();
	if ($exit{Destination} != 0){
		$exit{Var1}	= nextSLV();
		$exit{Var2}	= nextSLV();
		$exit{Var3}	= 0;
		$exit{Var3}	= nextSLV()			if $Gamefile_Version eq '4.00';
	}
	return \%exit;
}
sub parseRestriction(){
	my %restriction		= ();
	#number	Type
	$restriction{Type}		= nextSLV();
	if($restriction{Type} eq 0){
		$restriction{Var1}	= nextSLV();
		$restriction{Var2}	= nextSLV();
		$restriction{Var3}	= nextSLV();
	}
	if($restriction{Type} eq 1){
		$restriction{Var1}	= nextSLV();
		$restriction{Var2}	= nextSLV();
	}
	if($restriction{Type} eq 2){
		$restriction{Var1}	= nextSLV();
		$restriction{Var2}	= nextSLV();
	}
	if($restriction{Type} eq 3){
		$restriction{Var1}	= nextSLV();
		$restriction{Var2}	= nextSLV();
		$restriction{Var3}	= nextSLV();
	}
	if($restriction{Type} eq 4){
		$restriction{Var1}	= nextSLV();
		$restriction{Var1}++	if $Gamefile_Version eq '3.90' && $restriction{Var1};
		$restriction{Var2}	= nextSLV();
		$restriction{Var3}	= nextSLV();
		$restriction{Var4}	= '';
		$restriction{Var4}	= nextSLV()		if $Gamefile_Version eq '4.00';
	}
	$restriction{FailureText}	= nextSLV();
	return \%restriction;
#v4.00	TASK_RESTR
#	#Type
#	?#Type=0:#Var1,#Var2,#Var3
#	?#Type=1:#Var1,#Var2
#	?#Type=2:#Var1,#Var2
#	?#Type=3:#Var1,#Var2,#Var3
#	?#Type=4:#Var1,#Var2,#Var3,$Var4
#	$FailMessage"
#v3.90	TASK_RESTR
#	#Type
#	?#Type=0:#Var1,#Var2,#Var3
#	?#Type=1:#Var1,#Var2
#	?#Type=2:#Var1,#Var2
#	?#Type=3:#Var1,#Var2,#Var3
#	?#Type=4:#Var1,#Var2,#Var3,EVar4
#	|V390_TASK_RESTR:Var1>0?#Var1++|
#	$FailMessage
}
sub parseAction(){
	my %action;
	#number	Type
	$action{Type}		= nextSLV();
	$action{Type}++		if $action{Type} > 4 && $Gamefile_Version eq '3.90';
	if($action{Type} eq 0){
		$action{Var1}	= nextSLV();
		$action{Var2}	= nextSLV();
		$action{Var3}	= nextSLV();
	}
	if($action{Type} eq 1){
		$action{Var1}	= nextSLV();
		$action{Var2}	= nextSLV();
		$action{Var3}	= nextSLV();
	}
	if($action{Type} eq 2){
		$action{Var1}	= nextSLV();
		$action{Var2}	= nextSLV();
	}
	if($action{Type} eq 3){
		$action{Var1}	= nextSLV();
		$action{Var2}	= nextSLV();
		$action{Var3}	= nextSLV();
		$action{Expr}	= nextSLV()	if $Gamefile_Version eq '4.00';
		$action{Expr}	= nextSLV()	if $Gamefile_Version eq '3.90' && $action{Var2} eq 5;
		$action{Expr}	= ''		if $Gamefile_Version eq '3.90' && $action{Var2} != 5;
		$action{Var5}	= nextSLV()	if $Gamefile_Version eq '4.00';
		$action{Var5}	= nextSLV()	if $Gamefile_Version eq '3.90' && $action{Var2} != 5;
		$action{Var5}	= 0			if $Gamefile_Version eq '3.90' && $action{Var2} eq 5;
	}
	if($action{Type} eq 4){
		$action{Var1}	= nextSLV();
	}
	if($action{Type} eq 5){
		$action{Var1}	= nextSLV();
		$action{Var2}	= nextSLV();
	}
	if($action{Type} eq 6){
		$action{Var1}	= nextSLV();
		$action{Var2}	= 0			if $Gamefile_Version eq '3.90';
		$action{Var2}	= nextSLV()	if $Gamefile_Version eq '4.00';
		$action{Var3}	= 0			if $Gamefile_Version eq '3.90';
		$action{Var3}	= nextSLV()	if $Gamefile_Version eq '4.00';
	}
	if($action{Type} eq 7){
		$action{Var1}	= nextSLV();
		$action{Var2}	= nextSLV();
		$action{Var3}	= nextSLV();
	}
	return \%action;
#v4.00	TASK_ACTION",
#	#Type
#	?#Type=0:#Var1,#Var2,#Var3
#	?#Type=1:#Var1,#Var2,#Var3
#	?#Type=2:#Var1,#Var2
#	?#Type=3:#Var1,#Var2,#Var3,$Expr,#Var5
#	?#Type=4:#Var1
#	?#Type=5:#Var1,#Var2
#	?#Type=6:#Var1,#Var2,#Var3
#	?#Type=7:iVar1,iVar2,iVar3
#v3.90	TASK_ACTION
#	#Type |V390_TASK_ACTION:Type>4?#Type++|
#	?#Type=0:#Var1,#Var2,#Var3
#	?#Type=1:#Var1,#Var2,#Var3
#	?#Type=2:#Var1,#Var2
#	?#Type=3:#Var1,#Var2,#Var3,|V390_TASK_ACTION:$Expr_#Var5|
#	?#Type=4:#Var1
#	?#Type=6:#Var1,ZVar2,ZVar3
#	?#Type=7:iVar1,iVar2,iVar3
}
sub parseTopic(){
	my %topic;
	#text	Subject
	$topic{Subject}			= nextSLV();
	#text	Reply
	$topic{Reply}			= nextSLV();
	#number	Task
	$topic{AltReplyTask}	= nextSLV();
	#text	AltReply
	$topic{AltReply}		= nextSLV();
	return \%topic;
}
sub parseWalk(){
	my %walk;
	#number	NumStops
	my $stops				= nextSLV();
	print $File_Log "\t\t\t\t$stops stops(s)\n"	if defined $Option_Verbose;
	$walk{NumStops}			= $stops;
	#truth	Loop
	$walk{Loop}				= nextSLV();
	#number	StartTask
	$walk{StartTask}		= nextSLV();
	#number	CharTask
	$walk{CharTask		}	= nextSLV();
	#number	MeetObject
	$walk{MeetObject}		= nextSLV();
#TODO: ?!#MeetObject=0:|V380_WALK:_MeetObject_|
	#number	ObjectTask
	$walk{ObjectTask}		= nextSLV();
	#number	StoppingTask
	$walk{StoppingTask}		= 0			if $Gamefile_Version eq '3.80';
	$walk{StoppingTask}		= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#number	MeetChar
	$walk{MeetChar}			= 0			if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	$walk{MeetChar}			= nextSLV()	if $Gamefile_Version eq '4.00';
	#text	ChangedDesc
	$walk{ChangedDesc}		= ''		if $Gamefile_Version eq '3.80';
	$walk{ChangedDesc}		= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	#	{WALK:#Rooms_#Times}
	$walk{Stops}				= ();
	for (1 .. $stops){
		my %stop		= ();
		$stop{Room}		= nextSLV();
		$stop{Times}	= nextSLV();
		push @{ $walk{Stops} }, \%stop;
	}

	return \%walk;
#v4.00	WALK
#	#NumStops BLoop #StartTask #CharTask #MeetObject
#	#ObjectTask #StoppingTask #MeetChar $ChangedDesc
#	{WALK:#Rooms_#Times}
#v3.90	WALK
#	#NumStops BLoop #StartTask #CharTask #MeetObject
#	#ObjectTask #StoppingTask ZMeetChar $ChangedDesc
#	{WALK:#Rooms_#Times}
#v3.80	WALK
#	#NumStops BLoop #StartTask #CharTask #MeetObject
#	?!#MeetObject=0:|V380_WALK:_MeetObject_|
#	#ObjectTask ZMeetChar ZStoppingTask EChangedDesc
#	{WALK:#Rooms_#Times}
}
##Analyzing
#Convert the text to uniform name that can be used in I7
sub uniformName($) {
	my $text	= shift;
	return ''	unless defined $text;
	$text		=~ s/[-_\"\[\]\\%]//g;		# Trim all unwanted characters
	$text		=~ s/\s+/ /g;				# Convert all whitespace to spaces, and trim multiples
	$text		=~ s/^\s+|\s+$//g;			# Trim leading/trailing whitespace
	return $text;
}
#Convert the text to a safe variable name
sub variableName($) {
	my $text	= shift;
	return ''	unless defined $text;
	$text		= lc($text);				# Lower case
	$text		=~ s/[-_\'"*\[\]\\%]//g;	# Trim all unwanted characters
	$text		=~ s/\s+/ /g;				# Convert all whitespace to spaces, and trim multiples
	$text		=~ s/^\s+|\s+$//g;			# Trim leading/trailing whitespace
	$text		=~ s/ (.)/uc($1)/ge;		# Remove spaces, capitalizing the next letter
	return $text;
}
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
sub translate(){
	#Generate translation names
	print $File_Log "Generating names:\n";
	generateNames();
	#Print object mapping tables
	print $File_Log "Static Object IDs:\n";
	for my $id (1 .. $#ObjectStatic){
		print $File_Log "\t$id -> $ObjectStatic[$id] (".nameObject($ObjectStatic[$id]).")\n";
	}
	print $File_Log "Portable Object IDs:\n";
	for my $id (1 .. $#ObjectPortable){
		print $File_Log "\t$id -> $ObjectPortable[$id] (".nameObject($ObjectPortable[$id]).")\n";
	}
	print $File_Log "Holder Object IDs:\n";
	for my $id (0 .. $#ObjectHolder){
		print $File_Log "\t$id -> $ObjectHolder[$id] (".nameObject($ObjectHolder[$id]).")\n";
	}
}
#Generate translation names, printing to mapping file if asked for
sub generateNames(){
	#Rooms
	$Translate_Room[0]	= 'nowhere'				unless defined $Translate_Room[0];
	for my $room (1 .. $#Rooms){
		my $title				= uniformName($Rooms[$room]{Title});
		$Translate_Room[$room]	= $title		unless defined $Translate_Room[$room];
	}
	#TODO: RoomGroups
	#Objects
	$Translate_Object[0]		= 'nothing'		unless defined $Translate_Object[0];
	for my $object (1 .. $#Objects){
		my $name					= variableName("$Objects[$object]{Prefix} $Objects[$object]{Short}");
		$Objects[$object]{Name}		= $name;
		$Translate_Object[$object]	= $name		unless defined $Translate_Object[$object];
	}
	#Tasks
	for my $task (1 .. $#Tasks){
		my @commands	= @{ $Tasks[$task]{Commands} };
		my $name		= '';
		$name			= variableName($Translate_Task[$task])	if defined $Translate_Task[$task];
		foreach my $line (@commands){
			$line	= variableName($line);
			$name	= $line			if length($line) > length($name);
		}
		$Tasks[$task]{Name}		= $name;
		$Translate_Task[$task]	= $name			unless defined $Translate_Task[$task];
	}
	#Persons
	$Translate_Person[0]		= 'player'	unless defined $Translate_Person[0];
	for my $person (1 .. $#Persons){
		my $name					= uniformName($Persons[$person]{Prefix}.' '.$Persons[$person]{Name});
		$Translate_Person[$person]	= $name		unless defined $Translate_Person[$person];
	}
	#Variables
	for my $variable (1 .. $#Variables){
		my $name						= uniformName($Variables[$variable]{Name});
		$Translate_Variable[$variable]	= $name	unless defined $Translate_Variable[$variable];
	}

}
#Write the symbol mapping file - TODO this must be revamped, as the new generateNames sub *WILL* ensure all translations are set
sub writeMapping(){
	#Rooms
	print $File_Mapping "#\t$#Rooms Rooms:\n";
	for my $room (0 .. $#Rooms){
		my $title				= uniformName($Rooms[$room]{Title});
		print $File_Mapping "#Room$room\t = 'TODO'\t# Name: $title\n"	unless	defined $Translate_Room[$room];
		print $File_Mapping "Room$room\t = '$Translate_Room[$room]'\n"	if		defined $Translate_Room[$room];
	}
	#TODO: RoomGroups
	#Objects
	print $File_Mapping "#\t$#Objects Objects:\n";
	for my $object (0 .. $#Objects){
		my $name	= $Objects[$object]{Name};
		print $File_Mapping "#Object$object\t = '$name'\n"						unless	defined $Translate_Object[$object];
		print $File_Mapping "Object$object\t = '$Translate_Object[$object]'\n"	if		defined $Translate_Object[$object];
	}
	#Tasks
	print $File_Mapping "#\t$#Tasks Tasks:\n";
	for my $task (1 .. $#Tasks){
		my $name				= $Tasks[$task]{Name};
		print $File_Mapping "#Task$task\t = 'TODO'\t# Name: $name\n"	unless	defined $Translate_Task[$task];
		print $File_Mapping "Task$task\t = '$Translate_Task[$task]'\n"	if 		defined $Translate_Task[$task];
	}
	#Persons
	print $File_Mapping "#\t$#Persons Persons:\n";
	for my $person (0 .. $#Persons){
		my $name				= uniformName($Persons[$person]{Prefix}.' '.$Persons[$person]{Name});
		print $File_Mapping "#Person$person\t = 'TODO'\t# Name: $name\n"		unless	defined $Translate_Person[$person];
		print $File_Mapping "Person$person\t = '$Translate_Person[$person]'\n"	if		defined $Translate_Person[$person];
		$Translate_Person[$person]	= $name										unless defined $Translate_Person[$person];
	}
	#Variables
	print $File_Mapping "#\t$#Variables Variables:\n" if defined $Option_Generate;
	for my $variable (1 .. $#Variables){
		my $name					= uniformName($Variables[$variable]{Name});
		print $File_Mapping "#Variable$variable\t = 'TODO'\t# Name: $name\n"		if defined $Option_Generate && not defined $Translate_Variable[$variable];
		print $File_Mapping "Variable$variable\t = '$Translate_Variable[$variable]'\n"	if defined $Option_Generate && defined $Translate_Variable[$variable];
	}
}
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
}
#Analyze a room
sub analyzeRoom($){
	my $room		= shift;
	my $exits		= @{ $Rooms[$room]{Exits} };
	#Interpret the exit restrictions; sclibrar.lib_can_go
	for my $direction (0 .. $#Compass_Direction){
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
			my $objectID	= $ObjectOpenable[$var1];
			my $object		= nameTask($objectID);
			# ExpectedState		TODO
			my $state		= "UNKNOWN STATE $var2";
			#Assemble full text
			$text	= "if $object is $state";
		}
		$Rooms[$room]{Exits}[$direction]{Restriction}	= $text if defined $text;
	}
}
#Analyze an object
sub analyzeObject($){
	my $object			= shift;
	#An object can be one of several types, depending on properties. We make this evaluation only once.
	my $object_type;
	#If object is in multiple rooms, it must be a backdrop (even if it is a container in ADRIFT)
	if		($Objects[$object]{WhereType} eq 2
		or	 $Objects[$object]{WhereType} eq 3){
		$object_type	= 'backdrop';
	}
	#If object is classified as a body part, then we go with that
	elsif	($Objects[$object]{WhereType} eq 4){
		$object_type	= 'body part';
	}
	#Store what we've calculated
	$Objects[$object]{Type}		= $object_type;
}
#Analyze a task, taking a guess at what it's meant to do and find a suiting name for it
sub analyzeTask($){
	my $task			= shift;
	my $locations		= @{ $Tasks[$task]{Where} };
	my $restrictions	= @{ $Tasks[$task]{Restrictions} };
	my $actions			= @{ $Tasks[$task]{Actions} };
	my @commands		= @{ $Tasks[$task]{Commands} };
	#Interpret the restrictions of the task; screstrs.restr_pass_task_restriction (pp21-22)
	for my $id (0 .. $restrictions - 1){
		my %restriction	= %{ $Tasks[$task]{Restrictions}[$id] };
		my $text;
		#ObjectLocation: ObjectID, Condition, Location;
		if($restriction{Type} eq 0){
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
			if ($var1 > 2 && $var1 <= (2 + @ObjectPortable)) {
				my $objectID	= $ObjectPortable[$var1-2];
				$object			= nameObject($objectID);
				$ObjectTasks[$objectID][$task]++;
			}
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
			#Location; depending on condition
			my $location	= "UNKNOWN LOCATION $var3";
			# 0: Room
			if ($var2 % 6 eq 0) {
				my $roomID		= $var3;
				$location		= nameRoom($roomID);
				$RoomTasks[$roomID][$task]++;
			}
			# 1-3: Person
			if ($var2 % 6 >= 1 && $var2 % 6 <= 3) {
				# 0: The player
				$location		= 'the player'		if $var3 eq 0;
				# 1: The referenced person
				$location		= 'referenced'		if $var3 eq 1;
				# 2+: PersonID
				if ($var3 > 1 && $var3 <= (1 + @Persons)){
					my $personID	= $var3-1;
					$location		= 'by '.namePerson($personID);
					$TaskPersons[$task][$personID]++;
				}
			}
			#4: Container
			if ($var2 % 6 eq 4) {
				my $objectID	= $ObjectContainer[$var3];
				$location		= nameObject($objectID);
				$ObjectTasks[$objectID][$task]++;
			}
			#5: Supporter
			if ($var2 % 6 eq 5) {
				my $objectID	= $ObjectSurface[$var3];
				$location		= nameObject($objectID);
				$ObjectTasks[$objectID][$task]++;
			}
			#Assemble the full text
			$text	= "Unless $object is $condition $location";
		}
		#ObjectState:	ObjectID, State		TODO
		if($restriction{Type} eq 1){
			my $var1	= $restriction{Var1};
			my $var2	= $restriction{Var2};
			#ObjectID
			my $object		= "UNKNOWN OBJECT $var1";
			# 0: Referenced
			$object			= 'referenced object'		if $var1 eq 0;
			# 1+: Openable ObjectID
			if ($var1 > 0 && $var1 <= @ObjectOpenable) {
				my $objectID	= $ObjectOpenable[$var1];
				$object			= nameObject($objectID);
				$ObjectTasks[$objectID][$task]++;
			}
			#State
			my $state		= "UNKNOWN STATE $var2";
			#Assemble the full text
			$text	= "Unless $object is $state";
		}
		#TaskState:		Task, State
		if($restriction{Type} eq 2){
			my $var1	= $restriction{Var1};
			my $var2	= $restriction{Var2};
			#TaskID
			my $task		= "UNKNOWN TASK $var1";
			# 0: Referenced
			$task			= 'all tasks'		if $var1 eq 0;
			# 1+: TaskID
			if ($var1 > 0 && $var1 <= @Tasks) {
				my $taskID	= $var1;
				$task		= nameTask($taskID)
				#TODO Add task-task relation
			}
			#State
			my $state		= "UNKNOWN STATE $var2";
			# 0: Performed
			$state			= 'performed'		if $var2 eq 0;
			# 1: Not Performed
			$state			= 'not performed'	if $var2 eq 1;
			#Assemble the full text
			$text	= "Unless $task is $state";
		}
		#Person:		PersonID, Condition, Location
		if($restriction{Type} eq 3){
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
			if ($var1 > 1 && $var1 <= (1 + @Persons)){
				my $personID	= $var1-1;
				$person			= namePerson($personID);
				$TaskPersons[$task][$personID]++;
			}
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
			#Location; depending on condition
			my $location	= "UNKNOWN LOCATION $var3";
			#0-1: Person
			if ($var2 eq 0 or $var2 eq 1) {
				# 0=Player
				$location		= 'the player'			if $var3 eq 0;
				# 1=Referenced
				$location		= 'referenced'			if $var3 eq 1;
				# 2+: PersonID
				if ($var3 > 1 && $var3 <= (1 + @Persons)) {
					my $personID	= $var3-1;
					$location		= namePerson($personID);
					$TaskPersons[$task][$personID]++;
				}
			}
			#2-3: Blank
			if ($var2 eq 2 or $var2 eq 3) {
				$location		= '';
			}
			#4-5: Sit/Standable
			if ($var2 eq 4 or $var2 eq 5) {
				my $objectID	= $ObjectSitStandable[$var3];
				$location		= nameObject($objectID);
				$ObjectTasks[$objectID][$task]++;
			}
			#6: Lieable
			if ($var2 eq 6) {
				my $objectID	= $ObjectLieable[$var3];
				$location		= nameObject($objectID);
				$ObjectTasks[$objectID][$task]++;
			}
			#7: Gender
			if ($var2 eq 7) {
				$location		= nameGender($var3);
			}
			#Assemble the full text
			$text	= "Unless $person is $condition $location";
		}
		#Variable:		VariableID, Operator, Number, Text
		if($restriction{Type} eq 4){
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
			if ($var1 > 1 && $var1 <= (1 + @Variables)) {
				my $variableID	= $var1-1;
				$variable		= nameVariable($variableID);
				$numeric		= 1 if $Variables[$variableID]{Type} eq 0;
				$TaskVariables[$task][$variableID]++;
			}
			#Operator determines comparator
			my $operator	= "UNKNOWN OPERATOR $var2";
			my $comparator	= "UNKNOWN COMPARATOR $var2";
			if ($numeric) {	# Numeric variables
				# 0,10: <
				$operator		= '<'	if $var2 % 10 eq 0;
				# 1,11: <
				$operator		= '<='	if $var2 % 10 eq 1;
				# 2,12: ==
				$operator		= '=='	if $var2 % 10 eq 2;
				# 3,13: >=
				$operator		= '>='	if $var2 % 10 eq 3;
				# 4,14: >
				$operator		= '>'	if $var2 % 10 eq 4;
				# 5,15: !=
				$operator		= '!='	if $var2 % 10 eq 5;
				#Direct value comparison
				if ($var2 < 10){
					$comparator		= $var3;
				}
				#Reference comparison
				else {
					$comparator		= 'referenced number'	if $var3 eq 0;
					if ($var3 > 0 && $var3 <= @Variables) {
						my $variableID	= $var3;
						$comparator		= nameVariable($variableID);
						$TaskVariables[$task][$variableID]++;
					}
				}
			}
			else {	# String variables
				$comparator	= $var4;
				# 0: ==
				$operator	= '=='	if $var2 eq 0;
				# 1: !=
				$operator	= '!='	if $var2 eq 1;
			}
			#Assemble the full text
			$text	= "Unless $variable $operator $comparator";
			#Formula	TODO
			$text	.= " UNKNOWN FORMULA $var4"	unless $var4 eq '';
		}
		$Tasks[$task]{Restrictions}[$id]{Condition}		= $text if defined $text;
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
			if ($var1 > 2 && $var1 <= (2 + @ObjectPortable)) {
				my $objectID	= $ObjectPortable[$var1-2];
				$object			= nameObject($objectID);
				$ObjectTasks[$objectID][$task]++;
			}
			#DestinationType determines the value of the Location
			my $destination	= "UNKNOWN DESTINATION $var2 TO $var3";
			# 0: Room
			if ($var2 eq 0) {
				# 0: Nowhere
				$destination	= 'off stage'	if $var3 eq 0;
				# 1+: Room
				if ($var3 > 0 && $var3 <= @Rooms) {
					my $roomID		= $var3;
					$destination	= 'to '.nameRoom($roomID);
					$RoomTasks[$roomID][$task]++;
				}
			}
			# 1: RoomGroup
			if ($var2 eq 1) {
				my $groupID		= $var3;
				$destination	= 'to random room in '.nameGroup($groupID);
				$TaskGroups[$task][$groupID]++;
			}
			# 2: Container
			if ($var2 eq 2) {
				my $objectID	= $ObjectContainer[$var3];
				$destination	= 'inside '.nameObject($objectID);
				$ObjectTasks[$objectID][$task]++;
			}				
			# 3: Supporter
			if ($var2 eq 3) {
				my $objectID	= $ObjectSurface[$var3];
				$destination	= 'on top of '.nameObject($objectID);
				$ObjectTasks[$objectID][$task]++;
			}
			# 4: Carried by Person
			if ($var2 eq 4) {
				my $target	= "UNKNOWN TARGET $var3";
				# 0: The player
				$target		= 'the player'			if $var3 eq 0;
				# 1: Referenced Person
				$target		= 'referenced person'	if $var3 eq 1;
				# 2+: Person
				if ($var3 > 1 && $var3 <= 1 + @Persons) {
					my $personID	= $var3 - 1;
					$target			= namePerson($personID);
					$TaskPersons[$task][$personID]++;
				}
				$destination	= "to $target (carried)";
			}
			# 5: Worn by Person
			if ($var2 eq 5) {
				my $target	= "UNKNOWN TARGET $var3";
				# 0: The player
				$target		= 'the player'			if $var3 eq 0;
				# 1: Referenced Person
				$target		= 'referenced person'	if $var3 eq 1;
				# 2+: Person
				if ($var3 > 1 && $var3 <= 1 + @Persons) {
					my $personID	= $var3 - 1;
					$target			= namePerson($personID);
					$TaskPersons[$task][$personID]++;
				}
				$destination	= "to $target (worn)";
			}
			# 6: Location of Person
			if ($var2 eq 6) {
				my $target	= "UNKNOWN TARGET $var3";
				# 0: The player
				$target		= 'the player'			if $var3 eq 0;
				# 1: Referenced Person
				$target		= 'referenced person'	if $var3 eq 1;
				# 2+: Person
				if ($var3 > 1 && $var3 <= 1 + @Persons) {
					my $personID	= $var3 - 1;
					$target			= namePerson($personID);
					$TaskPersons[$task][$personID]++;
				}
				$destination	= "to location of $target";
			}
			#Assemble the full text
			$text	= "Move $object $destination";
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
			if ($var1 > 1 && $var1 <= (1 + @Persons)) {
				my $personID	= $var1-1;
				$person			= namePerson($personID);
				$TaskPersons[$task][$personID]++;
			}
			#DestinationType determines the value of the Location
			my $destination	= "UNKNOWN DESTINATION $var2 TO $var3";
			# 0: Room
			if ($var2 eq 0) {
				# 0: Nowhere
				$destination	= 'off stage'	if $var3 eq 0;
				# 1+: Room
				if ($var3 > 0 && $var3 <= @Rooms) {
					my $roomID		= $var3;
					$destination	= 'to '.nameRoom($roomID);
					$RoomTasks[$roomID][$task]++;
				}
			}
			# 1: RoomGroup
			if ($var2 eq 1) {
				my $groupID		= $var3;
				$destination	= 'to random room in '.nameGroup($groupID);
				$TaskGroups[$task][$groupID]++;
			}
			# 2: Location of Person
			if ($var2 eq 2) {
				my $target	= "UNKNOWN TARGET $var3";
				# 0: The player
				$target		= 'the player'			if $var3 eq 0;
				# 1: Referenced Person
				$target		= 'referenced person'	if $var3 eq 1;
				# 2+: Person
				if ($var3 > 1 && $var3 <= 1 + @Persons) {
					my $personID	= $var3 - 1;
					$target			= namePerson($personID);
					$TaskPersons[$task][$personID]++;
				}
				$destination	= "to location of $target";
			}
			# 3: Standing on
			if ($var2 eq 3) {
				my $objectID	= $ObjectSitStandable[$var3];
				$destination	= 'standing on '.nameObject($objectID);
				$ObjectTasks[$objectID][$task]++;
			}
			# 4: Sitting on
			if ($var2 eq 4) {
				my $objectID	= $ObjectSitStandable[$var3];
				$destination	= 'sitting on '.nameObject($objectID);
				$ObjectTasks[$objectID][$task]++;
			}
			# 5: Lying on
			if ($var2 eq 5) {
				my $objectID	= $ObjectLieable[$var3];
				$destination	= 'lying on '.nameObject($objectID);
				$ObjectTasks[$objectID][$task]++;
			}			
			#Assemble the full text
			$text	= "Move $person $destination";
		}
		#ObjectState:	ObjectID, State		TODO
		if($type eq 2){
			my $var1	= $action{Var1};
			my $var2	= $action{Var2};
			#ObjectID
			my $object		= "UNKNOWN OBJECT $var1";
			# 0: Referenced
			$object			= 'referenced object'		if $var1 eq 0;
			# 1+: Openable ObjectID
			if ($var1 > 0 && $var1 <= @ObjectOpenable) {
				my $objectID	= $ObjectOpenable[$var1];
				$object			= nameObject($objectID);
				$ObjectTasks[$objectID][$task]++;
			}
			#State
			my $state		= "UNKNOWN STATE $var2";
			#TODO VERIFY 0=open 1=closed?
			#Assemble the full text
			$text	= "Now $object is $state";
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
			if ($var1 >= 0 && $var1 < @Variables) {
				my $variableID	= $var1+1;
				$variable		= nameVariable($variableID);
				$numeric		= 1 if $Variables[$variableID]{Type} eq 0;
				$TaskVariables[$task][$variableID]++;
			}
			#Operator determines value
			my $operator	= "UNKNOWN OPERATOR $var2";
			my $value		= "UNKNOWN VALUE $var3:$var5:$expr";
			if ($numeric) {	#Numeric variable
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
				}
			}
			else {	#String variable
				# 0: assign
				if ($var2 eq 0){
					$operator	= 'to';
					$value		= $expr;
				}
				# 1: Referenced value
				if ($var2 eq 1){
					$operator	= 'to';
					$value		= 'referenced value';
				}
				# 2: to formula
				if ($var2 eq 2){
					$operator	= 'to';
					$value		= $expr;
				}
			}
			
			$text		= "Change $variable $operator $value";
		}
		#Score:			Modifier
		if($type eq 4){
			$text			= "Modify score by $action{Var1}";
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
			my $task		= "UNKNOWN TASK $var2";
			#0+: Task ID
			if ($var2 >= 0 && $var2 < @Tasks) {
				my $taskID	= $var2 + 1;
				$task		= nameTask($taskID);
				#TODO: Add task-task reference
			}
			$text		= "$direction $task";
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
			#Assemble final text
			$text		= "End the game in $ending";
		}
		#Battle:		TODO
		if($type eq 7){
			my $var1	= $action{Var1};
			my $var2	= $action{Var2};
			my $var3	= $action{Var3};
			#Assemble final text
			$text		= "UNKNOWN BATTLE $var1 $var2 $var3";
		}
		$Tasks[$task]{Actions}[$id]{Text}	= $text if defined $text;
	}
	#To decipher what the task is meant to do, we first check if we're given a translation that describes it.
	my $task_type;
	my $task_name;
	($task_type, $task_name) = analyzeTaskType($Translate_Task[$task])	if defined $Translate_Task[$task];
	#Otherwise we have to parse through all the commands to see if we find a fit.
	foreach my $line (@commands){
		last if defined $task_type;
		($task_type, $task_name) = analyzeTaskType($line);
	}
	#If we're unable to decipher, we can generate a name from the longest command
	unless (defined $task_name){
		$task_name	= '';
		$task_name	= variableName($Translate_Task[$task])	if defined $Translate_Task[$task];
		foreach my $line (@commands){
			$line		= variableName($line);
			$task_name	= $line			if length($line) > length($task_name);
		}
	}
	$Tasks[$task]{Name}		= $task_name if defined $task_name;
	$Tasks[$task]{Type}		= $task_type if defined $task_type;
	print $File_Log "\t".nameTask($task)." ($task)"	if defined $Option_Verbose;
	print $File_Log " -> $task_name"				if defined $Option_Verbose && $task_name;
	print $File_Log "\n"							if defined $Option_Verbose;
	foreach my $line (@commands){ print $File_Log "\t\t$line\n"	if defined $Option_Verbose }
}
sub analyzeTaskType($){
	my $line	= shift;
	#CASE 1: The task simulates examining a body part.
	#We expect this to take the following form:
	#	x/examine [PERSON]('s) [BODYPART]
	if($line =~ m/^(x|examine) ([a-z]*)('s)? (.*)$/i ){
		my $action		= 'examine';
		my $owner		= $2;
		my $bodypart	= $4;
		return (1, "$action $owner $bodypart");
	}
	#CASE 2: The task is an erotic action on a body part.
	#We expect this to take the following form:
	#	ACTION(ing) [PERSON]('s) [BODYPART]
	if($line =~ m/^(touch|rubb?|tickle?|spank|pinch|lick|bite?|fuck|kiss|suck)(ing)? ([a-z]*)('s)? (.*)$/i ){
		my $action		= $1 . 'ing';
		my $owner		= $3;
		my $bodypart	= $5;
		return (2, "$action $owner $bodypart");
	}
	return (undef, undef);
}
##Output
sub printSource(){
	generateXML();			# Generate XML based on bytecode
	generateInform();		# Generate equivalent Inform-source
}
#Generate XML Output
sub generateXML(){
	print $File_Log "Printing XML File\n";
	writeXMLElementOpen('Story');
	generateXMLGlobals();
	generateXMLOptions();
	generateXMLRooms();
	generateXMLObjects();
	generateXMLTasks();
	generateXMLPersons();
	#generateXMLEvents();
	generateXMLVariables();
	writeXMLElementClose('Story');
}
#Generate the story part of the XML output
sub generateXMLGlobals(){
	writeXMLElementOpen('Globals');
	writeXMLElement('Title',			$Game{Title});
	writeXMLElement('Author',			$Game{Author});
	writeXMLElement('Start_Location',	$Game{Start});
	writeXMLElement('WaitingTurns',		$Game{WaitTurns});
	writeXMLElement('Perspective',		$Game{Perspective});
	writeXMLElement('Compiled',			$Game{CompileDate});
	writeXMLElement('Decompiler',		$Decompiler_Version);
	writeXMLElement('Decompiled',		''.localtime);
	writeXMLElementClose('Globals');
}
#Generate the options part of the XML output, based on game flags
sub generateXMLOptions(){
	writeXMLElementOpen('Options');
	writeXMLElement('Battles')			if $Game{EnableBattle};
	writeXMLElement('NoMap')			if $Game{DisableMap};
	writeXMLElement('Sound')			if $Game{EnableSound};
	writeXMLElement('Graphics')			if $Game{EnableGraphics};
	writeXMLElement('ExpandedCompass')	if $Game{ExpandedCompass};
	writeXMLElement('InitialLook')		if $Game{InitialLook};
	writeXMLElement('ShowExits')		if $Game{ShowExits};
	writeXMLElementClose('Options');
}
#Generate the rooms part of the XML output
sub generateXMLRooms(){
	print $File_XML "<!-- $#Rooms rooms -->\n";
	writeXMLElementOpen('Rooms')	if $#Rooms;
	for my $room (1 .. $#Rooms){
		writeXMLElementOpen('Room');
		{	#Attributes
			writeXMLElementOpen('Attributes');
			writeXMLElement('ID', 		$room);
			writeXMLElement('Title', 	$Rooms[$room]{Title});
			writeXMLElement('Name', 	nameRoom($room));
			writeXMLElement('Hidden')	if $Rooms[$room]{Hidden};
			writeXMLElementClose('Attributes');
		}
		{	#Descriptions
			#TODO: Resource
			writeXMLElementOpen('Descriptions');
			#Default
			writeXMLElementOpen('Description');
			writeXMLElement('Text',	$Rooms[$room]{Description});
			writeXMLElementClose('Description');
			#v3 style alternate descriptions
			if($Rooms[$room]{AltDesc1Task}){
				writeXMLElementOpen('Description');
				writeXMLElement('Text',	$Rooms[$room]{AltDesc1});
				writeXMLElement('Task',	$Rooms[$room]{AltDesc1Task});
				writeXMLElement('Name',	nameTask($Rooms[$room]{AltDesc1Task}));
				writeXMLElementClose('Description');
			}
			if($Rooms[$room]{AltDesc2Task}){
				writeXMLElementOpen('Description');
				writeXMLElement('Text',	$Rooms[$room]{AltDesc2});
				writeXMLElement('Task',	$Rooms[$room]{AltDesc2Task});
				writeXMLElement('Name',	nameTask($Rooms[$room]{AltDesc2Task}));
				writeXMLElementClose('Description');
			}
			if($Rooms[$room]{AltDesc3Obj}){
				writeXMLElementOpen('Description');
				writeXMLElement('Text',		$Rooms[$room]{AltDesc3});
				writeXMLElement('Object',	$Rooms[$room]{AltDesc3Obj});
				writeXMLElement('Name',	nameObject( $ObjectPortable[ $Rooms[$room]{AltDesc3Obj}] ) );
				writeXMLElementClose('Description');
			}
			#v4 style alternate descriptions
			my @alternates	= ();
			@alternates		= @{ $Rooms[$room]{Alternates} } if defined $Rooms[$room]{Alternates};
			foreach my $alternate (0..$#alternates){
				writeXMLElementOpen('Description');
				writeXMLElement('M1',			$alternates[$alternate]{M1});
				writeXMLElement('Type',			$alternates[$alternate]{Type});
				#TODO: Resource1
				writeXMLElement('M2',			$alternates[$alternate]{M2});
				writeXMLElement('Var2',			$alternates[$alternate]{Var2});
				#TODO: Resource2
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
			foreach my $direction (0..$#Compass_Direction){
				my $destination	= $Rooms[$room]{Exits}[$direction]{Destination};
				if ($destination){
					writeXMLElementOpen('Exit');
					writeXMLElement('Direction',		$Compass_Direction[$direction]);
					writeXMLElement('DestinationID',	$destination);
					writeXMLElement('Destination',		nameRoom($destination));
					writeXMLElement('Restriction',		$Rooms[$room]{Exits}[$direction]{Restriction}) if defined $Rooms[$room]{Exits}[$direction]{Restriction};
					writeXMLElementClose('Exit');
				}
			}
			writeXMLElementClose('Exits');
		}
		{	#Relations
			my @task_relations	= ();
			for my $task (1..$#Tasks){ push @task_relations, $task if defined $RoomTasks[$room][$task] }
			my $relations	= @task_relations;
			writeXMLElementOpen('Relations')	if $relations;
			{	#Tasks
				writeXMLElementOpen('Tasks')		if @task_relations;
				for my $task (@task_relations) {
					writeXMLElementOpen('Task');
					writeXMLElement('ID', $task);
					writeXMLElement('Name', nameTask($task));
					writeXMLElementClose('Task');
				}
				writeXMLElementClose('Tasks')		if @task_relations;
			}
			writeXMLElementClose('Relations')	if $relations;
		}
		writeXMLElementClose('Room');
	}
	writeXMLElementClose('Rooms')	if $#Rooms;
}
#Generate the persons part of the XML output
sub generateXMLPersons(){
	print $File_XML "<!-- $#Persons persons (+ player) -->\n";
	#TODO: Add the player
	writeXMLElementOpen('Persons') if $#Persons;
	for my $person (1 .. $#Persons){
		writeXMLElementOpen('Person');
		{	#Attributes
			writeXMLElementOpen('Attributes');
			writeXMLElement('ID',			$person);
			writeXMLElement('Title',		$Persons[$person]{Name});
			writeXMLElement('Name',			namePerson($person));
			foreach my $alias ( @{$Persons[$person]{Alias} } ){
				writeXMLElement('Alias',	$alias) unless $alias eq '';
			}
			writeXMLElement('Gender',		nameGender($Persons[$person]{Gender}));
			writeXMLElement('Location_ID',	$Persons[$person]{StartRoom});
			writeXMLElement('Location',		nameRoom($Persons[$person]{StartRoom}));
			writeXMLElement('Presence',		$Persons[$person]{InRoomText});
			writeXMLElement('Entering',		$Persons[$person]{EnterText});
			writeXMLElement('Leaving',		$Persons[$person]{ExitText});
			writeXMLElementClose('Attributes');
		}
		#TODO: BattleStats
		{	#Descriptions
			#TODO: Resource
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
			my @task_relations	= ();
			for my $task (1..$#Tasks){ push @task_relations, $task if defined $TaskPersons[$task][$person] }
			my $relations	= @task_relations;
			writeXMLElementOpen('Relations')	if $relations;
			{	#Tasks
				writeXMLElementOpen('Tasks')		if @task_relations;
				for my $task (@task_relations) {
					writeXMLElementOpen('Task');
					writeXMLElement('ID', $task);
					writeXMLElement('Name', nameTask($task));
					writeXMLElementClose('Task');
				}
				writeXMLElementClose('Tasks')		if @task_relations;
			}
			writeXMLElementClose('Relations')	if $relations;
		}
		writeXMLElementClose('Person');
	}
	writeXMLElementClose('Persons')	if $#Persons;
}
#Generate the objects part of the XML output
sub generateXMLObjects(){
	print $File_XML "<!-- $#Objects objects -->\n";
	writeXMLElementOpen('Objects') if $#Objects;
	for my $object (1 .. $#Objects){
		writeXMLElementOpen('Object');
		{	#Attributes
			writeXMLElementOpen('Attributes');
			writeXMLElement('ID',			$object);
			writeXMLElement('Prefix',		$Objects[$object]{Prefix});
			writeXMLElement('Short',		$Objects[$object]{Short});
			writeXMLElement('Name',			nameObject($object));
			foreach my $alias ( @{$Objects[$object]{Alias} } ){
				writeXMLElement('Alias',	$alias) unless $alias eq '';
			}
			writeXMLElement('Type',			$Objects[$object]{Type})		if defined $Objects[$object]{Type};
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
			writeXMLElement('Key',			$Objects[$object]{Key})			if defined $Objects[$object]{Key};
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
			writeXMLElementClose('Object');
		}
		{	#Relations
			my @task_relations	= ();
			for my $task (1..$#Tasks){ push @task_relations, $task if defined $ObjectTasks[$object][$task] }
			my $relations	= @task_relations;
			writeXMLElementOpen('Relations')	if $relations;
			{	#Tasks
				writeXMLElementOpen('Tasks')		if @task_relations;
				for my $task (@task_relations) {
					writeXMLElementOpen('Task');
					writeXMLElement('ID', $task);
					writeXMLElement('Name', nameTask($task));
					writeXMLElementClose('Task');
				}
				writeXMLElementClose('Tasks')		if @task_relations;
			}
			writeXMLElementClose('Relations')	if $relations;
		}
	}
	writeXMLElementClose('Objects') if $#Objects;
}
#Generate the tasks part of the XML output
sub generateXMLTasks(){
	print $File_XML "<!-- $#Tasks tasks -->\n";
	writeXMLElementOpen('Tasks') if $#Tasks;
	for my $task (1 .. $#Tasks){
		writeXMLElementOpen('Task');
		{	#Attributes
			writeXMLElementOpen('Attributes');
			writeXMLElement('ID',			$task);
			writeXMLElement('Name',			nameTask($task));
			writeXMLElement('Title',		$Tasks[$task]{Name});
			writeXMLElement('Type',			$Tasks[$task]{Type});
			writeXMLElement('Repeatable')	if $Tasks[$task]{Repeatable};
			writeXMLElement('Reversible')	if $Tasks[$task]{Reversible};
			writeXMLElement('ShowRoomDesc',	nameRoom($Tasks[$task]{ShowRoomDesc})) unless $Tasks[$task]{ShowRoomDesc} eq 0;
			writeXMLElementClose('Attributes');
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
			my @room_relations	= ();
			for my $room (1..$#Rooms){ push @room_relations, $room if defined $RoomTasks[$room][$task] }
			my @object_relations	= ();
			for my $object (1..$#Objects){ push @object_relations, $object if defined $ObjectTasks[$object][$task] }
			my @person_relations	= ();
			for my $person (1..$#Persons){ push @person_relations, $person if defined $TaskPersons[$task][$person] }
			my @variable_relations	= ();
			for my $variable (1..$#Variables){ push @variable_relations, $variable if defined $TaskVariables[$task][$variable] }
			
			my $relations	= @room_relations + @object_relations + @person_relations + @variable_relations;
			writeXMLElementOpen('Relations')	if $relations;
			{	#Rooms
				writeXMLElementOpen('Rooms')		if @room_relations;
				for my $room (@room_relations) {
					writeXMLElementOpen('Room');
					writeXMLElement('ID', $room);
					writeXMLElement('Name', nameRoom($room));
					writeXMLElementClose('Room');
				}
				writeXMLElementClose('Rooms')		if @room_relations;
			}
			{	#Objects
				writeXMLElementOpen('Objects')		if @object_relations;
				for my $object (@object_relations) {
					writeXMLElementOpen('Object');
					writeXMLElement('ID', $object);
					writeXMLElement('Name', nameObject($object));
					writeXMLElementClose('Object');
				}
				writeXMLElementClose('Objects')		if @object_relations;
			}
			{	#Persons
				writeXMLElementOpen('Persons')		if @person_relations;
				for my $person (@person_relations) {
					writeXMLElementOpen('Person');
					writeXMLElement('ID', $person);
					writeXMLElement('Name', namePerson($person));
					writeXMLElementClose('Person');
				}
				writeXMLElementClose('Persons')		if @person_relations;
			}
			{	#Variables
				writeXMLElementOpen('Variables')		if @variable_relations;
				for my $variable (@variable_relations) {
					writeXMLElementOpen('Variable');
					writeXMLElement('ID', $variable);
					writeXMLElement('Name', nameVariable($variable));
					writeXMLElementClose('Variable');
				}
				writeXMLElementClose('Variables')		if @variable_relations;
			}
			writeXMLElementClose('Relations')	if $relations;
		}
		writeXMLElementClose('Task');
	}
	writeXMLElementClose('Tasks') if $#Tasks;
}
#Generate the tasks part of the XML output
sub generateXMLVariables(){
	print $File_XML "<!-- $#Variables tasks -->\n";
	writeXMLElementOpen('Variables') if $#Variables;
	for my $variable (1 .. $#Variables){
		writeXMLElementOpen('Variable');
		{	#Attributes
			writeXMLElementOpen('Attributes');
			writeXMLElement('ID',			$variable);
			writeXMLElement('Name',			$Variables[$variable]{Name});
			writeXMLElement('Type',			$Variables[$variable]{Type});
			writeXMLElement('Value',		$Variables[$variable]{Value});
			writeXMLElementClose('Attributes');
		}
		{	#Relations
			my @task_relations	= ();
			for my $task (1..$#Tasks){ push @task_relations, $task if defined $TaskVariables[$task][$variable] }
			my $relations	= @task_relations;
			writeXMLElementOpen('Relations')	if $relations;
			{	#Tasks
				writeXMLElementOpen('Tasks')		if @task_relations;
				for my $task (@task_relations) {
					writeXMLElementOpen('Task');
					writeXMLElement('ID', $task);
					writeXMLElement('Name', nameTask($task));
					writeXMLElementClose('Task');
				}
				writeXMLElementClose('Tasks')		if @task_relations;
			}
			writeXMLElementClose('Relations')	if $relations;
		}
		writeXMLElementClose('Variable');
	}
	writeXMLElementClose('Variables');
}

#Write a one line XML element with the specified title and content.
sub writeXMLElement($;$){
	my $title	= shift;
	my $content	= shift;
	undef $content	if defined $content && $content eq '';
	if (defined $content){
		#Convert brackets
		$content =~ s/</\[/g;
		$content =~ s/>/\]/g;
		#Indentation
		$File_XML_Indent++;
		foreach (1..$File_XML_Indent) { print $File_XML "\t" }
		#Write content wrapped in element
		print $File_XML "<$title>";
		print $File_XML $content;
		print $File_XML "</$title>\n";
		$File_XML_Indent--;
	}
	else{
		writeXMLElementEmpty($title);
	}
}
sub writeXMLElementEmpty($){
	my $title	= shift;
	$File_XML_Indent++;
	foreach (1..$File_XML_Indent) { print $File_XML "\t" }
	print $File_XML "<$title />\n";
	$File_XML_Indent--;
}
sub writeXMLElementOpen($){
	my $title	= shift;
	$File_XML_Indent++;
	foreach (1..$File_XML_Indent) { print $File_XML "\t" }
	print $File_XML "<$title>\n";
}
sub writeXMLElementClose($;$){
	my $title	= shift;
	foreach (1..$File_XML_Indent) { print $File_XML "\t" }
	print $File_XML "</$title>\n";
	$File_XML_Indent--;
}

#Generate Natural Inform output
sub generateInform(){
	print $File_Log "Printing Natural Inform File\n";
	generateInformIntro();
	#Start off with the first Volume
	print $File_Inform "\nVolume 1 - Act I\n";
	generateInformLocations();
	generateInformInhabitants();
	generateInformMechanics();
	generateInformChronology();
}
#Generate the introductionary setup of the Inform file
sub generateInformIntro(){
	#Title and author from input file
	print $File_Inform "\"$Game{Title}\" by $Game{Author}\n";
	#Write setup section
	print $File_Inform "\nVolume 0 - Setup\n\n";
	#Default import and options
	print $File_Inform "Use American dialect, full-length room descriptions, and the serial comma.\n";
	print $File_Inform "Use unabbreviated object names.\n";
	print $File_Inform "Use consensual persuasion. [Defer persuasion to consent for the actions that require consent.]\n\n";
	print $File_Inform "Include Directionality by Fictitious Frode.\n";
	print $File_Inform "Include Erotic Storytelling by Fictitious Frode.\n";
	print $File_Inform "Include Simple Conversations by Fictitious Frode.\n";
	#Titlepage
	print $File_Inform "\nBook 0.1 - Titlepage\n";
	#Metadata, partly from input file
	print $File_Inform "\nPart 0.1.1 - Metadata\n\n";
	print $File_Inform "The story creation year is ".substr($Game{CompileDate}, -4).".\n";
	print $File_Inform "The story genre is \"Erotica\".\n";
	print $File_Inform "The story headline is \"Decompiled $FileName_Compiled (ADRIFT v$Gamefile_Version) by v$Decompiler_Version\".\n";
	print $File_Inform "The story description is \"A short introduction giving the premise of the story. Will be used in the out-of-game titlecard.\"\n";
	print $File_Inform "The release number is 0.\n";
	#Contents
	print $File_Inform "\nPart 0.1.2 - Contents\n\n";
	print $File_Inform "[The story contents are based on guesswork and should be manually updated. TODO]\n";
	#Dramatis Personae
	print $File_Inform "\nPart 0.1.3 - Dramatis Personae\n\n";
	print $File_Inform "[Defining the actors taking part in the story.]\n";
	#TODO: The player
	for my $person (1 .. $#Persons){
		print $File_Inform namePerson($person)." is a ".nameGender($Persons[$person]{Gender});
		print $File_Inform ".\n" 													unless	$Persons[$person]{StartRoom};
		print $File_Inform " in ". nameRoom($Persons[$person]{StartRoom}) .".\n"	if		$Persons[$person]{StartRoom};
	}
	#Dramatis Personae
	print $File_Inform "\nPart 0.1.4 - Conversation Subjects\n\n";
	print $File_Inform "[Defining the general conversation subjects relevant to the story.]\n";
	#TODO - For each topic identified by the analysis, print the definition here
	#Declarations
	print $File_Inform "\nBook 0.2 - Declarations\n";
	#Body Parts
	print $File_Inform "\nPart 0.2.1 - Body Part Creation\n\n";
	#TODO - For each body part type identified by the analysis, print the definition here
	#Custom properties
	print $File_Inform "\nPart 0.2.2 - Custom Properties\n\n";
	print $File_Inform "[Any story-wide custom properties should go here.]\n";
	#Quality of Life statements
	print $File_Inform "\nBook 0.3 - A Helping Hand\n";
	#Text Substitutions
	print $File_Inform "\nPart 0.3.1 - Text Substitutions\n\n";
	print $File_Inform "To say i -- beginning say_i -- running on: (- style underline; -).\n";
	print $File_Inform "To say /i -- ending say_i -- running on: (- style roman; -).\n";
	print $File_Inform "To say b -- beginning say_b -- running on: (- style bold; -).\n";
	print $File_Inform "To say /b -- ending say_b -- running on: (- style roman; -).\n";
	#Text Substitutions
	print $File_Inform "\nPart 0.3.2 - Movement\n\n";
	print $File_Inform "[Make exit mean go outside.]\n";
	print $File_Inform "Instead of exiting when the player is not in something:\n\t	Try going outside instead;\n";
	#Math
	print $File_Inform "\nPart 0.3.3 - Math\n\n";
	print $File_Inform "To decide if (X - A number) is between (low - a number) and (high - a number):\n\tIf X >= low and X <= high, decide yes;\n\tDecide no;\n";
}
#Generate the locations book of the Inform file
sub generateInformLocations(){
	print $File_Inform "\nBook 1.1 - Locations\n\n";
	print $File_Inform "[The locations for the story, divided into one parts for each distinct region with chapters for each room.]\n";
	print $File_Inform "\nPart 1.1.1 - Main Region\n";
	generateInformRoomRecursive($Game{Start});
	#TODO Look for unprinted rooms, create a new region for each and add the rooms
}
#Generate a room in the Inform output, then recurse through all the exits
sub generateInformRoomRecursive($);
sub generateInformRoomRecursive($){
	my $room	= shift;
	#Check if room is generated
	return if defined $Rooms[$room]{i7generated};
	$Rooms[$room]{i7generated}	= 1;
	#Loop through compass directions to find all exits to the room, sorting into unvisited to recurse to and relations to existing rooms.
	my @unvisited	= ();
	my $relations	= 'is ';
	#TODO: For now we assume that all exits are bi-directional
	foreach my $direction (0..$#Compass_Direction){
		my $destination	= $Rooms[$room]{Exits}[$direction]{Destination};
		if ($destination){
			#TODO: We don't take task restrictions into account
			if (defined $Rooms[$destination]{i7generated}){
				#Destination is generated; add to relations
				$relations .= ' and '	unless $relations eq 'is ';
				$relations .= $Compass_Reversed[$direction] . ' ' . nameRoom($destination);
			}
			else {
				#Destination is not generated, add to recursion list
				push @unvisited, $destination;
			}
		}
	}
	#Declare as a room if there are no relations
	$relations .= 'a room'	if $relations eq 'is ';
	#Print out the room
	print $File_Inform "\nChapter - $Rooms[$room]{Title}\n\n";
	print $File_Inform "[Room$room]\n";
	print $File_Inform nameRoom($room) . " $relations.\n";
	print $File_Inform "The printed name is \"$Rooms[$room]{Title}\".\n" unless nameRoom($room) eq $Rooms[$room]{Title};
	#TODO: Alternate descriptions
	print $File_Inform "\"$Rooms[$room]{Description}\".\n";
	#TODO: Room Contents
	#TODO: Movement Restrictions
	#Call recursive generation of unvisited rooms
	foreach my $destination (@unvisited){ generateInformRoomRecursive($destination) }
	#TODO: Section - Contents
	#TODO: Section - Movement Restrictions
}

#Generate the inhabitant book of the Inform file
sub generateInformInhabitants(){
	print $File_Inform "\nBook 1.2 - Inhabitants\n\n";
	print $File_Inform "[The actors, one part for each.]\n";
}
#Generate the mechanics book of the Inform file
sub generateInformMechanics(){
	print $File_Inform "\nBook 1.3 - Mechanics\n\n";
	print $File_Inform "[Any mechanics pertaining to the act, one part for each main feature.]\n";
	#Metadata, partly from input file
	print $File_Inform "\nPart 1.3.1 - Task Overview\n\n";
	print $File_Inform "[Mapping ADRIFT tasks to actions in Inform is error-prone; what follows is an overview of each task and how it is mapped.]\n";
}
#Generate the chronology book of the Inform file
sub generateInformChronology(){
	print $File_Inform "\nBook 1.4 - Chronology\n\n";
	print $File_Inform "[Break the act into scenes.]\n";
	#As there is no clue to scening from ADRIFT, we put everything we have into the prologue
	print $File_Inform "\nPart 1.4.1 - Progression\n\n";
	print $File_Inform "[The scenes dealing with the story progression]\n";
	#As there is no clue to scening from ADRIFT, we put everything we have into the prologue
	print $File_Inform "\nChapter 1.4.1a - Prologue\n\n";
	print $File_Inform "Prologue is a scene.\nPrologue begins when play begins.\n";
	print $File_Inform "When prologue begins:\n\tSay \"".informString($Game{Intro})."\";\n\n";
	print $File_Inform "When prologue ends:\n\tSay \"".informString($Game{Ending})."\";\n\n";
	#TODO: Sex-scenes
}
#Take in a string and convert it into printing in Inform
sub informString($){
	my $text		= shift;
	#TODO
	return $text;
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
	$FileName_XML			= $1 . '.xml';
	$FileName_Inform		= $1 . '.ni';
	$FileName_Path			= $1 . '/'	unless defined $Option_Minimal;
}
else{
	$FileName_Log			= 'decompile.log';
	$FileName_Generate		= 'decompile.sym'	if defined $Option_Generate;
	$FileName_Decompiled	= 'decompile.src'	if defined $Option_Rawdump;
	$FileName_XML			= 'story.xml';
	$FileName_Inform		= 'story.ni';
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
	or die "$0: can't open $FileName_Path$FileName_Decompiled for writing: $!"
	if defined $Option_Rawdump;
readFile();										# Read the file, determining version from signature
close($File_Compiled);
close($File_Decompiled) if defined $Option_Rawdump;
#preloadConstants();							# Populate arrays with constants
print "Analyzing...\n";
parseFile();									# Parse the input file into the local data structures
#TODO	parseMapping() if defined $FileName_Mapping;	# Read symbol file if called for
open($File_Mapping, "> :raw :bytes", $FileName_Path . $FileName_Generate)
	|| die "$0: can't open " . $FileName_Path . $FileName_Generate . "for writing: $!"
	if defined $Option_Generate;
translate();
analyze();
print "Writing results...\n";
open($File_Inform, "> :raw :bytes", $FileName_Path . $FileName_Inform)
	or die "$0: can't open $FileName_Path$FileName_Inform for writing: $!";
open($File_XML, "> :raw :bytes", $FileName_Path . $FileName_XML)
	or die "$0: can't open $FileName_Path$FileName_XML for writing: $!";
writeMapping()		 if defined $Option_Generate;
close($File_Mapping) if defined $Option_Generate;
printSource();
#Close file output
close($File_Inform);
close($File_XML);
close($File_Log);
print "Decompiling completed in ".(time - $Time_Start)." seconds.\n";
