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
my $Decompiler_Version		= '0.7';
#v0.1:	Initial structure for flow and storage
#v0.2:	Signature parsing, inflation/decryption of source
#v0.3:	Raw dump
#v0.4:	Parse header
#v0.5:	Parse rooms with basic XML output
#v0.6:	Parse objects with basic XML output
#v0.7:	Parse tasks

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
##Translation

#Mappings
my @Compass_Direction;			# Names of the compass directions, populated by loadCompass
my @Compass_Reversed;			# Names of the reversed compass directions, populated by loadCompass

#Namings

#Mapping File Handling

sub loadCompass(){
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
sub uniformName($) {
	my $text	= lc(shift);				# Lower case
	$text		=~ s/\s+/ /;				# Convert all whitespace to spaces, and trim multiples
	$text		=~ s/[-_'\"]//g;			# Trim all unwanted characters
	$text		=~ s/^\s+|\s+$//g;			# Trim leading/trailing whitespace
	$text		=~ s/ (.)/uc($1)/ge;		# Remove spaces, capitalizing the next letter
	return $text;
}
sub parseFile(){
	print $File_Log "Decompiler v$Decompiler_Version on $FileName_Compiled";
	parseHeader();
	loadCompass();
	print $File_Log ", $Game{Title} by $Game{Author} (ADRIFT v$Gamefile_Version)\n";
	print $File_Log "\tBattles\n"			if $Game{EnableBattle};
	print $File_Log "\t8-point compass\n"	if $Game{ExpandedCompass};
	print $File_Log "\tGraphics\n"			if $Game{EnableGraphics};
	print $File_Log "\tSound\n"				if $Game{EnableSound};
	my $rooms		= nextSLV();
	print $File_Log "$rooms rooms\n";
	for (my $room=1 ; $room<=$rooms ; $room++){ push @Rooms, parseRoom($room); }
	my $objects		= nextSLV();
	print $File_Log "$objects objects\n";
	for (my $object=1 ; $object<=$objects ; $object++){ push @Objects, parseObject($object); }
	my $tasks		= nextSLV();
	print $File_Log "$tasks tasks\n";
	for (my $task=1 ; $task<=$tasks ; $task++){ push @Tasks, parseTask($task); }
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
	my @exits;
	my @restrictions;
	foreach my $dir (0..$#Compass_Direction){
		my $destination	= nextSLV();
		if ($destination != 0){
			$exits[$dir]	= $destination;
			$restrictions[$dir]{var1}	= nextSLV();
			$restrictions[$dir]{var2}	= nextSLV();
			$restrictions[$dir]{var3}	= 0				if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
			$restrictions[$dir]{var3}	= nextSLV()		if $Gamefile_Version eq '4.00';
		}
	}
	$room{Exits}			= \@exits;
	$room{ExitRestrictions}	= \@restrictions;
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
	for (1 .. $alt_count){
		push @alternates, parseRoomAlt();
	}
	$room{Alternates}		= \@alternates;
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
	my $alias_count;
	$alias_count				= 1			if $Gamefile_Version eq '3.80' or $Gamefile_Version eq '3.90';
	$alias_count				= nextSLV() if $Gamefile_Version eq '4.00';
	my $alias;
	for (1 .. $alias_count){
		$alias .= ', '		if defined $alias;
		$alias .= nextSLV();
	}
	#truth	Static
	$object{Static}				= nextSLV();
	#text	Description
	$object{Description}		= nextSLV();
	#number	InitialPosition
	$object{InitialPosition}	= nextSLV();
	#number	Task
	$object{AltDescTask}		= nextSLV();
	#truth	TaskNotDone
	$object{AltDescInvert}		= nextSLV();
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
	$object{Where}				= \[]		unless $object{Static};
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
	$object{EnterableType}		= nextSLV();
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
	$task{ReverseMessage}			= nextSLV();
	#text	RepeatText
	$task{RepeatText}				= nextSLV();
	#text	AdditionalMessage
	$task{AdditionalMessage}		= nextSLV();
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
	$task{CommandsReverse}			= ();
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
	$task{Where}					= ();
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
	$task{Restrictions}				= ();
	my $restrictions				= 0;
	$restrictions					= nextSLV()	if $Gamefile_Version eq '3.90' or $Gamefile_Version eq '4.00';
	print $File_Log "\t\t\t$restrictions restriction(s)\n"	if defined $Option_Verbose;
	for (1 .. $restrictions) { push @{ $task{Restrictions} }, parseRestriction(); }
	#Actions	Actions
	$task{Actions}					= ();
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
sub parseRestriction(){
	my %restriction;
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
		$restriction{Var2}	= nextSLV();
		$restriction{Var3}	= nextSLV();
		$restriction{Var4}	= 0;
		$restriction{Var4}	= nextSLV()		if $Gamefile_Version eq '4.00';
	}
	$restriction{FailMessage}	= nextSLV();
	$restriction{Var1}++	if $restriction{Var1} > 0 && $Gamefile_Version eq '3.90';
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
		$action{Expr}	= ''		if $Gamefile_Version eq '3.90' && $action{Var2} eq 5;
		$action{Expr}	= nextSLV()	if $Gamefile_Version eq '3.90' && $action{Var2} != 5;
		$action{Var5}	= nextSLV()	if $Gamefile_Version eq '4.00';
		$action{Var5}	= nextSLV()	if $Gamefile_Version eq '3.90' && $action{Var2} eq 5;
		$action{Var5}	= 0			if $Gamefile_Version eq '3.90' && $action{Var2} != 5;
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
##Analyzing

##Output
sub printSource(){
	generateXML();			# Generate XML based on bytecode
	#generateInform();		# Generate equivalent Inform-source
}
#Generate XML Output
sub generateXML(){
	print $File_Log "Printing XML File\n";
	print $File_XML "<Story title=\"$Game{Title}\" author=\"$Game{Author}\">\n";
	generateXMLOptions();
	generateXMLRooms();
	generateXMLObjects();
	print $File_XML "</Story>";
}
#Generate the options part of the XML output
sub generateXMLOptions(){

}
#Generate the rooms part of the XML output
sub generateXMLRooms(){
	print $File_XML "<!-- $#Rooms rooms -->\n";
	print $File_XML "\t<Rooms>\n"		if $#Rooms;
	for my $room (1 .. $#Rooms){
		print $File_XML "\t\t<Room";
		print $File_XML "\n\t\t\t".'id'		."\t\t= \"$room\"";
		print $File_XML "\n\t\t\t".'title'	."\t= \"$Rooms[$room]{Title}\"";
		print $File_XML " />\n";
	}
	print $File_XML "\t</Rooms>\n"		if $#Rooms;
}
#Generate the objects part of the XML output
sub generateXMLObjects(){
	print $File_XML "<!-- $#Objects objects -->\n";
	print $File_XML "\t<Objects>\n"		if $#Objects;
	for my $object (1 .. $#Objects){
		print $File_XML "\t\t<Object";
		print $File_XML "\n\t\t\t".'id'		."\t\t= \"$object\"";
		print $File_XML "\n\t\t\t".'prefix'	."\t= \"$Objects[$object]{Prefix}\"";
		print $File_XML "\n\t\t\t".'short'	."\t= \"$Objects[$object]{Short}\"";
		print $File_XML " />\n";
	}
	print $File_XML "\t</Objects>\n"	if $#Objects;
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
#preloadMapping();								# Load mapping defaults
#parseMapping() if defined $FileName_Mapping;	# Read symbol file if called for
#generateMapping() if $Option_Generate;			# Generate symbol file if called for
print "Writing results...\n";
open($File_Inform, "> :raw :bytes", $FileName_Path . $FileName_Inform)
	or die "$0: can't open $FileName_Path$FileName_Inform for writing: $!";
open($File_XML, "> :raw :bytes", $FileName_Path . $FileName_XML)
	or die "$0: can't open $FileName_Path$FileName_XML for writing: $!";
printSource();
#Close file output
close($File_Inform);
close($File_XML);
close($File_Log);
print "Decompiling completed in ".(time - $Time_Start)." seconds.\n";