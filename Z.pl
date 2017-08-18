use strict;					# 'Safest' operation level
use warnings;				# Give warnings
use File::Slurp;			# Read entire file at once
use Data::Dumper;			# Dumping data structures

my $Time_Start	= time();	# Epoch time for start of processing

##Version History
my $Decompiler_Version		= '0.2';
#v0.1:	Initial structure for flow and storage
#v0.2:	ZSCII decoding, object structure

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
my $Compiled;				# File contents

#Constants
my $Signature_Size	= 64;
my @Alphabets;

#Game Details
my $Gamefile_Version;		# The version of the z-machine the game is encoded in
my $Image_Version;			# The release version of the game
my $Image_Serial;			# The serial number of the game (usually compile date as YYMMDD)

#Memory Structure
my $Address_Start;			# Initial value of program counter/Address of main routine
my $Address_Dictionary;		# Location of Dictionary
my $Address_Globals;		# Location of Global Variables table
my $Address_Objects;		# Location of Object table
my $Address_Abbreviations;	# Location of Abbreviations table
my $Address_HighMem;		# Base of High Memory
my $Address_StaticMem;		# Base of Static Memory

#Story Data
my @Objects 			= ( undef );	# Objects, starting from ID 1.
my @Property_Defaults	= ();			# Default values for when a property isn't given a value


##Options and Arguments
#Available Options
my $Options	= "Available Options:\n";
my $Option_Minimal;		# Skip output directory and embedded resources
$Options	.= "-m\t\tMinimalist mode: Skip resources and output directory\n";
my $Option_Verbose;		# Extra information dumped to story file
$Options	.= "-v\t\tVerbose: Extra information printed to log\n";
my $Option_Naming;		# Be extra aggressive on trying to determine names
						# TODO: This will create duplicate names, remake to avoid that
$Options	.= "-a\t\tAggressive naming: Try extra hard to find names of objects and properties\n";
my $Option_Generate;	# Generate a new symbol file
$Options	.= "+s\t\tGenerate symbol file: Store symbol mapping in output directory\n";
$Options	.= "-s [file]:\tSymbol file: Parse the file for symbol mappings\n";
#Parse command-line arguments for options
sub parseOptions(){
    #Interpret any defined command-line arguments into options
    while (defined $ARGV[0]) {
        if	 ($ARGV[0] eq '-m') {
			# Minimalist mode
			$Option_Minimal	= 1;
			splice(@ARGV, 0, 1);
		}
        elsif($ARGV[0] eq '-v') {
			#Verbose logging
            $Option_Verbose = 1;
			splice(@ARGV, 0, 1);
        }
        elsif($ARGV[0] eq '-a') {
			#Aggressive naming search
            $Option_Naming  = 1;
			splice(@ARGV, 0, 1);
        }
		elsif($ARGV[0] eq '-s') {
			#Read symbol mapping file
			$FileName_Mapping	= $ARGV[1];
			splice(@ARGV, 0, 2);
		}
		elsif($ARGV[0] eq '+s') {
			#Generate symbol mapping file template
			$Option_Generate	= 1;
			splice(@ARGV, 0, 1);
		}
		elsif($#ARGV >= 0 && $ARGV[0] eq '-a') {		
			$Option_Naming		= 1;
			splice(@ARGV, 0, 1);
		}
        else{ last }
    }
	#There should be only one argument left, giving the name of the file to parse.
	die "Use: z [options] file.dat\n$Options" unless ($#ARGV eq 0);
	$FileName_Compiled	= $ARGV[0];
	#Determine names to use
	$FileName_Path	= './';	# Default to no directory
	if ($ARGV[0] =~ m/([-_\w\s]*)\.(dat|z\d)/i) {	# Use the name of the input file if possible
		$FileName_Log			= $1 . '.log';
		$FileName_Generate		= $1 . '.sym'	if defined $Option_Generate;
		$FileName_Decompiled	= $1 . '.src';
		$FileName_XML			= $1 . '.xml';
		$FileName_Inform		= $1 . '.ni';
		$FileName_Path			= $1 . './'	unless defined $Option_Minimal;
	}
	else{
		$FileName_Log			= 'decompile.log';
		$FileName_Generate		= 'decompile.sym'	if defined $Option_Generate;
		$FileName_Decompiled	= 'decompile.src';
		$FileName_XML			= 'story.xml';
		$FileName_Inform		= 'story.ni';
		$FileName_Path			= 'decoded/'	unless defined $Option_Minimal;
	}
}

##Translation
#Translation Mappings
#Constants
sub loadConstants(){
	loadAlphabet();
}
sub loadAlphabet(){
	$Alphabets[0][6]	= 'a';
	$Alphabets[1][6]	= 'A';
#	$Alphabets[2][6]	= ' ';	#Special 10-bit ZSCII flag
	$Alphabets[0][7]	= 'b';
	$Alphabets[1][7]	= 'B';
	$Alphabets[2][7]	= '^'	unless $Gamefile_Version eq 1;
	$Alphabets[2][7]	= '0'	if $Gamefile_Version eq 1;
	$Alphabets[0][8]	= 'c';
	$Alphabets[1][8]	= 'C';
	$Alphabets[2][8]	= '0'	unless $Gamefile_Version eq 1;
	$Alphabets[2][8]	= '1'	if $Gamefile_Version eq 1;
	$Alphabets[0][9]	= 'd';
	$Alphabets[1][9]	= 'D';
	$Alphabets[2][9]	= '1'	unless $Gamefile_Version eq 1;
	$Alphabets[2][9]	= '2'	if $Gamefile_Version eq 1;
	$Alphabets[0][10]	= 'e';
	$Alphabets[1][10]	= 'E';
	$Alphabets[2][10]	= '2'	unless $Gamefile_Version eq 1;
	$Alphabets[2][10]	= '3'	if $Gamefile_Version eq 1;
	$Alphabets[0][11]	= 'f';
	$Alphabets[1][11]	= 'F';
	$Alphabets[2][11]	= '3'	unless $Gamefile_Version eq 1;
	$Alphabets[2][11]	= '4'	if $Gamefile_Version eq 1;
	$Alphabets[0][12]	= 'g';
	$Alphabets[1][12]	= 'G';
	$Alphabets[2][12]	= '4'	unless $Gamefile_Version eq 1;
	$Alphabets[2][12]	= '5'	if $Gamefile_Version eq 1;
	$Alphabets[0][13]	= 'h';
	$Alphabets[1][13]	= 'H';
	$Alphabets[2][13]	= '5'	unless $Gamefile_Version eq 1;
	$Alphabets[2][13]	= '6'	if $Gamefile_Version eq 1;
	$Alphabets[0][14]	= 'i';
	$Alphabets[1][14]	= 'I';
	$Alphabets[2][14]	= '6'	unless $Gamefile_Version eq 1;
	$Alphabets[2][14]	= '7'	if $Gamefile_Version eq 1;
	$Alphabets[0][15]	= 'j';
	$Alphabets[1][15]	= 'J';
	$Alphabets[2][15]	= '7'	unless $Gamefile_Version eq 1;
	$Alphabets[2][15]	= '8'	if $Gamefile_Version eq 1;
	$Alphabets[0][16]	= 'k';
	$Alphabets[1][16]	= 'K';
	$Alphabets[2][16]	= '8'	unless $Gamefile_Version eq 1;
	$Alphabets[2][16]	= '9'	if $Gamefile_Version eq 1;
	$Alphabets[0][17]	= 'l';
	$Alphabets[1][17]	= 'L';
	$Alphabets[2][17]	= '9'	unless $Gamefile_Version eq 1;
	$Alphabets[2][17]	= '.'	if $Gamefile_Version eq 1;
	$Alphabets[0][18]	= 'm';
	$Alphabets[1][18]	= 'M';
	$Alphabets[2][18]	= '.'	unless $Gamefile_Version eq 1;
	$Alphabets[2][18]	= ','	if $Gamefile_Version eq 1;
	$Alphabets[0][19]	= 'n';
	$Alphabets[1][19]	= 'N';
	$Alphabets[2][19]	= ','	unless $Gamefile_Version eq 1;
	$Alphabets[2][19]	= '!'	if $Gamefile_Version eq 1;
	$Alphabets[0][20]	= 'o';
	$Alphabets[1][20]	= 'O';
	$Alphabets[2][20]	= '!'	unless $Gamefile_Version eq 1;
	$Alphabets[2][20]	= '?'	if $Gamefile_Version eq 1;
	$Alphabets[0][21]	= 'p';
	$Alphabets[1][21]	= 'P';
	$Alphabets[2][21]	= '?'	unless $Gamefile_Version eq 1;
	$Alphabets[2][21]	= '_'	if $Gamefile_Version eq 1;
	$Alphabets[0][22]	= 'q';
	$Alphabets[1][22]	= 'Q';
	$Alphabets[2][22]	= '_'	unless $Gamefile_Version eq 1;
	$Alphabets[2][22]	= '#'	if $Gamefile_Version eq 1;
	$Alphabets[0][23]	= 'r';
	$Alphabets[1][23]	= 'R';
	$Alphabets[2][23]	= '#'	unless $Gamefile_Version eq 1;
	$Alphabets[2][23]	= '\''	if $Gamefile_Version eq 1;
	$Alphabets[0][24]	= 's';
	$Alphabets[1][24]	= 'S';
	$Alphabets[2][24]	= '\''	unless $Gamefile_Version eq 1;
	$Alphabets[2][24]	= '"'	if $Gamefile_Version eq 1;
	$Alphabets[0][25]	= 't';
	$Alphabets[1][25]	= 'T';
	$Alphabets[2][25]	= '"'	unless $Gamefile_Version eq 1;
	$Alphabets[2][25]	= '/'	if $Gamefile_Version eq 1;
	$Alphabets[0][26]	= 'u';
	$Alphabets[1][26]	= 'U';
	$Alphabets[2][26]	= '/'	unless $Gamefile_Version eq 1;
	$Alphabets[2][26]	= '\\'	if $Gamefile_Version eq 1;
	$Alphabets[0][27]	= 'v';
	$Alphabets[1][27]	= 'V';
	$Alphabets[2][27]	= '\\'	unless $Gamefile_Version eq 1;
	$Alphabets[2][27]	= '<'	if $Gamefile_Version eq 1;
	$Alphabets[0][28]	= 'w';
	$Alphabets[1][28]	= 'W';
	$Alphabets[2][28]	= '-';
	$Alphabets[0][29]	= 'x';
	$Alphabets[1][29]	= 'X';
	$Alphabets[2][29]	= ':';
	$Alphabets[0][30]	= 'y';
	$Alphabets[1][30]	= 'Y';
	$Alphabets[2][30]	= '(';
	$Alphabets[0][31]	= 'z';
	$Alphabets[1][31]	= 'Z';
	$Alphabets[2][31]	= ')';
}
#Namings
#Mapping File Handling

#Constants

##File Handling
sub prepareFiles(){
	#Create path as needed
	mkdir $FileName_Path						unless -e $FileName_Path;
	die "$FileName_Path is not a valid path"	unless -d $FileName_Path;
	#Open log; use :unix to flush as we write to it
	open($File_Log, "> :raw :bytes :unix", $FileName_Path . $FileName_Log) # Use :unix to flush the log as we write to it
		or die "$0: can't open $FileName_Path$FileName_Log for writing: $!";
	#Open compiled file with some sanity checking
	die "$FileName_Compiled is not a valid file"	unless -f $FileName_Compiled;
	open($File_Compiled, "< :raw :bytes", $FileName_Compiled)
		or die("Couldn't open $FileName_Compiled for reading: $!");
	#Open decompiled files, creating path as needed
	open($File_Decompiled, "> :raw :bytes", $FileName_Path . $FileName_Decompiled)
		or die "$0: can't open $FileName_Path$FileName_Decompiled for writing: $!";
	open($File_Inform, "> :raw :bytes", $FileName_Path . $FileName_Inform)
		or die "$0: can't open $FileName_Path$FileName_Inform for writing: $!";
	open($File_XML, "> :raw :bytes", $FileName_Path . $FileName_XML)
		or die "$0: can't open $FileName_Path$FileName_XML for writing: $!";
	#Open mapping file with some sanity checking
	die "Overwriting existing symbol file with autogenerated is not supported in minimal mode"
		if defined $FileName_Generate && $Option_Minimal && -e $FileName_Generate;
	open($File_Mapping, "> :raw :bytes", $FileName_Path . $FileName_Generate)
		|| die "$0: can't open " . $FileName_Path . $FileName_Generate . "for writing: $!"
		if defined $Option_Generate;
}
sub parseFile(){
	parseHeader();
	#Constants can be loaded after header
	loadConstants();
	#Read in entire file for further parsing
	$Compiled	= read_file ( $FileName_Compiled, binmode => ':raw' );
	parseObjects();
}
sub parseHeader(){
	print $File_Log "Z-Code decompiler v$Decompiler_Version on $FileName_Compiled";
	my $block;
	my $bytes_read = read ($File_Compiled, $block, $Signature_Size);
	die 'Unable to read file signature' unless $bytes_read eq $Signature_Size;
	#0x00: Version number; 1 to 6 for InfoCom, up to 8 for Inform.
	$Gamefile_Version	= unpack('C', substr($block, 0, 1));
	die "Unhandled version number $Gamefile_Version" if $Gamefile_Version > 8;
	print $File_Log "(z$Gamefile_Version)";
	#0x02-0x03:
	$Image_Version		= unpack('n', substr($block, 2, 2));
	print $File_Log "\tRelease $Image_Version ";
	#0x12-0x17 (v2+): Serial
	$Image_Serial		= substr($block, 0x12, 6)	if $Gamefile_Version >= 2;
	print $File_Log "($Image_Serial)"				if $Gamefile_Version >= 2;
	print $File_Log "\n";
	#0x1A-0x1B (v3+): Length of file
	my $file_length		= unpack('n', substr($block, 0x1A, 2))	if $Gamefile_Version >= 3;
	print $File_Log "\t$file_length bytes"						if $Gamefile_Version >= 3;
	#0x1C-0x1D (v3+): Checksum of file
	my $file_checksum	= unpack('n', substr($block, 0x1C, 2))	if $Gamefile_Version >= 3;
	print $File_Log "\t($file_checksum)\n"						if $Gamefile_Version >= 3;
	
	#0x01: Flags1; Meaning of flags varies by version.
	my $flags1			= 0;
	$flags1				= unpack('C', substr($block, 1, 1));
	#	Bit 0, v1-3: Unused
	#	Bit 1, v1-3: Status line type: 0=score/turns, 1=hours:mins
	my $statusline_time	= $flags1 & 2**1				if ($Gamefile_Version <= 3);
	print $File_Log "\tUses hours:mins statusline\n"	if $statusline_time;
	#	Bit 2, v1-3: Story file split across two discs?
	my $storyfile_split	= $flags1 & 2**2				if ($Gamefile_Version <= 3);
	print $File_Log "\tUses split story file\n"			if $storyfile_split;
	#	Bit 3, v1-3: The legendary "Tandy" bit
	my $censorship		= $flags1 & 2**3				if ($Gamefile_Version <= 3);
	print $File_Log "\tUses 'Tandy' censorship\n"		if $censorship;
	#	Bit 4, v1-3: Status line not available?
	my $statusline_hide	= $flags1 & 2**4				if ($Gamefile_Version <= 3);
	print $File_Log "\tStatus line hidden\n"			if $statusline_hide;
	#	Bit 5, v1-3: Screen-splitting available?
	my $screen_split	= $flags1 & 2**5				if ($Gamefile_Version <= 3);
	print $File_Log "\tUses split screen\n"				if $screen_split;
	#	Bit 6, v1-3: Is a variable-pitch font the default?
	my $variable_font	= $flags1 & 2**6				if ($Gamefile_Version <= 3);
	print $File_Log "\tUses variable-pitch font\n"		if $variable_font;
	#	Bit 7, v1-3: Unused
	#	Bit 0, v4+: Colours available?
	my $setting_colours	= $flags1 & 2**0				if ($Gamefile_Version >= 4);
	print $File_Log "\tColours available\n"				if $setting_colours;
	#	Bit 1, v4+: Picture display available?
	my $setting_picture	= $flags1 & 2**1				if ($Gamefile_Version >= 4);
	print $File_Log "\tPictures available\n"			if $setting_picture;
	#	Bit 2, v4+: Boldface available?
	my $setting_bold	= $flags1 & 2**2				if ($Gamefile_Version >= 4);
	print $File_Log "\tBoldface available\n"			if $setting_bold;
	#	Bit 3, v4+: Italic available?
	my $setting_italic	= $flags1 & 2**3				if ($Gamefile_Version >= 4);
	print $File_Log "\tItalic available\n"				if $setting_italic;
	#	Bit 4, v4+: Fixed-space available?
	my $setting_fixed	= $flags1 & 2**4				if ($Gamefile_Version >= 4);
	print $File_Log "\tFixed-space available\n"			if $setting_fixed;
	#	Bit 5, v4+: Sound effects available?
	my $setting_sound	= $flags1 & 2**5				if ($Gamefile_Version >= 4);
	print $File_Log "\tSound effects available\n"		if $setting_sound;
	#	Bit 6, v4+: Unknown/Unusued
	#	Bit 7, v4+: Timed keyboard input?
	my $setting_timed	= $flags1 & 2**7				if ($Gamefile_Version >= 4);
	print $File_Log "\tTimed input available\n"			if $setting_timed;
	#0x10: Flags2; Meaning of flags varies by version. 
	#TODO

	#0x04-0x05: Base of high memory (byte address)
	$Address_HighMem		= unpack('n', substr($block, 0x04, 2));
	#0x06-0x07 (v1-5): Initial value of program counter (byte address)
	#0x06-0x07 (v6+): Packed address of initial "main" routine
	$Address_Start			= unpack('n', substr($block, 0x06, 2));
	#0x08-0x09: Location of dictionary (byte address)
	$Address_Dictionary		= unpack('n', substr($block, 0x08, 2));
	#0x0A-0x0B: Location of object table (byte address)
	$Address_Objects		= unpack('n', substr($block, 0x0A, 2));
	#0x0C-0x0D: Location of global variables table (byte address)
	$Address_Globals		= unpack('n', substr($block, 0x0C, 2));
	#0x0E-0x0F: Base of static memory (byte address)
	$Address_StaticMem		= unpack('n', substr($block, 0x0E, 2));
	#0x18-0x19 (v2+): Location of abbreviations table (byte address)
	$Address_Abbreviations	= unpack('n', substr($block, 0x18, 2))	if ($Gamefile_Version >= 2);
	
	
	#Current settings
	#0x1E (v4+): Interpreter number
	#0x1F (v4+): Interpreter version
	
	#TODO: Bytes 0x20 onwards unprocessed: http://inform-fiction.org/zmachine/standards/z1point1/sect11.html
	#TODO: Some extra bytes unprocessed: http://inform-fiction.org/zmachine/standards/z1point1/appb.html
	

}

#Object table begins at the adress specified in the header and stored in $Address_Objects
sub parseObjects(){
	my $pos	= $Address_Objects;
	#The first part is the property defaults table. Size varies by version.
	my $size_defaults;
	$size_defaults	= 31	if $Gamefile_Version <= 3;
	$size_defaults	= 63	if $Gamefile_Version >= 4;
#	for my $prop (1..$size_defaults){
	for (my $prop = 0 ; $prop < $size_defaults ; $prop++){
		my $value	= unpack('n', substr($Compiled, $pos, 2));
		$Property_Defaults[$prop]	= $value;
#		print $File_Log "Prop$prop: $value ($pos)\n";
		$pos += 2;
	}
	if ($Gamefile_Version <= 3){
		#Can contain up to 255 objects
		my $first_property	= unpack('n', substr($Compiled, $pos+7, 2));
		for my $obj (1..255){
			#Attribute flags: 32 in 4 bytes (v1-3):
			#TODO
			#Relations
			$Objects[$obj]{Parent}	= ord( substr($Compiled, $pos+4, 1));
			$Objects[$obj]{Sibling}	= ord( substr($Compiled, $pos+5, 1));
			$Objects[$obj]{Child}	= ord( substr($Compiled, $pos+6, 1));
			#Property table reference
			my $properties			= unpack('n', substr($Compiled, $pos+7, 2));
			$first_property			= $properties if $properties < $first_property;
			print $File_Log "Obj$obj:";
			parseProperties($obj, $properties);
			$pos += 9;
			#We assume that the object table lasts until the first property table appears
			last if $pos >= $first_property;
		}
	}
	if ($Gamefile_Version >= 4) {
		for my $obj (1..10){
			#Attribute flags: 48 in 6 bytes (v4+):
			#TODO
			#Relations
			$Objects[$obj]{Parent}	= unpack('n', substr($Compiled, $pos+6, 2));
			$Objects[$obj]{Sibling}	= unpack('n', substr($Compiled, $pos+8, 2));
			$Objects[$obj]{Child}	= unpack('n', substr($Compiled, $pos+10, 2));
			#Property table reference
			my $properties			= unpack('n', substr($Compiled, $pos+12, 2));
			$pos += 14;
		}
	}
}
sub parseProperties($$){
	my $obj	= shift;
	my $pos	= shift;
	die "Unable to parse properties for $obj at $pos" unless defined $obj && defined $pos;
	my $name_size	= ord( substr($Compiled, $pos, 1));
	$pos++;
	my $name		= decodeText(substr($Compiled, $pos, $name_size * 2));
	$Objects[$obj]{Name}	= $name;
	$pos += ($name_size * 2);
	print $File_Log "\t$name ($name_size)\n";
	#In Versions 1 to 3, each property is stored as a block
	my $found = 0;
	if ($Gamefile_Version <= 3){
		for (;;){
			#First byte gives both the size and the property ID; a 0 signals end of properties
			my $prop_size = ord( substr($Compiled, $pos, 1));
			$pos++;
			last if $prop_size eq 0;
			$found++;
			use integer;
			my $size	= ($prop_size / 32) + 1;
			my $prop	= ($prop_size % 32);
			my $value	= substr($Compiled, $pos, $size);
			$Objects[$obj]{Properties}[$prop]	= $value;
			print $File_Log "\t\tProp$prop ($size bytes)\n";
			$pos += $size;
		}
	}
	if ($Gamefile_Version >= 4) {
		#TODO
	}
	print $File_Log "\t$found properties\n";
}
##Parsing
#Text is stored as ZSCII, a special format using 5 bits for each character with 3 characters stored in 2 bytes
sub decodeText($){
	#http://inform-fiction.org/zmachine/standards/z1point1/sect03.html
	my $input		= unpackZSCII(shift);
	my $length		= length ($input);
	my $decoded		= '';
	#ZSCII has three alphabets: 0 (lower case), 1 (upper case) and 2 (punctuation) which control character mapping
	my $alphabet	= 0;
	my $locked		= 0;
	for (my $pos = 0 ; $pos < $length ; $pos++){
		#Reset to alphabet 0 unless locked
		$alphabet 	= 0 unless $locked;
		$locked--;
		#Get the next character value
		my $value	= ord (substr($input, $pos, 1));
#DEBUG		print $File_Log "$alphabet - $value\n";
		#0 is always space, regardless of alphabet
		if	($value eq 0){
			$decoded .= ' ';
		}
		#1 is newline for v1
		elsif($value eq 1	&& $Gamefile_Version eq 1){
			$decoded .= "\n";
		}
		#2 is shift char for v1-2
		#4 is shift lock for v1-2
		#4 is shift for v3+
		elsif(($value eq 2 && $Gamefile_Version < 3) ||	$value eq 4) {
			my $new;
			$new		= 1 if $alphabet eq 0;
			$new		= 2 if $alphabet eq 1;
			$new		= 0 if $alphabet eq 2;
			$alphabet	= $new;
			#Reset lock, and relock if applicable
			$locked		= 1;
			$locked		= 99 if ($value eq 4 && $Gamefile_Version < 3);
		}
		#3 is shift char for v1-2
		#5 is shift lock for v1-2
		#5 is shift for v3+
		elsif(($value eq 3 && $Gamefile_Version < 3) ||	$value eq 5) {
			my $new;
			$new		= 2 if $alphabet eq 0;
			$new		= 0 if $alphabet eq 1;
			$new		= 1 if $alphabet eq 2;
			$alphabet	= $new;
			#Reset lock, and relock if applicable
			$locked		= 1;
			$locked		= 99 if ($value eq 5 && $Gamefile_Version < 3);
		}
		#1-3 is abbreviation reference for v3+ (only 1 for v2)
		elsif( ($value eq 1 && $Gamefile_Version > 1)
			|| ($value eq 2 && $Gamefile_Version > 2)
			|| ($value eq 3 && $Gamefile_Version > 2) ) {
			my $syn = 32 * ($value -1) + ord (substr($input, $pos + 1, 1));
			$pos++;
			$decoded	.= "SYN$syn";
#			my $temp	= $Address_Abbreviations + $syn
#			print "SYN$syn\n";
		}
		#TODO
		#Code 6 in alphabet 2 is ten-bit zscii code
		elsif($value eq 6 && $alphabet eq 2){
			#Get next 2 extended characters
			my $ext1	= ord (substr($input, $pos + 1, 1)) << 5 ;
			my $ext2	= ord (substr($input, $pos + 2, 1)) ;
			$pos+=2;
			#Concatenate and append
			$decoded	.= chr ($ext1 | $ext2);
		}
		#All other values are looked up in alphabet
		else {
			#TODO: Sanity check the range
			print $File_Log "$alphabet-$value\n" unless defined $Alphabets[$alphabet][$value];
			$decoded	.= $Alphabets[$alphabet][$value];
		}
	}
	return $decoded;
}
#Unpacks ZSCII 3:2 -> 1:1
sub unpackZSCII($){
	my $input		= shift;
	die "Uneven number of bytes in input ZSCII string" if length($input) % 2;
	my $unpacked	= '';
	my $terminator	= 0;
	while (my $packed	= unpack ('n', substr($input, 0, 2, ''))){
		#1st character
		$unpacked	.= chr(($packed & 0b0111110000000000) >> 10);
		#2nd character
		$unpacked	.= chr(($packed & 0b0000001111100000) >> 5);
		#3rd character
		$unpacked	.= chr(($packed & 0b0000000000011111));
		#First bit of every 2-byte word is a terminator indicator; check if there is more content
		my $length	= length $input;
		my $terminator = $packed & 0x8000;
		print $File_Log "ZSCII String continues for $length bytes after terminator\n" if $terminator && $length;
	}
	return $unpacked;
}

##Testing
sub synonymTesting(){
	print $File_Log "Synonyms from $Address_Abbreviations\n";
	for my $i(0..95){
		my $loc = $Address_Abbreviations + $i*2;
		#my $val = ord( substr($Compiled, $loc, 1))
		my $val = unpack('n', substr($Compiled, $loc, 2));
		my $text = decodeText(substr($Compiled, $val/2, 2));
		print $File_Log "SYN$i: $val -> $text\n";
		#print $File_Log "SYN$i \@$loc: ".decodeText(substr($Compiled, $loc, 2))."\n";
	}	
}


##Analyzing

##Output
sub printObjectTree(){
	#Start by printing any objects that are without parent
	for my $obj (1..$#Objects) {
		if ($Objects[$obj]{Parent} eq 0){
#			next if ($Objects[$obj]{Sibling} eq 0 && $Objects[$obj]{Child} eq 0);
			printObjectNode($obj, 0);
		}
	}
}
sub printObjectNode($$);
sub printObjectNode($$){
	my $obj		= shift;
	my $level	= shift;
	for (1..$level) { print $File_Log "\t" }
	print $File_Log "Obj$obj: $Objects[$obj]{Name}\n";
	printObjectNode($Objects[$obj]{Child}, $level +1 )	unless $Objects[$obj]{Child} eq 0;
	printObjectNode($Objects[$obj]{Sibling}, $level)	unless $Objects[$obj]{Sibling} eq 0;

}

##Main Program Loop
#Parse command-line arguments
print "Starting\n";
parseOptions();
prepareFiles();
print "Parsing $FileName_Compiled\n";
parseFile();									# Read the file, determining version from signature
close($File_Compiled);
close($File_Decompiled);
#preloadConstants();							# Populate arrays with constants
print "Analyzing...\n";
#parseMapping() if defined $FileName_Mapping;	# Read symbol file if called for
#analyze();
close($File_Mapping) if defined $Option_Generate;
print "Writing results...\n";
printObjectTree();
#printSource();
#Close file output
close($File_Inform);
close($File_XML);
close($File_Log);
print "Decompiling completed in ".(time - $Time_Start)." seconds.\n";