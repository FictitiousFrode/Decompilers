use strict;					# 'Safest' operation level
use warnings;				# Give warnings
use File::Basename;			# Interpreting embedded filenames
use File::Path 'make_path';	# Creating directories
use Data::Dumper;			# Dumping data structures
use Carp;					# For stack tracing at errors

my $Time_Start	= time();	# Epoch time for start of processing

##Version History
my $Decompiler_Version		= '0.1';
#v0.1:	Initial structure for flow and storage

##Global variables##
#File handling
my $FileName_Compiled;		# Filename for the compiled gamefile to decompile
my $FileName_Path;			# Path to place output files in
my $FileName_Decompiled;	# Filename for the decompiled sourcecode
my $FileName_Log;			# Filename for the log
my $FileName_Mapping;		# Filename for the symbol mapping/translation input file
my $FileName_Mapping_Gen;	# Filename for the symbol mapping/translation output file
my $FileName_I7;			# Filename for the Inform output
my $FileName_XML;			# Filename for the XML output
my $File_Compiled;			# File handle for input compiled gamefile
my $File_Log;				# File handle for logging output
my $File_Decompiled;		# File handle for output decompiled sourcecode
my $File_Mapping;			# File handle for symbol mapping/translation (both input and output)
my $File_I7;				# File handle for Inform output
my $File_XML;				# File handle for XML output
my $Contents_Compiled;		# File contents

#Game Details
my $Gamefile_Version;		# The version used to encode the game

#Story Data
my @Objects 			= ( undef );	# Objects, starting from ID 1.

#Translation Names
my @Translate_Object;				# Object names for 'objects'

#Static Names

#Constants

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
	#TODO: UPDATE the name of script and expected extension
	die "Use: z [options] file.dat\n$Options" unless ($#ARGV eq 0);
	$FileName_Compiled	= $ARGV[0];
}
#Translation Naming
sub nameObject($){
	my $id	= shift;
	return 'UnknownObject'			unless defined $id;
	return $Translate_Object[$id]	if defined $Translate_Object[$id];
	return "Object$id";
}
#Mapping File Handling
sub parseMapping(){
	my $line;
	while ($line = <$File_Mapping>) {
		#Pre-process the line
		chomp $line;
		$line	= (split('#', $line))[0];		# Remove comments
		next if($line =~ m/\^s*$/i );			# Skip lines with only whitespace
		my $parsed;
		if($line =~ m/(Object|Obj)s?\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 				= $3;
			$Translate_Object[$2]	= $parsed;
		}
#		if($line =~ m/(Object|Obj)s?[-_]?(Arg|Argument)?\[?(\d*)[.-](\d*)\]?\s*=\s*['"](.*)['"]/i ) {
#			$parsed 									= $5;
#			$Translate_Object_Argument[$3][$4 - 1]	= $parsed;
#		}
		print "Unable to parse $line\n" unless defined $parsed;
	}
}
sub generateMapping(){
	#Generate mapping for objects
	print $File_Mapping "#Objects\n";
	for my $object (0 .. $#Objects) {
		print $File_Mapping "Obj$object\t= '" . nameObject($object) . "'\n"	if defined $Objects[$object];
	}

}

##File Handling
#Open file handles
sub prepareFiles(){
	#Determine filenames to use
	$FileName_Path	= './';	# Default to no directory
	#TODO: UPDATE the recognized extensions
	if ($FileName_Compiled	=~ m/([-_\w\s]*)\.(dat|z\d)/i) {
	#When input file has a recognized extension, use the name of the file
		$FileName_Log			= $1 . '.log';
		$FileName_Mapping_Gen	= $1 . '.sym'	if defined $Option_Generate;
		$FileName_Decompiled	= $1 . '.src';
		$FileName_XML			= $1 . '.xml';
		$FileName_I7			= $1 . '.ni';
		$FileName_Path			= $1 . './'	unless defined $Option_Minimal;
	}
	else{
	#Otherwise decide on input agnostic file names
		$FileName_Log			= 'decompile.log';
		$FileName_Mapping_Gen	= 'decompile.sym'	if defined $Option_Generate;
		$FileName_Decompiled	= 'decompile.src';
		$FileName_XML			= 'story.xml';
		$FileName_I7			= 'story.ni';
		$FileName_Path			= 'decoded/'	unless defined $Option_Minimal;
	}
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
	#Open symbol mapping file if defined
	open($File_Mapping, "< :raw :bytes", $FileName_Mapping)
		|| die("Couldn't open $FileName_Mapping for reading.")
		if defined $FileName_Mapping;
	#Open generated output files
	open($File_Decompiled, "> :raw :bytes", $FileName_Path . $FileName_Decompiled)
		or die "$0: can't open $FileName_Path$FileName_Decompiled for writing: $!";
	open($File_I7, "> :raw :bytes", $FileName_Path . $FileName_I7)
		or die "$0: can't open $FileName_Path$FileName_I7 for writing: $!";
	open($File_XML, "> :raw :bytes", $FileName_Path . $FileName_XML)
		or die "$0: can't open $FileName_Path$FileName_XML for writing: $!";
	#Open mapping file with some sanity checking
	die "Overwriting existing symbol file with autogenerated is not supported in minimal mode"
		if defined $FileName_Mapping_Gen && $Option_Minimal && -e $FileName_Mapping_Gen;
}
sub closeInputFiles(){
	close($File_Compiled);
	close($File_Mapping)	if defined $FileName_Mapping;
	#For when symbol mapping is generated, we re-open the filehandle in read mode
	open($File_Mapping, "> :raw :bytes", $FileName_Path . $FileName_Mapping_Gen)
		|| die "$0: can't open " . $FileName_Path . $FileName_Mapping_Gen . "for writing: $!"
		if defined $Option_Generate;
}
sub closeOutputFiles(){
	close($File_Decompiled);
	close($File_Mapping)		if defined $Option_Generate;
	close($File_Log);
}
##Parsing
#Routines for parsing the file contents into memory structure
sub parse(){
	#Parse the symol mapping file if possible. NOTE: Also read when generating
	parseMapping() if defined $FileName_Mapping;
	#Read enough of the header to determine version
	parseHeader();
	#Load constants based on the version determined in header
	loadConstants();
	#Read in entire file for further parsing
	$Contents_Compiled	= read_file ( $FileName_Compiled, binmode => ':raw' );
	#TODO Add detailed parsing here
}

##Analyzing
#Routines for analyzing the memory structure
sub analyze(){

}
##Generate Output
#Routines for generating decompiled output
sub generate(){
	#generateMapping();
	#generateSource();
	#generateXML();
	#generateI7();
}
##Main Program Loop
print "Starting\n";
parseOptions();
prepareFiles();
print "Parsing $FileName_Compiled\n";
parse();
closeInputFiles();
print "Analyzing contents\n";
analyze();
print "Generating output\n";
generate();
closeOutputFiles();
print "Decompiling completed in ".(time - $Time_Start)." seconds.\n";
