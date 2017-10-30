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

##Global Variables
#Story Settings
my $Compiler_Version;		# The version used to compile the storyfile
#Story

#Story Data
my @Objects 			= ( undef );	# Objects, starting from ID 1.

#Symbol Translation Names
my @Symbol_Object;						# Object names for 'objects'

#Constants & Static Names 

#File handling
my $FileName_Compiled;		# Filename for the compiled gamefile to decompile
my $FileName_Path	= './';	# Path to place output files in
my $FileName_Decompiled;	# Filename for the decompiled sourcecode
my $FileName_Log;			# Filename for the log
my $FileName_Symbol;		# Filename for the symbol mapping translation input file
my $FileName_Symbol_Gen;	# Filename for the symbol mapping translation output file
my $FileName_I7;			# Filename for the Inform output
my $FileName_XML;			# Filename for the XML output
my $File_Compiled;			# File handle for input compiled gamefile
my $File_Log;				# File handle for logging output
my $File_Decompiled;		# File handle for output decompiled sourcecode
my $File_Symbol;			# File handle for symbol mapping translation (both input and output)
my $File_I7;				# File handle for Inform output
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
##Initialization
sub initialize(){
	#Parse arguments;
	parseArguments();
	#There should be only one argument left, giving the name of the file to parse.
#TODO: UPDATE the name of script and expected extension
	die "Use: DECOMPILER [options] file.EXTENSION\n$Options" unless ($#ARGV eq 0);
	$FileName_Compiled	= $ARGV[0];
#TODO: UPDATE the recognized extensions
	if ($FileName_Compiled	=~ m/([-_\w\s]*)\.(dat|z\d)/i) {
	#When input file has a recognized extension, use the name of the file
		$FileName_Path			= $1 . '/'	unless defined $Option_Minimal;
		$FileName_Log			= $1 . '.log';
		$FileName_Decompiled	= $1 . '.src';
		$FileName_XML			= $1 . '.xml';
		$FileName_I7			= $1 . '.ni';
		$FileName_Symbol_Gen	= $1 . '.sym'	if defined $Option_Generate;
	}
	else{
	#Otherwise decide on input agnostic file names
		$FileName_Path			= 'decompiled/'	unless defined $Option_Minimal;
		$FileName_Log			= 'story.log';
		$FileName_Decompiled	= 'story.src';
		$FileName_XML			= 'story.xml';
		$FileName_I7			= 'story.ni';
		$FileName_Symbol_Gen	= 'story.sym'	if defined $Option_Generate;
	}
	openFiles();
}
sub parseArguments(){
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
		elsif($#ARGV >= 0 && $ARGV[0] eq '-a') {		
			$Option_Naming		= 1;
			splice(@ARGV, 0, 1);
		}
		else{ last }
	}
}
#Open file handles
sub openFiles(){
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
	#Open symbol mapping file if defined
	open($File_Symbol, "< :raw :bytes", $FileName_Symbol)
		|| die("Couldn't open $FileName_Symbol for reading.")
		if defined $FileName_Symbol;
	#Open generated output files
	open($File_Decompiled, "> :raw :bytes", $FileName_Path . $FileName_Decompiled)
		or die "$0: can't open $FileName_Path$FileName_Decompiled for writing: $!";
	open($File_I7, "> :raw :bytes", $FileName_Path . $FileName_I7)
		or die "$0: can't open $FileName_Path$FileName_I7 for writing: $!";
	open($File_XML, "> :raw :bytes", $FileName_Path . $FileName_XML)
		or die "$0: can't open $FileName_Path$FileName_XML for writing: $!";
	#Open mapping file with some sanity checking
	die "Overwriting existing symbol file with autogenerated is not supported in minimal mode"
		if defined $FileName_Symbol_Gen && $Option_Minimal && -e $FileName_Symbol_Gen;
}
#Determine compiler version by reading the story header
sub determineVersion(){

}
#Initialize constants that might depend on version
sub loadConstants(){

}
#Load symbol mapping translation from given file
sub loadSymbols(){
	return unless defined $FileName_Mapping;
	while (my $line = <$File_Symbol>) {
		#Pre-process the line
		chomp $line;
		$line	= (split('#', $line))[0];		# Remove comments
		#Skip ahead if the line doesn't contain anything
		next if($line =~ m/\^s*$/i );
		my $parsed;
		if ($line =~ m/(Object|Obj)s?\[?(\d*)\]?\s*=\s*['"](.*)['"]/i ) {
			$parsed 			= $3;
			$Symbol_Object[$2]	= $parsed;
		}
#		if($line =~ m/(Object|Obj)s?[-_]?(Arg|Argument)?\[?(\d*)[.-](\d*)\]?\s*=\s*['"](.*)['"]/i ) {
#			$parsed 							= $5;
#			$Symbol_Object_Argument[$3][$4 - 1]	= $parsed;
#		}
		print "Unable to parse $line\n" unless defined $parsed;
	}
}
sub loadFile(){

}
##Parsing each content type
sub parse(){

}
##Analyzing cross-type
sub analyze(){

}

##Generate output
sub generate(){

}



##Main Program Loop
initialize();		# Parse command line arguments for options and filename
print "Preparing to read $FileName_Compiled\n";
openFiles();		# Open file handles
determineVersion();	# Read the header to determine version
loadConstants();	# Initialize version dependant constants
loadSymbols();		# Parse the translation mapping file
print "Reading...\n";
loadFile();			# Read the compiled file into memory and close input files
print "Parsing...\n";
parse();			# Parse the compiled file into memory structure
print "Analyzing...\n";
analyze();			# Deeper analysis that depends on the entire story being parsed
print "Generating output...\n";
generate();			# Generate output and close the files
print "Decompiling completed in ".(time - $Time_Start)." seconds.\n";
