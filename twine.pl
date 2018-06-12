use strict;					# 'Safest' operation level
use warnings;				# Give warnings
use File::Slurp;			# Read entire file at once
use File::Basename;			# Interpreting embedded filenames
use File::Path 'make_path';	# Creating directories
use XML::LibXML;
use Data::Dumper;			# Dumping data structures
use Carp;					# For stack tracing at errors

my $Time_Start	= time();	# Epoch time for start of processing
##Version History
my $Decompiler_Version		= '0.2';
#v0.1:	Initial structure for flow and storage
#v0.2:	Transformation of Twine2; Twine1 converts passages but not header

##Global Variables
#Story Settings
my $Compiler;				# The program used to compile the storyfile
my $Compiler_Version;		# The version used to compile the storyfile
my $Format;					# The story format used to create the story
my $Format_Version;			# The version used to create the story

#Story Data
my @Passages 			= ( undef );	# Passages, starting from ID 1.

#Symbol Translation Names
my @Symbol_Passage;						# Symbol names for passages

#Static Symbol Names

#File handling
my $FileName_Compiled;		# Filename for the compiled gamefile to decompile
my $FileName_Path	= './';	# Path to place output files in
my $FileName_Story;			# Filename for the decompiled story passages
my $FileName_Script;		# Filename for the decompiled scripts
my $FileName_Style;			# Filename for the decompiled stylesheets
my $FileName_Log;			# Filename for the log
my $FileName_XML;			# Filename for the XML output
my $File_Compiled;			# File handle for input compiled gamefile
my $File_Log;				# File handle for logging output
my $File_Story;				# File handle for output decompiled story passages
my $File_Script;			# File handle for output decompiled scripts
my $File_Style;				# File handle for output decompiled stylesheets
my $File_XML;				# File handle for XML output
my $Document;				# File contents
#Decompiling Options; see parseArguments()
my $Options	= "Decompiling Options:\n";
my $Option_Minimal;		# Skip output directory and embedded resources
$Options	.= "-m\t\tMinimalist mode, skipping output directory and resources\n";
my $Option_Verbose;		# Extra information dumped to story file
$Options	.= "-v\t\tVerbose loging output\n";
my $Option_Naming;		# Be extra aggressive on trying to determine names
						# TODO: This will create duplicate names, remake to avoid that
$Options	.= "-a\t\tAggressive naming of objects and properties\n";
##Initialization
sub initialize(){
	#Parse arguments;
	parseArguments();
	#There should be only one argument left, giving the name of the file to parse.
	die "Use: twine [options] file.html\n$Options" unless ($#ARGV eq 0);
	$FileName_Compiled	= $ARGV[0];
	if ($FileName_Compiled	=~ m/([-_\w\s]*)\.(html)/i) {
	#When input file has a recognized extension, use the name of the file
		$FileName_Path			= $1 . '/'	unless defined $Option_Minimal;
		$FileName_Log			= $1 . '.log';
		$FileName_Story			= $1 . '.tw2';
		$FileName_Script		= $1 . '-script.tw2';
		$FileName_Style			= $1 . '-style.tw2';
		$FileName_XML			= $1 . '.xml';
	}
	else{
	#Otherwise decide on input agnostic file names
		$FileName_Path			= 'decompiled/'	unless defined $Option_Minimal;
		$FileName_Log			= 'story.log';
		$FileName_Story			= 'story.tw2';
		$FileName_Script		= 'story-script.tw2';
		$FileName_Style			= 'story-style.tw2';
		$FileName_XML			= 'story.xml';
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
	#Open generated output files
	open($File_Story, "> :utf8", $FileName_Path . $FileName_Story)
		or die "$0: can't open $FileName_Path$FileName_Story for writing: $!";
	open($File_Script, "> :utf8", $FileName_Path . $FileName_Script)
		or die "$0: can't open $FileName_Path$FileName_Script for writing: $!";
	open($File_Style, "> :utf8", $FileName_Path . $FileName_Style)
		or die "$0: can't open $FileName_Path$FileName_Style for writing: $!";
	open($File_XML, "> :raw :bytes", $FileName_Path . $FileName_XML)
		or die "$0: can't open $FileName_Path$FileName_XML for writing: $!";
}
#Determine compiler version by reading the story header
sub determineVersion(){

}
#Initialize constants that might depend on version
sub loadConstants(){

}
sub loadFile(){
	#Read in the entire document; We need to use recover 2 because twine2 files contain illegal HTML elements that would normally be fatal
#	$Document		= XML::LibXML->load_html(location => $FileName_Compiled, recover => 2);
	$Document		= XML::LibXML->load_html(IO => $File_Compiled, recover => 2);
}
##Parsing each content type
sub parse(){
	#Header info for Twine2 is stored in tw-storydata
	my @headers	= $Document->findnodes( '//tw-storydata');
	#Only one header is expected, but if more than one is found...
	foreach my $header (@headers){
		{	#Story properties
			$Compiler			= $header->findnodes('./@creator');
			$Compiler_Version	= $header->findnodes('./@creator-version');
			$Format				= $header->findnodes('./@format');
			$Format_Version		= $header->findnodes('./@format-version');
			my $name			= $header->findnodes('./@name');
			my $ifid			= $header->findnodes('./@ifid');
			my $start			= $header->findnodes('./@startnode');
			my $options			= $header->findnodes('./@options');
			#Log header
			print $File_Log "Decompiler v$Decompiler_Version on $FileName_Compiled ($Format $Format_Version)\n";
			print $File_Log "Compiled by $Compiler $Compiler_Version\n";
			#Generate a configuration passage
			print $File_Story "::Configuration [twee2]\n";
			print $File_Story "Twee2::build_config.story_ifid = '$ifid'\n";
			print $File_Story "Twee2::build_config.story_format = '$Format'";
			#Include stylesheet and scripts
			print $File_Story "\n\n::StoryIncludes\n";
			print $File_Story "$FileName_Script\n";
			print $File_Story "$FileName_Style";
		}
		{	#Custom Stylesheets
			my @styles		= $header->findnodes('./style');
			my $style_count	= @styles;
			print $File_Log "$style_count stylesheets found:\n";
			foreach my $style (@styles){
				my $name		= $style->findnodes('./@id');
				print $File_Log "\t$name\n";
				#Generate a configuration passage
				print $File_Style "::$name [stylesheet]\n";
				print $File_Style $style->to_literal();
			}
		}
		{	#Custom Scripts
			my @scripts			= $header->findnodes('./script');
			my $script_count	= @scripts;
			print $File_Log "$script_count scripts found:\n";
			foreach my $script (@scripts){
				my $name		= $script->findnodes('./@id');
				print $File_Log "\t$name\n";
				#Generate a configuration passage
				print $File_Script "::$name [script]\n";
				print $File_Script $script->to_literal();
			}
		}
	}
	#Each passage in Twine2 is stored as a tw-passagedata element
	my @passages	= $Document->findnodes( '//tw-passagedata');
	my $pass_count	= @passages;
	#Twine2; tw-passagedata found
	if ($pass_count > 0) {
		print $File_Log "$pass_count passages found:\n";
		foreach my $passage (@passages){
			#Parse the passage; splitting out the header and closing tag
			my $pid		= $passage->findnodes('./@pid');
			my $name	= $passage->findnodes('./@name');
			my $tags	= $passage->findnodes('./@tags');
			my $pos		= $passage->findnodes('./@position');
			my $size	= $passage->findnodes('./@size');
			#Prepare tags and pos
			$tags	= " [$tags]"	unless $tags eq '';
			$pos	= " <$pos>"		unless $pos eq '';
			#Log the passage
			print $File_Log "\t$pid\t$name$tags\n";
			#Create Twee2 passage
			print $File_Story "\n\n::$name$tags$pos\n";
			print $File_Story $passage->to_literal();
		}
	}
	#Assumed Twine1; look for div with the the tiddler attribute
	else {
		@passages	= $Document->findnodes( '//div[@tiddler]');
		$pass_count	= @passages;
		print $File_Log "$pass_count passages found:\n";
		my $pid	= 1;
		foreach my $passage (@passages){
			#Parse the passage; splitting out the header and closing tag
			my $name	= $passage->findnodes('./@tiddler');
			my $tags	= $passage->findnodes('./@modifier');
			my $pos		= $passage->findnodes('./@twine-position');
			my $created	= $passage->findnodes('./@created');
			#Prepare tags and pos
			$tags	= " [$tags]"	unless $tags eq '';
			$pos	= " <$pos>"		unless $pos eq '';
			#Log the passage
			print $File_Log "\t$pid\t$name$tags\n";
			$pid++;
			#Create Twee2 passage; converting some special characters
			print $File_Story "\n\n::$name$tags$pos\n";
			my $text	= $passage->to_literal();
			$text		=~ s/\\n/\n/g;
			$text		=~ s/\\t/\t/g;
			print $File_Story $text;
		}
	}
}
##Analyzing cross-type
sub analyze(){

}

##Generate output
sub generate(){

}

##Utility


##Main Program Loop
initialize();		# Parse command line arguments for options and filename
print "Preparing to read $FileName_Compiled\n";
openFiles();		# Open file handles
determineVersion();	# Read the header to determine version
print "Reading...\n";
loadFile();			# Read the compiled file into memory and close input files
loadConstants();	# Initialize version dependant constants
print "Parsing...\n";
parse();			# Parse the compiled file into memory structure
print "Analyzing...\n";
analyze();			# Deeper analysis that depends on the entire story being parsed
print "Generating output...\n";
generate();			# Generate output and close the files
print "Decompiling completed in ".(time - $Time_Start)." seconds.\n";
