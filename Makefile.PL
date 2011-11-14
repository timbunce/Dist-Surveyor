
use strict;
use warnings;

use 5.006;

use ExtUtils::MakeMaker 6.30;



my %WriteMakefileArgs = (
  "ABSTRACT" => "Survey installed modules and determine the specific distribution versions they came from",
  "AUTHOR" => "Tim Bunce <Tim.Bunce\@pobox.com>",
  "BUILD_REQUIRES" => {
    "File::Temp" => 0,
    "Test::More" => "0.88"
  },
  "CONFIGURE_REQUIRES" => {
    "ExtUtils::MakeMaker" => "6.30"
  },
  "DISTNAME" => "Dist-Surveyor",
  "EXE_FILES" => [],
  "LICENSE" => "perl",
  "NAME" => "Dist::Surveyor",
  "PREREQ_PM" => {
    "CPAN::DistnameInfo" => 0,
    "Carp" => 0,
    "Compress::Zlib" => 0,
    "Config" => 0,
    "DBI" => 0,
    "DB_File" => 0,
    "Data::Dumper::Concise" => 0,
    "Digest::SHA" => 0,
    "ExtUtils::Perllocal::Parser" => 0,
    "Fcntl" => 0,
    "File::Basename" => 0,
    "File::Fetch" => 0,
    "File::Find" => 0,
    "File::Path" => 0,
    "File::Slurp" => 0,
    "File::Spec" => 0,
    "File::Spec::Unix" => 0,
    "Getopt::Long" => 0,
    "LWP::Simple" => 0,
    "List::Util" => 0,
    "MLDBM" => 0,
    "Memoize" => 0,
    "MetaCPAN::API" => "0.32",
    "Module::CoreList" => 0,
    "Module::Metadata" => 0,
    "Storable" => 0,
    "Try::Tiny" => 0,
    "URI" => 0,
    "autodie" => 0,
    "constant" => 0,
    "strict" => 0,
    "version" => 0,
    "warnings" => 0
  },
  "VERSION" => "0.001",
  "test" => {
    "TESTS" => "t/*.t"
  }
);


unless ( eval { ExtUtils::MakeMaker->VERSION(6.56) } ) {
  my $br = delete $WriteMakefileArgs{BUILD_REQUIRES};
  my $pp = $WriteMakefileArgs{PREREQ_PM};
  for my $mod ( keys %$br ) {
    if ( exists $pp->{$mod} ) {
      $pp->{$mod} = $br->{$mod} if $br->{$mod} > $pp->{$mod};
    }
    else {
      $pp->{$mod} = $br->{$mod};
    }
  }
}

delete $WriteMakefileArgs{CONFIGURE_REQUIRES}
  unless eval { ExtUtils::MakeMaker->VERSION(6.52) };

WriteMakefile(%WriteMakefileArgs);



