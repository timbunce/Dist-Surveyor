#!/bin/env perl

=head1 NAME

dist_surveyor.pl - determine exactly what dist versions are installed

=head1 SYNOPSIS

  dist_surveyor.pl [options] /some/perl/lib/dir

=head1 DESCRIPTION

This utility examines all the modules installed within the specified perl
library directory and uses the metacpan API to work out what versions of what
distributions could have provided those modules. It then works out which of
those candidate distributions is the most likely one. It is fairly robust and
copes well with edge cases like installation of non-released versions from git
repos and local modifications.

Distributions are written to stdout. Progress and issues are reported to stderr.

It can take a long time to run for the first time on a directory with a
large number of modules and candidate distributions.  The data fetched from
metacpan is cached so future runs are much faster.  (The system this code was
tested on took about 60 minutes to process around 500 distributions with no
cached data, and under 10 minutes for later runs that coud reuse the cached
data. The cache file ended up about 40MB in size.)

=head1 OPTIONS

    --verbose    Show more detailed progress

    --debug      Show much more information

    --match R    Ignore modules that don't match regex R (unanchored)

    --perlver V  Ignore modules that are shipped with perl version V

    --remnants   Include old distribution versions that have left old modules behind

    --uncached   Don't use or update the persistent cache

    --makecpan D Create a CPAN repository in directory D

    --output S   List of field names ot output, separate by spaces.
                 
    --format S   Printf format string with a %s for each field in --output

=head2 --makecpan

Creates a CPAN repository in the specified directory by fetching the selected
distributions into authors/id/... and writing the index files into modules/...

If the directory already exists then selected distributions that already exist
are not refetched, any distributions that already exist but aren't selected by
this run are left in place.

New package distribution information is merged into the modules/02packages index file.

Some additional files are written into a dist_surveyor subdirectory:

=head3 dist_surveyor/token_packages.txt

This file lists one unique 'token package' per distribution. It's very useful
to speed up re-running a full install after some distributions have failed.

=head1 WORKING WITH THE RESULTS

Firsly you should check the results related to any modules that generated
warnings during the run.

You can use cpanm --scandeps to put the list in dependency order:

    dist_surveyor.pl --makecpan my_cpan /some/perl/lib/dir > installed_dists.txt
    cpanm --mirror file:$PWD/my_cpan [--mirror-only] -l new_lib < installed_dists.txt

That will always reinstall all the listed distributions. If some distributions
fail to install (typically due to test failures) then it's much faster to use the
'token package list':

    cpanm --mirror file:$PWD/my_cpan [--mirror-only] -l new_lib < my_cpan/dist_surveyor/token_packages.txt

Using package name allows cpanm to skip those that it knows are already installed.

=head1 BUGS

Probably.

The fine metacpan folk will probably want to shoot me for the load this places
on their servers.

=head1 POSSIBLE ENHANCEMENTS

* Auto-detect when directory given isn't the root of a perl library dir tree.
    E.g. by matching file names to module names

* Sort out ExtUtils::Perllocal::Parser situation

* Avoid hard-coded %distro_key_mod_names related to perllocal.pod where the
    dist name doesn't match the key module name.

* Optimise use of metacpan. Use ElasticSearch.pm.

* For installed modules get the file modification time (last commit time)
    and use it to eliminate candidate dists that were released after that time.

* Add support for matching Foo.pm.PL files (e.g. FCGI and common::sense)

* Consider factoring in release status ('authorized') so rogue releases
    that ship copies of many other modules (like Net-Braintree-0.1.1)
    are given a lower priority.

* Fully handle merging of pre-existing --makecpan directory data files.

* Consider factoring install date in the output ordering. May help with edge cases
    where a package P is installed via distros A then B. If A is reinstalled after B
    then the reinstalled P will be from A but should be from B. (I don't know of any
    cases, but it's certainly a possibility. The LWP breakup and Class::MOP spring to
    mind as possible candidates.)

=cut

use strict;
use warnings;
use version;
use autodie;
use Carp;
use Compress::Zlib;
use Config;
use CPAN::DistnameInfo;
use Data::Dumper::Concise;
use DBI qw(looks_like_number);
use Digest::SHA qw(sha1_base64);
use Fcntl qw(:DEFAULT :flock);
use File::Fetch;
use File::Basename;
use File::Find;
use File::Path;
use File::Slurp;
use File::Spec;
use File::Spec::Unix;
use Getopt::Long;
use List::Util qw(max sum);
use LWP::Simple;
use Memoize;
use MetaCPAN::API 0.32;
use DB_File;
use MLDBM qw(DB_File Storable);
use Module::CoreList;
use Module::Metadata;
use Storable qw(nfreeze);
use Try::Tiny;
use URI;

use constant PROGNAME => 'dist_surveyor';
use constant ON_WIN32 => $^O eq 'MSWin32';
use constant ON_VMS   => $^O eq 'VMS';

$| = 1;

GetOptions(
    'match=s' => \my $opt_match,
    'v|verbose!' => \my $opt_verbose,
    'd|debug!' => \my $opt_debug,
    # target perl version, re core modules
    'perlver=s' => \my $opt_perlver,
    # include old dists that have remnant/orphaned modules installed
    'remnants!' => \my $opt_remnants,
    # don't use a persistent cache
    'uncached!' => \my $opt_uncached,
    'makecpan=s' => \my $opt_makecpan,
    # e.g., 'download_url author'
    'output=s' => \(my $opt_output ||= 'url'),
    # e.g., 'some-command --foo --file %s --authorid %s'
    'format=s' => \my $opt_format,
) or exit 1;

$opt_verbose++ if $opt_debug;
$opt_perlver = version->parse($opt_perlver || $])->numify;

my $major_error_count = 0; # exit status

my $metacpan_size = 999; # don't make too large, hurts the server
my $metacpan_calls = 0;
my $metacpan_api ||= MetaCPAN::API->new(
    ua_args => [ agent => $0 ],
);


# caching via persistent memoize

my $db_generation = 1; # XXX increment on incompatible change
my $memoize_file = PROGNAME."-$db_generation.db";
my %memoize_cache;
if (not $opt_uncached) {
    # XXX no need for MLDBM now? Could just use DB_File
    my $db = tie %memoize_cache => 'MLDBM', $memoize_file, O_CREAT|O_RDWR, 0640
        or die "Unable to use persistent cache: $!";
    # XXX this locking is flawed but good enough for my needs
    # http://search.cpan.org/~pmqs/DB_File-1.824/DB_File.pm#HINTS_AND_TIPS
    my $fd = $db->fd;
    open(DB_FH, "+<&=$fd") || die "dup $!";
    flock (DB_FH, LOCK_EX) || die "flock: $!";
}
my %memoize_subs = (
    get_candidate_cpan_dist_releases => { generation => 1 },
    get_module_versions_in_release   => { generation => 1 },
);
for my $subname (keys %memoize_subs) {
    my %memoize_args = %{$memoize_subs{$subname}};
    my $generation = delete $memoize_args{generation} || 1;
    $memoize_args{SCALAR_CACHE} = [ HASH => \%memoize_cache ];
    $memoize_args{LIST_CACHE}   = 'FAULT';
    # TODO use faster normalizer for subs that don't get refs
    # not needed because we don't pass refs
    #$memoize_args{NORMALIZER} = sub { $Storable::canonical = 1; sha1_base64(nfreeze([ $subname, $generation, wantarray, @_ ])) }
    memoize($subname, %memoize_args);
}



# for distros with names that don't match the principle module name
# yet the principle module version always matches the distro
# Used for perllocal.pod lookups
# # XXX should be automated lookup rather than hardcoded
my %distro_key_mod_names = (
    'PathTools' => 'File::Spec',
    'Template-Toolkit' => 'Template',
    'TermReadKey' => 'Term::ReadKey',
    'libwww-perl' => 'LWP',
    'ack' => 'App::Ack',
);


# give only top-level lib dir, the archlib will be added automatically
my @libdir = shift;
die "$libdir[0] isn't a directory\n" unless -d $libdir[0];
if (-d (my $archdir = "$libdir[0]/$Config{archname}")) {
    unshift @libdir, $archdir;
}

my @installed_releases = determine_installed_releases(@libdir);
write_fields(\@installed_releases, $opt_format, [split ' ', $opt_output], \*STDOUT);

warn sprintf "Completed survey in %.1f minutes using %d metacpan calls.\n",
    (time-$^T)/60, $metacpan_calls;


if ($opt_makecpan) {
    warn "Updating $opt_makecpan for ".@installed_releases." releases...\n";
    mkpath("$opt_makecpan/modules");

    my %pkg_ver_rel;    # for 02packages
    for my $ri (@installed_releases) {

        # --- get the file

        my $main_url = URI->new($ri->{download_url});
        my $di = distname_info_from_url($main_url);
        my $pathfile = "authors/id/".$di->pathname;
        my $destfile = "$opt_makecpan/$pathfile";
        mkpath(dirname($destfile));

        my @urls = ($main_url);
        for my $mirror ('http://backpan.perl.org') {
            push @urls, "$mirror/$pathfile";
        }

        my $mirror_status;
        for my $url (@urls) {
            $mirror_status = eval { mirror($url, $destfile) };
            last if not is_error($mirror_status||500);
        }
        if ($@ || is_error($mirror_status)) {
            my $err = ($@ and chomp $@) ? $@ : $mirror_status;
            my $msg = "Error $err mirroring $main_url";
            if (-f $destfile) {
                warn "$msg - using existing file\n";
            }
            else {
                # better to keep going and add the packages to the index
                # than abort at this stage due to network/mirror problems
                # the user can drop the files in later
                warn "$msg - continuing, ADD FILE MANUALLY!\n";
                ++$major_error_count;
            }
        }
        else {
            warn "$mirror_status $main_url\n" if $opt_verbose;
        }


        my $mods_in_rel = get_module_versions_in_release($ri->{author}, $ri->{name});

        if (!keys %$mods_in_rel) { # XXX hack for common::sense
            (my $dist_as_pkg = $ri->{distribution}) =~ s/-/::/g;
            warn "$ri->{author}/$ri->{name} has no modules! Adding fake module $dist_as_pkg ".$di->version."\n";
            $mods_in_rel->{$dist_as_pkg} = {
                name => $dist_as_pkg,
                version => $di->version,
                version_obj => version->parse($di->version),
            };
        }


        # --- accumulate package info for 02packages file

        for my $pkg (sort keys %$mods_in_rel ) {
            # pi => { name=>, version=>, version_obj=> }
            my $pi = $mods_in_rel->{$pkg};

            # for selecting which dist a package belongs to
            # XXX should factor in authorization status
            my $p_r_match_score = p_r_match_score($pkg, $ri);

            if (my $pvr = $pkg_ver_rel{$pkg}) {
                # already seen same package name in different distribution
                if ($p_r_match_score < $pvr->{p_r_match_score}) {
                    warn "$pkg seen in $pvr->{ri}{name} so ignoring one in $ri->{name}\n";
                    next;
                }
                warn "$pkg seen in $pvr->{ri}{name} - now overridden by $ri->{name}\n";
            }

            my $line = _fmtmodule($pkg, $di->pathname, $pi->{version});
            $pkg_ver_rel{$pkg} = { line => $line, pi => $pi, ri => $ri, p_r_match_score => $p_r_match_score };
        }

    }


    # --- write 02packages file

    my $pkg_lines = _readpkgs($opt_makecpan);
    my %packages;
    for my $line (@$pkg_lines, map { $_->{line} } values %pkg_ver_rel) {
        my ($pkg) = split(/\s+/, $line, 2);
        if ($packages{$pkg} and $packages{$pkg} ne $line) {
            warn "Old $packages{$pkg}\nNew $line\n" if $opt_verbose;
        }
        $packages{$pkg} = $line;
    };
    _writepkgs($opt_makecpan, [ sort values %packages ] );


    # --- write extra data files that may be useful XXX may change
    # XXX these don't all (yet?) merge with existing data
    my $survey_datadump_dir = "$opt_makecpan/".PROGNAME;
    mkpath($survey_datadump_dir);

    # Write list of token packages - each should match only one release.
    # This makes it _much_ faster to do installs via cpanm because it
    # can skip the modules it knows are installed (whereas using a list of
    # distros it has to reinstall _all_ of them every time).
    # XXX maybe add as a separate option: "--mainpkgs mainpkgs.lst"
    my %dist_packages;
    while ( my ($pkg, $line) = each %packages) {
        my $distpath = (split /\s+/, $line)[2];
        $dist_packages{$distpath}{$pkg}++;
    }
    my %token_package;
    my %token_package_pri = (       # alter install order for some modules
        'Module::Build' => 100,     # should be near first
        Moose => 50,

        # install distros that use Module::Install late so their dependencies
        # have already been resolved (else they try to fetch them directly,
        # bypassing our cpanm --mirror-only goal)
        'Olson::Abbreviations' => -90,

        # distros with special needs
        'Term::ReadKey' => -100,    # tests hang if run in background
    );
    for my $distpath (sort keys %dist_packages) {
        my $dp = $dist_packages{$distpath};
        my $di = CPAN::DistnameInfo->new($distpath);
        #warn Dumper([ $distpath, $di->dist, $di]);
        (my $token_pkg = $di->dist) =~ s/-/::/g;
        if (!$dp->{$token_pkg}) {
            if (my $keypkg = $distro_key_mod_names{$di->dist}) {
                $token_pkg = $keypkg;
            }
            else {
                # XXX not good - may pick a dummy test package
                $token_pkg = (grep { $_ } keys %$dp)[0] || $token_pkg;
                warn "Picked $token_pkg as token package for ".$di->distvname."\n";
            }
        }
        $token_package{$token_pkg} = $token_package_pri{$token_pkg} || 0;
    }

    my @main_pkgs = sort { $token_package{$b} <=> $token_package{$a} or $a cmp $b } keys %token_package;
    open my $key_pkg_fh, ">", "$survey_datadump_dir/token_packages.txt";
    print $key_pkg_fh "$_\n" for @main_pkgs;
    close $key_pkg_fh;

    # Write list of releases, like default stdout
    open my $rel_fh, ">", "$survey_datadump_dir/releases.txt";
    write_fields(\@installed_releases, undef, [qw(url)], $rel_fh);
    close $rel_fh;

    # dump the primary result data for additional info and debugging
    my $gzwrite = gzopen("$survey_datadump_dir/_data_dump.perl.gz", 'wb')
        or croak "Cannot open $survey_datadump_dir/_data_dump.perl.gz for writing: $gzerrno";
    $gzwrite->gzwrite("[\n");
    for my $ri (@installed_releases) {
        $gzwrite->gzwrite(Dumper($ri));
        $gzwrite->gzwrite(",");
    }
    $gzwrite->gzwrite("]\n");
    $gzwrite->gzclose;

    warn "$opt_makecpan updated.\n"
}

exit $major_error_count;



sub p_r_match_score {
    my ($pkg_name, $ri) = @_;
    my @p = split /\W/, $pkg_name;
    my @r = split /\W/, $ri->{name};
    for my $i (0..max(scalar @p, scalar @r)) {
        return $i if not defined $p[$i]
                  or not defined $r[$i]
                  or $p[$i] ne $r[$i]
    }
    die; # unreached
}


sub write_fields {
    my ($releases, $format, $fields, $fh) = @_;

    $format ||= join("\t", ('%s') x @$fields);
    $format .= "\n";

    for my $release_data (@$releases) {
        printf $fh $format, map {
            exists $release_data->{$_} ? $release_data->{$_} : "?$_"
        } @$fields;
    }
}


sub determine_installed_releases {
    my (@search_dirs) = @_;

    warn "Searching @search_dirs\n" if $opt_verbose;

    my %installed_mod_info;

    warn "Finding modules in @search_dirs\n";
    my ($installed_mod_files, $installed_meta) = find_installed_modules(@search_dirs);

    # get the installed version of each installed module and related info
    warn "Finding candidate releases for the ".keys(%$installed_mod_files)." installed modules\n";
    foreach my $module ( sort keys %$installed_mod_files ) {
        my $mod_file = $installed_mod_files->{$module};

        if ($opt_match) {
            if ($module !~ m/$opt_match/o) {
                delete $installed_mod_files->{$module};
                next;
            }
        }

        module_progress_indicator($module) unless $opt_verbose;

        my $mod_version = do {
            # silence warnings about duplicate VERSION declarations
            # eg Catalyst::Controller::DBIC::API* 2.002001
            local $SIG{__WARN__} = sub { warn @_ if $_[0] !~ /already declared with version/ };
            my $mm = Module::Metadata->new_from_file($mod_file);
            $mm->version; # only one version for one package in file
        };
        $mod_version ||= 0; # XXX
        my $mod_file_size = -s $mod_file;

        # Eliminate modules that will be supplied by the target perl version
        if ( my $cv = $Module::CoreList::version{ $opt_perlver }->{$module} ) {
            $cv =~ s/ //g;
            if (version->parse($cv) >= version->parse($mod_version)) {
                warn "$module $mod_version is core in perl $opt_perlver (as v$cv) - skipped\n";
                next;
            }
        }

        my $mi = $installed_mod_info{$module} = {
            file => $mod_file,
            module => $module,
            version => $mod_version,
            version_obj => version->parse($mod_version),
            size => $mod_file_size,
        };

        # ignore modules we know aren't indexed
        next if $module =~ /^Moose::Meta::Method::Accessor::Native::/;

        # XXX could also consider file mtime: releases newer than the mtime
        # of the module file can't be the origin of that module file.
        # (assuming clocks and file times haven't been messed with)

        try {
            my $ccdr = get_candidate_cpan_dist_releases($module, $mod_version, $mod_file_size);
            if (not %$ccdr) {
                $ccdr = get_candidate_cpan_dist_releases($module, $mod_version, 0);
                if (%$ccdr) {
                    # probably either a local change/patch or installed direct from repo
                    # but with a version number that matches a release
                    warn "$module $mod_version on CPAN but with different file size (not $mod_file_size)\n"
                        if $mod_version or $opt_verbose;
                    $mi->{file_size_mismatch}++;
                }
                elsif ($ccdr = get_candidate_cpan_dist_releases_fallback($module, $mod_version) and %$ccdr) {
                    warn "$module $mod_version not on CPAN but assumed to be from @{[ sort keys %$ccdr ]}\n"
                        if $mod_version or $opt_verbose;
                    $mi->{cpan_dist_fallback}++;
                }
                else {
                    $mi->{version_not_on_cpan}++;
                    # Possibly:
                    # - a local change/patch or installed direct from repo
                    #   with a version number that was never released.
                    # - a private module never released on cpan.
                    # - a build-time create module eg common/sense.pm.PL
                    warn "$module $mod_version not found on CPAN\n"
                        if $mi->{version} # no version implies uninteresting
                        or $opt_verbose;
                    # XXX could try finding the module with *any* version on cpan
                    # to help with later advice. ie could select as candidates
                    # the version above and the version below the number we have,
                    # and set a flag to inform later logic.
                }
            }
            $mi->{candidate_cpan_dist_releases} = $ccdr if %$ccdr;
        }
        catch {
            warn "Failed get_candidate_cpan_dist_releases($module, $mod_version, $mod_file_size): $_";
        }

    }


    # Map modules to dists using the accumulated %installed_mod_info info

    warn "*** Mapping modules to releases\n";

    my %best_dist;
    foreach my $mod ( sort keys %installed_mod_info ) {
        my $mi = $installed_mod_info{$mod};

        module_progress_indicator($mod) unless $opt_verbose;

        # find best match among the cpan releases that included this module
        my $ccdr = $installed_mod_info{$mod}{candidate_cpan_dist_releases}
            or next; # no candidates, warned about above (for mods with a version)

        my $best_dist_cache_key = join " ", sort keys %$ccdr;
        our %best_dist_cache;
        my $best = $best_dist_cache{$best_dist_cache_key}
            ||= pick_best_cpan_dist_release($ccdr, \%installed_mod_info);

        my $note = "";
        if (@$best > 1) { # try using perllocal.pod to narrow the options
            my @in_perllocal = grep {
                my $distname = $_->{distribution};
                my ($v, $dist_mod_name) = perllocal_distro_mod_version($distname, $installed_meta->{perllocalpod});
                warn "$dist_mod_name in perllocal.pod: ".($v ? "YES" : "NO")."\n"
                    if $opt_debug;
                $v;
            } @$best;
            if (@in_perllocal && @in_perllocal < @$best) {
                $note = sprintf "narrowed from %d via perllocal", scalar @$best;
                $best = \@in_perllocal;
            }
        }

        if (@$best > 1 or $note) { # note the poor match for this module
            # but not if there's no version (as that's common)
            my $best_desc = join " or ", map { $_->{release} } @$best;
            my $pct = sprintf "%.2f%%", $best->[0]{fraction_installed} * 100;
            warn "$mod $mi->{version} odd best match: $best_desc $note ($best->[0]{fraction_installed})\n"
                if $note or $opt_verbose or ($mi->{version} and $best->[0]{fraction_installed} < 0.3);
            # if the module has no version and multiple best matches
            # then it's unlikely make a useful contribution, so ignore it
            # XXX there's a risk that we'd ignore all the modules of a release
            # where none of the modules has a version, but that seems unlikely.
            next if not $mi->{version};
        }

        for my $dist (@$best) {
            # two level hash to make it easier to handle versions
            my $di = $best_dist{ $dist->{distribution} }{ $dist->{release} } ||= { dist => $dist };
            push @{ $di->{modules} }, $mi;
            $di->{or}{$_->{release}}++ for grep { $_ != $dist } @$best;
        }

    }

    warn "*** Refining releases\n";

    # $best_dist{ Foo }{ Foo-1.23 }{ dist=>$dist_struct, modules=>, or=>{ Foo-1.22 => $dist_struct } }

    my @installed_releases;    # Dist-Name => { ... }

    for my $distname ( sort keys %best_dist ) {
        my $releases = $best_dist{$distname};

        my @dist_by_version  = sort {
            $a->{dist}{version_obj}        <=> $b->{dist}{version_obj} or
            $a->{dist}{fraction_installed} <=> $b->{dist}{fraction_installed}
        } values %$releases;
        my @dist_by_fraction = sort {
            $a->{dist}{fraction_installed} <=> $b->{dist}{fraction_installed} or
            $a->{dist}{version_obj}        <=> $b->{dist}{version_obj}
        } values %$releases;
        
        my @remnant_dists  = @dist_by_version;
        my $installed_dist = pop @remnant_dists;

        # is the most recent candidate dist version also the one with the
        # highest fraction_installed?
        if ($dist_by_version[-1] == $dist_by_fraction[-1]) {
            # this is the common case: we'll assume that's installed and the
            # rest are remnants of earlier versions
        }
        elsif ($dist_by_fraction[-1]{dist}{fraction_installed} == 100) {
            warn "Unsure which $distname is installed from among @{[ keys %$releases ]}\n";
            @remnant_dists  = @dist_by_fraction;
            $installed_dist = pop @remnant_dists;
            warn "Selecting the one that apprears to be 100% installed\n";
        }
        else {
            # else grumble so the user knows to ponder the possibilities
            warn "Can't determine which $distname is installed from among @{[ keys %$releases ]}\n";
            warn Dumper([\@dist_by_version, \@dist_by_fraction]);
            warn "\tSelecting based on latest version\n";
        }

        if (@remnant_dists or $opt_debug) {
            warn "Distributions with remnants (chosen release is first):\n"
                unless our $dist_with_remnants_warning++;
            warn "@{[ map { $_->{dist}{release} } reverse @dist_by_fraction ]}\n"; 
            for ($installed_dist, @remnant_dists) {
                my $fi = $_->{dist}{fraction_installed};
                my $modules = $_->{modules};
                my $mv_desc = join(", ", map { "$_->{module} $_->{version}" } @$modules);
                warn sprintf "\t%s\t%s%% installed: %s\n",
                    $_->{dist}{release},
                    $_->{dist}{percent_installed},
                    (@$modules > 4 ? "(".@$modules." modules)" : $mv_desc),
            }
        }

        # note ordering: remnants first
        for (($opt_remnants ? @remnant_dists : ()), $installed_dist) {
            my ($author, $distribution, $release)
                = @{$_->{dist}}{qw(author distribution release)};

            $metacpan_calls++;
            my $release_data = $metacpan_api->release( author => $author, release => $release );
            if (!$release_data) {
                warn "Can't find release details for $author/$release - SKIPPED!\n";
                next; # XXX could fake some of $release_data instead
            }

            # shortcuts
            (my $url = $release_data->{download_url}) =~ s{ .*? \b authors/ }{authors/}x;

            push @installed_releases, {
                # 
                %$release_data,
                # extra items mushed inhandy shortcuts
                url => $url,
                # raw data structures
                dist_data => $_->{dist},
            };
        }
        #die Dumper(\@installed_releases);
    }

    # sorting into dependency order could be added later, maybe

    return @installed_releases;
}


# pick_best_cpan_dist_release - memoized
# for each %$ccdr adds a fraction_installed based on %$installed_mod_info
# returns ref to array of %$ccdr values that have the max fraction_installed

sub pick_best_cpan_dist_release {
    my ($ccdr, $installed_mod_info) = @_;

    for my $release (sort keys %$ccdr) {
        my $release_info = $ccdr->{$release};
        $release_info->{fraction_installed}
            = dist_fraction_installed($release_info->{author}, $release, $installed_mod_info);
        $release_info->{percent_installed} # for informal use
            = sprintf "%.2f", $release_info->{fraction_installed} * 100;
    }

    my $max_fraction_installed = max( map { $_->{fraction_installed} } values %$ccdr );
    my @best = grep { $_->{fraction_installed} == $max_fraction_installed } values %$ccdr;

    return \@best;
}


# returns a number from 0 to 1 representing the fraction of the modules
# in a particular release match the coresponding modules in %$installed_mod_info
sub dist_fraction_installed {
    my ($author, $release, $installed_mod_info) = @_;

    my $tag = "$author/$release";
    my $mods_in_rel = get_module_versions_in_release($author, $release);
    my $mods_in_rel_count = keys %$mods_in_rel;
    my $mods_inst_count = sum( map {
        my $mi = $installed_mod_info->{ $_->{name} };
        # XXX we stash the version_obj into the mods_in_rel hash
        # (though with little/no caching effect with current setup)
        $_->{version_obj} ||= eval { version->parse($_->{version}) };
        my $hit = ($mi && $mi->{version_obj} == $_->{version_obj}) ? 1 : 0;
        # demote to a low-scoring partial match if the file size differs
        # XXX this isn't good as the effect varies with the number of modules
        $hit = 0.1 if $mi && $mi->{size} != $_->{size};
        warn sprintf "%s %s %s %s: %s\n", $tag, $_->{name}, $_->{version_obj}, $_->{size},
                ($hit == 1) ? "matches"
                    : ($mi) ? "differs ($mi->{version_obj}, $mi->{size})"
                    : "not installed",
            if $opt_debug;
        $hit;
    } values %$mods_in_rel) || 0;

    my $fraction_installed = ($mods_in_rel_count) ? $mods_inst_count/$mods_in_rel_count : 0;
    warn "$author/$release:\tfraction_installed $fraction_installed ($mods_inst_count/$mods_in_rel_count)\n"
        if $opt_verbose or !$mods_in_rel_count;

    return $fraction_installed;
}


sub get_candidate_cpan_dist_releases {
    my ($module, $version, $file_size) = @_;

    $version = 0 if not defined $version; # XXX

    # timbunce: So, the current situation is that: version_numified is a float
    # holding version->parse($raw_version)->numify, and version is a string
    # also holding version->parse($raw_version)->numify at the moment, and
    # that'll change to ->stringify at some point. Is that right now? 
    # mo: yes, I already patched the indexer, so new releases are already
    # indexed ok, but for older ones I need to reindex cpan
    my $v = (ref $version && $version->isa('version')) ? $version : version->parse($version);
    my %v = map { $_ => 1 } "$version", $v->stringify, $v->numify;
    my @version_qual;
    push @version_qual, { term => { "file.module.version" => $_ } }
        for keys %v;
    push @version_qual, { term => { "file.module.version_numified" => $_ }}
        for grep { looks_like_number($_) } keys %v;

    my @and_quals = (
        {"term" => {"file.module.name" => $module }},
        (@version_qual > 1 ? { "or" => \@version_qual } : $version_qual[0]),
    );
    push @and_quals, {"term" => {"file.stat.size" => $file_size }}
        if $file_size;

    # XXX doesn't cope with odd cases like 
    # http://explorer.metacpan.org/?url=/module/MLEHMANN/common-sense-3.4/sense.pm.PL
    $metacpan_calls++;
    my $results = $metacpan_api->post("file", {
        "size" => $metacpan_size,
        "query" =>  { "filtered" => {
            "filter" => {"and" => \@and_quals },
            "query" => {"match_all" => {}},
        }},
        "fields" => [qw(release _parent author version version_numified file.module.version file.module.version_numified date stat.mtime distribution)]
    });

    my $hits = $results->{hits}{hits};
    die "get_candidate_cpan_dist_releases($module, $version, $file_size): too many results (>$metacpan_size)"
        if @$hits >= $metacpan_size;
    warn "get_candidate_cpan_dist_releases($module, $version, $file_size): ".Dumper($results)
        if grep { not $_->{fields}{release} } @$hits; # XXX temp, seen once but not since

    # filter out perl-like releases
    @$hits = grep {
        $_->{fields}{release} !~ /^(perl|ponie|parrot|kurila|SiePerl-5.6.1-)/;
    } @$hits;

    for my $hit (@$hits) {
        $hit->{release_id} = delete $hit->{_parent};
        # add version_obj for convenience (will fail and be undef for releases like "0.08124-TRIAL")
        $hit->{fields}{version_obj} = eval { version->parse($hit->{fields}{version}) };
    }

    # we'll return { "Dist-Name-Version" => { details }, ... }
    my %dists = map { $_->{fields}{release} => $_->{fields} } @$hits;
    warn "get_candidate_cpan_dist_releases($module, $version, $file_size): @{[ sort keys %dists ]}\n"
        if $opt_verbose;

    return \%dists;
}

sub get_candidate_cpan_dist_releases_fallback {
    my ($module, $version) = @_;

    # fallback to look for distro of the same name as the module
    # for odd cases like
    # http://explorer.metacpan.org/?url=/module/MLEHMANN/common-sense-3.4/sense.pm.PL
    (my $distname = $module) =~ s/::/-/g;

    # timbunce: So, the current situation is that: version_numified is a float
    # holding version->parse($raw_version)->numify, and version is a string
    # also holding version->parse($raw_version)->numify at the moment, and
    # that'll change to ->stringify at some point. Is that right now? 
    # mo: yes, I already patched the indexer, so new releases are already
    # indexed ok, but for older ones I need to reindex cpan
    my $v = (ref $version && $version->isa('version')) ? $version : version->parse($version);
    my %v = map { $_ => 1 } "$version", $v->stringify, $v->numify;
    my @version_qual;
    push @version_qual, { term => { "version" => $_ } }
        for keys %v;
    push @version_qual, { term => { "version_numified" => $_ }}
        for grep { looks_like_number($_) } keys %v;

    my @and_quals = (
        {"term" => {"distribution" => $distname }},
        (@version_qual > 1 ? { "or" => \@version_qual } : $version_qual[0]),
    );

    # XXX doesn't cope with odd cases like 
    $metacpan_calls++;
    my $results = $metacpan_api->post("file", {
        "size" => $metacpan_size,
        "query" =>  { "filtered" => {
            "filter" => {"and" => \@and_quals },
            "query" => {"match_all" => {}},
        }},
        "fields" => [qw(release _parent author version version_numified file.module.version file.module.version_numified date stat.mtime distribution)]
    });

    my $hits = $results->{hits}{hits};
    die "get_candidate_cpan_dist_releases_fallback($module, $version): too many results (>$metacpan_size)"
        if @$hits >= $metacpan_size;
    warn "get_candidate_cpan_dist_releases_fallback($module, $version): ".Dumper($results)
        if grep { not $_->{fields}{release} } @$hits; # XXX temp, seen once but not since

    # filter out perl-like releases
    @$hits = grep {
        $_->{fields}{release} !~ /^(perl|ponie|parrot|kurila|SiePerl-5.6.1-)/;
    } @$hits;

    for my $hit (@$hits) {
        $hit->{release_id} = delete $hit->{_parent};
        # add version_obj for convenience (will fail and be undef for releases like "0.08124-TRIAL")
        $hit->{fields}{version_obj} = eval { version->parse($hit->{fields}{version}) };
    }

    # we'll return { "Dist-Name-Version" => { details }, ... }
    my %dists = map { $_->{fields}{release} => $_->{fields} } @$hits;
    warn "get_candidate_cpan_dist_releases_fallback($module, $version): @{[ sort keys %dists ]}\n"
        if $opt_verbose;

    return \%dists;
}


# this can be called for all sorts of releases that are only vague possibilities
# and aren't actually installed, so generally it's quiet
sub get_module_versions_in_release {
    my ($author, $release) = @_;

    $metacpan_calls++;
    my $results = eval { $metacpan_api->post("file", {
        "size" => $metacpan_size,
        "query" =>  { "filtered" => {
            "filter" => {"and" => [
                {"term" => {"release" => $release }},
                {"term" => {"author" => $author }},
                {"term" => {"mime" => "text/x-script.perl-module"}},
            ]},
            "query" => {"match_all" => {}},
        }},
        "fields" => ["path","name","_source.module", "_source.stat.size"],
    }) };
    if (not $results) {
        warn "Failed get_module_versions_in_release for $author/$release: $@";
        return {};
    }
    my $hits = $results->{hits}{hits};
    die "get_module_versions_in_release($author, $release): too many results"
        if @$hits >= $metacpan_size;

    my %modules_in_release;
    for my $hit (@$hits) {
        my $path = $hit->{fields}{path};

        # XXX try to ignore files that won't get installed
        # XXX should use META noindex!
        if ($path =~ m!^(?:t|xt|tests?|inc|samples?|ex|examples?|bak)\b!) {
            warn "$author/$release: ignored non-installed module $path\n"
                if $opt_debug;
            next;
        }

        my $size = $hit->{fields}{"_source.stat.size"};
        # files can contain more than one package ('module')
        my $rel_mods = $hit->{fields}{"_source.module"} || [];
        for my $mod (@$rel_mods) { # actually packages in the file

            # Some files may contain multiple packages. We want to ignore
            # all except the one that matches the name of the file.
            # We use a fairly loose (but still very effective) test because we
            # can't rely on $path including the full package name.
            (my $filebasename = $hit->{fields}{name}) =~ s/\.pm$//;
            if ($mod->{name} !~ m/\b$filebasename$/) {
                warn "$author/$release: ignored $mod->{name} in $path\n"
                    if $opt_debug;
                next;
            }

            # warn if package previously seen in this release
            # with a different version or file size
            if (my $prev = $modules_in_release{$mod->{name}}) {
                my $version_obj = eval { version->parse($mod->{version}) };
                die "$author/$release: $mod $mod->{version}: $@" if $@;

                if ($opt_verbose) {
                    # XXX could add a show-only-once cache here
                    my $msg = "$mod->{name} $mod->{version} ($size) seen in $path after $prev->{path} $prev->{version} ($prev->{size})";
                    warn "$release: $msg\n"
                        if ($version_obj != version->parse($prev->{version}) or $size != $prev->{size});
                }
            }

            # keep result small as Storable thawing this is major runtime cost
            # (specifically we avoid storing a version_obj here)
            $modules_in_release{$mod->{name}} = {
                name => $mod->{name},
                path => $path,
                version => $mod->{version},
                size => $size,
            };
        }
    }

    warn "\n$author/$release contains: @{[ map { qq($_->{name} $_->{version}) } values %modules_in_release ]}\n"
        if $opt_debug;

    return \%modules_in_release;
}


sub get_file_mtime {
    my ($file) = @_;
    # try to find the time the file was 'installed'
    # by looking for the commit date in svn or git
    # else fallback to the file modification time
    return (stat($file))[9];
}


sub find_installed_modules {
    my (@dirs) = @_;

    ### File::Find uses follow_skip => 1 by default, which doesn't die
    ### on duplicates, unless they are directories or symlinks.
    ### Ticket #29796 shows this code dying on Alien::WxWidgets,
    ### which uses symlinks.
    ### File::Find doc says to use follow_skip => 2 to ignore duplicates
    ### so this will stop it from dying.
    my %find_args = ( follow_skip => 2 );

    ### File::Find uses lstat, which quietly becomes stat on win32
    ### it then uses -l _ which is not allowed by the statbuffer because
    ### you did a stat, not an lstat (duh!). so don't tell win32 to
    ### follow symlinks, as that will break badly
    # XXX disabled because we want the postprocess hook to work
    #$find_args{'follow_fast'} = 1 unless ON_WIN32;

    ### never use the @INC hooks to find installed versions of
    ### modules -- they're just there in case they're not on the
    ### perl install, but the user shouldn't trust them for *other*
    ### modules!
    ### XXX CPANPLUS::inc is now obsolete, remove the calls
    #local @INC = CPANPLUS::inc->original_inc;

    # sort @dirs to put longest first to make it easy to handle
    # elements that are within other elements (e.g., an archdir)
    my @dirs_ordered = sort { length $b <=> length $a } @dirs;

    my %seen_mod;
    my %dir_done;
    my %meta; # return metadata about the search
    for my $dir (@dirs_ordered) {
        next if $dir eq '.';

        ### not a directory after all
        ### may be coderef or some such
        next unless -d $dir;

        ### make sure to clean up the directories just in case,
        ### as we're making assumptions about the length
        ### This solves rt.cpan issue #19738

        ### John M. notes: On VMS cannonpath can not currently handle
        ### the $dir values that are in UNIX format.
        $dir = File::Spec->canonpath($dir) unless ON_VMS;

        ### have to use F::S::Unix on VMS, or things will break
        my $file_spec = ON_VMS ? 'File::Spec::Unix' : 'File::Spec';

        ### XXX in some cases File::Find can actually die!
        ### so be safe and wrap it in an eval.
        eval {
            File::Find::find(
                {   %find_args,
                    postprocess => sub {
                        $dir_done{$File::Find::dir}++;
                    },
                    wanted => sub {

                        unless (/\.pm$/i) {
                            # skip all dot-dirs (eg .git .svn)
                            $File::Find::prune = 1
                                if -d $File::Find::name and /^\.\w/;
                            # don't reenter a dir we've already done
                            $File::Find::prune = 1
                                if $dir_done{$File::Find::name};
                            # remember perllocal.pod if we see it
                            push @{$meta{perllocalpod}}, $File::Find::name
                                if $_ eq 'perllocal.pod';
                            return;
                        }
                        my $mod = $File::Find::name;

                        ### make sure it's in Unix format, as it
                        ### may be in VMS format on VMS;
                        $mod = VMS::Filespec::unixify($mod) if ON_VMS;

                        $mod = substr( $mod, length($dir) + 1, -3 );
                        $mod = join '::', $file_spec->splitdir($mod);

                        return if $seen_mod{$mod};
                        $seen_mod{$mod} = $File::Find::name;

                        ### ignore files that don't contain a matching package declaration
                        ### warn about those that do contain some kind of package declaration
                        #my $content = read_file($File::Find::name);
                        #unless ( $content =~ m/^ \s* package \s+ (\#.*\n\s*)? $mod \b/xm ) {
                        #warn "No 'package $mod' seen in $File::Find::name\n"
                        #if $opt_verbose && $content =~ /\b package \b/x;
                        #return;
                        #}

                    },
                },
                $dir
            );
            1;
        }
            or die "File::Find died: $@";

    }

    return (\%seen_mod, \%meta);
}


sub perllocal_distro_mod_version {
    my ($distname, $perllocalpod) = @_;

    ( my $dist_mod_name = $distname ) =~ s/-/::/g;
    my $key_mod_name = $distro_key_mod_names{$distname} || $dist_mod_name;

    our $perllocal_distro_mod_version;
    if (not $perllocal_distro_mod_version) { # initial setup
        warn "Only first perllocal.pod file will be processed: @$perllocalpod\n"
            if @$perllocalpod > 1;

        $perllocal_distro_mod_version = {};
        # extract data from perllocal.pod
        if (my $plp = shift @$perllocalpod) {
            # The VERSION isn't always the same as that in the distro file
            if (eval { require ExtUtils::Perllocal::Parser }) {
                my $p = ExtUtils::Perllocal::Parser->new;
                $perllocal_distro_mod_version = { map {
                    $_->name => $_->{data}{VERSION}
                } $p->parse_from_file($plp) };
                warn "Details of ".keys(%$perllocal_distro_mod_version)." distributions found in $plp\n";
            }
            else {
                warn "Wanted to use perllocal.pod but can't because ExtUtils::Perllocal::Parser isn't available\n";
            }
        }
        else {
            warn "No perllocal.pod found to aid disambiguation\n";
        }
    }

    return $perllocal_distro_mod_version->{$key_mod_name};
}


sub module_progress_indicator {
    my ($module) = @_;
    my $crnt = (split /::/, $module)[0];
    our $last ||= '';
    if ($last ne $crnt) {
        warn "\t$crnt...\n";
        $last = $crnt;
    }
}


# copied from CPAN::Mini::Inject and hacked

sub _readpkgs {
    my ($cpandir) = @_;

    my $packages_file = $cpandir.'/modules/02packages.details.txt.gz';
    return [] if not -f $packages_file;

    my $gzread = gzopen($packages_file, 'rb')
        or croak "Cannot open $packages_file: $gzerrno\n";

    my $inheader = 1;
    my @packages;
    my $package;

    while ( $gzread->gzreadline( $package ) ) {
        if ( $inheader ) {
            $inheader = 0 unless $package =~ /\S/;
            next;
        }
        chomp $package;
        push @packages, $package;
    }

    $gzread->gzclose;

    return \@packages;
}

sub _writepkgs {
    my ($cpandir, $pkgs) = @_;

    my $packages_file = $cpandir.'/modules/02packages.details.txt.gz';
    my $gzwrite = gzopen($packages_file, 'wb')
        or croak "Cannot open $packages_file for writing: $gzerrno";
    
    $gzwrite->gzwrite( "File:         02packages.details.txt\n" );
    $gzwrite->gzwrite(
        "URL:          http://www.perl.com/CPAN/modules/02packages.details.txt\n"
    );
    $gzwrite->gzwrite(
        'Description:  Package names found in directory $CPAN/authors/id/'
        . "\n" );
    $gzwrite->gzwrite( "Columns:      package name, version, path\n" );
    $gzwrite->gzwrite(
        "Intended-For: Automated fetch routines, namespace documentation.\n"
    );
    $gzwrite->gzwrite( "Written-By:   $0 0.001\n" ); # XXX TODO
    $gzwrite->gzwrite( "Line-Count:   " . scalar( @$pkgs ) . "\n" );
    # Last-Updated: Sat, 19 Mar 2005 19:49:10 GMT
    my @date = split( /\s+/, scalar( gmtime ) );
    $gzwrite->gzwrite( "Last-Updated: $date[0], $date[2] $date[1] $date[4] $date[3] GMT\n\n" );
    
    $gzwrite->gzwrite( "$_\n" ) for ( @$pkgs );
    
    $gzwrite->gzclose;
}

sub _fmtmodule {
    my ( $module, $file, $version ) = @_;
    $version = "undef" if not defined $version;
    my $fw = 38 - length $version;
    $fw = length $module if $fw < length $module;
    return sprintf "%-${fw}s %s  %s", $module, $version, $file;
}

sub first_word {
    my $string = shift;
    return ($string =~ m/^(\w+)/) ? $1 : $string;
}

sub distname_info_from_url {
    my ($url) = @_;
    $url =~ s{.* \b authors/id/ }{}x
        or warn "No authors/ in '$url'\n";
    my $di = CPAN::DistnameInfo->new($url);
    return $di;
}
