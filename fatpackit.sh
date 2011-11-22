#!/bin/sh

fatpack trace $1
fatpack packlists-for `sort fatpacker.trace` > fatpacker.packlists
fatpack tree `sort fatpacker.packlists` # sort to put Moose before Moose::
(fatpack file; cat $1 )
rm fatpacker.trace fatpacker.packlists
