% Francois FAGES (fages@dmi.ens.fr)
% May 96

% File to load under Sicstus Prolog version 3 or 2
% in order to install the system.

:-use_module(library(lists)).

:- op(700,xfx,[ .>= , .<= , .= , .> , .< , .=\= ]).

:- version('
Prototype Implementation of CLP(FD) on Top of Sicstus Prolog. 
Version 2, May 1996.
').

% For Sicstus version 2 only
:- compile(sicstusV2).

:- compile(clpFD).

% Execute at top-level
% save_program('../clpFD').
