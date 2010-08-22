
#import std
#import nat
#import ext
#import pag
#import lag
#import ogl
#import ops
#import eto
#import dir
#import pru
#import for

#comment -[
This module defines the data structure specifying the run-time mutable
parts of the compiler and some of its default field values.

Copyright (C) 2007-2010 Dennis Furey]-

#export+
#library+
#optimize+

------------------------------------------------------ data structures ------------------------------------------------------

formulation ::   # specifies a compiler possibly customized with command line options

command_name  %s                    # the command whereby the compiler is invoked
source_filter %fOZ                  # a function taking a list of input files to a list of input files
token_filter  %fOZ                  # a function taking a list of lists of tokens to a list of lists of tokens
preformer     %fOZ                  # a function taking a list of unprocessed parse trees to a list of parse trees
postformer    %fOZ                  # a function taking a processed parse tree to a parse tree suitable for evaluation
target_filter %fOZ                  # a function taking a list of output files to a list of output files
import_filter %fOZ                  # see below
precedence    pag-_ruleset%fOWWU    # a quadruple of pairs of lists of strings (not functions as defined in pag.fun)
operators     _operator%L
directives    _directive%L
formulators   _formulator%L
help_topics   %fOm

--------------------------------------------- miscellaneous default formulation fields ---------------------------------------

default_postformer = # allows identifiers to be qualified by their module names at compile time

~&i&& -+
   ?(
      ~&a^& ~&ad.lexeme~='#import'&& ^T\~&favPML ~&ad.semantics.&Z&& ~&iNC+ ~&ad.lexeme,
      ~&/~& *^0 ||~& -&~&d.lexeme=='#import',~&v,~&vt,~&vttZ,~&vth&-),
   ~&a^& ~lexeme=='#hide'?ad\~&adPfavPMV ^V/~&ad ~&favPD; * ~&aa^& ?(
      ~&aad.lexeme-= `#-* :/'hide' ~&nS ~&m.compilation*~ default_directives,
      ~&/~&afaR -&~&aad.lexeme=='#import',~&aav,~&aavh,~&aavhd.semantics.&Z&-?(
         ^V/~&aad :^\~&fafavt2DPM ~&aavh; &d.semantics:= 0!!!,
         ~&aad2fafavPDPMV)),
   ~&ar^& ||~&ard2falrvPDPMV -&
      -&~&ard.lexeme=='-',~&arv,~&arvt,~&arvttZ,~&arvhd.semantics.&Z,~&arvthd.semantics&-,
      ~&ihrPB+ ~&lrlPE~|+ ~/&arvhthPXd.lexeme &al&-,
   _token%TdsWwXLwXMk+ ^\~& ~&llPF+ ~&v; *= ~&a^& ~lexeme=='#hide'?ad(
      ~&favPJ; ~&aa^& ^T\~&fafatPJPR ~&aahd.lexeme=='#export'?/~&afahv2ML &&~&fafahv2JPR ~&aahd.lexeme~='#hide',
      ~&a; ~&a^& ||~&favPML -&
         -&~&ad.lexeme=='=',~&av,~&avt,~&avttZ,~&avthd.lexeme-={'(evaluated)','(imported)'}&-,
         ^iNC\~&avth ^\~&avhd.lexeme ~&l+ ~=`.-~+ ~&avhd.filename&-)+-

(# The import filter saves a significant amount of time by causing #import directives to refrain from importing unused
symbols, based on the assumption that all identifiers used in the source files can be found before preprocessing starts.
Although the import filter in a formulation record can be changed to something other than the default value, there's no
command line option to change it because it would never be necessary unless some new compiler directives were introduced that
invalidated this assumption, e.g., by building additional parse trees during preprocessing that contain identifiers needing to
be imported. Changing the import filter to the identity function will disable import filtering. #)

default_import_filter =

-+
   ~&ar^& ~&ard.lexeme-={'#hide+','#hide-','(separation)'}?/~&ard2falrvPDPMV ?(
      ~&ar; -&
         -&~&d.lexeme=='#import',~&v,~&vhZ,~&vt,~&vttZ&-,
         ~&vth; -&~&,~&d.lexeme=='#import-',~&v,~&vt,~&vttZ,~&vthZ&-,
         ~&vthvh; -&~&,~&d.lexeme=='(separation)',~&v,~&vh&-&-,
      ~&\~&ar ~&ar+ &arvthvhvh:= ~&alrvthvhvh7X; ^V\~&rNC ~&rd+ &rd.(lexeme,preprocessor,semantics):= -+
         ~&/'(import filter)'+ ~&NiX+ !,
         ~&l; "s". ~&D/"s"; *= -+
            gint -!~&lZ,~&lnZ,~&llPrE!-,
            ^\~&l ~&r; -&not %soXLI,extractable&-?\~& extract+-+-),
   ^\~& ^T(~&,~&tS+ *~ -&~&h==`_,~&t,~&th~=`_&-)+ ~&s+ *^0 ^T\~&vL ~&d.semantics.&Z&& ~&iNC+ ~&d.lexeme+-

------------------------------------------------ the default compiler specification -----------------------------------------

#optimize-

default_formulation = # takes a set of default formulators to the default compiler specification

"f". formulation[
   command_name: 'fun',
   source_filter: ~&,
   token_filter: ~&,
   preformer: ~&,
   postformer: default_postformer,
   target_filter: ~&,
   import_filter: default_import_filter,
   precedence: default_rules,
   operators: extra_tabular default_operators,
   directives: ~&mS default_directives,
   formulators: ~&mS "f"]
