
#import std
#import nat
#import pag
#import lag
#import ogl
#import ops
#import eto

#comment -[
This module defines the operator precedence rules of the language, and
also contains a pretty printer used by the --parse command line option
based on those rules.

Copyright (C) 2007-2010 Dennis Furey]-

#library+

default_hierarchies = # operator precedence relations on representatives of each operator equivalence class

ruleset[
   inin: ~&T\<('+','/')> ~&j(
      closure ~&ytp sep`  '= ? / -< + :- == != ^ := $ ! -- ~ : . -',
      <('-<','^'),('$','^'),(':-','^')>),
   prein: ~&j\<('+','=='),('-<','^'),('$','^'),(':-','^')> closure ~&ytp sep`  '= ? / -< + :- == != ^ := $ ! -- ~ : . -',
   inpost: ~&j(
      closure ~&ytp sep`  '= ? -< + / $ :- == != ^ := ! -- ~ : . -',
      ~&T(
         <('-<','+'),('-<','$'),('-<','^'),('$','^'),(':-','^'),('==','!=')>,
         <('+','=='),('/','=='),('==',':'),('/',':'),('+',':')>)),
   prepost: ~&j(
      closure ~&ytp sep`  '= ? / + -< :- == != ^ := $ ! -- ~ : . -',
      <('==','!='),('-<','$'),('-<','^'),('$','^'),('!=','$'),(':-','$'),(':-','^'),('~',':'),('==',':')>)]

operator_classes = # takes a set of operators to the equivalance classes of their mnemonics implied by the peer relation

~mnemonic**+ (==+ ~/&l.mnemonic &r.peer)|=*=+ *~ ~meanings; ~aggregate.&Z&& -!~ogl-prefix,~ogl-postfix,~ogl-infix!-

rule_base = cross*=^DlrHS\~&r ~~+ -:+ ~&iiDrlXS*=+ operator_classes+ ~&l  # infers all relations from representatives

pretty = # takes a list of operators to a function taking an unprocessed parse tree to a list of strings

"o". ||<'(nothing to print)'>! (~&d.lexeme-={',',']--['}?\~& ^V/~&d ~&v; *= ~&d.lexeme-={',',']--['}?/~&v ~&iNC)*^0; ~&a^& -?
   :(mat0+~&favPM) ~&ad.lexeme== '(separation)',
   -&~&ad.lexeme=='-{',~&avZ&-: %xP+ evaluation+ ~&a,
   :(^T(^lrhPTrtPC\~&favthvhvh7R --' '+ ~&ad.lexeme,~&NiC+ ~&favthdvhvth4vtPCV4R)) -&
      -&~&ad.lexeme; ~&h==`#&& not ~&z-='+-',~&av,~&avhZ,~&avt,~&avttZ&-,
      ~&avth; -&~&,~&v,~&vt,~&vthZ,~&vttZ,~&vh; -&~&,~&d.lexeme=='(separation)',~&v,~&vh,~&vt,~&vth,~&vttZ&-&-&-,
   (~&ad.lexeme.&h==`#): ~&avihZB?/(:^/~&ad.lexeme ~&favt2ML; (~&h&& ~&hh==`#)?/~& ~&NiC) ?(
      -&~&av,~&avh,~&avt,~&avthZ,~&avttZ&-,
      ((~&lz&& ~&lzh==`#)?/~&T ~&lNrCT)^/~&favh2R ~&iNC+ ~&ad.lexeme,
      ^D(~&ad.lexeme,~&favPM); :-0 ~&L+ <.~&lr,~&NllPNNCCC,~&rr>),
   ~&avZ: ~&iNC+ -+
      (~&l; \/-= ~ogl-mnemonic* ~meanings.aggregate.&Z*~ "o")?\~&T :/`(+ (`.?=ihB\~& :/` )+ --')'+ --,
      ^/~&ad.lexeme ~&nSL+ ~&ad.lag-suffix+-,
   (~&ad.lexeme-= :/']-]-' ~ogl-match* ~meanings.aggregate*~ "o"): -+
      ~&r?\~&lNC ^T/~&ryL ^lrNCT/~&rzy ~&rzz2lT,
      ^/~&ad.lexeme ~&favPMiF+-,
   (~&ad.lexeme-= <']--[',','>): ^(~&ad.lexeme,~&favPM); (~&r; -&all ~&tZ,leql\iota40+ ~&LL&-)?(
      ~&iNC+ ~&ar^& ^T/~&arhh ^rlrTB/~&al ~&falrtPXPR,
      -*; ^T\~&zr ~&y; *= ^T/~&ry ~&iNC+ ~&rzPlT),
   -&~&ad.lexeme-= ~ogl-mnemonic* ~loose*~ "o",~&av&-: ^(~&ad.lexeme,~&favPM); -?
      ~&/(~&r; -&all ~&tZ,(leql\iota40)+ ~&LL&-) ^TNC/~&rhL :/` + ^T/~&l :/` + ~&rtLL,
      ~&/~&rhtZ :^\~&NrtL2C ^T/~&rhL2 :/` + ~&l,
      ~&rhPlrtL2CT?-,
   (~&ad.lexeme-= :/'-[-[' ~ogl-mnemonic* ~meanings.aggregate*~ "o"): -+
      ~&r?\~&lNC -!any~&t+ ~&r,~&rt&& (leql/iota40)+ ~&rLL!-?(
         :^/~&l ~&r; *= * '   '--,
         ^T\~&rtL ~&lrhh2Trht2C),
      ^\~&favPMiF ^T/~&ad.lexeme ~&nSL+ ~&ad.lag-suffix+-,
   ~&r+ -+
      :-0 ~&llPbrPX; ^/~&l ~&rl?(
         ~&rr?\^lrNCT(~&rly,^T\~&l ~&rlz) -+
            -!~&l,~&rrhh==`(,~&rrh; (any [=+ ~&rlX)+ \/~&D :/'-[-[' ~ogl-mnemonic* ops-aggregation!-?(
               ^T/~&rly :^\~&rrt ^T/~&rlz ^T/~&l ~&rrh,
               ^T/~&rly ^lrNCT(~&y, --')'+ ~&z)+ :^\~&rrt ^T/~&rlz ^T/~&l :/`(+ (`.?=ihB\~& :/` )+ ~&rrh),
            {0,' '}?<l\~& ^/~&l ^\~&rr ~&rl; ~&iNC+ *= ->~&t ~&ihB&& ~&h==`  +-,
         ~&rr?(:^\~&rrt ^T/~&l ~&rrh,~&iNC+ :/`(+ (`.?=ihB\~& :/` )+ --')'+ ~&l)),
      (~&ad.lexeme; -=/`(&& ~='(tight application)')?/(' '-*+ ~&favPM) ^D(
         ^T(~&ad.lexeme; -=/`(?\~& &&' '! ~='(tight application)',~&nSL+ ~&ad.lag-suffix),
         ~&favPD; ~&JS; * ~&a&& ?(
            ~&avZ!| ~&ad.lexeme-= :/'-[-[' ~ogl-mnemonic* ~meanings.aggregate*~ "o",
            ~&/~&R ~&R; :^(:/`(+ (`.?=ihB\~& :/` )+ ~&h,~&t)+ ^lrNCT/~&y --')'+ ~&z))+-?-

rules = # takes a set of operators and a hierarchy ruleset

ruleset$[
   inin: ^c/(rule_base+ ~/&l &r.inin) cross+ ~&iiX+ ~ogl-mnemonic*+ ~meanings.infix*~+ ~&l,
   prein: ^c/(rule_base+ ~/&l &r.prein) ~ogl-mnemonic~~*+ cross^(~meanings.prefix*~,~meanings.infix*~)+ ~&l,
   inpost: ^c/(rule_base+ ~/&l &r.inpost) ~ogl-mnemonic~~*+ cross^(~meanings.infix*~,~meanings.postfix*~)+ ~&l,
   prepost: ^c/(rule_base+ ~/&l &r.prepost) ~ogl-mnemonic~~*+ cross^(~meanings.prefix*~,~meanings.postfix*~)+ ~&l]

default_rules = rules\default_hierarchies extra_tabular default_operators
