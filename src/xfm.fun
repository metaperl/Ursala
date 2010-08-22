
#import std
#import nat
#import lag
#import sol
#import apt

#comment -[
This module contains useful routines for parse tree transformation and
evaluation.

Copyright (C) 2007-2010 Dennis Furey]-

profile = +^(-=/'trace'?\~&l! ! guard^|/~& ^C\~&+ !,-=/'profile'?\~&! ! ^\~&r std-profile) __switches

#library+
#optimize+

unseparate = 

^V/~&d ~&v; *= ~&i&& ~lexeme=='(separation)'?d\~&iNC (~lexeme=='(separation)'?d/~&v ~&iNC)^H\~& ~&d.preprocessor|| ~&!

disallow_duplicates =

profile\'duplicate disallowance' ||~& -+
   ~&i&& ~&L; % :/'duplicate declarations: '+ ~&hrPSx+ nleq-<&l*+ |=&r+ num+ ~&x+ * '   '--+ ~&L+ <.
      ~filename&& --':'+ ~filename,
      ~filename~='command-line'&& ~location; ~&ilrBB&& --+ ~~ --':'+ ~&h+ %nP,
      ^T(&&' '! ~location!| ~filename,~lexeme; ~&x+ ~&x; takewhile ~=`-)>,
   ~lexeme.&ihB~=`#*~; ~&tF+ |= ==+ ~~ ~lexeme,
   ~&v; *= ~&a^& ^T/-&~&ad.lexeme=='=',~&av,~&avh,~&avhdNC&- &&~&favPML ~&ad.lexeme~<{'#hide','#hide+'}+-

visible_symbols = # returns a module of lists of declarations visible looking down from the top level of the given tree

profile\'visibility analysis' _token%TLmMk+ ~&i&& -+
   *~ ~&m; any ~&vZ&& ~&d.semantics,
   |=&rvhd.lexeme; * ^A(~&hvhd.lexeme,~&vth2S)+ _token%TtLLwXLMk; ~&lrPS+ ~&iiDrlXS; *~ not ~| ~&rlXl; ~=&& [=,
   _token%TtLLwXLMk+ ~&lxPrXS+ ~&v; ~&DNlhPCltPCrXK9/<<>>; *= ~&ar^& ~lexeme=='='?ard/~&aNC ~lexeme=='#hide'?ard(
      ~&faNlCrvPXPJ; -|
         ~&aar^& ~lexeme=='#export'?aarhd(
            _token%TLtLLwXJJMk; ~&afalrhv2DNlhPCltPCrXK9PPML2fafarhvNS3lhPTltPCrtPXPJPRT,
            -&~lexeme.&h==`#,~lexeme~='#hide'&-?aarhd/~&fafalrhvPtTPXPJPR ~&fafaNlhPCltPCrtPXPJPR),
         ~&aar^& ~lexeme=='#export'?aarhd/<>! -&~lexeme.&h==`#,~lexeme~='#hide'&-?aarhd(
            ~&fafalrhvPtTPXPJPR,
            ~&aartZ?/~&afalrhPXPR ~&fafalrtPXPJPR)|-,
      ~&falrvPDPML)+-

before = # computes textual precedence for a pair of parse trees

~&bd; -?
   :0! not nleq+ ~&b.filenumber,
   :&! ~=+ ~&b.filenumber,
   :0! not nleq+ ~&b.location.&l,
   :&! ~=+ ~&b.location.&l,
   nleq+ ~&b.location.&r?-

substitute = # substitutes values for identifiers consistently with the rules of scope

profile\'substitution' -+
   ~&ar^& -&~&d.lexeme=='-',~&v&-?ar/~&ard2falrvh2XPRarvt3CV -&~&vZ,~&d.semantics.&Z&-?ar\~&ard2falrvPDPMV -+
      ~&r?\~&l ~&rt?\~&rh ||~&l -&~&,~&vZ,~&d.semantics,~&i&-+ -|~&l&& before$^+ ~&l,~&r&& before$^+ ~&r|-+ *| before+ ~&rlX,
      _token%TfOwXJMk; ~&arlrHX+-,
   _token%TfOwXMk+ ^\~& ~&d.lexeme;+ -:0!+ visible_symbols+-

remove_dead_code = # gets rid of anything not used and not exported

-+
   *^0 ^V/~&d ~&viF; *= ~&d.lexeme=='(separation)'?/~&v ~&iNC,
   ~&r&& ^V/~&rd ~&lrvPD; * ~&ar^& ~lexeme.&ihB==`#?ard(
      ~&ard.lexeme-={'#export','#export+'}?/~&ar ^V/~&ard ^M/~&f ^D\~&arv ~&al; *~ ~&w/`-,
      &&~&ard2falrvPDPMV not -&~&ard.lexeme=='=',~&arv,^w/~&arvhd.lexeme ~&al&-),
   ^\~& ^js(
      ~&a^& ^T\~&favPML -&~&ad.lexeme=='=',~&av,~&avh,~&iNC+ ~&avhd.lexeme&-,
      ~&a^& -&~&ad.lexeme=='=',~&av&-?/~&favt2ML :^/~&ad.lexeme ~&favPML)+-

global_dead_code_removal =

-+
   *^0 ^V/~&d ~&viF; *= ~&d.lexeme=='(separation)'?/~&v ~&iNC,
   ~&r&& ^V/~&rd ~&lrvPD; * ~&ar^& ~lexeme.&ihB==`#?ard(
      ^V/~&ard ^M/~&f ^D\~&arv ~&al; *~ ~&w/`-,
      &&~&ard2falrvPDPMV not -&~&ard.lexeme=='=',~&arv,^w/~&arvhd.lexeme ~&al&-),
   ^\~& ^js(
      ~&a^& ^T\~&favPML -&~&ad.lexeme=='=',~&av,~&avh,~&iNC+ ~&avhd.lexeme&-,
      ~&a^& -&~&ad.lexeme=='=',~&av&-?/~&favt2ML :^/~&ad.lexeme ~&favPML)+-

(# hide_invisible_code suppresses code that can't be removed because output generating directives need it, but shouldn't be
seen outside of its enclosing scope because it's not exported. It's done by modifying the semantics of the output generating
directive to return an empty list of declarations but the same file list as usual. This modification has to be done only once
or else preprocessing won't terminate. It's prevented from being done more than once by modifying the semantics to return an
empty value for a non-empty argument, which normally won't occur during evaluation because the semantics will be applied only
to an empty suffix field. This condition can be tested and the modification is not repeated if it holds. #)

hide_invisible_code =

^V/~&d ~&v; * ~&a^& ~lexeme-={'#export','#export+'}?ad/~&a ?(
   ~&ad.lexeme.&ihB== `#,
   ~&\~&adPfavPMV ^V\~&av ~&ad; semantics:= ~semantics; ~&i&& ~&H\&?\~& ~&Z&&+ ~&NrX++)

resolve = # gets rid of cyclic dependences using the general solution algorithm defined in the sol module

profile\'general solution' (~&r?\~&l ~&rlX; ~&ar^& ~&fallrHXPJ; ~&ard2falrvPDPMV)^/~& -+
   -&~&,general_solution+ %fOsfOXTXmMk+ * ^A/~&n ^\~&mr evaluation+ ~&ml&-; ~&i&& ?^(
      (~&d.lexeme=='=')&&+ ~&v&&+ ~&vt&&+ ~&vttZ&&+ ~&vhd.lexeme;+ \/-=+ ~&nS,
      ~&\~&+ &vth:=+ ~&V\<>++ -+
         //+ token$l[lexeme: '(evaluated)'!,preprocessor: 0!,semantics: !+ !+ ~&r],
         ^/~&vthd+ ~&vhd.lexeme;+ -:+-),
   ^= ~&rnPlw~|^\~& ~&s+ *= ~&mr; *^0 ^T\~&vL ~&drZ&& ~&dlNC,
   (~&rS+ *~ subset+ ~&rmrdlPvLPCo3NlCX)+ _token%TsoXTXswXsLwXLMk^D/~&nS *~ ~&ml; *^0 ~&d.semantics&& ~&vig,
   _token%TsoXTXmMk+ ~&mlPg?/~& ~&mlZPFhn; % -+
      ~&iNC+ --': circular definition; try #fix',
      substring/'command-line'?/'command-line'! (~&~<'()')*~+ * ',-'?</`:! ~&+-,
   _token%TsoXTXmMk+ ^= ~&rnPlw~|^\~& %sSMk+ ~&s+ *= ~&mr; *^0 ^T\~&vL ~&drZ&& ~&dlNC,
   _token%TsoXTXmMk+ ~&/0; ~&ar^& -&~&ard.lexeme=='#fix',~&arv&-?/~&farvhtD3ML ?(
      -&~&ard.lexeme=='=',~&arv,~&arvt,~&arvttZ,not ~&arvthd.lexeme-={'(evaluated)','(imported)'}&-,
      ~&\~&falrvPDPML ^ANC/~&arvhd.lexeme ^/~&al -+
         *^0 ^V\~&v ~&d; ~semantics?\~&iNX+~lexeme ^NlrHX\~lag-suffix guard^/~semantics //:+ ~/filename location,
         ~&arvth+-)+-
