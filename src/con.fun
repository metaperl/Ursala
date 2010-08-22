
#import std
#import nat
#import ext
#import opt
#import lag
#import ogl
#import ops
#import apt
#import eto
#import xfm
#import dir
#import fen
#import pru
#import for
#import mul
#import def

#comment -[
This module contains the functions that interpret the compiler
specification data structures defined in the for and mul modules.

Copyright (C) 2007-2010 Dennis Furey]-

profile = +^(-=/'trace'?\~&l! ! guard^|/~& ^C\~&+ !,-=/'profile'?\~&! ! ^\~&r std-profile) __switches

#library+
#optimize+

(# The customized function takes a default formulation and a command line record to a customized formulation and a list of
input files. It starts with the default formulation and uses its formulators field to identify command line options in the
given command line, and applies the formula of each recognized option sequentially to the formulation, skipping the ones it
doesn't recognize, and repeating until a fixed point is reached. If some unidentified command line options remain, they are
reported as an error. In order to identify an option, it searches for the keyword in the list of formulator mnemonics and
checks the filial field in each, so as to use a file in the next position as the file parameter to the option instead of an
input file if there is one and the filial field is true. The files that aren't used as formulator file parameters are returned
as input files along with the customized formulation as the result of this function. If custom operators are defined but the
precedence rules aren't changed, the function attempts to make allowances by redefining the precedence according to the system
of default hierarchies in pru.fun, so that a peer field in a user defined operator will suffice to determine its precedence.
Similarly, if the default help topics are updated but the help formulator is not, it will be adjusted automatically, so
that the user need only update the help topics table. #)

customized =

profile\'command parsing' -+
   ^/~&l ~&r; * ~&l|| ~&r; % ~&iNC+ ' unrecognized option: '--+ ~keyword,
   (_formulation,(_file%oUZ,std-_option%gUZ)%XL)%XMk; ~&liX; ^=r -+
      ?(
         ~&lrlPX; -&~=+ ~operators~~,==+ ~precedence~~&-,
         ~&\~& &rl.precedence:= pru-rules\default_hierarchies+ ~&rl.operators),
      ?(
         ~&lrlPX; -&~=+ ~help_topics~~,==+ ~~ ~formulators; *~ ~mnemonic=='help'&-,
         ~&\~& &rl.formulators:= :^/help_formulator+~&rl.help_topics ~mnemonic~='help'*~+ ~&rl.formulators),
      ^/~&l ~&r; ~&ar^?\~&a ?(
         ~&arhr&& (any [=)^D/~&arhr.keyword ~mnemonic*+ ~&al.formulators,
         ~&\~&arh2falrtPXPRXrlPlrrPCX -+
            (_formulation,(_file%Z,_option%Z)%XL)%XMk^(
               ^H/~&rl.formula ^\~&l ~&r; ^/~&rhr.parameters -&~&l.filial,~&rt,~&rthl&-,
               ~&r; -&~&l.filial,~&rt,~&rthl&-?/~&rtt ~&rt),
            ^/~&al (_formulator,(_file%Z,_option%Z)%XL)%XMk^\~&ar -+
               ~&rt?\~&rh % :^(
                  ' ambiguously truncated option: '--+ ~&l,
                  :^('please distinguish '--+ ~&rtt?/'among'! 'between'!,~&r; * '   '--+ ~mnemonic)),
               ^/~&l ~&z+ nleq-<&h.for-favorite+ |=(for-favorite)+ ||~&r ~| ==+ ~/&l &r.mnemonic,
               (^/~&l ~| [=+ ~/&l &r.mnemonic)^/~&arhr.keyword ~&al.formulators+-+-)+-,
   ^/~&l ~&r.(files,std-options); ~&NiX; ~&arl^?\~&arrNiXS ~&arr?\~&arliNXS (^E/~&al ~&arrh.position)?(
      :^/~&Narrh3X ^R/~&f ^/successor+~&al ^/~&arl ~&arrt,
      :^/~&arlh3NX ^R/~&f ^/successor+~&al ^/~&arlt ~&arr)+-

#optimize-

phases = # a list of functions each taking a formulation to a function that computes a phase of the compilation

optimization* <
   profile\'phase 3'+ ~target_filter; ; ~&irB+ ||evaluation -+
      ~&i&& ~&t?(
         % :/' unrecognized identifiers: '+ (* '   '--+ ~&L)+ ~&hrPSx+ nleq-<&l*+ |=&rhthPX+ num+ ~&x+ * <.
            ~filename&& --':'+ ~filename,
            ~filename~='command-line'&& ~location; ~&ilrBB&& --+ ~~ --':'+ ~&h+ %nP,
            ^T\~lexeme &&' '! ~location!| ~filename>,
         ~&h; % ^TNC(
            ^T(~filename&& --':'+ ~filename,~filename~='command-line'&& ~location; ~&ilrBB&& --+ ~~ --':'+ ~&h+ %nP),
            ' unrecognized identifier: '--+  ~lexeme)),
      -|~| ^wZ/~&r.lexeme ~&l,~&r|-^(
         ~&a^& ^T\~&favPML -&~&ad.lexeme=='=',~&av,~&avh,~&avhd,~&iNC+ ~&avhd.lexeme&-,
         *^0 ^T\~&vL -&~&d.semantics.&Z,~&d.lexeme; -&~&wZ/`#,~&itBhthPXB~= ~&iiX `_&-,~&dNC&-)+-,
   profile\'phase 2'+ _token%TMk++ ~&i&&+ global_dead_code_removal++ +^(
      ^=+ (*^0 ~&vik!| ~&d.semantics.&Z)?(guard/resolve panhandler,~&)++ ~postformer~=~&?(
         ^=+ preprocess;+ ~postformer,
         preprocess!),
      +^/~import_filter ~preformer; //+ -+
         ^rlhPNlth2rNNCCVNCCVB/~&l -+
            ~&i&& ~&t?\~&h ~&V/apt-separation,
            -*; * ^lhPNlth2rNNCCVNCCV\~&r (* ~&r+ &r.filename:= ~&l)^D\~&l ~&r&& ~&rd.filename+-,
         //~& dir-token_forms(default_operators) <default_directives-hide>+-),
   profile\'phase 1'+ _token%TLMk++ +^\~source_filter num;+ ~&r.preamble!=;+ -+
      //^T ~&l; * -+
         //~&lhPNlth2rNNCCVNCCV dir-token_forms(default_operators) <default_directives-export>,
         //~&V ~&h ogl-token_forms <ez_declaration>,
         ~&iNVS+ (location:= &!)*+ <.
            token$[lexeme: spell+ ~&r.path.&ihB,filenumber: ~&l,filename: ~&r.path.&ihB],
            token$[lexeme: ~&r.path.&ihB,filenumber: ~&l,filename: ~&r.path.&ihB,semantics: !+ !+ ~&r.contents]>,
         &r.path:= ~&r.path; -&~&,std-suffix/'.avm'+ ~&h&-?\~& :^\~&t ~&x+ ~&hxtttt+-,
      ~&r;+ +^(
         *+ -+  # generating the parser is costly and not required unless new operators are defined
            ?=(
               ~&/pru-default_rules extra_tabular default_operators,
               ~&\fen-parser ! fen-parser/pru-default_rules extra_tabular default_operators),
            ~/precedence operators+-,
         +^/~token_filter *+ _token%LLMk++ -+
            (-*; * &r.(filenumber,filename):=r ~&l)*++ ^D/(^/~&l -|~&r.path.&ihB,! 'stdin'|-),
            //+ * -*; * -+
               ~lexeme=='__switches'?\~& semantics:= <>!!!,
               ~lexeme=='__ursala_version'?\~& semantics:= for-version_number!!!,
               ~&r+ ~lexeme=='__source_time_stamp'?r\~& &r.semantics:= !+ !+ ~&l+-,
            ^D/~&r.stamp+ ~&r.(path.&h,contents);+ -+
               ?=(                                                       # same with the lexer
                  ~&\default_directives extra_tabular default_operators,
                  ~&\fen-lexer ! fen-lexer\default_directives extra_tabular default_operators),
               ~/operators directives+-+-)+->

#optimize+

compiler = # takes a formulation to a function taking a list of source files to a list of target files

profile\'instantiation' -++-+ gang phases

(# core_dumper takes a phase number n and returns a function invoked like the compiler but performing only the first n phases
of the compilation and dumping the resulting intermediate data structure to a binary file formatted as a self describing type
and hence printable with %yP #)

core_dumper =

"n". (compress1000++ -++-+ gang ~&x take/"n" ~&x phases); //+ ~&iNC+ file$[
   stamp: &!,
   preamble: <''>!,
   path: <'phase'--(~&h %nP "n")>!,
   contents: ~&H\"n" (case ~&)\_file%LQY! {1: _token%TLQY!,2: _token%TQY!}]
