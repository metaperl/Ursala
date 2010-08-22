
#import std
#import nat
#import tag
#import tco
#import opt

profile = +^(-=/'trace'?\~&l! ! guard^|/~& ^C\~&+ !,-=/'profile'?\~&! ! ^\~&r std-profile) __switches

#library+
#optimize+

token ::

lexeme         %s 
filename       %s 
filenumber     %n 
location       %nWZ 
preprocessor   %fOZ 
postprocessors %fOZLZ 
semantics      %fOZ
suffix         %om
exclusions     %fOZ
previous       %o

#optimize-

(# plugins are numbered pairs of predicates and functions that serve as cases within the main -??- construct of the tokenizer
function. The predicate and the function therefore operate on a job ~&J(f,a), where refer(f) is the tokenizer function, and a
is of the form %nWsLLX. The number indicates the order in which the plugins should be tried, which is determined by the
particular patterns they detect. If new plugins are added for new lexical classes, they should normally have numbers greater
than 8 and less than 100, with the more general ones having higher numbers. #)

------------------------------------------------------ operator plugins -----------------------------------------------------

#library-

letters = std-letters--+ ~&ihB+ ~&j/<'_'>+ ~lexeme*

recognition =

"t". (\/~&D ~lexeme*~ "t"); ~&rS+ *~ -&
   [=+ ~/&r.lexeme &l,
   -!~&rZ,~&lzPrhPX; not both \/-= letters "t"!-+ ^/~&r.lexeme ^H\~&l ~+ :/0+ 0!*+ ~&r.lexeme&-

#library+

built_ins = # takes a list of built in tokens to a plugin that recognizes and initializes them during lexical analysis

-+
   "t". ~&/100 ~&/recognition"t"@arh -+
      :^/&r.location:=r~&lal -+
         ^R/~&lf ^(^/~&lall nat-sum@lalr3rX,:^/skip@rlarh3X ~&lart),
         ^/~&l length+ --+ ~&r.(lexeme,suffix)+-,
      ^/~& -+
         (&l.suffix:=l~&r)^/~&l ~&llrHX^=rlx+ ^/~&l.suffix ~&NrX,
         ^/~&l ^|H\~& //skip+ length+ ~lexeme,
         ^\~&arh (leql+ ~lexeme~~)$^+ recognition"t"@arh+-+-,
   * suffix:= ~exclusions?(
      -+
         ~&r?\~&! ?^|(@r,^/~&! ?^(~&r&&+ @rh+ lsm@nhPS,~&\~&+ ^\~&rt+ :^\~&l+ @rh+ -:@nhPiXS)),
         ^/~exclusions ~suffix; *~ ~&i&& ~&n; ~&i&& %sI+-,
      -+
         ~&?\~&! ?^(~&r&&+ @rh+ lsm@nhPS,~&\~&+ ^\~&rt+ :^\~&l+ @rh+ -:@nhPiXS),
         ~suffix; *~ ~&i&& ~&n; ~&i&& %sI+-)+-

markup = # supports -[ and ]- operators

12: ~&/-&~&arht,~&arhhthPX-={(`-,`[),(`],`-)}&- -+
   :^(
      token$[
         lexeme: ~&rrll,
         location: ~&lal,
         suffix: -&~&rrll=='-[-[',~&rrrihB; ==`.-~; ~&liNCNXS&-,
         preprocessor: case~&rrll\0! {
            ']-]-': ! <'unbalanced ]-'>!%,
            ']--[': ! <'unbalanced ]- or -['>!%,
            '-[-[': ! ~&dviFPV; -&~&v,~&vtZ,~&vhd.lexeme==']-]-'&-?(
               &vhd.(preprocessor,suffix):= ~&d.suffix; //~& ~&dviFPV; ~&v?\~& ~&vt?(
                  <'bad parse tree'>!%,
                  ^V/~&d ~&iNC+ ~(&d.suffix,&vh); ^?(
                     -&~&ar,~&ard.lexeme==']--[',~&arv,~&arvt,~&arvttZ&-,
                     ~&\~&ar ^V(&ard.(preprocessor,suffix):=ard~&NalPX,:^/~&arvh ~&iNC+ ~&falrvth3XPR))),
               <'unbalanced -['>!%)},
         semantics: case~&rrll\-+!,!,~&rrlr+- {
            '-[-[': lift+ ~&rrlr; ~&?\~&! "t". ~&h; (~&y "t")--+ :^\~&itB (~&z "t")--+ ~&ihB,
            ']-]-': lift+ ~&rrlr; ~&?\~&! "t". ~&h; --(~&t "t")+ ^T/~&iyB ~&iNC+ --(~&h "t")+ ~&izB,
            ']--[': lift+ ~&rrlr; ~&?\-+^T/~&liyB :^/~&lizBPrihBPT ~&ritB,~&hthPX+-! ~&t?(
               "t". ~&hthPX; ^T(^lrNCT/~&liyB --(~&h "t")+ ~&lizB,(~&ty "t")--+ :^\~&ritB (~&z "t")--+ ~&rihB),
               ~&h; "t". ~&hthPX; ^T(~&liyB,:^/~&lizBPrhPT ~&rt)+ ^/~&l :^\~&ritB "t"--+ ~&rihB)}],
      ^R/~&lf -&~&rrll-={'-[-[',']--['},~&rrr&-?\~&rlrrPX ~&rlrrPX; ^llPrlPXrrPlrPCX/~&llPrtPX -+
         -&~&r,~&rh==`.&--> ^/successor+~&l ~&rt,
         ~&lrPrhPX+-),
   ^/~& ~&a; %nWssLXsLXXMk+ -+
      ^/~&l ^\~&rr ~&rl; ^/~&hhthPNCCPzyz2zzPNCCT ~&yzyy2NCT+ ~&htt2tC,
      ^rlPllPlrPrrlh3CCrrlt3Crrr2XX/~&rhhthPX -+
         ~&ar^?\<.--' can''t scan; unfinished markup'+ --+ (~~ --':'+ ~&h+ %nP+ successor)+ ~&al>% ~&arh?(
            -!-&~&arhh==`-,~&arht,~&arhth==`[&-,-&~&arhh==`],~&arht,~&arhth==`-&-!-?(
               ^\~&arhhthPNCCPNChtt2tCX ^/~&all successor+ successor+ ~&alr,
               ^rlPlrrlh3Crrlt3Crrr2XX/~&arhh ^R/~&f ^\~&arhtPtC ^/~&all successor+ ~&alr),
            ^RlNrlPCrrPXX/~&f ^\~&art ^/successor+~&all 0!),
         ^/^(~&ll,successor+ successor+ ~&lr) ~&rhtt2tC+-+-+-

------------------------------------------------------ character plugins -----------------------------------------------------

(# quoted_characters is a parameterized plugin taking a pair of quote characters to a plugin that selects strings enclosed by
the character, on a single line with no internal occurrences of the quotes #)

quoted_characters =

9: ~&/(~&arhh==``) -+
   :^\~&lfPlall3rrlr3Xrrr2lart3CXR token$[
      lexeme: ~&larhh4rlPC,
      location: ~&lal,
      semantics: !+ !+ ~&rlh],
   ^/~& ^(^/~&all successor+ ~&alr,~&arht); ~&r?(
      ^/~&rhNC ^\~&rt ^/~&ll successor+ ~&lr,
      <.--' can''t scan; unfinished character'+ --+ (~~ --':'+ ~&h+ %nP+ successor)+ ~&l>%)+-

quoted_variables =

("l","r"). 8: ~&/(~&arhh=="l") -+
   :^\~&lfPlall3rrlr3Xrrr2lart3CXR token$[
      lexeme: ~&larhh4rlPC,
      location: ~&lal,
      semantics: ~&ty+~&larhh4rlPC; "v". <'unbound variable: '-- "v">!%],
   ^/~& -+
      ~&ar^?\<.--' can''t scan; unfinished variable'+ --+ (~~ --':'+ ~&h+ %nP+ successor)+ ~&al>% ~&arh=="r"?(
         ^/~&arhNC ^\~&art ^/~&all successor+ ~&alr,
         ^lrlPCrrPX/~&arh ^R/~&f ^\~&art ^/~&all successor+ ~&alr),
      ^\~&arht ^/~&all successor+ ~&alr+-+-

nested_quotes = # allows the closing quotation to be represented by two consecutive quotes

("l","r"). 10: ~&/(~&arhh=="l") -+
   :^\~&lfPlall3rrlr3Xrrr2lart3CXR token$[
      lexeme: ~&larhh4rlPC,
      location: ~&lal,
      semantics: !+ !+ ~&ty+ ~&larhh4rlPC],
   ^/~& -+
      ~&ar^?\<.--' can''t scan; unfinished quote'+ --+ (~~ --':'+ ~&h+ %nP+ successor)+ ~&al>% ~&arh=="r"?(
         -&~&art,~&arth=="r"&-?(
            ^lrlPCrrPX/~&arh ^R/~&f ^\~&artt ^/~&all successor+ successor+ ~&alr,
            ^/~&arhNC ^\~&art ^/~&all successor+ ~&alr),
         ^lrlPCrrPX/~&arh ^R/~&f ^\~&art ^/~&all successor+ ~&alr),
      ^\~&arht ^/~&all successor+ ~&alr+-+-

-------------------------------------------- identifier plugins -------------------------------------------------------------

#library-

default_token = # takes a directive lexeme to the token containing the default preprocessor for an undefined directive

token$[
   lexeme: ~&,
   preprocessor: "l". <'unrecognized or misused directive: '--"l">!%,
   semantics: "l". ! <'unrecognized or misused directive: '--"l">!%]

#library+

(# directives takes a list of built in directives to a plugin selecting either one of those or an unrecognized directive
beginning with a hash and optionally ending with + or - #)

directives =

"t". 7: ~&/(~&arhh==`# ) -+
   :^\~&lfPlall3rrl2Xrrr2lart3CXR &r.location:=r~&l+ ^/~&lal -|
      ~&ihB+ (==+ ~/&l &r.lexeme)~|+ ~&\"t"+ ~&larhh4rlPC,
      default_token+ ~&larhh4rlPC|-,
   ^/~& ^(successor+~&alr,~&arht); ^?(
      -&~&ar,~&arh-= std-letters-- '%_0123456789'&-,
      ^lrlPCrrPX/~&arh ^R/~&f ^\~&art successor+ ~&al,
      -&~&ar,~&arh-='+-'&-?\~&NaX ^/~&arhNC ^\~&art successor+ ~&al)+-

identifiers = # takes a set of acceptable characters in identifiers to a plugin that selects identifiers containing them

"i". 1000: ~&/(~&arhh-= "i") -+
   :^\~&lfPlall3rrl2Xrrr2lart3CXR token$[lexeme: ~&larhh4rlPC,location: ~&lal],
   ^/~& -+-&~&ar,~&arh-="i"&-^?\~&NaX ^lrlPCrrPX/~&arh ^R/~&f ^\~&art successor+ ~&al,^/successor+~&alr ~&arht+-+-

---------------------------------------------- numeric plugins ---------------------------------------------------------------

numbers = # selects natural, rational, address, and native floating point types with C syntax

5: (
   ~&arh; -!
      ~&h-= '0123456789',
      -&~&h==`.,~&t,~&th-= '0123456789'&-,
      -&~&h==`-,~&t,-!~&th-='0123456789',-&~&th==`.,~&tt,~&tth-='0123456789'&-!-&-!-,
   -+
      :^\(^R/~&lf ^\~&rrPlart3C ^/~&lall nat-sum^/~&lalr length+ ~&rl) token$[
         lexeme: ~&rl,
         location: ~&lal,
         semantics: !+ !+ ^H\~&rl -+
            //guard -?
               (~&z-='ij'): ~&iNC; ~reader type_constructors-j,
               (~&z==`_): ~&iNC; ~reader type_constructors-v,
               (-=/`E): ~&iNC; ~reader type_constructors-E,
               (~&c/'.e'): library/'math' 'strtod',
               (-=/`/): ~&iNC; ~reader type_constructors-q,
               (-=/`-): ~&iNC; ~reader type_constructors-z,
               (-=/`:): ~=`:-~; ~&lrtPX; -+
                  leql?\<'bad address'>!% (~&a^?\~&aaX ~&ah?/~&NfatPRX ~&fatPRNX)+ ~&rSx+ zipp0+ ~&rlX,
                  ^(~&r,iota+~&l)+ ~~ ~&iNC; ~reader type_constructors-n+-,
               ~&iNC; ~reader type_constructors-n?-,
            ("s". :^\~&t "s"--+ ~&h)+ --': can''t scan; '+ ^T(--+ (~~ --':'+ ~&h+ %nP+ successor)+ ~&lal,~&rl)+-],
      ^/~& @Narh2X ~&lxPrX+ -+
         ||~& -&~&r,~&rh==`_,~&cZ/'/:+-eE.ij'+ ~&ly,~&lz-='-0123456789',~&rhPlCrtPX&-,
         ||~& -&~&r,~&rh-='+-',~&rt,~&rth-='0123456789',~&cZ/'/:'+ ~&l&-&& -+
            -&~&r,~&rh-='ij',~&l,~&lh-='0123456789',~&rtZ!| ~&rth~< letters0--'0123456789',~&rhPlCrtPX&-,
            -&~&r,~&rh-='0123456789'&-->~&rhPlCrtPX,
            -&~&l,~&lh-='e',~&r,~&rh-='+-'&-?/~&rhPlCrtPX ~&,
            -&~&r,~&rh-='0123456789'&-->~&rhPlCrtPX,
            ?\(~&/~&rhPlCrtPX ~&) -&~&l,~&lh-='.01234546789',~&r,~&rh-='eE',~&rt&-&& -!
               ~&rth-='0123456789',
               -&~&rth-='+-',~&rtt,~&rtth-='0123456789'&-!-,
            -&~&r,~&rh-='0123456789'&-->~&rhPlCrtPX,
            -&~&r,~&rh==`.,~&wZ/`.+~&l&-?/~&rhPlCrtPX ~&,
            ~&rhPlCrtPX; -&~&r,~&rh-='0123456789'&-->~&rhPlCrtPX+-,
         -&~&r,~&rh==`:,~&rt,~&rth-='0123456789',~&cZ/'.eE-/'+~&l&-?\~& ~&rhPlCrtPX; -&~&r,~&rh-='0123456789'&-->~&rhPlCrtPX,
         -&~&r,~&rh==`/,~&rt,~&rth-='0123456789',~&cZ/'.eE'+~&l&-?\~& -+
            (~&rr; ~&ihB==`.)?/~&l ~&r,
            ^/~& ~&rhPlCrtPX; -&~&r,~&rh-='0123456789'&-->~&rhPlCrtPX+-,
         -&~&r,~&rh-='0123456789'&-->~&rhPlCrtPX,
         -&~&l,~&lh-='eE',~&r,~&rh-='+-'&-?/~&rhPlCrtPX ~&,
         ?\(~&/~&rhPlCrtPX ~&) -&~&l,~&lh-='.01234546789',~&r,~&rh-='eE',~&rt&-&& -!
            ~&rth-='0123456789',
            -&~&rth-='+-',~&rtt,~&rtth-='0123456789'&-!-,
         -&~&r,~&rh-='0123456789'&-->~&rhPlCrtPX,
         -&~&r,~&rh==`.,~&wZ/`.+~&l&-?/~&rhPlCrtPX ~&,
         -&~&r,~&rh-='0123456789'&-->~&rhPlCrtPX,
         -&~&r,~&rh==`-,~&rt,-!~&rth-='0123456789',-&~&rth==`.,~&rtt,~&rtth-='0123456789'&-!-&-?/~&rhPlCrtPX ~&+-+-)

raw_data = # allows constants expressed in raw format -{...}-

11: ~&/-&~&arhh==`-,~&arht,~&arhth==`{&- -+
   :^\~&lfPrlrrPXPR token$[
      lexeme: ! '-{',
      location: ~&lal,
      semantics: !+ !+ ^H\~&rrl -+
         //guard ~reader type_constructors-x,
         ("s". :^\~&t "s"--+ ~&h)+ --' can''t scan; '+ --+ (~~ ~&h+ %nP+ successor)+ ~&lal+-],
   ^/~& ~&a; ~&ar^?\<.--': can''t scan; unfinished raw constant'+ --+ (~~ --':'+ ~&h+ %nP+ successor)+ ~&al>% ~&arh?(
      -&~&arhh==`},~&arht,~&arhth==`-&-?(
         ^\~&arhhthPNCCPNChtt2tCX ^/~&all successor+ successor+ ~&alr,
         ^rlPlrrlh3Crrlt3Crrr2XX/~&arhh ^R/~&f ^\~&arhtPtC ^/~&all successor+ ~&alr),
      ^RlNrlPCrrPXX/~&f ^\~&art ^/successor+~&all 0!)+-

-------------------------------------------------------- comment plugins -----------------------------------------------------

non_terminating_comments = # lets three hashes comment out the rest of the file

1: ~&/(~&arh; -&~&,~&t,~&tt,<.~&h,~&th,~&tth>; all ==`#&-) 0!

smart_comments = # lets a pair of consecutive hashes be a token

2: ~&/(~&arh; -&~&,~&t,<.~&h,~&th>; all ==`#,~&ttZ!| ~&tth~= `#&-) :^(
   token$[lexeme: '##'!,location: ~&al],
   ^R/~&f ^\~&arhtt2tC ^/~&all nat-sum/2+ ~&alr)

line_comments = # selects line oriented comments beginning with hashes or dash quadruples, continuable with backslashes

3: (
   -!
      -&~&arhh==`#,~&arhtZ!| not ~&arhth-= :/`# std-letters&-,
      ~&arh; -&~&t,~&tt,~&ttt,<.~&h,~&th,~&tth,~&ttth>; all ==`-&-!-,
   -+
      ^R/~&lf ^\~&rritB ~&iNX+ successor+ ~&rl,
      ^/~& ~&allPrX; -&~&r,~&rh,~&rhz==`\&--> ^\~&rt successor+ ~&l+-)

nested_comments = # selects nested multi-line comments enclosed by (# and #)

4: ~&/-&~&arhh==`(,~&arht,~&arhth==`#&- ^R/~&f -+
   ~&arr^?\<.--' can''t scan; unfinished comment'+ --+ (~~ --':'+ ~&h+ %nP+ successor)+ ~&arl>% -?
      ~&/~&arrhZhtPZY ^R/~&f ^/~&al ^\~&arrt ~&iNX+ successor+ ~&arll,
      ~&/-&~&arrhh==`(,~&arrhth==`#&- ^R/~&f ^/~&NalPC ^\~&arrhtt2tC ^/~&arll nat-sum/2+ ~&arlr,
      ~&/-&~&arrhh==`#,~&arrhth==`),~&al&- ^R/~&f ^/~&alt ^\~&arrhtt2tC ^/~&arll nat-sum/2+ ~&arlr,
      ~&/-&~&arrhh==`#,~&arrhth==`),~&alZ&- ^\~&arrhtt2tC ^/~&arll nat-sum/2+ ~&arlr,
      ^R/~&f ^/~&al ^\~&arrhtPtC ^/~&arll successor+ ~&arlr?-,
   ^NiX\~&arhtt2tC ^/~&all nat-sum/2+ ~&alr+-

-------------------------------------------------- semantic functions --------------------------------------------------------

#optimize+

panhandler = # an exception handler that displays the filename and location where the error occurred

-&~&,%snWXI+~&h&-?\~& -+
   ^T\~&rt -!leql/':::'+ ==`:*~,substring/'command-line:'!-?rh(
      ~&iNC+ ~&rh; 'usage: #'%= 'usage: --',
      (//leql 0!* iota72)?lrhPT/~&lrhPNCC ~&lrhPTNC),
   ^(
      ^T(~&hl; ~&i&& --':',--' '+ ~&hl~='command-line'&& ~&hr; ~&ilrTB+ ~&Y&& ~~ --':'+ ~&h+ %nP),
      ~&t; -&any~&,~&,all %sI,~&i&-|| :/'undiagnosed error'+ ~&x+ ~&x; takewhile subset\'0123456789')+-

(# preprocess applies preprocessors to the trees whose roots they're in from the top down. It does one application at each
level and then repeats from the top until a fixed point is reached. It saves some time by making a list of trees that don't
need to be preprocessed because they didn't change last time. Without all the exception handling, profiling, and making lists,
it would be equivalent to ^= ~&a^& ^aadPfavPMVB/~&f ^H\~&a ||~&! ~&ad.preprocessor. #)

preprocess =

~&NiX; ~&r+ guard\panhandler ^= refer profile\'preprocessing' ~&arZrlwY?/~&arNCrX profile\'descent' ~preprocessor?ard(
   (~&rar?\&! ^lrrPElrlPCrrPXrQ/~&l ~&r; ~&rlSL2lrrSPVX^/~&ard ~&falrvPDPM)^/~&ar ^J/~&f ^/~&al ~&ar; ^H\~& -+
      //guard ^H\~& ~&d; ~preprocessor&& profile^/~preprocessor 'pre-'--+ ~lexeme,
      ~&d; ^(~filename,~location; ~&iNNXY); -&~&,%snWXI+~&h&-?/~&+ //:+-,
   ^rlSL2lrrSPVX/~&ard ~&falrvPDPM)

(# evaluation takes a tree of tokens to a value, based on the assumption that the tree has been preprocessed first, by
evaluating each of the subtrees, and then applying the semantics of the root to the suffix, with the result of that
application applied to the list of values of the subtrees. Without profiling and exception handling, it would be equivalent to
~&a^& ^H\~&favPM ~&H+ ~&ad.(semantics,lag-suffix). #)

evaluation =

profile\'parse tree evaluation' guard\panhandler ~&a^& ^H\~& -+
   //guard ^H(
      ||~&! ~&ad.postprocessors.&ihB,
      ^H\~&favPM ~&ad; ^H\~suffix ~semantics|| %+ !+ ~&iNC+ 'unrecognized identifier: '--+ ~lexeme),
   ~&ad; ^(~filename,~location; ~&iNNXY); -&~&,%snWXI+~&h&-?/~&+ //:+-

(# lift is useful for operators whose suffix length indicates the order to which they should be raised, such as the markup
operators. It takes the zero order semantic function to a function that takes the suffix to the lifted semantic function. #)

lift =

"f". "s". -+
   ~&l (~&r-> ^\~&rt ~&l; "g". "g"+) ("f","s"),
   -++- ~&x (|\ "g". "g"+) (~&a^?\<>!! :^^/~&ah ~&fatPR)!* "s"+-

---------------------------------------------------- lexical analyzer generator ----------------------------------------------

(# tokenizer takes a list of plugins to to a function that takes a list of strings to a list of lists of tokens, which could
then be used as the input to a parser generated by pag-parser. #)

tokenizer =

"p". (* * (previous,location):= ~&NiX+ successor~~+ ~location)+ ~&hF+ rlc~&B+ ~&/&; ~&ar^& -??- ~&lrNCT(
   --(~&rS nleq-<&l "p") <
      (~&arhZ): ~&ihB?(:/0,~&)+ ^R/~&f ^\~&art ~&iNX+ successor+ ~&all,
      (~&arhh-={` ,~&h skip/9 characters}): ~&ihB?(:/0,~&)+ ^R/~&f ^\~&arhtPtC ^/~&all successor+ ~&alr>,
   % ^TNC/(^T(~&l,:/`:+ ~&r)+ ~&al; ~~ ~&h+ %nP+ successor) %sI+~&arh?(
      ': can''t scan; invalid token: '--+ --'...'+ take/8+ ~&arh; *~ ~=(~&h skip/9 characters),
      ! ': can''t scan; unprintable character'))
