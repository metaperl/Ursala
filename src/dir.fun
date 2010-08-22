
#import std
#import nat
#import ext
#import opt
#import ogl
#import ops
#import lam
#import apt
#import eto
#import tag
#import tco
#import lag
#import xfm

#comment -[
This module contains functions and specifications in support of
compiler directives.

Copyright (C) 2007-2010 Dennis Furey]-

#library+
-------------------------------------------------- data structures -----------------------------------------------------------
#optimize+

directive ::     # specifies a compiler directive

mnemonic        %s   # the identifier used for the directive in the source code
parameterized   %s   # means the directive needs something besides + or -
parameter       %o   # default parameter value, empty means there is none
nestable        %b   # means the directive is required to appear in matched + and - pairs
blockable       %b   # means the scope of the directive doesn't automatically extend inside nestable directives
commentable     %b   # means output files generated by the directive can have comments included by the comment directive
mergeable       %b   # means multiple instances in the same file can be merged
direction       %fOZ # a function from parse trees to parse trees that does most of the work of the directive
compilation     %fOZ # for output generating directives, a function taking a module and a list of files to a list of files
favorite        %n   # higher numbers take precedence in command line disambiguation
help            %s   # a one line description of the directive for on-line documentation

-------------------------------------------- semantic functions --------------------------------------------------------------

token_forms = # converts a list of directives to a list of tokens suitable for the lexical analyzer generator

"o". *= <.
   token$[
      lexeme: ~parameterized?(:/`#+ ~mnemonic,:/`#+ --'+'+ ~mnemonic),
      preprocessor: ~&dviFPV;+ -+.
         ~&i&&+ ?^/(~mnemonic; "m". -&~&v,~&vh,~&vtZ,~&vhd.lexeme== '#'--"m"--'-'&-) ^(
            -|~direction,! ~&|-; "d". ~&dvhv2V; ^H(~&d.preprocessor,~&)+ &d.(preprocessor,lexeme):= -+
               //~& ~&dviFPV; ~&v&& ~&ivigPB?(unseparate,~&)+ "d"+ unseparate,
               ~&d.lexeme; `+?=z/~&y ~&+-,
            ~parameterized?(~mnemonic; "m". <'unmatched #'--"m">!%,~mnemonic; "m". <'unmatched #'--"m"--'+'>!%)),
         ~parameterized?\~&! ! ^V/~&d ~&v&& :^\~&vt ~&vh; ~&a^& ~lexeme=='(separation)'?ad/~&adPfavh2Ravt2CV ?(
            ~&ad.lexeme; ~&i&& ~&h==`#,
            ~&/~&adPfavPMV ~&a; *^0 ^V\~&v ||~&d -&~&v,~&d.lexeme=='(juxtaposition)'&-&& -+
               lexeme:='(application)'!,
               ~&H\application"o"+ (filename,location):=+ !+ ~&d.(filename,location)+-)+-,
      semantics: !+ -+
         //+ _file%LomwXMk+ ^/~&l ~&riF; _file%LI?\<'bad output file list'>!% -+
            * -&~path.&Z,~preamble.&Z,~contents.&izB; *~ ~=` &-?\~& contents:= --<''>+ ~contents,
            *= all_same~preamble.&Z?(
               (any ~preamble.&ihB== '!\bin\sh')?(
                  ~&h.path.&h; -&~&,--': '&-; % ~&iNC+ --'duplicate executable file names',
                  ~&hNC+ &h.(stamp,preamble,contents):= ^/any~stamp ^(
                     ~preamble*; -+
                        ^T\~&l (~&x+ skip+ ~&lrxPX)*=+ ^D\~&r length+ ~&l,
                        ^(:-0 ~&bx; gcp,~&)+ ~&i&& ^(gcp:-0,~&); :^/~&rh skip*+ ^D\~&rt length+ ~&l+-,
                     ~contents*=)),
               any~path?\~& ~&h.path.&ihB; -&~&,--': '&-; % ~&iNC+ --'duplicate file names'),
            (~&l.path&& ==+ ~&b.path)|=+ -!~path,~contents; ~&i&& any~&!-*~+-,
         _file%LomwXsoAULMk;+ (%soAI&& ~&n)!=;+ ~&lrlSL2TrrSL2X;+ ^/~&l+ ^T\~&r+ ~compilation|| <>!!+-],
   token$[
      lexeme: :/`#+ --'-'+ ~mnemonic,
      semantics: ~mnemonic; "m". <'unresolved #'--"m"--'-'>!%,
      preprocessor: ~nestable?(~mnemonic; "m". <'unmatched #'--"m"--'-'>!%,! unseparate)]>

-------------------------------------- tables of compiler directives --------------------------------------------------------

#library-
#optimize-

user_defined_directives = # these depend on a user supplied function to do something

^A(~mnemonic,~&)* <
   directive[
      mnemonic: 'depend',
      direction: ~&v&& ^V\~&vt ~&H\separation+ (filename,location):=+ !+ ~&d.(filename,location),
      parameterized: 'build dependence specification',
      help: 'specify build dependences for external development tools'],
   directive[
      mnemonic: 'preprocess',
      direction: ~&v&& ~&vt&& (*^0 -&~&,~&d.semantics,~&vig&-)?vh\~& -+
         ^H/~&d.preprocessor ~&,
         (&d.preprocessor,&v):= ^\~&vt evaluation+preprocess+~&vh; (%fI&& ~&)|| <'usage: #preprocess tree_transformer'>!%+-,
      parameterized: 'tree-transformer',
      help: 'filter parse trees through a given function before evaluating'],
   directive[
      mnemonic: 'fix',
      direction: (*^0 &&~&vig ~&d.semantics)?vh\~& ~lexeme=='(evaluated)'?vhd(
         conditional(
            -+all ~&i&& ~&d.lexeme-= {'(evaluated)','(imported)'},~&a^& ~lexeme=='='?ad/~&avitB ~&favPML+-,
            ~&\~& ~&a^& ~lexeme=='#fix'?ad(
               ~&avitB&& ~&avtt?\~&avth ^V\~&avt ~&H\separation+ (filename,location):=+ !+ ~&ad.(filename,location),
               ~&adPfavPMV)),
         (&d.semantics,&vh):= ^(
            !+ ~&r;+ ~&iNH+ ~&d.semantics,
            preprocess@vh; -+
               ~&V\<>+ &ld.((preprocessor,postprocessors),lexeme,semantics):=ld ~&/&+ ~&/'(evaluated)'+ !+ !+ ~&r,
               ^/~& evaluation; %fI?/~& <'usage: #fix (fixed point combinator)'>!%+-)),
      parameterized: 'fixed-point-combinator',
      help: 'specify a fixed point combinator for solving circular definitions'],
   directive[
      mnemonic: 'postprocess',
      direction: ~&v&& ~&vt&& -+
         (*^0 -&~&,~&d.semantics,all~&+ ~&v&-)?vh\~& ^V(
            ~&H\separation+ (filename,location):=+ !+ ~&d.(filename,location),
            (^D\~&vt evaluation+~&vh; (%fI&& ~&)|| <'usage: #postprocess file_list_filter'>!%); * ~&ar^& ?(
               ~&ard; &&~semantics ~lexeme.&h==`#,
               ~&\~&ard2falrvPDPMV ^V\~&falrvPDPM ~&ard+ &ard.semantics:= -+
                  ("p","s"). ^(~&l,"p"+ ~&r)++ "s",
                  ~/&al &ard.semantics+-)),
         ^V/~&d :^\~&vt preprocess+ ~&vh+-,
      parameterized: 'file-list-filter',
      help: 'filter output files through a given function before writing'],
   directive[
      mnemonic: 'output',
      commentable: &,
      direction: ~&vigPo?\~& ~&v&& ~&vt&& ?(
         ~&vh; *^0 -&~&,~&d.semantics,~&vig&-,
         ~&\~& ~&dvtPV+ &d.(preprocessor,semantics):= ~&NiX+ !+ -+
            //+ ^/~&l ~&riF; (_file%LI)?(
               -!~path,~contents!-*~; |=(path); -+
                  * -&~path.&Z,~preamble.&Z,~contents.&izB; *~ ~=` &-?\~& contents:= --<''>+ ~contents,
                  *= all_same~preamble.&Z?(
                     (any ~preamble.&ihB== '!\bin\sh')?(
                        ~&h.path.&h; -&~&,--': '&-; % ~&iNC+ --'duplicate executable file names',
                        ~&hNC+ &h.(stamp,preamble,contents):= ^/any~stamp ^(
                           ~preamble*; ^(gcp:-0,~&); ^T/~&l skip*=+ ^D\~&r length+ ~&l,
                           any~preamble?\~contents*= (#~&tihQ+#) ~contents*=)),
                     any~path?\~& ~&h.path.&ihB; -&~&,--': '&-; % ~&iNC+ --'duplicate file names')+-,
               <'usage: #output (file list generating function)'>!%),
            (%soAI&& ~&n)!=;+ ~&lrlSL2TrrSL2X;+ ^/~&l+ ^T\~&r+ ~&l;,
            evaluation+preprocess+~&vh; (%fI&& ~&)|| <'usage: #output (file list generating function)'>!%+-),
      parameterized: 'file-list-generator',
      help: 'write output files generated by a given function']>

selective_tree_map = # like *^+ -&~&d.lexeme=='=',~&v,~&vt,~&vttZ&-?\~& but avoiding type expressions and field identifiers

"f". ~&NiX; ~&r+ _token%TswXCRk ~&ar^& -&~&d.lexeme=='=',~&v,~&vh,~&vt,~&vttZ,~&vth&-?ar(
   ~lexeme.&ihB==`_?arvhd(
      ^/~&arvhd.lexeme.&t ~&ar; (*^0 ~&vik!| ~&d.lexeme.&ihB==`")?/"f" ~&,
      -!~&alZ,==+ ~/&al &arvhd.lexeme!-?\~&a ~&NiX+ "f"+ ~&ar),
   ^rlPlrrPVX/~&ard ~&falrvPXPJ; _token%oUTLswXJCRk ~&aar^?\~&aa (^rlPlrrPCX/~&rr ~&lfPlaf2rlPlaart4XJR)^/~& ~&afalrhPXPR)

code_motion_directives = # to move the code around

^A(~mnemonic,~&)* <
   directive[
      mnemonic: 'order',
      direction: ~&v&& ~&vt?\~&vh ^V\~&v ~&H\separation+ (filename,location):=+ !+ ~&d.(filename,location),
      help: 'no effect at present, reserved for future use'],
   directive[
      mnemonic: 'pessimize',
      compilation: (@r any ~preamble&& ~path.&ihB~= 'core')&& ! <
         file[contents: <'warning: output files may contain pessimized code'>]>,
      direction: ^V/~&d ~&v; * ~&a^& ~lexeme=]'#hide'?ad/~&a ^V(
         &ad.(preprocessor,lexeme,postprocessors):=ad @ad ^(
            ~preprocessor; ~&i&& -|
               -&~&rZ,~&l,~&ll== lambda_optimization,~&lr&-,
               -&~&rZ,~&l&-&& -&
                  ~&ll== optimization &d.postprocessors:= ~&d.postprocessors; ~&i&& :^\~&t ~&h; &&~& ~=optimization,
                  ~&i&-,
               //+ optimization &d.postprocessors:= ~&d.postprocessors; ~&i&& :^\~&t ~&h; &&~& ~=optimization|-,
            ^(~lexeme; '.'?=/'(pessimal point)'! ~&,~postprocessors; ~&i&& :^\~&t @h &&~& ~=optimization)),
         ~&favPM),
      help: 'inhibit default functional optimizations'],
   directive[
      mnemonic: 'optimize',
      favorite: 1,
      direction: (*^& ~&vik!| ~&d.lexeme.&ihB==`"!| ~&d.lexeme=='='&& ~&v&& ~&vhivB!| ~&d.semantics.&Z)?/~& -+
         &d.(preprocessor,semantics):= ~&NiX+ -+
            !+ //+ ^/~&l ^T/~&r ~&l; *= -&not singly_branched+~&m,not ~&nihB==`_,not %fI+ ~&m&-&& ~&iNC+ file$[
               contents: ~&iNC+ 'warning: no optimization performed for non-function '--+ ~&n],
            ~&iNH+ ~&d.semantics|| ~&!+-,
         selective_tree_map &vthd.(lexeme,postprocessors):= ~&vthd; ^(
            ~lexeme; {'(evaluated)','(imported)'}?<\~& ^T/~&y ' except for optimization'--+ ~&zNC,
            ~postprocessors; :^\~&itB optimization++ ~&ihB|| ~&!)+-,
      help: 'perform extra first order functional optimizations'],
   directive[
      mnemonic: 'profile',
      direction: (*^& ~&vik!| ~&d.lexeme.&ihB==`"!| ~&d.lexeme=='='&& ~&v&& ~&vhivB!| ~&d.semantics.&Z)?/~& -+
         &d.(preprocessor,semantics):= ~&NiX+ -+
            !+ //+ ^/~&l ^T/~&r ~&l; *= -&not singly_branched+~&m,not ~&nihB==`_,not %fI+ ~&m&-&& ~&iNC+ file$[
               contents: ~&iNC+ 'warning: no profiling applied to non-function '--+ ~&n],
            ~&iNH+ ~&d.semantics|| ~&!+-,
         selective_tree_map &vthd.postprocessors:= -+
            ("fs","l"). ((-|~&h,! ~&|- "fs"); %fI?\~& profile\"l"):(~&t "fs"),
            ^(~&vthd.postprocessors|| <~&>!,~&r+ ~=`-~-+ ~&vhd.lexeme)+-+-,
      help: 'add run time profiling annotations to functions']>

output_generating_directives = # these directives generate or annotate standard types of files

^A(~mnemonic,~&)* <
   directive[
      mnemonic: 'binary',
      commentable: &,
      compilation: ~&l; * file$[stamp: &!,path: ~&nNC,preamble: &!,contents: ~&m],
      help: 'dump each symbol in the current scope to a binary file'],
   directive[
      mnemonic: 'text',
      commentable: &,
      compilation: ~&l; file$[stamp: &!,path: ~&iNC+ --'.txt'+ ~&n,contents: ~&m]*+ *~ %sLI+ ~&m,
      help: 'write printable symbols in the current scope to text files'],
   directive[
      mnemonic: 'show',
      favorite: 1,
      direction: -&~&v,~&vh,~&vhd.lexeme-={'=','(separation)'}&-?/~& ~&v&& ~&vt?\~&vh ~&V/separation+ ~&v,
      compilation: ~&l; *= %sLI?m(
         ~&iNC+ file$[contents: ~&m],
         ^lrNCC/file$[contents: ~&iNC+ 'warning: '--+ --' is not displayable; core dumped'+ ~&n] file$[
            stamp: &!,
            path: <'core'>!,
            preamble: ~&iNC+ ' core dump of non-displayable symbol '--+ ~&n,
            contents: ~&m]),
      help: 'display text valued symbols to standard output'],
   directive[
      mnemonic: 'cast',
      favorite: 1,
      compilation: ~&l; * file$[
         stamp: &!,
         path: <'core'>!,
         preamble: ~&iNC+ ' core dump of unknown type symbol '--+ ~&n,
         contents: ~&m],
      direction: ~&vigPo?\~& ~&v&& ~&vt&& -&~&d.semantics,~&vig&-*^0?vh\~& _token%TMk+ -+
         ~&V/separation+ ~&dvxPD; ~&x+ ~&a^& -+
            :^/~&r ~&lahr3rE?/~&lfatPR ~&latrS,
            ^/~& ~&ah; ~&ar^& -&~&ard.lexeme=='=',~&arv,~&arvh,~&wZ/`-+ ~&arvhd.lexeme&-?/~&alrNCV ~&ard2falrvPDPMV+-,
         ~&dvtPV+ &d.(preprocessor,semantics):= ~&NiX+ -+
            ("s","t"). "u". -+
               ^/~&l ~&r; *= -!~stamp.&Z,~path~= <'core'>!-?/~&iNC ((^H/~&lhd.recognizer ~&)/<"t">+ ~contents)?(
                  ~&iNC+ ((path,preamble),contents):= ~&NNXiX+ --<''>+ (^H/~&lhd.printer ~&)/<"t">+ ~contents,
                  :/file[contents: ~&iNC 'warning: can''t display as indicated type; core dumped']+ ~&iNC),
               _file%LomwXMk+ _file%LomwXsoAULMk; "s" "u"+-,
            ^/(~&d.semantics; ~&iNNXH?/~& ^/-&%soAI,~&n&-*~++ ~&irB++) evaluation+preprocess+~&vh; ?(
               ~&i&& _type_constructor%TI,
               ~&/~& <'usage: #cast (type expression)'>!%)+-+-,
      help: 'display values to standard output formatted as a given type',
      parameter: %g,
      parameterized: 'type-expression'],
   directive[
      mnemonic: 'executable',
      commentable: &,
      compilation: ~&l; * %fI?m(
         file$[stamp: &!,path: ~&nNC,preamble: &!,contents: ~&m],
         file$[contents: ~&iNC+ 'warning: no executable written for non-function '--+ ~&n]),
      direction: ~&vigPo?\~& ~&v&& ~&vt&& ?(
         ~&vh; *^0 -&~&,~&d.semantics,all~&+ ~&v&-,
         ~&\~& ~&dvtPV+ &d.(preprocessor,semantics):= ~&NiX+ -+
            ("s","p","c"). "s"; //+ ^/~&l ~&r; * ?(
               -!~stamp.&Z,~path.&Z,~preamble~=&!-,
               ~&/~& preamble:= <'!/bin/sh','\','exec avram '--"p"--' "$0" '--"c"--' "$@"'>!),
            ^\~&r ~&l; ~&r?\~&l ~&l; "s". "s"; //+ ^/~&l ~&r; :/file[
               contents: <'warning: executable file contains pessimized code'>],
            ^/(^/~&d.semantics *^0 ~&vik!| ~&d.lexeme-={'#pessimize','#pessimize+'}) -+
               mat` ~~+ ^\~&r ~&l; * =]'-'?/~& '--'--,
               ~&?\&! ~~ %sLI?/~& %sI?/~&iNC <'usage: #executable (<avram options..>,<configuration filenames..>)'>!%,
               evaluation+preprocess+~&vh+-+-),
      help: 'write an executable file for each function in the current scope',
      parameterized: '(<avram options..>,<config-filenames..>)'],
   directive[
      mnemonic: 'library',                       # compresses record type expressions before writing
      commentable: &,
      mergeable: &,
      compilation: ~&l; |=hS&n; ~&iNC+ file$[
         stamp: &!,
         preamble: -+
            -&~&,:/` &-*+ --<''>+ * ^T/~&l :/` + ~&r,
            ^T\~&r ~&l; *= :^/~&z ~&y; * ^('   - '--+ ~&x+ ~&ttttt+ ~&lx,` !*+ ~&r),
            ~&lrhSPX+ ~&t!=+ -<&zn+ ~&a^& `_?=ahnh\~&ahPNCfatPRC -+
               -&~&rl,~&rlzn3lahnt4X; ==+ ~&bl+ ~=` -~~~&-?/~&rlPlfPrrPRC ~&lah2NClfatPRPC,
               ^/~& ~&ahnt2tX; ~&ar^?\&! (~&alrhn2X; ==+ ~&bl+ ~=` -~~~)?/~&arhPNCrtPX ~&arh2falrtPXPRClrlPCrrPX+-,
            * ^A(((nleq\32+ length)-> --' ')+ ~&n,((nleq\15+ length)-> ' '--)+ ' ('--+ --')'+ ~&h+ %nP+ weight+ ~&m)+-,
         contents: * ||~& -&~&,~&n,~&nh==`_,~&nt,~&nth~=`_,~&m&-&& -|
            _type_constructor%TI+~&m&& ^A/~&n ~&m; 1000%Q+ *^ ^V\~&t ~tag-mnemonic-=(~&j\<'Q'> ~&nS atypical_types)?d(
               ~&NdX+ &d.((reader,generator),(microcode,arity),(tag-help,target)):= (&,&,&)!,
               ~&d.tag-mnemonic),
            -&~&r,^A/~&l note+ ~&rK6lX&-^/~&n %fI+~&m|-],
      direction: (^|V/~& *= ||~&iNC -&~&,~&d.lexeme-={'#library'},~&v&-)*^0; &d.semantics:= -+
         (~&rl; ~&i&& ~&H\&)?\~&rl ~&Z&&+ +^^\~&rl !+ ~&l?\(&rh.path:=+ ^T\~&rh.path.&itB+ !+ ~&rr) -+
            //+ ^/~&l ~&r; :^(~&h,~=+~&b.contents~|)+ :/file[contents: <'warning: library contains pessimized code'>],
            &rh.path:=+ ^T\~&rh.path.&itB+ !+ ~&rr+-,
         %bfOsLXXMk^(
            *^0 !|~&vik ~&d.lexeme-={'#pessimize','#pessimize+'},
            ~&d; ^/~semantics ~filename; ~&iNC+ --'.avm'+ ||'noname'! ||~& ~&x; ~&itBx+ skipwhile ~=`.)+-,
      help: 'write a library file of the symbols defined in the current scope',
      blockable: &]>

scope_delimiting_directives =

^A(~mnemonic,~&)* <
   directive[
      mnemonic: 'export',
      help: 'allow declarations to be visible outside the current scope',
      blockable: &],
   directive[
      mnemonic: 'hide',
      direction: -+
         hide_invisible_code+ substitute+ disallow_duplicates,
         unseparate+ *^0 ^V/~&d ~&v; ~&g?\~& ~&hdPvSLPVS+ |= (==+ ~~ ~&d.lexeme)&& ~&ld.lexeme; -&
            ~&h== `#,
            ~&t-= ~mnemonic* ~mergeable*~ ~&LmS <user_defined_directives,output_generating_directives>&-,
         ^V/~&d preprocess*+ ~&v+-,
      help: 'make enclosed declarations invisible outside unless exported',
      nestable: &]>

important_directives =

^A(~mnemonic,~&)* <
   directive[                  # assumes record type expressions are in compressed form and decompresses them
      mnemonic: 'import',
      direction: -!~&vZ,~&vhd.lexeme.&h==`#!-?/<'misused #import directive'>!% ?(
         ~&vh; *^0 ~&d.semantics&& all~&+ ~&v,
         ~&\~& -+
            ^V/(~&H\separation+ (filename,location):=+ !+ ~&d.(filename,location)) ~&h?(~&,~&t)+ :^\~&vt -+
               //~&rlhPNlth2rNNCCVNCCVB token_forms(default_operators) <scope_delimiting_directives-hide>,
               //~&rlhPNlth2rNNCCVNCCVB token_forms(default_operators) <scope_delimiting_directives-export>,
               (~&i&& ~&t?\~&h ^V\~& ~&H\separation+ (filename,location):=+ !+ ~&hd.(filename,location))+ -?
                  (~&r; any ~&Z!| ~&nZ,<'usage: #import <(identifier,value)...> or library file name'>!%),
                  (
                     ~&r; any ~&n; (=]'__')!| not all \/-= :/`_ letters,
                     <'unprintable identifier in imported module'>!%),
                  ~&\<'bad #import type expression'>!% ~&r; any -&
                     ~&nt&& ~&nh==`_,
                     not -!
                        ~&m; extractable&& extract; *^0 (all~&+ ~&v)&& -!
                           ~&dlZ&& ~&dr; ~&i&& _type_constructor%I&& ~tag-mnemonic-= ~&nS atypical_types,
                           ~&d-= ~&nS type_constructors!-,
                        ^(~&n,%fI+~&m); ~&r&& ^E/~&l ~&rdl=='note'&& ~&rvthK6!-&-,
                  (~&r; |=&n; any ~&t,% :/'duplicate #import identifiers:'+ (* '   '--)+ ~&tFhnPS+ |=&n+ ~&r),
                  -*; * (&vhthPXd.(filename,filenumber,location):= ~&iiX+ ~&d.(filename,filenumber,location))^V/~&l <.
                     ~&V\<>+ token$[lexeme: ~&rn,semantics: !+ !+ ~&rn],
                     ~&V\<>+ token$[
                        lexeme: '(imported)'!,
                        semantics: !+ !+ ~&r; ?(
                           -&~&nh==`_,~&nt&-&& not ^(~&n,%fI+~&m); ~&r&& ^E/~&l ~&rdl=='note'&& ~&rvthK6,
                           ~&\~&m ^H\~&m -+
                              //guard type_decompression type_constructors-y,
                              !+ ~&iNC+ 'bad imported type expression: '--+ ~&n+-)]>?-,
               ^\-+~&inBF+ -&~&,not %soXLI,extractable&-?\~& extract,evaluation+ preprocess+ ~&vh+- -+
                  \/~&H token[lexeme: '=',semantics: ~&hthPA!],
                  (filename,filenumber,location):=+ !+ ~&d.(filename,filenumber,location)+-+-+-),
      help: 'make a given list of symbols visible in the current scope',
      parameterized: 'library-file-name'],
   directive[
      mnemonic: 'comment',
      direction: ~&vigPo?\~& ~&v&& ~&vt&& (~&v; all *^0 -&~&,~&d.semantics,all~&+ ~&v&-)?\~& ^V(
         ~&H\separation+ (filename,location):=+ !+ ~&d.(filename,location),
         (^D\~&vt evaluation+preprocess+~&vh; %sLI?/~& %sI?/~&iNC <'usage: #comment <strings..>'>!%); ~&a^& -+
            ~&r?/~&rlatrS3C ~&lahr2fatPRC,
            ^/~& ~&ah; ~&ar^& ?(
               ~&ard; (~lexeme.&h== `#)&& ~lexeme.&t-= ~mnemonic* ~commentable*~ ~&LmS <
                  user_defined_directives,
                  output_generating_directives,
                  scope_delimiting_directives>,
               ^(~&al,^H\~&ar ~&ard.preprocessor|| ~&!); ^V\~&rv ~&rd+ &rd.semantics:= -+
                  ("c","s"). "s"; //+ ^/~&l ~&r; * ~path?\~& ~preamble?(
                     -&~preamble.&h=='!/bin/sh',~preamble.&z=]'exec avram',~preamble.&y,~preamble.&yzz==`\&-?(
                        preamble:= ^T/~preamble.&yy (-&~&,:/` &-* "c")--+ ~preamble.&yzPzNCC,
                        preamble:= (--<''> -&~&,:/` &-* "c")--+ ~preamble),
                     contents:= "c"--+ ~contents),
                  ~/&l &rd.semantics+-,
               ^EZrB/~&ar ^V/~&ard ~&falrvPDPJ; ~&aa^& (~&r?/~&rlaatrS4C ~&laahr3fafatPJPRC)^/~& ~&afahPR)+-),
      help: 'insert a given string or list of strings into output files',
      parameterized: 'string-list']>

#library+

default_directives = 

^A(~&n,~&m; (direction,compilation):= optimization~~+ ~/direction compilation)* ~&L <
   important_directives,
   user_defined_directives,
   code_motion_directives,
   output_generating_directives,
   scope_delimiting_directives>
