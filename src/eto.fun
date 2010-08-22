
#import std
#import nat
#import ext
#import opt
#import sol
#import lag
#import tag
#import tco
#import ogl
#import apt
#import lam

#comment -[
This module describes a few operators not included in ops-operators
because they are defined in terms of other operators appearing in the
table.

Copyright (C) 2007-2010 Dennis Furey]-

#optimize+
#library+  # not everything is a useful entry point unless you're debugging the compiler

order = preprocess; ~&NiX; ~&rd.lexeme-={'(juxtaposition)','(tight application)'}->l ^\~&rvh successor+~&l

------------------------------------------ functions in support of record declarations -------------------------------------

field_gatherer = # picks the fields out of the parse tree of a record declaration

_token%TdLLXMk++ ^/~&vh+ ~&vth;+ -+.
   "o". * :^\~&rt -+
      //~&V ~&h ogl-token_forms <declaration "o">,
      ^lrNVNCC/~&rh token$[lexeme: '(pointer)'!,semantics: !+ !+ ~&l]+-,
   ! ~&itB?\<'not enough fields'>!% (^p\~& ~&liNXSPrNiXSPT:-<&>+ <&>!*)+ * ~&rtttPBiB|| take/3+ ~&rlT,
   ! ~&iiiNCCClrVO(token[lexeme: '(null type or initializer)',semantics: 0!!],<>)-*+ rlc not ~&r; -&
      not ~&v!| ~&d.semantics,
      ~&d.lexeme; ~&h~=`_&& all \/-= :/`_ letters&-,
   ! ~&av&&~&ad.lexeme=='(juxtaposition)'^?\~&aNC :^/~&avh ~&favth3R+-

type_declarer = # takes the result of the field_gatherer to the parse trees of the fields and type declaration for a record

_token%TLMk++ :^\~&rhS+ -+.
   ! //~&V token[
      preprocessor: (\/? ~&\~& ~&a^& -&~&ad.lexeme=='#fix',~&av&-?/~&avz ~&adPfavPMV) -+
         all ~&i&& ~&d.lexeme-= {'(evaluated)','(imported)'},
         ~&a^& -&~&ad.lexeme=='=',~&av,~&avt,~&avttZ&-?/~&avt ~&favPML+-,
      lexeme: '#fix'],
   "o". <.
      ~&V\<>+ order+~&l; token$[
         lexeme: '(general type fixer '--+ --')'+ ~&h+ %nP,
         semantics: "l". ~&?/lifted_type_fixer! ! ! general_type_fixer "l"],   # might be used by fix_lifing
      ~&V/(~&h ogl-token_forms <declaration "o">)+ ^lrNCC(
         ~&l; *^0 ^V\~&v ||~&d ~&vZ&& ~&d; ~semantics.&Z&& lexeme:= :/`_+ ~lexeme,
         ~&V/token[lexeme: '(type builder)',semantics: ! execution\<type_constructors-B>+ ~&iNC]+ :^(
            ~&l; ^V\~&iNC token$[
               lexeme: '(initializer namer)'!,
               semantics: preprocess; !+ ~&h;+ //~&+ ~semantics^?ad\~&ad.lexeme --'(1%oi&)'+ ~&favh2R],
            ~&r; * ^(~&hvhd.lexeme,~&th); ^V\~&rNC token$[
               lexeme: '(field namer)'!,
               semantics: !+ ~&h;+ -+
                  ; -|
                     _type_constructor%TI?/~& <'ambiguous record declaration; please parenthesize'>!%,
                     ! ~&V/type_constructors-o <>|-,
                  //~&+ ~&l+-]))>+-

record_initializer = # takes the result of the field_gatherer to a parse tree for the record initializer function

-+.
   ! //~&V token[
      lexeme: '#fix',
      preprocessor:  (\/? ~&\~& ~&a^& -&~&ad.lexeme=='#fix',~&av,~&avt,~&avttZ&-?/~&avth ~&adPfavPMV) -+
         all ~&i&& ~&d.lexeme-= {'(evaluated)','(imported)'},
         ~&a^& -&~&ad.lexeme=='=',~&av,~&avt,~&avttZ&-?/~&avt ~&favPML+-],
   "o". <.
      ~&V\<>+ order+~&l; token$[
         lexeme: '(general function fixer '--+ --')'+ ~&h+ %nP,
         semantics: "l". ~&?/lifted_function_fixer! ! ! general_function_fixer "l"], # might be used by fix_lifing
      ~&V/(~&h ogl-token_forms <declaration "o">)+ ^lrNCC/~&l ~&r; -+
         //~&V token[
            semantics: ! _type_constructor%TfZWXawXLMk; ~&?^\(~&lS; !+ =>0 ^H\~&r :=0!+ ~&l) (~&?=l/~&r ~&?=r/~&l +)^(
               ~&rrr2k?\~&! ^(~&l,~&rrr?\~&NlX ~&rrr)*; glimit+ ~&at^?\~&ahr -+
                  (both -&~&rZ,~&l,~&llZ&-)?/!+~&blr both~&lZrB?\couple ~&NiX+ embedded_pointer_reduction+ ~&br,
                  ^W/~&f ~&lllPrXSPrlrPrXSPX+ ~&ll!=+ ~&a+-,
               (~&?=l/~&r ~&?=r/~&l +)^(
                  ^(~&l,~&rrl?\~&NlX +^\~&NlX ~&rrl)*; ~&at^?\~&ahr -+
                     (both -&~&rZ,~&l,~&llZ&-)?/!+~&blr both~&lZrB?\couple ~&NiX+ embedded_pointer_reduction+ ~&br,
                     ^W/~&f ~&lllPrXSPrlrPrXSPX+ ~&ll!=+ ~&a+-,
                  (~&lS; =>0 ^H\~&r :=0!+ ~&l); (lesser nleq+ weight~~)^(
                     //(~&al^?\~&ar ~&ar?\~&al ~&fabbIPW),
                     -|-&~&llrB,~&r,~&ll== ~&,~&lr&-,~&|-+ ~&a^?\~&! ~&?^\-+!,~&a+- ~&al?(
                        ~&ar?(~&W; ~&E?/fan+~&l ^^(~&l;+ ~&l,~&r;+ ~&r),^\~&r+ ~&l;+ ~&falPR),
                        ~&ar?(^/~&l+ ~&r;+ ~&farPR,~&!))))),
            lexeme: '(initializing function builder)'],
         * -+
            //~&V token[lexeme: '(quadrupler)',semantics: ~&hthPtth2ttth3XXX!],
            <.~&h,~&th,~&V/token[lexeme: '(initializer_of)',semantics: ! initializer_of+ ~&h]+ ~&thNC,~&tth>+-,
         ~&hvth3tCS+ ~&/<>; ~&lx+ ~&r-> ~&rlPlCrrPX+ ^/~&l ~&rhtX; -+
            ^/~&lr ~&llPrDrlPljrrPXS,
            ~&ar^?\~&a ~&rlPlrrPCX+ leql+~&alrhPXl?/~&arh2falrtPXPRX ~&alPfarhtX2RX+-,
         ^p\~& ^DlrcS/~&hvhd.lexeme* * ~&s+ ~&tth; *^0 -&~&v,~&d.lexeme=='-'&-?/~&vh ~/&d.lexeme &vL,
         * :^/~&h :^/~&th ~&tt; ~&iNC+ (~&V/juxtaposition+ ~&lrNCC)=>+->+-

---------------------------------------- functions in support of function declarations -------------------------------------

ovulation = # generalized parse tree evaluation that infers the order of higher order functions and optimizes them accordingly

^(~&litB+ ==optimization-~+ ~&d.postprocessors,~&); ||evaluation@r ~&l&& -+
   ~&r&& ~&drPvHo+ @lNrXX + (~~ ~&l->r+ ^/~&lt) (
      optimizing_inverse_concretion@lhPrX,
      @r ||~& ^|rrlPlCrrPXB/~& lambda_concretion; ~&i&& ^|riB/~& abstract_disassembly),
   ^|/~& disassembly+ evaluation+ &d.postprocessors:= 0!+-

fix_lifting = # transforms record parse trees to use lifted function and type fixers if possible

~&a^& -&~&d.lexeme=='#fix',~&v,~&vh&-?a\~&adPfavPMV -+
   _token%TdnWLwXXMk; -&~&lk,all_same~&i&-?rl\~&l ~&r; &rvhd:=r token$rvhd[
      semantics: !+ !+ ^H\~&lh ~&iNNXH+ ~&rvhd.semantics,        # the appropriate lifted fixer should have been stored here
      lexeme: '(lifted fixer'--+ --')'+ ~&h+ %nWP+ ~&lh],
   ~&a; ^/~& ~lexeme=='='^?ad\~&adPlSLPrSXfavPMOXrlPlrrPXX _token%TnWLwXMk+ ^rlPNClrrPVX/~&ad ~&av; _token%TLnWwXMk+ -+
      ^lrlPXrrPX(difference^/order+~&rihB ~&l,~&)^rlPlrrPCX/~&lihB ^(order+~&ihB,~&itB)+ ->l (
         ~&rNXlD; all_same -+
            %sTSMk+ ~&s+ * *^0 ^V\~&v ~&d.lexeme; '(tight application)'?=\~& '(juxtaposition)'!,
            _token%TLMk+ _token%TdsLwXwXMk; ~&ar^& (-=+ ~/&rd.lexeme &ll)?a/~&alrNC ~&fallPrivDPDlrlPXrrPXS2ML+-,
         ^\~&r ~&rlD; * _token%TMk+ ~&ar^& ||~&ard2falrvPDPMV ~&alrvPX; ~&ihB+ ~| ~&r&& -=+ ~/&rd.lexeme &l),
      ^/~& ~&ihB; *^0 ^T\~&vL ~&vZ&& ~&d; ~semantics.&Z&& ~lexeme.&iNC+-+-

-------------------------------------------------- the main declaration operators ------------------------------------------

(# The '::' operator performs record declarations by translating them into a set of ordinary declarations using the =
operator, as well as throwing in the relevant #fix directives for recursive type expressions and initializing functions and
inferring the right order, which is evident for record declarations though maybe not in general because higher order records
are expressible only as lambda abstractions. Higher order records tend to be very bloated and even more so when lambda
optimized, so lambda optimization is inhibited for the record parameters by way of the root token of the generated set of
declarations, which otherwise would just be a separation. However, they respond well to a moderate granularity of compression,
so self-extraction with a granularity of 6000 is thrown in as a postprocessor. #)

manifestation =

operator$[
   mnemonic: '::'!,
   loose: &!,
   preprocessors: mode$[
      infix: -+
         //+ fix_lifting+ ~&V/token[
            lexeme: '(lambda pessimization and compression)',
            preprocessor: (*^0 ~&vik!| ~&d.lexeme.&ihB==`")?(
               ~&a^& -&~&d.lexeme=='=',~&v&-?a\~&adPfavPMV ^V/~&ad :^/~&avh ~&avt; * ~&a^& ?a(
                  -&~&d.lexeme=='(application)',~&v,~&vt,~&vttZ&-&& ~&vh; -&~&d.lexeme=='.',~&v,~&vtZ&-,
                  ~&\~&a ^V/~&ad :^/&avhd.lexeme:=avh'(pessimal point)'! ~&favt2M),
               ~&V/separation+ ~&v; * ~&a^& -&~&d.lexeme=='=',~&v,~&vt,~&vttZ&-?a(
                  ^V/~&ad :^/~&avh ~&avth; &d.(postprocessors,lexeme):=iNC ~&d; ^(
                     ~postprocessors; :^\~&itB -+
                        //+ -!singly_branched,_type_constructor%TI!-?/~& self_extracting 6000,
                        ~&ihB|| ~&!+-,
                     ~lexeme; '(evaluated)'?=\~& ^T/~&y ' except for compression'--+ ~&zNC),
                  ~&adPfavPMV))],
         +^\field_gatherer ^lrNCT^/type_declarer record_initializer+-],
   meanings: mode[infix: <'misused :: operator'>!%]!,
   help: mode[infix: 'declares a record data structure']!,
   peer: '='!]

(# The '=' operator performs declarations and has a preprocessor that performs evaluation as well if there are no unrecognized
identifiers in the expression. The value of any expression whose root is a declaration operator should be an assignment (i.e.,
a pair) of a string and the value of the right subexpression. One function of the declaration preprocessor is therefore to
transform its left subexpression to that which evaluates to its lexeme stem. The preprocessor also transforms juxtapositions
to applications, and moves dummy variables from the left hand side to lambda abstractions on the right. The application
preprocessor disambiguates between infix '.' operators and lambda abstraction, so it isn't done by the declaration
preprocessor directly. However, the #pessimize directive and the root token of record declarations need to inhibit lambda
optimization if necessary in between preprocessing and evaluation by the declaration preprocessor, so the latter interacts
with them by preprocessing only up to evaluation, deleting all the preprocessors of its subexpressions, and sitting on them
for one iteration, after which it restores the subexpression preprocessors and continues. Pessimization works on lambda
abstractions just by changing the '.' tokens to pessimal points, which is detected by the abstract function in apt.fun. #)

declaration =

"o". operator[
   mnemonic: '=',
   loose: &,
   meanings: mode[infix: ~&A],
   preprocessors: mode[
      infix: -+
         ==?(                      # pause here for pessimization if neccessary
            ~&l; _token%TMk+ -+
               &vth:= preprocess@vth; ?(
                  ~&d.lexeme~<{'(evaluated)','(imported)'}&& *^0 -&~&,~&d.semantics,~&vig&-,
                  ~&\~& ~&dNV+ &d.((preprocessor,postprocessors),lexeme,semantics):= ~&NNXiX/'(evaluated)'+ !+ !+ ovulation),
               ^V/~&d :^\~&vt ~&vh; ?(
                  ~&v!| -!
                     ~&d.semantics&& ^EZ/~&d.semantics !+ !+ ~&d.lexeme; ~=`-~-r,
                     not ~&d.lexeme; ~=`-~-r; all \/-= :/`_ letters!-,
                  ~&/<'misused =, ::, or #import'>!% &d.semantics:= ~&d.semantics|| !+ !+ ~&d.lexeme)+-,
            _token%TMk+ ~&r; (&ld.preprocessor:=l ~&r)^/(*^0 &d.preprocessor:= 0!) -+
               "f". *^0 &d.preprocessor:= "f"+ &d.preprocessor:=d 0!,
               -:~preprocessor+ *^0 :^\~&vL ^\~&d.preprocessor &d.preprocessor:=d 0!+-),
         _token%TWMk+ ^/~& -> (
            ~&vhd; ==application"o"+ ((filename,previous),lexeme,location):= (&,&)!,
            ^V/~&d ^lrNCC/~&vhvh ^V/~&vhd :^\~&vt -+
               &d.(filename,location):= ~&vhd.(filename,location),
               @vhvt //~&V ~&h ogl-token_forms <
                  operator[ogl-mnemonic: '.',meanings: mode$[infix: ~&,postfix: ~&,solo: ~&] <'internal error'>!%]>+-),
         ^V(~&d,:^\~&vt preprocess@vh)+ *^0 ^V\~&v ||~&d -&~&v,~&d.lexeme-={'(juxtaposition)','(tight application)'}&-&& -+
            \/~&H lexeme:='(application)'! application "o",
            (filename,location):=+ !+ ~&d.(filename,location)+-+-],
   help: mode[infix: 'declares an identifier to have a value'],
   peer: '::']

#optimize-

ez_declaration = # this version performs no algebraic transformations

operator[
   mnemonic: '=',
   loose: &,
   meanings: mode[infix: ~&A],
   preprocessors: mode[
      infix: -+
         &vth:= preprocess+~&vth; ?(
            ~&d.lexeme~<{'(evaluated)','(imported)'}&& *^0 -&~&,~&d.semantics,all~&+ ~&v&-,
            ~&\~& ~&dNV+ &d.((preprocessor,postprocessors),lexeme,semantics):= ~&NNXiX/'(evaluated)'+ !+ !+ evaluation),
         ^V/~&d :^\~&vt ~&vh; (\/? ~&/<'misused ='>!% &d.semantics:= ~&d.semantics|| !+ !+ ~&d.lexeme) -!
            ~&d.semantics&& ^EZ/~&d.semantics !+ !+ ~&d.lexeme; ~&r+ ~=`-~-,
            ~&v!| not ~&d.lexeme; (~&r+ ~=`-~-); all \/-= :/`_ letters!-+-],
   help: mode[infix: 'declares an identifier to have a value'],
   peer: '::']

----------------------------------------------- the main operator table ------------------------------------------------------

#optimize+

extra_tabular = # takes a list of most operators and adds the declaration operators

:^/manifestation :^\~& declaration; preprocessors.infix:= -+
   //+ ~lexeme.&h==`_?vhd\~& <'reserved identifier usage'>!%,
   ~preprocessors.infix+-
