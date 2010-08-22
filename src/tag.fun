
#import std
#import nat
#import ext
#import opt
#import sol
#import tco

#comment -[
This module contains the stuff needed for type expressions and the
like, including printing and instance checking functions.

Copyright (C) 2007-2010 Dennis Furey]-

profile = +^(-=/'trace'?\~&l! ! guard^|/~& ^C\~&+ !,-=/'profile'?\~&! ! ^\~&r std-profile) __switches

#library+
#export+

---------------------------------------------------- data structures -------------------------------------------------------

type_constructor :: # a type expression is represented as a tree of these

mnemonic    %s    # a string of exactly one character uniquely identifying the type constructor
microcode   %fOZ  # executed while parsing an rpn sequence of type constructors as defined by the execution function below
printer     %fOZ  # returns a list of strings given a stack of type expressions and raw data; the stack starts with itself
reader      %fOZ  # optional field used only by the lexical analyzer, taking a list of strings to raw data
recognizer  %fOZ  # same calling convention as the printer, returns true iff the data are an instance of the type
precognizer %fOZ  # same as the recognizer except without checking for initialization
initializer %fOZ  # takes (<subtype initializing function...>,<type expression..>) to the root type initializing function
help        %s    # short character string to be displayed by the compiler when help is requested
arity       %n    # documentation for help, specifies the number of compile time stack operands of the constructor
target      %fOZ  # used by the microcode in type_operators to store a function value
generator   %fOZ  # takes <subtype generator...> to the root random pre-instance generator

----------------------------- functions used in the definitions of various type constructors -------------------------------

#optimize+

type_decompression = # used for printing self-describing types

"y". extract; *^ (~mnemonic=='B'?d\~& &d.generator:= ! rand_pair:- 0!)^V\~&v ~&d; ~&l?\~&r -: ~&H(
   * &m.((reader,generator),(microcode,arity),(help,target)):= (&,&,&)!,
   <'y': "y",'Q': atypical_types-Q,'h': stacking_types-h>-- type_optimization ~&L <primitive_types,unary_types,binary_types>)

filler = # takes a list of pointers to a function that fills in an argument to make it indexable by them

(=>0 ^H\~&r :=0!+ ~&l); (lesser nleq+ weight~~)^/(//(~&al^?\~&ar ~&ar?\~&al ~&fabbIPW)) ~&a^?\~&! ~&?^\-+!,~&a+- ~&al?(
   ~&ar?(~&W; ~&E?/fan+~&l ^^(~&l;+ ~&l,~&r;+ ~&r),^\~&r+ ~&l;+ ~&falPR),
   ~&ar?(^/~&l+ ~&r;+ ~&farPR,~&!))

decombination = # takes a type stack and grid data and teases out the first layer of grid nodes

_type_constructor%TLasaLXXLsaLXNLXXMk+ ~&Nlhvh2iCPNNXrhPXNCrtPXXX; ~&lZrrl2B->rlPlrrr2XX -+
   (%asaLXXL,(_type_constructor%TL,(%asaLXNXL,%saLXNL)%X)%X)%XMk,
   ^\~&r ~&l; * ^\~&r ~&l; ~&ailrYB^?\~&a -+
      ~&arlrY^?\~&al ~&arl?/~&falrlPXPRNX ~&NfalrrPXPRX,
      ^\~&WlrY ~&al?/&l! &r!+-,
   ^\~&rrl2rrr2lXX &&~&rl ~&rrlPlXPlX; ((_type_constructor%TL,%asaLXXL)%X,%saLXNL)%XMk; ~&ilrrrPSL3ZB+ ~&ar^?\~&a -&
      ~&allPrhPXlrrrPSLs4D; all indexable+~&rlrPX&& ~&llPNrXlrPHX; -&
         ~&r&& ~&rv; -&all_same weight,all %aI&-,
         ^H/~&lhd.recognizer ~&lrdPX&-,
      ^R/~&f ^\~&art ^/~&all ~&arhPlrrrPSLs4DrNrXlHXS&-,
   ^/~&rrr ~&lrlPrrl2XX; (%b,(_type_constructor%TL,%asaLXNXL)%X)%XMk; ~&lZrrPB-> ^(
      &&~&rr ~&rlrrSPD; _type_constructor%TLsaLXNXLMk; all -&
         ~&r&& ~&rv; -&all_same weight,all %aI&-,
         ^H/~&lhd.recognizer ~&lrdPX&-,
      (_type_constructor%TL,%asaLXNXL)%XMk+ ^/~&rl ~&rr; (all~&r)&& -<&l+ ~&rF+ *= <.~&lNXrlPX,~&NlXrrPX>)+-

precognizer_of = # takes a type expression to a function that recognizes instances of the subtype prior to initialization

-&~&,~&v,~&vhd.recognizer&-&& -+
   ~&l-=(~&nS primitive_types)?(
      ~&rhd; ~precognizer|| ~&NiX;+ ~recognizer,
      ~&r; "t". ~&/"t"; ^H\~& ~&lhd; ~precognizer|| ~recognizer),
   ^/~&vhd.mnemonic ~&vhPiNCC+ *^ ^V\~&v ~&d+ assign(
      &d.(((reader,initializer),(mnemonic,printer),(microcode,arity),(help,target)),recognizer,precognizer),
      ~&/(&,&,&,&)+ ~precognizer?d(~&NiX+ ~&d.precognizer,~&iNX+ ~&d.recognizer))+-

-------------------------------------------------- fixed point combinators -------------------------------------------------

type_fixer = # the fixed point combinator of type expressions, takes a function f to a type expression x such that x = f(x)

general_type_fixer 0

(# general_type_fixer is a generalization of type_fixer such that if t = "x1". ... "xn". h(t,"x1".."xn"), then t =
general_type_fixer(n) "t". "x1". ... "xn". h("t","x1".."xn"). It's needed to solve for the type expressions of mutually
dependent parameterized record declarations. #)

general_type_fixer = 

~&?(
   iota; ~&t; ^H(
      -++-+ * ! ///++ ; //+ ^H\~&r+ ~&l;,
      (-++-+ * ! ///); "n". /// refer ^(refer+~&f,~&a); ("g","h","b"). ~&H\"b" ~&iNV+ type_constructor$[
         initializer: /// /// (("b","st"),"x"). ~&H\"x" initializer_of ("h" "n" "g"/"h") "b",
         printer: /// ("b","t","d"). ^H(~&lhd.printer,~&) ((("h" "n" "g"/"h") "b"):(~&t "t"),"d"),
         recognizer: /// ("b","t","d"). ^H(~&lhd.recognizer,~&) ((("h" "n" "g"/"h") "b"):(~&t "t"),"d"),
         precognizer: /// ("b","t","d"). ^H(~&lhd; ~precognizer|| ~recognizer,~&) ((("h" "n" "g"/"h") "b"):(~&t "t"),"d"),
         generator: /// /// (("b","s"),"x"). ~&H\"x" generator_of ("h" "n" "g"/"h") "b"]),
   ! (~~; \/~&H (~&iNV+ type_constructor$[recognizer: ~&])~~ (0!,&!)); -+
      *^ &d.(microcode,help,arity):= (0,&)!,
      ~&NiX; ~&arl^& (~&arlvZ&& ~=+ ~&ar)?/~&al ^V/~&arld ^M/~&f ^D\~&arlvPrvPp ~&V/type_constructors-h+ ~&aliiNCB+-)

(# If t = "x1". ... "xn". general_type_fixer(m) "t". "y1". ... "ym". h("t","x1".."xn","y1".."ym") then t =
lifted_type_fixer(n,m) "t". "x1". ... "xn". "y1". ... "ym". h("t","x1".."xn","y1".."ym"). In some cases a source level
optimization allows a lower order of general type fixer to be used with lifting instead of the order that would otherwise be
required. #)

lifted_type_fixer = 

~&r?(
   ("n","m"). fix_lifter"n" general_type_fixer"m",
   ~&l; "n". (~~; \/~&H (~&iNV+ type_constructor$[recognizer: ~&])~~ (0!,&!)); (-++- (^;+ //+)!* iota "n") -+
      *^ &d.(microcode,help,arity):= (0,&)!,
      ~&NiX; ~&arl^& (~&arlvZ&& ~=+ ~&ar)?/~&al ^V/~&arld ^M/~&f ^D\~&arlvPrvPp ~&V/type_constructors-h+ ~&aliiNCB+-)

----------------------------------------------- printing and validation functions ------------------------------------------

short            = ^(40!,~&); ~&B->l ^\~&rt ~&l; ~&ah^?(~&at&& ~&NatPC,^/&! recur&fatPJ)
binary_reduction = "m". ~&litB?\<'type underflow at '--"m">!% ~&rhPlthPhNCCPVltt2CrtPX
parenthetic      = -!~&h==`~,-&~&w/` ,not -=(:/`_ letters)-~; @r ~&i&& ~&hzX==(`[,`])&-!-

pretty_pair =

"A". ~&t?\~&h (~&tZg&& short@hSL)?(
   ~&iNC+ ("A"--'(')--+ --')'+ mat`,+ ~&hS; ^lrNCT/~&y ~&z; ||~& -&~&,~&h==`(,~&z==`),~</`)+ ~&y,~&ty&-,
   ?(
      -&~&htZ,short@hh&-&& ~&tt!| -&short+ --+ ~&hthPXh,~&thhz-='<[{('&-,
      ~&tt?\(:^\~&tht ^T(((-|~&,! '~&'|- "A")--'/')--+ @hh parenthetic?\~& :/`(+ --')',:/` + ~&thh)) :^(
         ((-|~&,! '~&'|- "A")--'/')--+ --' ('+ @hh parenthetic?\~& :/`(+ --')',
         @t (* '   '--)^T(@y *= ^lrNCT/~&y --','+ ~&z,@z ^lrNCT/~&y --')'+ ~&z)),
      :/("A"--'(')+ (* '   '--)^T(@y *= ^lrNCT/~&y --','+ ~&z,@z ^lrNCT/~&y --')'+ ~&z)))

-------------------------------------------- random data generating functions ----------------------------------------------

rand_nat = # takes a number to a random natural number of that weight unless it's 1; not fixed size so & yields 0

~=(&)&& -&~&,~=1&-&& -+
   ~&r->l ^(~&l,predecessor+ ~&r)+ -!==1,50%~!-?r/~&NlCrX ^/~&NNXlC predecessor+ ~&r,
   ~&/<&>+ predecessor+ predecessor+-

rand_raw = # takes a number to a random datum of that weight; not fixed size so & yields 0

~=(&)&& ~&a^& 1?=a/&! 50%~?(
   ^W/~&f ~&ah?/~&attX ~&attX; ^(~&l,predecessor+~&r); 50%~?/~& ~&rlX,
   (^R/~&f predecessor+~&a); 50%~?/~&iNX ~&NiX)

rand_list "f" =

~=(&)&& ^(~&,||~& skip^\~& ~&itBitB+ length); ~&NiX; ~&rl->l -+
   (nleq^\~&rl successor+ weight+ ~&lh)?\~&ltPNrrPXX ^/~&l ^\~&rr difference^/~&rl successor+ weight+ ~&lh,
   ^\~&r :^\~&l "f"+ nleq?r/predecessor+~&rl mtwist..u_disc+ ~&rr+-

rand_rat = # takes a number to a random rational number of that weight unless it's less than 6; not fixed size so & yields 0

~=(&)&& iota4?</(0,1)! iota7?</(-1,1)! ~&\(&,0,0); ~&rl==<0>->r @l ^/~& 50%~?(~&/<0>+ predecessor,~&NiX); ^|rlPlTrrPX/~& -+
   ~&\&; (gcd@r~= 1)->r @l ^/~& -+
      rand_nat^~/difference ~&r,
      ^/~& ~&\1; -!~&r==1,^E/~&r predecessor+ ~&l!-->r @l ^/~& mtwist..u_disc+ ||1! ~&+-,
   predecessor+-

rand_str = # takes a number to a random printable character string of that weight unless it's 1, 2, or 3

~=(&)&& {0,1,2,3}?</''! ~&NiX; ~&r->l -+
   ^/~&rllPC difference^/~&lr successor+ weight+ ~&r,
   ^/~& case~&r ~&H\(take/95 skip/32 characters) ^\arc -+
      \/~&H {4: {3},5: {4},6: {5},7: {6},8: {3,7},9: {3,4},10: {3,4,5},11: {3,4,5,6}},
      *+ ^A/~&n+ arc++ (*~+ weight-=+ ~&m);+ \/~&H+-+-

rand_double "x" = 

^(~&,~&llrHX/"x"+ &!); &?=l/~&rr ~&rr?/^H(^+~&rllX,~&litB) {0,1}?<l/&! ~&ilZX; ~&/15; ->rr (
   &&~&l ^EZ\~&rll weight+ ~&rr,
   ^/~&lt ~&rl; ^/~& ^H\~&l ~&rl; "x". -+
      ^("x"+ ~&l,~&r)^\~&r -&~&,predecessor&-+ -&nleq+ ~&rlX,difference&-^/~&l weight+ ~&r,
      ^/~& "x"+ mtwist..u_disc+-)

rand_bcd =

~=(&)&& cases~& (
   ^|(~&,arc)* {
      {0,1}: {0_},
      {2,3,4}: {1_},
      {5}: {-1_,2_,10_},
      {6}: {-10_,-2_,3_,4_,20_,100_},
      {7}: {-100_,-20_,-4_,-3_,5_,6_,8_,11_,30_,40_,200_,1000_},
      {8}: {-1000_,-200_,-40_,-30_,-11_,-8_,-6_,-5_,7_,9_,12_,21_,50_,60_,80_,101_,110_,300_,400_,2000_}},
   ^(~&,(arc ~&tiNCS iota10); 50%~?/~&NiX ~&/&); -+
      ^/~&rl ^T\~&rr case(difference^|/~& weight)\0! ^|(~&,arc)* {
         7: <<7>,<9>>,
         6: <<5>,<6>,<8>>,
         5: <<3>,<4>>,
         4: <<2>>,
         3: <<1>>,
         1: <<0>>,
         2: <<0,0>>},
      (~&wZ\iota8+ difference^|/~& weight)-> ^|/~& ^|/~& ^C\~& arc iota10+-)

rand_gen = # takes a number to a general type instance of that weight or more; not fixed size so & yields 0

&?=/&! nleq/500?(500!,~&); ~&iNX; (^EZ\~&l weight+ ~&r)->r ~&l; ^/~& -+
   ~&al^& case~&ard\arc2 {
      's': rand_str+ ~&al,
      'n': rand_nat+ ~&al,
      'c': arc characters,
      'z': @al -&~&,50%~&-?(~&\<0>+ predecessor,~&\<>); ^|T/rand_nat ~&,
      'e': math..sub\10.+ mtwist..u_cont+ 20.0!,
      'L': -+
         (-&~&EZ,nleq&-^/weight+~&r ~&lall)->r ^/~&l :^\~&r ^R/~&lf ^\~&lar -+
            nleq?/~&l ~&r,
            ^/~&lalr difference^/~&lall weight+ ~&r+-,
         ^JNX/~&f ^\~&arvh ^/~&al (~&i&& ||~& predecessor)+ quotient^/~&al arc ~&t iota 10+-,
      'X': ?arvhthPX(
         -!~&rr,~&rlZ&& ~&lr; *^ ~&d=='L'!| ~&vik!-^/~& ~~ ~&a^& -!~&ad=='L'&& ~&avhd== 'b',~&adh-= 'sn',~&av&& ~&favPMik!-,
         ~&ifalitBPrvh2XPRX; ^/~&r ^R/~&lf ^\~&larvth (nleq&& difference+~&rlX; ~&i&& predecessor)^/weight+~&r ~&lal,
         ~&ifalitBPrvth3XPRX; ^\~&r ^R/~&lf ^\~&larvh (nleq&& difference+~&rlX; ~&i&& predecessor)^/weight+~&r ~&lal)},
   ^/~& refer stochasm {0.25: ~&V/'L'+ ~&RNC,0.25: ~&V/'X'+ ~&faaXWlrNCC,0.5: ~&iNCNV+ arc 'nbscez'}+-

rand_tree = # takes a pair of random data generators for the root and the leaves; variable size regardless

("d","v"). ~=(&)&& ^(||~& skip^\~& ~&itBitB+ length,~&); ~&ar^& -+
   ~&r?\-+~&iNV,"v",predecessor,~&llar+- ^V/~&lr ~&llf2llal3rXJ; ~&aar^& -+
      :^/~&r ^R/~&lf ^/~&laf ^/~&laal -+
         ~&B->r nleq?lrhPX(:^NiX\~&rt difference+~&rhPlX,^\~&rt difference+~&lrhPX),
         ^\~&larrt -&nleq+~&rlX,difference&-^/weight+~&r ~&laarh+-,
      ^/~& ~&afalrhPXPR+-,
   ^(~&,"d"+ mtwist..u_disc+ ||1! ~&al); ^/~& -+
      ~&i&& 1?=/<0>! predecessor; ^(~&,(-&~=,nleq&-?/~&l predecessor+~&r)^\~& arc iota 5); -+
         50%~?(~&,~&x)+ difference*+ ~&typ+ nleq-<+ :^NiC/~&l ^DlK8PS/iota+~&l ~&r,
         %nnLXMk^\iota+~&r &&difference nleq+ ~&rlX+-,
      -&nleq,difference+~&rlX&-^\~&lar successor+ weight+ ~&r+-+-

rand_bal = # takes a random variate generator to a function taking a weight to a list of addresses and a balanced tree

"r". ~=(&)&& (#-|~&rlPrB,~&/<&>+ "r"+ ~&l|-^/~&#) successor; ^(~&lS,=>0 ^H\~&r :=^/~&ll !+ ~&lr)+ %aoXLMk+ -+
   ~&lrrr2B->rrl %ntLnXaoXLngUXXXMk+ ^/~&lt ~&r; ~&lNlCrX; ^/~& -+
      %aoXLnXMk+ ~&NiX; -&~&rr,~&rll,nleq+~&rrhr2llPX&-->lrll2X -+
         (nleq^\~&rll sum^/weight+~&lhr ~&lhlr)?(
            ^/~&lhllPrXPtC ^\~&rr ^\~&rlr difference^/~&rll sum^/weight+~&lhr ~&lhlr,
            ~&ltPNrlr2XrrPXX),
         ^\~&rlrtPX :^\~&l ^/~&rrh "r"+ (nleq^/~&ll sum+~&lrhPXr)?r/difference+~&rllPrhr2X mtwist..u_disc+ ||1! ~&rlr+-,
      %nWanXLXMk^lrPrlPXrrPX/~& -+
         %nanXLXMk^/~&r -+
            %anXLMk+ ~&xlrlPXS+ %anoXXLMk+ =>0 :^\~&r ^/~&ll ^\~&lr difference^/weight+~&lr ~&r&& weight+ ~&rhrr,
            %axXLMk+ =>0 ~&r?\~&llXNC :^\~&r ^/~&l ^H\~&rhr :=0!+ ~&l,
            %nWMk; %aLMk+ |=hS&+ mtwist..u_path*+ ~&l; ^DlNXS\iota sum^/length mtwist..u_disc+ 8!+-,
         ^(^T/~&ll quotient+~&lrPrX,~&r)^/~& ~&r; ||~& skip^\~& ~&itBitB+ length+-+-,
   ~&NiX; ~&\(0,&); ~&/15+-

rand_pair ("x","y") = 

^(~&,^(~&l,^H\~&r ^+ ~&l)/("x","y")+ &!); &?=l/~&rrlrB ~&rrlrB?/^H(^+~&rl,~&litB) ~&ilZX; ~&/15; ->rr (
   ~&l&& ^EZ\~&rll weight+ ~&rr,
   (#%nnfOWbWXXoXXLM+ next18#) ^/~&lt ~&rl; ^/~& -?
      ~&rrl: ^H\~&l ~&rl; ("x","y"). -+
         ^(~&r,"y"+~&l)^\~&r -&~&,predecessor&-+ -&nleq+ ~&rlX,difference&-^/~&l weight+ ~&r,
         ^/~& "x"+ ~&itB+-,
      ~&rrr: ^H\~&l ~&rl; ("x","y"). -+
         ^("x"+~&l,~&r)^\~&r -&~&,predecessor&-+ -&nleq+ ~&rlX,difference&-^/~&l weight+ ~&r,
         ^/~& "y"+ ~&itB+-,
      ^H\~&l 50%~?(
         ~&rl; ("x","y"). -+
            ^("x"+ ~&l,~&r)^\~&r -&~&,predecessor&-+ -&nleq+ ~&rlX,difference&-^/~&l weight+ ~&r,
            ^/~& "y"+ mtwist..u_disc+ ||1! ~&+-,
         ~&rlrlX; ("y","x"). -+
            ^(~&r,"y"+ ~&l)^\~&r -&~&,predecessor&-+ -&nleq+ ~&rlX,difference&-^/~&l weight+ ~&r,
            ^/~& "x"+ mtwist..u_disc+ ||1! ~&+-)?-)

rand_fun = # takes a non-zero natural number to a function of that size; not fixed size so & yields 0

~=(&)&& refer case~&a(
   --<0: compare!,5: transpose!,6: weight!,7: version!> ^A(weight+ ~&h,arc)* (==+ weight~~)|= %fI*~ upto 4,
   -!nleq/25,90%~!-?a(
      -!nleq/125,90%~!-?a(
         -&~=8,3%~&-?a(
            note+ -+
               ^\rand_raw+~&ar ^R/~&f difference\7+ ~&al,
               ^J/~&f ^(difference,~&r)^/~&a successor+ mtwist..u_disc+ (nleq?/~&l ~&r)/20+ difference\8+ ~&a+-,
            -&nleq/12,3%~&-?a(
               std-profile+ -+
                  ^\rand_str+~&ar ^R/~&f difference\7+ ~&al,
                  ^J/~&f ^(difference,~&r)^/~&a sum/4+ mtwist..u_disc+ (nleq?/~&l ~&r)/80+ difference\11+ ~&a+-,
               -&nleq\100,nleq/14,5%~&-?a(
                  ~&a; choice{library,have}+ rand_str~~+ difference\13; (sum/4)^~(difference,~&r)^/~& mtwist..u_disc,
                  stochasm{
                     0.05: reduce+ -+
                        ^\rand_raw+~&ar ^R/~&f difference\4+ ~&al,
                        ^J/~&f ^(difference,~&r)^/~&a mtwist..u_disc+ (nleq?/~&l ~&r)/20+ difference\4+ ~&a+-,
                     0.05: assign+ -+
                        ^/rand_raw+~&ar ^R/~&f difference\3+ ~&al,
                        ^J/~&f ^(difference,~&r)^/~&a successor+ mtwist..u_disc+ (nleq?/~&l ~&r)/20+ difference\4+ ~&a+-,
                     0.5: -+
                        ^H/~&rm ^R/~&lf difference+ ~&laPrnPX,
                        ^/~& arc -**= {3: {refer},4: {map,filter,transfer},5: {fan,sort},7: {interact}}+-,
                     0.4: -+
                        ^H/~&rm ^W/~&lf successor^~(difference,~&r)^(~&,mtwist..u_disc)+ difference\2+ difference+~&laPrnPX,
                        ^/~& arc -**= {2: {guard,couple,compose},4: {iterate},5: {race}}+-}))),
         constant+ rand_gen+ difference\2+ ~&a),
      choice{field+ rand_raw+ predecessor+ ~&a,recur+ rand_raw+ difference\3+ ~&a,mapcur+ rand_raw+ difference\5+ ~&a}))

rand_type =

&d.((reader,help),(microcode,arity)):=(&,&)!*^+ 0!; (~&Z!| nleq/10+ *^0 successor+ sum:-0+ ~&v)-> refer stochasm{
   0.02: ~&iNV+ type_constructor$[
      mnemonic: 'y'!,
      recognizer: ! ~&r&& -&
         ~&rl; extractable&& extract; (0,_type_constructor)%dluwrXsUTMk; *^0 &&~&vig -!
            ~&dlZ&& ~&dr; -&_type_constructor%I,~mnemonic-= ~&nS atypical_types&-,
            ~&d-= :/'y' :/'h' :/'Q' ~&nS ~&L <primitive_types,unary_types,binary_types>!-,
         ^H(~&lhd.recognizer,~&)+ ^\~&rr <.^H\~&rl type_decompression+ ~&lhd>&-,
      printer: ! ^H(~&lhd.printer,~&)+ ^\~&r :^\~&l -+
         //~&V type_constructor[printer: ~printer binary_types-X,recognizer: ~recognizer binary_types-X],
         //: ~&V\<> type_constructor[printer: ~printer primitive_types-x,recognizer: &!],
         ^HNC\~&rl type_decompression+ ~&lhd+-,
      generator: -+
         "r". ! ^lrPllPrHH(~&l,-&nleq+ ~&rlX,difference&-^/~&r weight+ ~&iNH+ ~&lr)^\~& ^(generator_of,%-Y)+ "r",
         _type_constructor%TMk++ 0!;+ (~&Z!| nleq/10+ *^0 successor+ sum:-0+ ~&v)->+ refer+ ~&f+-],
   0.03: ~&iNV+ -+
      type_constructor$[mnemonic: 'u'!,generator: !+ !,printer: !+ %gP,recognizer: ! ~&E?/~&r+ !],
      choice{mtwist..u_disc+ 100!,rand_str+ mtwist..u_disc+ 100!,arc characters,50%~}+-,
   0.25: ^V\~&RNC arc ~&mS type_optimization type_validation unary_types,
   0.25: ^V\~&faaXWlrNCC arc ~&mS type_optimization binary_types,
   0.45: ~&iNV+ arc ~&mS type_optimization primitive_types}

----------------------------- useful functions for operating on type expressions -------------------------------------------

implicit_type  = ~&l; type_decompression type_constructors-y
similar_types  = ~&alrB^& -&~&aldPrdPX; ==+ ~&b.mnemonic,eql+~&abv,~&g+ ~&falvPrvPpPM&-
initializer_of = ~&ilB+ *^0 ^HrrPX(~&d.initializer|| ~&!!,^/~&vlSP :^/~&dvrhPSPV ~&v&& ~&vhrt)

type_optimization =

* -+
   &m.printer:= ~&m.printer&& profile^/~&m.printer '%'--+ --' printer'+ ~&n,
   ^A/~&n ~&m; (microcode,printer,reader,recognizer):= ~&=>+ optimization*+ <.~microcode,~printer,~reader,~recognizer>+-

type_validation =

* -+
   &m.printer:= ~&m.printer; ~&i&& "p". (~&lhv; all ~&d.printer)?/"p" <'bad type expression'>!%,
   &m.recognizer:= ~&m.recognizer; ~&i&& "r". (~&lhv; all ~&d.recognizer)?/"r" <'bad type expression'>!%+-

generator_of = # returns the whole generator if it's defined, including the initialization phase

(~&ilB&& ||~&l ~&B&& ("g","i"). (&?=r/~&l "i"+ ~&l)^/"g" ~&)+ -+
   *^& ^(
      ^lrigPBlrHB/~&dhd.generator ~&v; * ~&i&& ||~&l ~&B&& ("g","i"). (&?=r/~&l "i"+ ~&l)^/"g" ~&,
      ^llrHB/~&dhd.initializer ~&vrSPdX),
   _type_constructor%TLTMk+ ~&NiX; ~&ar^& ~&arlCPfarlCrvPDPMV+-

execution = # takes (<stack item..>,<type constructor...>) to either a function or a type expression

guard\?(-&~&,~&h; -!=]'bad',=]'type'!-&-,~&,<'bad type specification'>!) -+
   ~&i&& ~&hd.target|| -+
      *^ ^V\~&v ~&d+ &d.(reader,(microcode,arity),(help,target)):= (0,&,&)!,
      ~&t?\~&h ~&V/binary_types-X+-,
   ~&r->l ^H\~& ~&rh.microcode,
   -&~&r,~&rh.arity==2&-?\~& ^/~&l <stacking_types-d,stacking_types-l,stacking_types-w,stacking_types-r>--+ ~&r+-

