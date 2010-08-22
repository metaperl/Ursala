
#import std
#import nat
#import opt

#comment -[
This module contains functions used for solving systems of mutually recursive
definitions of functions or anything else.

Copyright (C) 2007-2010 Dennis Furey]-

fixable = {'mapcur','iterate','assign'}

#optimize+
#library+

--------------------------------------------- fixed point combinators ------------------------------------------------------

(# function_fixer takes a second order function h to a first order function f such that (h f) x = f x for all x. It can be
used for solving any functional recurrence equations, and is used in particular by the compiler for solving for record
initializer functions in systems of mutually dependent record declarations. The minimal implementation needed to avoid using
the extensional method in most non-pathological instances could exclude specific transformations for the map, fan, filter,
reduce, and sort combinators, allowing them to be rewritten instead as is currently done with the fixable combinators noted
above.  Alternatively, the quality of generated code could be improved by defining a transformation for the case of each
remaining fixable combinator noted above rather than rewriting them, although there is reason to believe it's impossible
for iterate and inefficient for mapcur. #)

function_fixer =

||extensional_function_fixer -+
   ~&i&& ~&rrhPB|| @l -&~&,refer&-+ @NiX %tLsoXTXCRk refer cases~&ardl\0! {
      {'refer'}: ^rigPlrHB/~&ardr ~&faNlCrvPDPM,
      {'couple','conditional'}: ^rigPlrHB/~&ardr ~&falrvPDPM,
      {'map'}: ~&alZ&& (~&i&& @D)^rigPlrHB/~&ardr ~&falrvPDPM,
      {'fan'}: ~&alZ&& (~&i&& @G)^rigPlrHB/~&ardr ~&falrvPDPM,
      {'filter'}: ~&alZ&& (~&i&& ~&aS++ @D)^rigPlrHB/~&ardr ~&falrvPDPM,
      {'reduce'}: -+
         ~&ilB&& ("f","k"). @D ~&a+ :-((),"k") ^/~&lf "f"@lfPlaPraPXJ,
         -&~&alZ,~&arv,~&arvt,~&arvttZ,~&arvthdrPvigPBo,~&falrvh2XPRarvth4K6X&-+-,
      {'sort'}: -&~&alZ,~&arv,~&arvtZ,~&falrvh2XPR&-; ~&i&& "p". ~&aS+ @D sort "p"@lfPlaPraPXJ,
      {''}: ~&ardr?(+^/~&arK6 @al ~+ --<0,0>+ <1,0>!*=,@al recur+ ~&?\&! ^/--<&> --<0,0>+ <1,0>!*=),
      {'note','profile','guard'}: ~&arv&& ~&arvtdrPvigPBog&& ^rigPlrHB/~&ardr ~&falrvh2XPRarvtiK6S4C,
      {'compose'}: ~&arvt?\~&falrvh2XPR (~&B&& +)^/~&faNrvh2XPR (~&r&& ^)^\~&falrdvtPVPXPR ~+ --<&>@al,
      {'recur'}: ~&ardrPvigPBo&& ~&arvitZB&& recur+ ~&l?(~&rfNfaXXJ,~&rNfXfNaXXJ)^/~&al split_p@arvhK6},
   @iNX ^= ~&r?/~& @l ^(^|V/~& * ||~&l @r ~&i&& ~&NiXNV+ !@h,~&dl~='recur'&& ~&drPvrgPB&& ~&drPvrhPSPHNC)*^; ^|\~& -+
      *^ ||~& ~&v&& -+
         ~&B&& ==^?a/~&al (~&B&& ==@bd&& eql@bv)?a\~&arK6NH ^V/~&ald ^|M/~& ~&p@bv,
         @dlPvX ^|H(~~lSrSX+ ~&=>;+ %fI++ -:0!! ~&n-=fixable*~ -|%QI,~&|- com,* ^/&! !)+-,
      ~&a^& -&~&dl=='refer',~&drPvigPBo&-?a\~&adPfavPMV ~&NiXNV+ !@aK6+-,
   ~~; (\/~&H (~&,&!)); %fI~~; ==^?a/~&al (~&B&& ==@bd&& eql@bv)?a\~&NNXNV ^V/~&ald ^|M/~& ~&p@bv+-

extensional_function_fixer "h" = refer ^H("h"+ refer+ ~&f,~&a) # naive implementation of a function fixer

---------------------------------------- generalized fixed point combinators -----------------------------------------------

(# general_function_fixer is a generalization of function_fixer such that if f = "x1". ... "xn". h(f,"x1".."xn"), then f =
general_function_fixer(n) "f". "x1". ... "xn". h("f","x1".."xn"). This function is needed to solve for the initializing
functions of mutually dependent parameterized record declarations. It reverts to function_fixer for an argument of n equal to
0 but otherwise works by constructing a generalization of the extensional function fixer above. I.e.,

general_function_fixer 1 = "h". /// refer ^H(^H("h"+ ///+ refer+ ~&f,~&al),~&ar)
general_function_fixer 2 = "h". /// /// refer ^H(^H(^H("h"+ ///+ ///+ refer+ ~&f,~&all),~&alr),~&ar)

and so on. /// works like a curry combinator, in that ((/// f) x) y = f(x,y). A generalization of the intensional form would
give better results but hasn't been worth developing because it would be very difficult and rarely used. #)

general_function_fixer =

~&?\function_fixer! iota; +^(~&l,+^/~&r ;+ ~&f;+ ~&l)^/-+refer;,-++-,* ! ///+- -+-++-,/*/\ ^H,~&iNX|\NNiXXS,--<&>,&r!*+-

(# If f = "x1". ... "xn". general_function_fixer(m) "f". "y1". ... "ym". h("f","x1".."xn","y1".."ym") then f =
lifted_function_fixer(n,m) "f". "x1". ... "xn". "y1". ... "ym". h("f","x1".."xn","y1".."ym"). In some cases a source level
optimization allows a lower order of general function fixer to be used with lifting instead of the order that would otherwise
be required. #)

lifted_function_fixer("n","m") = fix_lifter"n" general_function_fixer"m"

(# fix_lifter takes n to a function taking a general fixer of order m to a lifted fixer of order (n,m) as defined above. It
performs the transformations

fix_lifter0 = ~&
fix_lifter1 = "g". "h". "x1". "g" "f". ("h" "f") "x1",
fix_lifter2 = "g". "h". "x1". "x2". "g" "f". (("h" "f") "x1") "x2",
fix_lifter3 = "g". "h". "x1". "x2". "x3". "g" "f". ((("h" "f") "x1") "x2") "x3"
fix_lifter4 = "g". "h". "x1". "x2". "x3". "x4". "g" "f". (((("h" "f") "x1") "x2") "x3") "x4"
...

#)

fix_lifter =

~&?\~&! 1?=(
   ! "g". "h". "x1". "g" "f". ("h" "f") "x1",
   iota; ;;++ -++-+ -++-*+ :^/(~&t+ * ! //+;) ^rlNCC/(* ! //+) (+)^*p(
      //+|\+ * ! //+ ; \/~&H,
      ~&x+ :/~&+ ~&t; (+)^*lxPrp(//+|\+ * ! ;;+,:/~&+ -++-*+ //+|\txiNCShiCK9+ * ! //+;)))

-------------------------------------------- functions to solve recurrences ------------------------------------------------

(# solution takes a fixed point combinator h to a function solving a system of recurrences. The recurrences can be over any
semantic domain for which a fixed point combinator can be specified. For a given semantic domain T, such as type expressions,
a fixed point combinator is a function that takes a continuous function f from T into T as an argument and returns an element
t of T such that either t = f(t), or at least t is equivalent to f(t) in some sense. An example of a fixed point combinator on
the semantic domain of functions is function_fixer defined above. f can be envisioned as a function that plugs its argument
into a known expression and then evaluates the expression. The recurrences are equations of the form x = f(x), and their
solutions are therefore fixed points of the fs.  The solution algorithm also handles more complicated cases like x = f(x,y)
and y = g(x,y), obtaining y = h g/x and its generalizations. The calling convention is that the argument to solution(h) should
be a list of pairs whose left side is an identifier (normally a character string) and whose right side is an expression tree
of type %sfZXT. The strings in the tree are identifiers of other trees in the list, and the functions are that which will
evaluate a tree given a list of values of its subtrees as an argument. I.e., ~&drPvHo will evaluate a whole tree if every node
in it has a function. Nodes with identifiers of other trees in them need not contain a function and vice versa. The result
returned by solution(h) will be a list of pairs whose left sides are identifiers and whose right sides are fully evaluated
trees consistent with the input (i.e., elements of the semantic domain of interest). #)

solution = general_solution++ //~&DrnPlrmPXAS

(# general solution is a generalization of the solution function allowing each equation in the system to nominate its own
fixed point combinator, which would be necessary for example in a system of equations in which some of the unknowns are
functions and some are type expressions, or if functions are of different orders and therefore require different degrees of
the general_function_fixer form. The input is of the form %fsfZXTXm, where the ~&ml of each equation is its fixed point
combinator and ~&mr is the expression tree as above. For example, the following invocation will solve for the triangular
successor and predecessor functions (cf. contrib/tri.fun).

hp("s","p") = &?=/0! ~&l?/^|("p","s") ~&\0+ "p"@r
hs("s","p") = ~&?\&! ~&r?/^|("s","p") ~&/0+ "s"@l

system =

%fmMk general_solution <
   's': ~&/general_function_fixer0 ~&V/('',hs+~&hthPX) <~&V/('s',0) <>,~&V/('p',0) <>>,
   'p': ~&/general_function_fixer0 ~&V/('',hp+~&hthPX) <~&V/('s',0) <>,~&V/('p',0) <>>>

Some optimization is included for constant folding and factoring out common subexpressions to prevent exponential sized trees,
to make it practical for use in the compiler (cf. xfm.fun). #)

general_solution =

(~&nNCmrdlPvLPCo2iFs2Eg&& * ^|A/~& fixation)+ (* &mr:= @mr *^ ^|V\~& ~&r?/~&NrX ~&lNX); glimit %fOsfOZXTXmMk; -+
   %fOsfOZXTXmsSXMk; ~&r?\~&l -+
      * %sfOZXTmsfOsfOZXTXAXMk; -+
         ^|A/~& ^|/~& -+
            |=tk&?FdrZlBPvLPCoO\~& %sfOZXTMk; -+
               %sfOZXTMk^V\~&llNXNVS ~&/''+ ^|(-:,~&); ~&ardr^?\~&alrdl2H +^/~&ardr gang@falrvPDPM,
               %sfXLsfOZXTXMk^\~& ~&NlCrX|\rNlXXS+ &h-*+ ~&FdlPvLPCoOs+-,
            %sfOZXTMk+ ~&rlY+ *^ ^/~&dvrlYSPV -&~&dr,~&virgB,~&NiXNV+ !+ %sfOZXsfOZXTWLXCk ~&drPvrSPH&-+-,
         %sfOsfOZXTXAMk^H\~&l @r //=> ~&EbnPO?/~&r ^A/~&rn ^/~&rml @lrmr2X ~&alnPrdl2E^?/~&alm ~&ard2falrvPDPMV+-,
      ^D\~&l gint~&lnPrE; %sfOZXTmMk+ * -+
         ^A/~&rn ^V\~&llS ~&/''+ ^H\~& @rml "fix". -+
            "h". "v". quick_fix/"fix" "h" "v",
            ~&ardr^?\~&alrH @ard2falrvPDPMX couple^|/! gang,
            %fOsfOZXTXMk^\~&rmr -:+ %sfOZXTfXLMk+ :^(@rnNXNV ^/~& !,@l * ^|/~& "f". !+ ^:0@NiX+ "f")+-,
         %sfOZXTfXLsfOsfOZXTXAXMk^\~& ^(~&rNXNV,~+ ~&l)*+ ~&NlCrX|\+ &h-*+ ^j\~&nNC ~&FmrdlPvLPCo2Os+-+-,
   ^/~& ^c/~&nS ~&Fs+ *= ^j\~&nNC ~&dlPvLPCo@mr+-

----------------------------------------- functions used when solving recurrences -------------------------------------------

(# fixation takes a fixed point combinator and an expression describing a function of one variable (fix,e) to the fixed point
of the function.  The expression e should be of the form %sfZXT with mnemonics on the left and semantic functions on the right
of each node. If the fixed point combinator is one of a family of general function fixers, higher order functional
optimizations are applied to the result. #)

fixation =

^(~&l,~&r; optimization+ ~&adr^?\~&! +^/~&adr gang+ ~&favPM); ?(
   ~&l-= general_function_fixer* iota 6,
   ~&\~&H optimization^H/~&l ~&r; ||~& (*^0 &&~&vig nleq\5000+ weight+ ~&d)&& -+
      ~&i&& -+
         optimization+ ~&adr^?\~&! +^/~&adr gang+ ~&favPM,
         -&~&adl=='tuple',~&av,~&avt&-^?\~&adPfavPMV (~&V/('tuple',~&hthPX)+ ~&lrNCC)=>+ ~&favPM,
         -&~&adl=='couple',~&av,~&avt&-^?\~&adPfavPMV (~&V/('couple',~&hNXthPX)+ ~&lrNCC)=>+ ~&favPM,
         -&~&adl=='compose',~&av,~&avt&-^?\~&adPfavPMV (~&V/('compose',~&hthPXNX)+ ~&lrNCC)=>+ ~&favPM+-,
      abstract_optimization+ abstract_disassembly+ \/abstract_interpretation ~&V/('f',0) <>+-)

(# quick_fix is equivalent to fixation but without the optimization, which has to be avoided in situations where the fixation
function itself ends up embedded in the result. #)

quick_fix = ^H/~&l ~&r; ~&adr^?\~&! +^/~&adr gang+ ~&favPM
