
#import std
#import nat
#import tag
#import psp
#import lag
#import opt

#comment -[
This module contains some miscellaneous functions needed for constructing the
the compiler's main table of operators.

Copyright (C) 2007-2010 Dennis Furey]-

#library+
#optimize+
-------------------------------------------------- data structures -----------------------------------------------------------

mode      :: prefix %sbUbLUfOU postfix %sbUbLUfOU infix %sbUbLUfOU solo %sbUbLUfOU aggregate %sbUbLUfOU

operator  ::  # specifies an operator in the language

mnemonic       %s       # the name used to invoke the operator in source code
match          %s       # right matching grouper in the case of an aggregate operator
meanings       _mode%Z  # semantic specifications
help           _mode%Z  # a one line description for each arity
preprocessors  _mode%Z  # some optional extra stuff to transform the parse tree in advance for operators that need to
optimizers     _mode%Z  # code optimizations or other additional semantics applicable only for compile time evaluation
excluder       %fOZ     # predicates indicating suppression of token suffix interpretation
options        %om      # a module of entities to be recognized by the lexer if they appear in the suffix of the operator
opthelp        %sL      # documentation of the options
dyadic         _mode%Z  # a true value means the transformation @ (a,b) to a@b is valid for an operator @
tight          %b       # indicates higher than normal precedence, used by the parser generator
loose          %b       # indicates lower than normal precedence, used by the parser generator
peer           %s       # an optional mnemonic of another operator having the same precedence, used in pru.fun

------------------------------------------- the interface between operators and tokens ---------------------------------------

(# token_forms transforms a list of operator records to a list of tokens usable by the lexical analyzer generator. The
transformation requires constructing a preprocessor for each token to disambiguate among prefix, postfix, infix, or solo forms
for overloaded operators, and composing it with the given operator specific preprocessor if any. It also requires converting
the operator meanings to a token semantics, of which the latter is always a second order function using lists but of which the
former can be a zero, first, or second order function, operating on tuples. Aggregate operators have a preprocessor supplied
that checks for the matching operator in the parse tree and deletes smart comments. The semantics is lifted by the number
of dots appearing as a suffix. A comma token is added to the list if there are any aggregate operators, which the parser
specification should include as a very low precedence right associative binary operator, whose preprocessor reports
an error if it appears outside of any aggregate operators. #)

agribusiness = # takes an aggregate operator to a list of two tokens derived from it

~meanings.((prefix,postfix),infix,solo)==(&,&)?\<.'ambiguously specified operator: '--+ ~mnemonic>!% <.
   token$[
      lexeme: ~mnemonic,
      preprocessor: "o". ~&dviFPV; ?(
         -&~&v,~&vhd.lexeme==(~match "o")&-,
         ~&\<'unbalanced '--(~mnemonic "o")>!% ^V(
            &d.(preprocessor,postprocessors):=d -+
               //~& -+
                  collect; ~preprocessors.aggregate||~&! "o",
                  &d.semantics:= (~&/(~meanings.aggregate "o")+ 0!*+ ~&v); ("f","v"). -+.
                     ~&/"f"; ~&l+ ~&r-> ^\~&rt //++ ~&l,
                     ~&H\((~)* ~&NiC|\ &h!* "v")+ =>+ ^bl(
                        ~&/^; ~&r-> ^\~&rt ~&l; //+; ^;,
                        ~&/0!; ~&r-> ^\~&rt !+ ~&l)+-+-,
               --(~optimizers.aggregate "o")+ optimization!*+ ~&d.lag-suffix+-,
            ~&vhvihB; ~&d.lexeme~='##'*~+ ~&a^& ~lexeme==','?ad/~&avh2favth3RC ~&aNC)),
      lag-suffix: <'.': 0>!],
   token$[
      lexeme: ~match|| <.'matching operator not defined for '--+ ~mnemonic>%,
      preprocessor: ~match; "m". <'unbalanced '--"m">!%,
      semantics: ~&h!!]>

collect = # gets rid of subtree postprocessors that coincide with those of their parents

~&dviFPV; ~&a^& -&~&ad.postprocessors.&ihB,^w/~&ad.postprocessors.&h ~&d.postprocessors.&ihB*+ ~&aviF&-?\~&a ^V/~&ad -+
   * ~&r+ ^E(~&l,~&r; ~&i&& ~&d.postprocessors.&ihB)?\~& &rd.postprocessors:= ~&NtC+ ~&rd.postprocessors,
   ^D/~&ad.postprocessors.&h ~&favPM+-

disambiguation_to = # takes a mode type to a function taking an operator to a preprocessor

^H(~&d.preprocessor,~&)+++ &d.((postprocessors,preprocessor),semantics):=++ <solo,prefix,postfix,infix>-$ (* !+) <
   ^(^/~optimizers.solo ~preprocessors.solo||~&!,~&l?(!++ ~&r,!+ !+ ~&r)+ ~/options meanings.solo),
   ^(^/~optimizers.prefix collect;+ ~preprocessors.prefix||~&!,~&l?(~&h;++ ~&r,!+ ~&h;+ ~&r)+ ~/options meanings.prefix),
   ^(^/~optimizers.postfix collect;+ ~preprocessors.postfix||~&!,~&l?(~&h;++ ~&r,!+ ~&h;+ ~&r)+ ~/options meanings.postfix),
   ^(^/~optimizers.infix collect;+ ~preprocessors.infix||~&!,~&l?(~&hthPX;++ ~&r,!+ ~&hthPX;+ ~&r)+ ~/options meanings.infix)>

token_forms = # takes a list of operators to a list of tokens usable by the lexical analyzer generator

~meanings*~; -+
   ^T(
      *= ~meanings.aggregate?/agribusiness ~&iNC+ token$[
         lexeme: ~mnemonic,
         lag-suffix: ~options,
         exclusions: ~excluder,
         preprocessor: case(~&bbiNNXNQ+ ~meanings.((prefix,infix),(postfix,solo)))\<.'invalid operator: '--+ ~mnemonic>% {
            ((0,0),(0,&)): disambiguation_to solo,
            ((0,&),(0,0)): disambiguation_to infix,
            ((&,0),(0,0)): disambiguation_to prefix,
            ((0,0),(&,0)): disambiguation_to postfix,
            ((0,&),(0,&)): ~&v?^(disambiguation_to infix,disambiguation_to solo),
            ((&,0),(0,&)): ~&v?^(disambiguation_to prefix,disambiguation_to solo),
            ((0,0),(&,&)): ~&v?^(disambiguation_to postfix,disambiguation_to solo),
            ((&,&),(0,0)): ~&vh?^(disambiguation_to infix,disambiguation_to prefix),
            ((&,0),(&,0)): ~&vh?^(disambiguation_to postfix,disambiguation_to prefix),
            ((0,&),(&,0)): ~&vtihB?^(disambiguation_to infix,disambiguation_to postfix),
            ((&,&),(0,&)): ~&v?^(~&vh?^(disambiguation_to infix,disambiguation_to prefix),disambiguation_to solo),
            ((&,0),(&,&)): ~&v?^(~&vh?^(disambiguation_to postfix,disambiguation_to prefix),disambiguation_to solo),
            ((0,&),(&,&)): ~&v?^(~&vtihB?^(disambiguation_to infix,disambiguation_to postfix),disambiguation_to solo),
            ((&,&),(&,0)): ~&vh?^(~&vtihB?^(disambiguation_to infix,disambiguation_to postfix),disambiguation_to prefix),
            ((&,&),(&,&)): ~&v?^(
               ~&vh?^(~&vtihB?^(disambiguation_to infix,disambiguation_to postfix),disambiguation_to prefix),
               disambiguation_to solo)}],
      any~meanings.aggregate&& ! ~&iNC token[lexeme: ',',semantics: <'misplaced comma'>!%]),
   * (optimizers,preprocessors):= ^/-|~optimizers,! mode[]|- ~preprocessors|| ! mode[]+-

-------------------------- some functions for tree transformations needed by pseudo pointers --------------------------------

propagation = # modifies a tree of tokens representing a pseudo-pointer to make it evaluate to a pair (pointer,function)

preprocess; ~&a^& -|
   -&~&ad.lexeme=='&',~&avZ,~&a; &d.semantics:= !+ !+ psp-percolation+ ~&mS+ ~&d.lag-suffix&-,
   -&~&ad.lexeme==':',~&av,~&avt,~&avttZ&-&& ~&adPfavPMV; &d.semantics:= ! ! ~&lrZYg?(
      ~&iNX+ ~&lS; ~&hthPX,
      ~&NiX+ couple+ ~&hthPX+ * ~&lNlXBrY),
   -&~&ad.lexeme-={'.','(pessimal point)'},~&av,~&avt,~&avttZ&-&& ~&adPfavPMV; &d.semantics:= ! ! ~&lrZYg?(
      ~&iNX+ ~&lS; :-0 ~&al^& ~&allrY?\~&ar ~&fallPrXlrPrXXPW,
      ~&NiX+ -++-+ ~&x+ * ~&lNlXBrY),
   -&~&ad.lexeme=='(',~&av&-&& ~&avhtZB?/~&favh2R ~&adPfavPMV; &d.(preprocessor,semantics):= ~&NiX+ ! ! ~&lrZYg?(
      ~&iNX+ ~&=>+ ~&lS,
      ~&NiX+ couple=>+ * ~&lNlXBrY),
   ~&aNC; -+
      &d.(filename,location):= ~&vhd.(filename,location),
      //~&V token[lexeme: '(propagation)',previous: <>,semantics: ! ~&hNX]+-|-

-------------------------------- functions needed for miscellaneous operator semantics ---------------------------------------

triangle    = ~&a^&+ :^/~&ah+ ~&fatPR;+ *
partition   = (//?+ ~&alrhh2X;); (~&x++ =>{}+ ~&ar^?\~&alNCNC)+ ~&H\(~&alrhPCrtPC,:^/~&arh ~&falrtPXPR)
concom      = ~&NiX;+ ~&r->l+ ^\~&rt+ ~&rhPlX;+ ^lrlL2CrrPC/~&l+ *|+ -*;+ any
limit       = ~&ZiX;+ ~&l++ ~&EZ->+ ~&r;+ ^/~&
glimit      = "f". ~&iNC; ~&h+ ~&htwZ-> ^("f"+ ~&h,~&); :^/~&l ^(weight+~&l,~&r); ~| nleq^\~&l weight+ ~&r
minimum     = ~&at^?\~&ah+ ~&ahthPX;; \/? ~&/~&fahttPCPR ~&fatPR
maximum     = ~&at^?\~&ah+ ~&ahthPX;; \/? ~&\~&fahttPCPR ~&fatPR
bipartition = "p". ~&a^?\~&NNX "p"?ah/~&ahPfatPRXlrlPCrrPX ~&ahPfatPRXrlPlrrPCX
dipart      = "p". ~&ar^?\&! "p"?alrhPX/~&arh2falrtPXPRXlrlPCrrPX ~&arh2falrtPXPRXrlPlrrPCX

dollar = # meaning of the $ combinator

"i". (("r","e","d"). ~&?\"e"! "r"++ "d")+ ^/~& ~&H\0; ^/~& -+
   "a". -+
      ~&at^?\~&ahr ^^W/~&f ~&lllPrXSPrlrPrXSPX+ ~&ll!=+ ~&a,
      "a"*-; * ^/~&l -|~&ar^& ~&all?/~&fabl2R ~&alr?/~&fabr2R ~&ar,~&riNXB\"i"+ ~&NlX,! ! 0|-+-,
   ~&a^?\<&>! ~&W; ^|T(*-0,0-*)+-

----------------------------------------------------- reification functions -------------------------------------------------

#library-

# breadth first search for a deconstructor on a dataset satisfying a given criterion

bfs = ufs/<~&l,~&r>
ufs = ("s","p"). ~&/"s"; "p"->lihB ^\~&r ^T\~&lt ^|H(all@h,~&)&& @lh ~&a^& ~&Y?a\<&l,&r>! ~&liNXSPrNiXSPT@W

#library+

(# Each of these functions takes a list of <(input: output)..> to a logarithmic time function mapping inputs to respective
outputs.  A list with non-unique inputs may cause an exception. An empty list doesn't cause an exception but maps to a
function that will cause an exception if it's evaluated. #)

easy_map = # fast compilation

~&?\<'unmapped'>!%! ~&mK1^?a/!@ahm -+
   ~&r?\<'bad map'>!% ?^|(~&,~&W)^/~&r ^J/~&lf ^H\~&la !=+ @n@r,
   ^/~& @anS ufs/<~&> ^|H\~& all_same+ ~&iNNXB+@h+-

fast_map = # slightly slower compilation, but maybe faster run time by incorporating compositions

~&?\<'unmapped'>!%! ~&mK1^?a/!@ahm ~&ng?a(
   (^/~& @anS bfs ~&l&& ^|HiK2tk\~& *@h); ~&r?(
      -+
         (@l ~&lrZB&& @l ~&B&& @r ~&lZrB)?\(+) +^/~&lll @rllrr3X ~&ll^?a/~&fallPrXPRNX ~&lr?a/~&NfalrPrXPRX ~&ar,
         ^\~&r ^R/~&lf ^H\~&la @r *+ ^|A\~&+-,
      @l -+
         ~&r?\<'bad map'>!% ?^|(~&,~&W)^/~&r ^J/~&lf ^H\~&la !=+ @n@r,
         ^/~& @anS bfs ^|H\~& all_same+ ~&iNNXB+@h+-),
   @fanK20PJ ~&?^/~&falPR !@arhm)

small_map = # very costly or impractical compilation, but smallest code size

~&?\<'unmapped'>!%! ~&mk^?a\0!! ~&Eg?a/~&! (nleq+ weight~~)$-+ ^T/(~&amK1&& <.!@ahm>) ^T/(~&amg&& <.^^|W/~& ~&lSrSX@nmGS>) -+
   ^|T/(*= (~&l&& <.~&?=l/~&r +>)^\~&r ^R/~&lf ^H\~&la @r *+ ^|A\~&) *= -+
      ~&B@r&& ~&iNC+ ||(?) (@r both ~&r&& @l ~&i&& ~&lrZB)&& ~&E?rbll(^^/~&rlll ?^|/~& ~&br,~&E@rbr&& ^^\~&rlr ?^|/~& ~&bll),
      ^/~&r ^W/~&lf ^H\~&la !=+ @n@r+-,
   -*^~G/~& @anS -+
      ^/(~=~&*~+ ~| ^HiK2tkZ\~&l *@r) ~| ^HZ\~&l all_same+ ~&iNNXB+@r,
      ^/~& (~)*+ @alrBPfabbIPWNqK21 ~&a^?\<&>! ~&WliNXSPrNiXSPT+-+-

(# bitmaps are possibly more efficient reifications applicable when the inputs are naturals or bit strings, or at least are
mutually distinguishable when treated as such, and no input is a prefix of any other input that maps to a different
output. Bitmaps aren't currently used by the reification operators. #)

bitmap =

~&i&& @niNNXBSPmAS -+
   ~&aingB^& ~&mK1?a/!@ahm ~&nhPK1?a(@fantPmASPR ~&i&& @t,@fanhPK20PW ~&B&& ~&h?),
   *=mK2 ^DrlXS/~&hm @nSs eql|=; leql-<&h; ~&a^& ^T/~&ah ^|R/~& @htD *rlXS ~&rlK4K13+-

# specialized reification applicable to inputs that are addresses

address_map = ~&?\<'unmapped'>!%! ~&t?\!@hm @nSmSX @biK21 ~;+ \/~&H+ ~&iNH+ :=^|/~& !
