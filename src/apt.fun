
#import std
#import nat
#import lag
#import ogl
#import ops
#import lam

#comment -[
This module contains specifications for a few invisible tokens inferred
during parsing, such as application, juxtaposition, and separation.

Copyright (C) 2007-2010 Dennis Furey]-

#library+

-------------------------- source transformations applied during preprocessing of function application ----------------------

resembles = ~&d.suffix.&Z&&+ ~&d.lexeme== # will break if /,\, and (, are redefined incompatibly

smart = ~&vthd.lexeme=='##'&& ~&vh # elimination of smart comments

slash = # removal of binary to unary combinators

"o". -|
   (~&vh; -&resembles '/',~&v,~&vt,~&vttZ,all~&+ ~&v&-)&& -+
      ^V/~&rd <.~&rvhvh,^V/~&lh <.! ~&V(),^V/~&lth <.^V/~&lz <.~&rvhvth,~&rvth>>,! ~&V()>>,
      ~&/(&h.lag-suffix:=0! ogl-token_forms ~ogl-mnemonic=='('*~ "o")+-,
   (~&vh; -&resembles '\',~&v,~&vt,~&vttZ,all~&+ ~&v&-)&& -+
      ^V/~&rd <.~&rvhvh,^V/~&lh <.! ~&V(),^V/~&lth <.^V/~&lz <.~&rvth,~&rvhvth>>,! ~&V()>>,
      ~&/(&h.lag-suffix:=0! ogl-token_forms ~ogl-mnemonic=='('*~ "o")+-|-

ub = # transformation of unary operators to equivalent binary forms

"o". -|
   &&~&vhd2vth2vhvt3CV -&
      ~&vh; -&~&v,~&vt,~&vhZ,~&vth,~&vttZ,~&d.semantics.&Z&-,
      ~&vhd.lexeme-= ~&H\"o" -+
         ~ogl-mnemonic*+ *~ ~meanings; ~ogl-prefix&& ~infix,
         ~meanings*~; *~ ~dyadic; ~&i&& ~ogl-prefix+-&-,
   &&~&vhd2vhvh3vtPCV -&
      ~&vh; -&~&v,~&vt,~&vh,~&vthZ,~&vttZ,~&d.semantics.&Z&-,
      ~&vhd.lexeme-= ~&H\"o" -+
         ~ogl-mnemonic*+ *~ ~meanings; ~postfix&& ~infix,
         ~meanings*~; *~ ~dyadic; ~&i&& ~postfix+-&-,
   &&~&vhd2vthvh4vthdvtPV3NCCV -&
      -&~&vhvZ,~&vt,~&vttZ,~&vth; -&resembles '(',~&v,~&vh,~&vt&-&-,
      @vhd ~semantics.&Z&& ~lexeme-= ~&H\"o" -+
         ~ogl-mnemonic*+ *~ ~meanings; ~solo&& ~infix,
         ~meanings*~; *~ ~dyadic; ~&i&& ~solo+-&-|-

abstract = # recognition of lambda abstraction operators

(~&vh; -&~&v,~&vh,~&vtZ!| -&~&vthZ,~&vttZ&-,~&d.lexeme-={'.','(pessimal point)'}&-)&& ^H(
   &d.preprocessor:=+ !+ +^(
      ~lexeme=='.'?vhd(
         ! lambda_optimization,
         ! ~&a^& (~(lexeme,semantics)== ~&/'(lambda constant)' csem!)?ad/~&a ~&adPfavPMV; &d.postprocessors:= 0!),
      lambda_abstraction+ ~&d),
   ~&vhd2vhvh3vtPCV)

hop = # removal of unnecessary ~&H operators

&&~&dvthv3V -&
   ~&v&& @vh ~&i&& ~&d.lexeme=='~'&& @v ~&i&& @h ~&i&& ~&vZ&& @d -&
      ~lexeme== '&',
      ~lag-suffix; -&~&,~&hn=='H',~&tZ&-&-,
   @vt ~&i&& ~&tZ&& @h -&~&,~&d.lexeme=='(',~&v,~&vh,~&vt,~&vhd.lexeme~<{'.','(pessimal point)'}&-&-

scotch = # removal of unnecessary ~& operators

&&~&vth -&
   ~&v&& @vh ~&i&& ~&d.lexeme=='~'&& @v ~&i&& @h ~&i&& ~&vZ&& @d -&
      ~lexeme== '&',
      ~lag-suffix; ~&Z!| -&~&hn=='i',~&tZ&-&-,
   @vt ~&i&& ~&tZ&-

mate = # transformation of solo operators to equivalent unary and binary forms

"o". ~&vhv?(^V/~&d <.~&vh; ^H\~& ||~&! ~&d.preprocessor,~&vth>,~&); ~&vhvZ&& ~&vhd.semantics.&Z&& -|
   &&(^V/~&vhd ~&NvtPC) ~&vhd.lexeme-= ~&H\"o" ~meanings*~; ~ogl-mnemonic*+ *~ -&
      ~meanings.ogl-prefix&& ~meanings.aggregate.&Z,
      ==+ ~meanings.(solo,ogl-prefix)&-,
   &&(^V/~&vhd ~&NvtPCx) ~&vhd.lexeme-= ~&H\"o" ~meanings*~; ~ogl-mnemonic*+ *~ -&
      ~meanings.postfix&& ~meanings.aggregate.&Z,
      ==+ ~meanings.(solo,postfix)&-,
   -&
      ~&vhd.lexeme-= ~&H\"o" ~meanings*~; ~ogl-mnemonic*+ *~ -&
         ~meanings.infix&& ~meanings.aggregate.&Z,
         ==+ ~meanings.(solo,infix)&-,
      @vth @dviFPV -&resembles '(',@vh ~&i&& ~&d.lexeme== ')',@vhvh ~&i&& ~&d.lexeme== ','&-,
      ^V/~&vhd :^/(@vth @dviFPV @vhvh ~&vh) ~&iNC+ ?(
         @vth @dviFPV @vhvh @vth ~&i&& ~&d.lexeme== ',',
         ~&/(@vth @dviFPV ^V/~&d <.@vh ^V/~&d @vh <.~&vth>>) @vth @dviFPV ~&vhvhvth)&-|-

-------------------------------------------- inferrable token specifications ------------------------------------------------

(# The token representing function application is inferred by the parser where function application is indicated, as specified
in fen.fun, and is also substituted for the juxtaposition token by the preprecessor of the = operator in its right operand, as
shown in eto.fun. The token is parameterized by a list of operators because many operators are transformed by the preprocessor
of the application token depending on their particular algebraic properties, which may include not only those that are built
into the compiler but those that are added at run time. These transformations are advantageous because they make it possible
for the preprocessors and postprocessors of individual operators to be invoked where they otherwise wouldn't, which may
perform code optimization among other things. #)

application =

"o". token[
   preprocessor: -+
      @diX -+
         ==?lrdPX(
            @r -+
               ~lexeme=='.'?vhd\~& &vhd.lexeme:= '(pessimal point)'!,
               _token%TMk+ &vhd2dX.postprocessors:= ~&NiX+ ~&d.postprocessors|| ~&vhd.postprocessors.&itB+-,
            ~lexeme=='.'?rd/~&r @r ~&d.preprocessor?\~& ^H/~&d.preprocessor ~&),
         _token%dTXMk+ ^= ==?lrdPX\~& ^/~&l ~&r; -|smart,slash "o",ub "o",abstract,hop,scotch,mate "o",~&|-+-,
      (==+ ~semantics~~)?dvhd2X\~& ^V/~&d :^\~&vt @vh ^H\~& ||~&! ~&d.preprocessor,
      ^= ~lexeme=='('?vhd\~& rep2 &vh:= @vh ~&i&& ^H\~& ~&d.preprocessor|| ~&!+-,
   semantics: ~&hthPH!]

separation = # inferred between declarations

token[
   lexeme: '(separation)',
   semantics: <'unresolved separation'>!%, # because it should have been transformed out before evaluation
   preprocessor: ~&a^& ~lexeme=='(separation)'?ad\~&a ~&adPfavPMV; -+
      ~&vt?\~&vh (~&v; all ~&d.lexeme=='=')?\~& &d.semantics:= ~&!,
      ^V/~&d ~&d.lexeme~='##'*~+ ~&viF; *= -&~&v,~&d.lexeme=='(separation)'&-?/~&v ~&iNC+-]

(# juxtaposition is inferred by default between two consecutive non-operators separated by white space when there isn't enough
contextual information to distinguish between application and something else. It should usually be substituted with
application by the preprocessor of a token somewhere above it in the parse tree where the context is known. The only case when
it has a different interpretation is in a record declaration. If it hasn't been substituted or eliminated by the time it's
evaluated, an exception is thrown. #)

juxtaposition = 

token[
   lexeme: '(juxtaposition)',
   semantics: <'ambiguous juxtaposition'>!%,
   preprocessor: ||~& -&~&v,~&vt,~&vttZ,~&vth,~&vthd,~&vthd.lexeme=='##',~&vh&-]
