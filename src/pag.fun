
#import std
#import nat

#comment <'','generic parsing functions','Copyright (C) 2007-2010 Dennis Furey'>

#library+
#optimize+

ruleset :: # predicates on pairs of operator tokens that are true if the left has lower or equal precedence

prein   %fO # takes a prefix and an infix operator
prepost %fO # takes a prefix and a postfix operator
inpost  %fO # takes an infix and a postfix operator
inin    %fO # takes two infix operators

syntax ::  # a language syntax is described by these functions

prefix        %fO       # takes a token and returns true iff it can be used as a prefix operator
infix         %fO       # takes a token and returns true iff it can be used as an infix operator
postfix       %fO       # takes a token and returns true iff it can be used as a postfix operator
parameterless %fO       # takes an operator token and returns true iff it can be used without parameters
rules         _ruleset  # operator precedence relations
juxtaposition %fO       # returns the operator token to be inferred between a pair of separated consecutive token trees
concatenation %fO       # returns the operator token to be inferred between a pair of concatenated token trees

#optimize-

(# parser takes a syntax record to a function from a list of lists of tokens to a pair (p,t) where p is the tree of tokens
that were successfully parsed and t is the list of tokens that were not parsed due to a syntax error. At most one of them will
be non-empty. Prefix and postfix operators with equal precedence (i.e., symmetrically related with respect to the prepost
relation) are simultaneously reduced. That allows opening parentheses to be modeled as prefix operators and closing
parentheses to be modelled as postfix operators. #)

parser =

"s". (#_token%gUToXM+#) ~&?\&! -+
   ~&r?/~&NrrdPSPX ~&l; ~&i&& ~&itZBhrPNXB+ ^= -+
      ->~&hlPthrd3NhrPNCCVXttPC -&~&hllz,~&t,~&thllh&-,
      ->~&hlPthrd3tthr3hrPNCCVXttt2C -&~&hllz,~&t,~&thllth&-+-,
   ~&/<>; ^= (#_token%tLtXwgUTXLWLM+ next0#) ~&r?\~& cases~&rhll\~& {
      {<&,0,0,&>}: (#_token%tLtXwTXLWM;#) -&~&rt,~&rthll; ~&thPtth2YZ&-?(
         ^/~&l :^\~&rt ~&rh; ^\~&r ~&l; ~&/<&,0,0,0>+ ~&r,
         ^/~&l :^\~&rt ~&rh; ^\~&r ~&l; ~&/<0,0,0,&>+ ~&r),
      {<0,0,&,&>,<&,0,&,0>,<&,0,&,&>}: ~&lZlhllz4ZY?(
         ^/~&l :^\~&rt ~&rh; ^\~&r ~&l; ^\~&r &tth:=0!+ ~&l,
         ^/~&l :^\~&rt ~&rh; ^\~&r ~&l; ~&/<0,0,&,0>+ ~&r),
      {<0,&,0,0>}: (#_token%tLtXwTXLWM;#) -&~&l,~&lhllz,~&rt,~&rthllhzY&-?(~&rhPlCrtPX,~&)+ ~&l?\~& ^= -+
         ->~&lhl2lthrd4Nlhr2NCCVXltt2CrX -&~&lhllz,~&lt,~&lthllh,~&lthrd4rhrd3X; not ~rules.prein "s"&-,
         ->~&lhl2lthrd4ltthr4lhr2NCCVXlttt3CrX -&~&lhllz,~&lt,~&lthllth,~&lthrd4rhrd3X; not ~rules.inin "s"&-+-,
      {<&,&,0,0>,<0,&,0,&>,<&,&,0,&>,<0,&,&,0>,<0,&,&,&>,<&,&,&,0>,<&,&,&,&>}: ?(
         -&~&l,~&lhllz,~&rt,~&rthllhzY&-&& ~&rhlltthZ!| ~&rthlrZ&& not ~&rthlltth!| -&~&rthllth,~&rtt,~&rtthll; ~&hzY&-,
         ^/~&l :^\~&rt ~&rh; ^\~&r ~&l; ~&/<0,&,0,0>+ ~&r,
         ^/~&l :^\~&rt ~&rh; ^\~&r ~&l; ^\~&r &th:=0!+ ~&l),
      {<0,0,&,0>}: -+
         ~&lZlhllz4ZY?/~& ?(
            -&~&lt,~&lthllh,~&lthrd4rhrd3X; ~&irlXX; both ~rules.prepost "s"&-,
            ~&/~&lhl2lthrd4Nrhrd3lhr2NNCCVNCCVXltt2CrtPX ~&lhl2rhrd3lhr2NNCCVXltPCrtPX),
         (#_token%tLtXwTXLWM+#) ~&l?\~& ^= -+
            ->~&lhl2lthrd4ltthr4lhr2NCCVXlttt3CrX -&~&lhllz,~&lt,~&lthllth,~&lthrd4rhrd3X; not ~rules.inpost "s"&-,
            ->~&lhl2lthrd4Nlhr2NCCVXltt2CrX -&~&lhllz,~&lt,~&lthllh,~&lthrd4rhrd3X; not ~rules.prepost "s"&-+-+-,
      {<&,0,0,0>,<0,0,0,&>}: -&~&rhllz,~&l,~&lhllh,~&bhrd; ~&irlXX; both ~rules.prepost "s"&-?(
         ~&rhl2lhrd3Nrhr2NCCVXltPCrtPX,
         -!~&rhllz,~&rt&& ~&rthllhzY!-?\~& ~&lZlhllz4ZY?/~&rhPlCrtPX -+
            ~&r?\~&l ^/~&ll :^\~&lr ~&/(<0,&,0,0>,0)+ ~&rNV,
            ^/~& ~&rhlr?(~&bhr; ~juxtaposition "s",~&bhr; ~concatenation "s"),
            ^= -+
               ~&r?\~&l (^/~&ll :^\~&lr ~&/(<0,&,0,0>,0)+ ~&rNV); ~&lrtPX+ ^= -+
                  ->~&lhl2lthrd4Nlhr2NCCVXltt2CrX -&~&lhllz,~&lt,~&lthllh,~&lthrd4rhrd3X; not ~rules.prein "s"&-,
                  ->~&lhl2lthrd4ltthr4lhr2NCCVXlttt3CrX -&~&lhllz,~&lt,~&lthllth,~&lthrd4rhrd3X; not ~rules.inin "s"&-+-,
               ^/~& ~&rhlr?(~&bhr; ~juxtaposition "s",~&bhr; ~concatenation "s")+-+-)},
   (#_token%TtLtXwXLM+#) *= :^/~&hlNNXXrXP ~&lNXrXS+ ~&t,
   (#_token%TtLwXLLM;#) * :^(~&h; ~&lhttth3Y?\~& &lththPX:= &!,~&t)+ ^lrNCT(~&y,~&z; ~&ltththPY?\~& &lh:= 0!),
   ~&F; * * ^\~&iNV ~&iNNXNQS+ -+
      ^T/~&yiNNXBS <.^Y/~&ttthNNXB ~&hthPtth2YYZ>,
      <.~prefix "s",~infix "s",~postfix "s",~parameterless "s">+-+-
