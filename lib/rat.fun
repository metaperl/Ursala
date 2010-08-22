#comment -[
Here are some operations on rational numbers, represented as
(numerator,denominator) of types integer and natural,
respectively. The compiler recognizes rationals in this form as type
q, making them printable with %qP, among other things.

Copyright (C) 2007-2009 Dennis Furey]-

#import std
#import nat
#import int

#library+
#optimize+

abs        = ^|/int-abs ~&
difference = sum^|/~& negation
inverse    = ^\int-abs@l (-1?=l/int-negation@r ~&r)^/int-sgn@l ~&r
negation   = ^|/int-negation ~&
quotient   = product^|/~& inverse
product    = int-quotient^~brlXPlrGO(gcd^|/int-abs ~&,~&)+ @bbI ^|/int-product nat-product
sum        = int-quotient^~brlXPlrGO(gcd^|/int-abs ~&,~&)+ ^\nat-product@br int-sum+ int-product~~llPrrPXlrPrlPXX
rleq       = ^(int-sgn~~bl,~&); ~&l-={(0,1),(-1,0),(-1,1),(0,0)}!| ==@l&& zleq+ int-product~~rllPrrPXlrPrlPXX
simplified = (==?l/~&r @r ^|\~& ~&i&& --<0>)^/int-sgn~~ int-abs~~; int-quotient^~brlXPlrGO/gcd ~&

power = # returns a^b for rational a and b if the result is rational, () otherwise

(int-sgn== -1)^?arl/(^|R(~&,^|/~& abs); ~&i&& inverse) @a -!sgn@ll~=-1,odd@rr!-&& -+
   ~&r&& ~&l?(negation@r,~&r); int-quotient^~brlXPlrGO/gcd ~&,
   ^/-&sgn@ll==-1,odd@rl&- abs~~; (both ^E/~&ll nat-power@rlrPX)&&~&br+ (@rlX ^/~& root)^~G/~&rr ~~rlPlG nat-power@rlX+-

#library-

smag = int-sgn==-1?l\~&NiX ~&NNX+ abs

#library+

fixed = 

"n". smag; ~&rlZrB?/<'0.'--(`0!* iota "n")>! :\<>+ -+
   @NxX ~&/"n"; -+^T/(~&rrx||'0'!) :/`.+ ~&rl,~&l-> ^|/predecessor ~&r?/~&rhPlCrrPX ~&\''+ @l ~&/`0+-,
   ~&h+ %nP+ nat-quotient^\~&rr @rl ~&/"n"; ~&r+ ~&l-> ^|/predecessor tenfold+-

scientific = # takes a number to a rational printer in scientific notation with that number of decimal places

successor; "n". smag; ~&rlZrB?/<'0.'--(~&itB `0!* iota "n")--'e+0'>! :\<>+ -+
   ^T(^T/~&rll :/`.+ ~&rlr,^T\-+~&t?/~& :/`0,~&h,%nP,~&rrPlY+- ~&rr?/'e-'! 'e+'!),
   (->~&lrllryPXPrXPX ~&rlr; //leql 0!* iota "n")+ ~&rllPllt2B-> ^/successor+~&l ~&rllyPlzPrCXPrX,
   ~&l-> ^/predecessor+~&l ~&r; ~&llPllt2B?/~&llyPlzPrCXPrX ^/~&l successor+~&r,
   ^(~&l,~&r; ~&\0+ ~&lrtPX+ ~=`.-~)^/~&lr ~&NllPrXX; ~&rlZrB?/<'0.'--(`0!* iota "n")>! -+
      @NxX ~&/"n"; -+^T/(~&rrx||'0'!) :/`.+ ~&rl,~&l-> ^|/predecessor ~&r?/~&rhPlCrrPX ~&\''+ @l ~&/`0+-,
      ~&h+ %nP+ nat-quotient^\~&rr @rl ~&/"n"; ~&r+ ~&l-> ^|/predecessor tenfold+-,
   ~&r; ^\~&r ~&l+ (leql+~&llPrX-> ^\~&r ^/tenfold+~&ll successor+~&lr)^/~&lNX ~&r; //-- iota double double successor "n"+-

engineering = # takes a number to a rational printer in engineering notation with that number of decimal places

iota2?<(2!,~&); scientific; //+ :^\~&t @h -+
   ^T(^T/~&ll :/`.+ ~&lr,^T\-+~&t?/~& :/`0,~&h,%nP,~&rr+- :/`e+ ~&rl|| '+'!),
   (remainder\3+ ~&rr)-> ^\^(~&rl,~&rl?/successor@rr predecessor@rr) @l ~&r?/~&lrhPNCTrtPX ^\~&r --'0'+ ~&l,
   ~=`e~-; ^/(~&lrtPX+ ~=`.-~+ ~&ly) @r ^|(~&,%np+~&iNC)+ `-?=h/~&hNCtX ~&NtX+-
