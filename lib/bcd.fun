#comment -[
This module defines operations on signed integers represented in
binary converted decimal, type %bnLX, with a boolean for the sign
which is true if it's negative, and the digits in order of increasing
significance.

Copyright (C) 2010 Dennis Furey]-

#import std
#import nat

base = 10 # this library could be recompiled with other bases, but the %v type in the language assumes base 10

# some unexported operations on unsigned bcd numbers

leq = ==!| zipp0; @x ==@h->h~&t; -: (*iiK0lrEZF ^/~& nleq) iota base
dec = <1>^?=a/0! ~&ah?(@a ^|C\~& ~&tyK25 iota base,@fatPR :/(nat-predecessor base))

inc "n" =

~&?\<"n">! ^C(
   @h (iota base)-$ rep"n"~&thNCT iota base,
   (take/"n" ~&x iota base)?<h\~&t @t ~&a^?\<1>! (nat-predecessor base)?=ah/~&NfatPRC @a ^|C\~& ~&ytK25 iota base)

mag =

~&a^&+ -+
   (^C)^(@ah+ -:+ num+ nat-remainder\*base,cases~&ah\~&fatPR+ nat-quotient\*base; num; *rFrK2 ^/~&lS @fatPR+ inc@hr),
   ~&H\(iota base)+ /*/ nat-product+-

add =

~&B^?a\~&Y@a -+
   ^C/~&all ~&alr?\~&farPR inc1@farPR,
   ^|J/~& ^\~&bt @bh ~&iiK0zyCK33thNCTxL3NSNNXyCK33xSL3pK25 iota base+-

sub = 

~&ar^?\~&al ~=<0>&&~&+ -+
   ^C/~&all ~&alr?\~&farPR dec@farPR,
   ^|J/~& ^\~&bt @bh ~&iiK0lrpzyCK33NSNNXyCK33PXbxxSL4OK25 iota base+-

qmul =

(@NiX ~&rr->l ^/add@rlrhPHPliNiCBPX ~&rlrtPX)^\~&rx -+
   case~&^\!@hr *t ^|/~& !,
   *lrsPD ^/~&r case~&r\0! ^(~&,@l+ mag)*t iota base+-

mul =

~&B&& (@NiX ~&rr->l ^/add@rlrhPHPliNiCBPX ~&rlrtPX)^\~&rx -+
   nleq/3400?l/-:@r @r case~&^\!@hr *t ^|/~& !,
   ^/weight@r *lrsPD ^/~&r case~&r\0! ^(~&,@l+ mag)*t iota base+-

div = 

leql?rlX\~&NlX ^|(@x ~&ihZB->x ~&t,~&)+ -+
   ~&l->rr ^|/nat-predecessor ^/~&lt @lNrlPCrrPXX %nLnLWXMk+ leq@lrrPX->r ^/~&l ^\sub@rrPlX @rl ^|C\~& ~&ytK25 iota base,
   %nnLnLWXXMk+ ^/nat-difference+length~~lrtPX ^/~&xrSP+zipp0@bx ~&NlX+-

pow = ~&ar^?\<1>! mul=>+ ^T/~&arhihB2lNCB ^|RiiNCC/~& ^|/~& add^|\mag5 (iota base)-$ ~&iiNCBS half* iota base

range = <'integer out of range'>!%

#optimize+
#library+

abs         = ~&NrX
bleq        = @bbI ~&l==(&,0)!| ~&l~=(0,&)&& ^|EZ/~&l leq
brange      = bleq?(~&NiX,~&NNXrlXX); ^|lrrxPQ/~& @lNCrX ~&lhPrEZ->l ^|\~& ^C/successor@h ~&
choose      = ~&Y?bl/range ~&NiX+ @br ~&ar^?\<1>! ~&l+ div^\~&ar (~&B&& qmul)^/~&al ^|R/~& dec~~
difference  = sum@lrlZrXPX
division    = @bbI ^|G/~= div
factorial   = ~&l?/range @r ~&/(<1>,<>); ~&r->NlrlTPX ^\dec@r ^(qmul@lrrPX,~&rl)^/~&ll ^rlPlTrrPX/~&lr ~&Z-~@r
fromint     = ~&?\&! ~&z?(~&NxX,~&NNXxtPX); ^|/~& @NiX ~&r->l ^\~&rt (~&l?\~&r inc1@r)^/~&rh mag2@l
gcd         = ~&B?br\~&lrPlrQ ~&r^?ar\~&al ^|R/~& ^/~&r remainder
negation    = ~&lZrX
odd         = @r ~&i&& @h ~&ihB
power       = ~&rl?/range ^/~&llPrrihB2B pow@br
predecessor = ~&r?\<&,<1>>! ^/~&l ~&l?/inc1@r dec@r
product     = leql?(~&rlX,~&); @bbI ^|/~= mul
quotient    = ~&l+ division
remainder   = ~&r+ division
sgn         = ~&r?\&! @l ~&\<1>
sum         = ==?bl/^(~&ll,add@br) @bbI ^|(~&l,sub)+ leq?r\~& ~&brlX
successor   = (&,<1>)?=/&! ^/~&l ~&l?/dec@r inc1@r
tenfold     = ~&lriNiCBPX
toint       = (~&l?\~&r @r --<0>)^|/~& @NxX ~&r->l ^\~&rt nat-sum^|/(10?=(nat-tenfold!,//nat-product) base) ~&h
