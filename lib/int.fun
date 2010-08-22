#import std
#import nat

#comment -[
This module defines operations on signed integers. The virtual machine
representation of a non-negative integer is the same as that of the
corresponding natural number. Negative integers are represented as
the natural number equal to their absolute value with a zero bit
appended. The bit operations double, half, and odd defined in the
nat module will also work on integers in this representation.

Copyright (C) 2009,2010 Dennis Furey]-

#optimize+

gams = ~&l?/~&r @r ~&i&& --<0>
smag = ~&bbI+ ~~ ~&?\&! ~&z?/~&NNXiX ~&NyX
smad = gams+ ==?l/^|(~&l,nat-sum) ^|(~&l,nat-difference)+ nleq?r\~& ~&brlX

#library+

abs         = ~&i&& ~&xhitQx
difference  = smad@llrZXPrX+ smag
division    = smag; gams~~^|G/== nat-division
negation    = ~&i&& ~&z?\~&y --<0>
predecessor = ~&?\<&,0>! ~&z?/nat-predecessor --<0>+ nat-successor@y
product     = smag; gams^|/== nat-product
quotient    = ~&l+ division
remainder   = ~&r+ division
sgn         = ~&i&& ~&z?/1! <&,0>!
sum         = smad+ smag
successor   = ~=<&,0>&& ~&?\1! ~&z?/nat-successor --<0>+ nat-predecessor@y
zleq        = smag; ~&l==(0,&)!| ~&l~=(&,0)&& ^|E/~&l nleq
zrange      = zleq?(~&NiX,~&NNXrlXX); ^|lrrxPQ/~& @lNCrX ~&lhPrEZ->l ^|\~& ^C/successor@h ~&
