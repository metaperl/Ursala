
#import std
#import nat
#import sol

#comment -[
This module contains some functions for counting with trees according
to one possible enumeration (the fastest I can think of). There is a
one to one correspondence between trees and natural numbers, but
sometimes smallish trees can have extremely large ordinals. I'm not
convinced dendriform always works (the inverse of the ordinal
function) but have never found a counterexample.

Copyright (C) 2007 Dennis Furey]-

#library+
#optimize+

# tsuc  = ~&a^?\~&aaX ~&ar?\~&NfalPRX ^/~&falPR ~&farPJ; ~&aal2fafalPJPRafarPRPXaar2fafarPJPRNXBq

#fix function_fixer

tsuc  = ~&?\&! ~&r?/^(tsuc+~&l,tpred+~&r) ~&/0+ tsuc+ ~&l
tpred = &?=/0! ~&l?/^(tpred+~&l,tsuc+~&r) ~&\0+ tpred+ ~&r

ordinal = # returns the position any tree would have in the above series

~&a^& ~&W; ^(sum,~&l); successor+ sum^\~&r ~&l; half+ product^/~& successor

dendriform = # returns the tree given the ordinal; uses newton's method to solve a quadratic recurrence

~&a^?\0! ^W/~&f predecessor+~&a; -+
   ^(~&r,nat-difference)+ ^/~&rl nat-difference+~&lrrPX,
   ^/~& ^(~&,half+ product^/~& successor)+ {0,1}?</~& ^H\(skip^\~& predecessor+ half+ length) -+
      predecessor++ ^=+ nat-difference^/~&+ quotient+,
      ^\successor+double+ nat-difference^/(product^/successor ~&)+ !+ double+-+-
