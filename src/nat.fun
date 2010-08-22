
#comment -[
This module contains some frequently used operations on natural numbers, which
are represented as lists of booleans lsb first with the msb always true.

Copyright (C) 2007-2010 Dennis Furey]-

#import std
#export+
#optimize+

#library+ # some unary operations

double           = ~&iNiCB
factorial        = ~&?\1! ^T(~&lSL,product:-0+ ~&rS)+ ~&Z-~*+ @iNC ~&h->t ~&hahPatPNatPCBNNXfatPRCqPiC
half             = ~&itB
iota             = @iNC ~&h->y ~&hahPatPNatPCBNNXfatPRCqPiC
length           = =>0 successor@r
odd              = ~&ihB
predecessor      = guard/~&ahPatNtCBPNNXfatPRCq <'natural out of range'>!
successor        = ~&a^?\1! ~&ah?/~&NfatPRC :/&+ ~&at
tenfold          = ~&i&& sum^/~&NiC <0,0,0>--

# some binary operations

choose    = ~&ar^?\1! quotient^\~&ar product^/~&al ^|R/~& predecessor~~
gcd       = ~&B?\~&Y ~&alh^?\~&arh2faltPrXPRNfabt2RCQ @a ~&ar^?\~&al ^|R/~& ^/~&r remainder
nleq      = ==!| zipp0; @x ==@h->hr ~&t
product   = ~&alrB^& sum@NfalrtPXPRCarh2alPNQX
quotient  = ~&l+ division
remainder = ~&r+ division
sum       = ~&B^?a\~&Y@a ~&alh?\~&arh2fabt2RC ~&arh?\~&NNXfabt2RC ~&NiC+ successor@fabt2R
power     = ~&ar^?\1! (~&lr?/product@llPrX ~&r)^/~&alrhPX product@falrtPXPRiiX
nrange    = nleq?(~&NiX,~&NNXrlXX); ^|lrrxPQ/~& @lNCrX ~&lhPrEZ->l ^|\~& ^C/successor@h ~&

difference =

guard(
   ~&ar^?\~&al ~&arh?\~&alh2fabt2RClrYiB ~&alh?/~&fabt2RiNiCB ^|NNXfaRC/~& ^|\~&t @t ~&ah^?/~&atPNatPCB ~&NNXfatPRC,
   <'natural out of range'>!)

division = # takes (numerator,denominator) to (quotient,remainder)

guard(
   ~&rhtY&& leql?rlX\~&NlX ^H\~&rNrNSPXlHDlSNiCK9 @NlX //=> nleq?lrrPX\~&rliNiCB2rrPX ^/~&NNXrlPC difference@rrPlX,
   <'division by zero'>!)

root = # takes (y,n) to truncated y^(1/n) using interval halving; if n=0, y must be 1

~&r?\(1?=l/1! <'zeroth root of non-unity'>!%) ~&l&& -+
   ~&rll+ ^= ^(~&,^(~&l,power)^\~&lr ~&itB+ sum@rbl); nleq?rrPlll2X/~&llPrlrr2XX ~&llPlrl2rXX,
   ^/~& (^/~&r power@rlX)~~^G/~&r ~&iNNiCCX+ --<&>+ 0!*itB+ iota+ quotient^|/length ~&+-
