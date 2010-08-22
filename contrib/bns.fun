
#import std
#import nat

#comment -[
This module contains some fast operations on subsets of a finite
universe represented as the type %bN of boolean a-trees. E.g., a
universe {`a,`b,`c,`d} could have a subset {`b,`d} which would be
represented by the tree [2:1: true,2:3: true].

Copyright (C) 2007 Dennis Furey]-

---------------------------------------------------- conversion functions --------------------------------------------------

#library+
#optimize+

representation = union:-0++ *+ -$^/~& addresses                            # inverse semantics
rtree          = ~&iNH+ :=^|(~&:-0,:-0! ^)+ ^\!* addresses                 # takes a list to an a-tree

semantics = # takes a universe to a function that converts a %bN tree to a subset of the universe in the usual representation

~&iNX+rtree; (; \/~&H) ; ~&?\0!! ~+ --<0,0>+ ~&iNX; ~&al^?(~&ar?/~&WliNXSPrNiXSPXlrT ~&falPRiNXS,~&ar?\~&aNC ~&farPRNiXS)

leaves =  # takes a non-full a-tree to a list

~&iNC; ^= ||~& ~&YgiB+ ~&a^& ~&at?\~&ahlrlrNCClNCQrNCQ ~&ahl?\~&ahr2fatPRCtiBP ~&ahr?/~&ahl2ahr2fatPRCCttPiB ~&ahl2fatPRCtiB

----------------------------------------------------- binary operators -----------------------------------------------------

union        = ~&alParPfabbIPWalPQarPq
subtraction  = ~&alParPfabbIPWlrYiBPalPQNq
contains     = ~&alParPfabbIPWlrBPNNXQarZPq
intersecting = ~&alrEPNNXalParPfabbIPWlrYPNQNQq    # returns a boolean
intersection = ~&alrEPalPalParPfabbIPWlrYiBPNQNQq  # returns a set

----------------------------------------------- curried binary operators ---------------------------------------------------

(# These work like the corresponding binary operators but with one of the arguments fixed in advance (i.e., being invoked as
(f x) y instead of f(x,y)). If the same set is to be combined with many others, it's usually much quicker to use one of
these. #)

contains_element = ~&al^?(~&i&&+ ~&l;+ ~&falPR,~&ar?\~&! ~&i&&+ ~&r;+ ~&farPR)

contains_set = # also works on a single element

~&/&; ((&!,0!)?=r/~&l ?)^: ^/~+~&al ~&\0!+ ~&arl?(
   ~&arr?((?^/~&l ~&\0!+ ~&r)^W/~&f ^(^\~&arl dot_l+ ~&al,^\~&arr dot_r+ ~&al),^R/~&f ^\~&arl dot_l+ ~&al),
   ~&arr?\&!! ^R/~&f ^\~&arr dot_r+ ~&al)

union_with = # takes s to a function equivalent to union/s but faster

~&/&; ==?r(~&rl,?)^: ^/~+~&al ^\!+~&ar ~&arl?(
   ~&arr?(
      (both~&rZllZPB?\^ !+ ~&blr)^W/~&f ^(^\~&arl dot_l+ ~&al,^\~&arr dot_r+ ~&al),
      ^^(^R/~&f ^\~&arl dot_l+ ~&al,~+ dot_r+ ~&al)),
   ~&arr?\&!! ^^(~+ dot_l+ ~&al,^R/~&f ^\~&arr dot_r+ ~&al))

subtractor_of = # takes a tree or a single address

~&/&; ==?r(~&rl,?)^: ^/~+~&al ~&\0!+ ~&arl?(
   ~&arr?(
      (0!?=l(0!?r/0!! ^riB,0!?=r/^liB ^YiB))^W/~&f ^(^\~&arl dot_l+ ~&al,^\~&arr dot_r+ ~&al),
      (0!?=l/^riB ^YiB)^\~+dot_r+~&al ^R/~&f ^\~&arl dot_l+ ~&al),
   ~&arr?\0!! (0!?=r/^liB ^YiB)^/~+dot_l+~&al ^R/~&f ^\~&arr dot_r+ ~&al)

remover_of = # takes a single address

~&/&; ==?r(~&rl,?)^: ^/~+~&al ~&\0!+ ~&arl?(
   (0!?=l/^riB ^YiB)^\~+dot_r+~&al ^R/~&f ^\~&arl dot_l+ ~&al,
   ~&arr?\0!! (0!?=r/^liB ^YiB)^/~+dot_l+~&al ^R/~&f ^\~&arr dot_r+ ~&al)

intersection_with =

~&/&; ==?lrlPX(~&l,?)^: ^/~+~&al ~&\0!+ ~&arl?(
   ~&arr?(
      (0!?=l(0!?r/0!! ^riB,0!?=r/^liB ^YiB))^W/~&f ^(^\~&arl dot_l+ ~&al,^\~&arr dot_r+ ~&al),
      (0!?=l/~&r ^liB)^\0!! ^R/~&f ^\~&arl dot_l+ ~&al),
   ~&arr?\~+~&al (0!?=r/~&l ^riB)^/0!! ^R/~&f ^\~&arr dot_r+ ~&al)

--------------------------------------------------- other functions --------------------------------------------------------

dot_l       = ~&alPfalPRNXarPNfarPRXNNXNXQq                             # equivalent to .\&l for a singly branched argument
dot_r       = ~&alPfalPRNXarPNfarPRXNNNXXQq                             # equivalent to .\&r for a singly branched argument
cardinality = length+ ~&a^& ||&! --+ ~&W                                # takes a set in %bN form to its cardinality
addresses   = ~&rSxaahPNfatPRXfatPRNXQaaXq2S+ iol; zipp0^*D\~& 0!*+ ~&z # takes a list to a list of addresses
