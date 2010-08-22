
#comment -[
This module contains data compression and extraction functions.
Copyright (C) 2007-2010 Dennis Furey]-

#import std
#import nat

profile = +^(-=/'trace'?\~&l! ! guard^|/~& ^C\~&+ !,-=/'profile'?\~&! ! ^\~&r std-profile) __switches

#optimize+
#library+

paths = # takes (subtree,tree) and returns the paths if there are more than one

profile\'paths' -+
   ~&itB&& :-0 ~&B^?a\~&Y@a ~&fabbIPW,
   ~&alrE^?/<&>! -&not @arlX nleq+ weight~~,@falrGPW ^|T/~&iNXS ~&NiXS&-+-

trim = # takes (path,tree) and deletes subtrees at the ends of the paths

profile\'trim' ~&l?\~&r ~&Y^?al\0! ^YiB(~&all?/~&fabl2R ~&arl,~&alr?/~&fabr2R ~&arr)

(# The hash function is used to enhance performance of the heavy_common_subtrees function. It can be anything that maps
natural numbers to a finite set. A set of cardinality 8 has been found to give optimal results in the examples tested (i.e.,
better than higher or lower cardinalities), being slightly more than twice as fast as the analogous algorithm without
hashing. The precise hash value is irrelevant because it is used only for comparison with other hash values. #)

hash = ~&hthPtth2XX # assumes numbers have at least three bits

(# heavy_common_subtrees takes w to a function returning shared subtrees of weight w or more in decending order by weight.
The algorithm works by breaking the input data into a list of lists of trees with the trees in each sublist having the same
weight, and the sublists ordered by decreasing weight. A version without hashing would work by selecting the duplicates from
the first sublist as part of the results to be returned. It would then split the unique items and one copy of each repeated
item in the first sublist into their respective left and right sides and insert each subree into a subsequent sublist
containing trees of the matching weight. Then it would discard the head sublist and proceed down the tail until the weights
were less than w. Hashing speeds it up by partitioning the main list into a set of lists for which the weights in each element
share a common hash value instead of having just one long list. In this way, less time is spent finding the right sublist into
which subtrees should be inserted. #)

heavy_common_subtrees =

iota4?<(4!,~&); "w". profile\'heavy_common_subtrees' ^NiNCNCX(weight,~&iNC); nleq/"w"?rhhl\0! ~&r->lx %oLnoLXLLXMk+ -+
   ^|/~& %oLnoLXLLXMk; -+
      %noLXLLMk+ ~&al^?\~&ar ^|R/~& ^/~&lt @lhPrX %noLXLLMk+ %noLXLdLXCRk ~&ar^?\~&a (==+ hash~~)?alhl2rhhl3X(
         ^C\~&art @alrhPX ~&B^?a\~&Y@a ==?abhl/~&alhl2lhr2rhr2TXPfabt2RC nleq?abhl/~&arh2falrtPXPRC ~&alh2faltPrXPRC,
         ~&arh2falrtPXPRC),
      %noLXLLWMk^|\~& -+
         ~&xS+ nleq-<&l*+ %noLXLLMk+ (==+ hash~~)|=x&l+ %noLXLMk+ |=xhlPrSXS&l+ *~ @l nleq/"w",
         %noXLMk+ ^(weight,~&)*+ ~&a^& ~&ahl2ahr2fatPRCC+-+-,
   %oLoLnoLXLLXXMk+ (^/~&rltFhS3lT @r %oLLnoLXLLXMk; ^|/~&hS ~&)^|/~& %noLXLLMk; -+
      %oLLnoLXLLXMk^\~&hitQhtPtCO |=x&@hhr,
      ~&a^& @ahPfatPRX ~&r?\~&C nleq?lhl2rhhl3X/~&rhPlrtPCC ~&C+-+-
(#
old_heavy_common_subtrees =

iota4?<(4!,~&); "w". ^NiNCNCX(weight,~&iNC); (~&rhhl; nleq/"w")?\0! ~&r->lx %oLnoLXLLXMk+ -+
   ^/~&l ~&r; %oLnoLXLLXMk; -+
      %noLXLLMk+ ~&al^?\~&ar ^R/~&f ^/~&alt ~&alhPrX; %noLXLLMk+ %noLXLdLXCRk ~&ar^?\~&a (==+ hash~~)?alhl2rhhl3X(
         :^\~&art ~&alrhPX; ~&al^?\~&ar ~&ar?\~&al ==?abhl(
            ~&alhl2lhr2rhr2TXPfabt2RC,
            nleq?abhl/~&arh2falrtPXPRC ~&alh2faltPrXPRC),
         ~&arh2falrtPXPRC),
      %noLXLLWMk^\~&r ~&l; -+
         ~&xS+ nleq-<&l*+ %noLXLLMk+ (==+ hash~~)|=x&l+ %noLXLMk+ ~&hlPrSXS+ |=x&l+ *~ nleq/"w"+ ~&l,
         %noXLMk+ ^(weight,~&)*+ ~&a^& ~&ahl2ahr2fatPRCC+-+-,
   %oLoLnoLXLLXXMk+ (^/~&rltFhS3lT ~&r; %oLLnoLXLLXMk; ^/~&lhS ~&r)^/~&l ~&r; %noLXLLMk; -+
      %oLLnoLXLLXMk^\~&hitQhtPtCO |=x&+ ~&hhr,
      ~&a^& ~&ahPfatPRX; ~&r?\~&C nleq?lhl2rhhl3X/~&rhPlrtPCC ~&C+-+-
#)

(# compress takes a natural w to a function returning a compressed version of its argument, with greater compression
achieved at a greater cost by smaller values of w #)

compress = "w". profile\'compress' (recompress "w")/0

recompress = # takes a natural to a function that takes something that's already compressed and compresses it more

"w". profile\'recompress' ^= -+
   ~&l->r (nleq+weight~~?r/~&lrlPX ~&NrrPX)^/~&lt @lhPrX ^\~&r (^/~&l trim@llPrX)^\~&r ^/paths ~&l,
   ^\~& heavy_common_subtrees "w"+-

(#
recompress = # takes a natural to a function that takes something that's already compressed and compresses it more

"w". profile\'recompress' -+
   ^= -+
      ~&l->r (nleq+weight~~?r/~&lrlPX ~&NrrPX)^/~&lt @lhPrX ("s","t"). ^(^(~&l,trim@llPrX),~&r) ((paths("s","t"),"s"),"t"),
      ^/heavy_common_subtrees"w" ~&+-,
   ~&l->r (nleq+weight~~?r/~&lrlPX ~&NrrPX)^/~&lt @lhPrX ("s","t"). ^(^(~&l,trim@llPrX),~&r) ((paths("s","t"),"s"),"t"),
   ~&l?/~& @r %oC <'no common subtrees found'>!%,
   ^/heavy_common_subtrees"w" ~&+-
#)
extract = # takes compressed data and reconstructs the original tree from it

~&l->r @llPrXlrPX ~&Y^?all\~&ar ~&alr?(
   ^(~&alll?\~&alrl ~&falbl2rXPR,~&allr?\~&alrr ~&falbr2rXPR),
   ^|R/~& ^|\~& ~&\&+ ~&l)

extractable = # tries to detect whether something is in the form of compressed data

~&i&& ~&lZ!| (nleq+ weight~~)^/~& ~&irB+ ("f". "f"; ~&ilrBB-> "f") ~&ll&& ~&llPrXlrPX; ~&alllrY^?\~&alrPZrB ~&alr?(
   ~&alll?(~&allr?/^BiB(~&falbl2rXPR,~&falbr2rXPR) ^liB/~&falbl2rXPR ~&alrr,^riB/~&alrl ~&falbr2rXPR),
   ^|R/~& ^|\~& ~&\&+ ~&l)

(# self_extracting takes a compression number to a function that maps functions to compressed versions of themselves that
uncompress themselves at run time. #)

self_extracting = (lesser nleq+ weight~~)^\~&+ //^|H(extract,~&)++ compress

shared_subtrees = # takes compressed data to the list of shared subtrees used to compress it

@NiX ~&rl->l ^/~&rlr2lC @rllPrXlrPX ~&Y^?all\~&ar ~&alr?(
   ^(~&alll?\~&alrl ~&falbl2rXPR,~&allr?\~&alrr ~&falbr2rXPR),
   ^|R/~& ^|\~& ~&\&+ ~&l)
