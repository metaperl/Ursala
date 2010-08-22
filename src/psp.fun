

#import std
#import nat
#import tag
#import tco
#import opt

#comment -[
This module contains the specifications for pointer operators used in
the language.

Copyright (C) 2007-2010 Dennis Furey]-

#library+
#optimize+

pnode ::       # describes a pointer or pseudo-pointer constructor

mnemonic %snU  # a single character unique identifier or a natural if it's an escaped constructor
pval     %fOZ  # takes a tuple of pointers to a pointer
fval     %fOZ  # takes a tuple of functions to a function
pfval    %fOZ  # takes a pointer and a function to a function
help     %s    # one line of text to remind the user of the meaning
arity    %n    # the number of operands
escaping %fOZ  # the node takes a numeric value to a new node

#library-
#optimize-

-------------------------------------------------- pointer operator semantic tables -----------------------------------------

triples = # associated binary constructors and deconstructors

^A(~mnemonic,~&)* (fval:= ~fval; (^)?=\~& ! (~&l,~&r)?=/~&! ||(^) -&both ~&lrZB&& ~&llZ,!+ ~&blr&-)* <
   pnode[mnemonic: 'n',pval: (&,0)!,help: 'name in an assignment'],
   pnode[mnemonic: 'm',pval: (0,&)!,help: 'meaning in an assignment'],
   pnode[mnemonic: 'A',pval: (&l,&r)?=/&! ~&,fval: ^,help: 'assignment constructor',arity: 2],
   pnode[mnemonic: 'h',pval: (&,0)!,help: 'head of a list'],
   pnode[mnemonic: 't',pval: (0,&)!,help: 'tail of a list'],
   pnode[mnemonic: 'C',pval: (&l,&r)?=/&! ~&,fval: ^,help: 'list constructor',arity: 2],
   pnode[mnemonic: 'f',pval: (&,0)!,help: 'function in a job'],
   pnode[mnemonic: 'a',pval: (0,&)!,help: 'argument in a job'],
   pnode[mnemonic: 'J',pval: (&l,&r)?=/&! ~&,fval: ^,help: 'job constructor',arity: 2],
   pnode[mnemonic: 'd',pval: (&,0)!,help: 'root of a tree'],
   pnode[mnemonic: 'v',pval: (0,&)!,help: 'subtrees of a tree'],
   pnode[mnemonic: 'V',pval: (&l,&r)?=/&! ~&,fval: ^,help: 'tree constructor',arity: 2],
   pnode[mnemonic: 'l',pval: (&,0)!,help: 'left side of a pair'],
   pnode[mnemonic: 'r',pval: (0,&)!,help: 'right side of a pair'],
   pnode[mnemonic: 'X',pval: (&l,&r)?=/&! ~&,fval: ^,help: 'pair constructor',arity: 2]>

functionals = # non-binary

^A(~mnemonic,~&)* <
   pnode[
      mnemonic: 'Q',
      fval: ||conditional -&~&l,conditional&-^\~&rrlX complement+ ~&l,
      help: 'conditional',
      arity: 3],
   pnode[
      mnemonic: 'q',
      fval: refer+ ||conditional -&~&l,conditional&-^\~&rrlX complement+ ~&l,
      help: 'recursive conditional',
      arity: 3],
   pnode[mnemonic: 'o',fval: *^0,help: 'tree folding combinator',arity: 1],
   pnode[
      mnemonic: 'K',
      fval: <'escape code missing after K'>!%,
      help: 'escape to numerically coded operators',
      escaping: %nI?(~&ihrPB+ ^E(~&l,~&r.mnemonic)*~+ ~&D\(~&mS escapes),<'numeric escape code missing after K'>!%),
      arity: 1],
   pnode[
      mnemonic: 'g',
      fval: ^(complement,~&); -|
         ~&l; ~&i&& not+ ~&a^&+ !|~&fatPR+ ~&lZrB?(~+ ~&NiNXX+ ~&r,~&ah;),
         ~&r; ~&a^?\&!+ &&~&fatPR+ ~&lZrB?(~+ ~&NiNXX+ ~&r,~&ah;)|-,
      help: 'list conjunction',
      arity: 1],
   pnode[
      mnemonic: 'k',
      fval: ^(complement,~&); -|
         ~&l; ~&i&& not+ ~&a^?\&!+ &&~&fatPR+ ~&lZrB?(~+ ~&NiNXX+ ~&r,~&ah;),
         ~&r; ~&a^&+ !|~&fatPR+ ~&lZrB?(~+ ~&NiNXX+ ~&r,~&ah;)|-,
      help: 'list disjunction',
      arity: 1],
   pnode[mnemonic: 'F',fval: filter,help: 'filter combinator',arity: 1],
   pnode[mnemonic: 'S',fval: map,help: 'map combinator',arity: 1],
   pnode[mnemonic: 'Z',fval: ||not complement,help: 'negation',arity: 1]>

soloists = # parameterless functions and pointers

^A(~mnemonic,~&)* (* fval:= ~fval&& !+ ~fval) <
   pnode[mnemonic: 'b',pval: (&l,&r)!,help: 'both'],
   pnode[mnemonic: 'i',pval: &!,help: 'identity function'],
   pnode[mnemonic: 'e',pval: (&,0)!,help: 'element in a set'],
   pnode[mnemonic: 'u',pval: (0,&)!,help: 'proper subset of a set'],
   pnode[mnemonic: 'L',fval: (--):-0,help: 'list flattening function'],
   pnode[mnemonic: 'N',fval: 0!,help: 'empty value'],
   pnode[
      mnemonic: 's',
      fval: -<&; ~&aitB^?\~&a ~&ahthPE?/~&fatPR ~&ahPfatPRC,
      help: 'list to set conversion function'],
   pnode[mnemonic: 'x',fval: reverse,help: 'list reversal'],
   pnode[mnemonic: 'y',fval: reverse+ ~&t+ reverse,help: 'lead items in a list'],
   pnode[mnemonic: 'z',fval: ~&h+ reverse,help: 'last item in a list']>

binaries =

^A(~mnemonic,~&)* (* arity:=2!) <
   pnode[mnemonic: 'c',fval: (*-; ~&l*+ *~ -=)^,help: 'intersection of sets'],
   pnode[
      mnemonic: 'j',
      fval: -|
         ==(~&l,~&rNC)&& ! ~&al^&~&arlhPEPfaltPrXPRalh2faltPrXPRCQ,
         ~&r;-&~&B,~&llrZB,~&r==0!&-&& ~&rll2lX; (-*; ~&r*+ *~ not ==)^,
         (*-; ~&l*+ *~ not -=)^ |-,
      help: 'difference of sets'],
   pnode[mnemonic: 'w',fval: (-=)^,help: 'membership'],
   pnode[
      mnemonic: 'p',
      fval: case~&\((~&lrNCCiK7hthPXS)^) {
         (~&,~&): ! ~&iiXS, 
         (~&t,~&y): ! ~&aitB^&~&athPhXPfatPRC, 
         (~&y,~&t): ! ~&aitB^&~&ahthPXPfatPRC,
         (~&lS,~&rS): ! ~&,
         (~&rS,~&lS): ! ~&rlXS},
      help: 'zip function'],
   pnode[
      mnemonic: 'B',
      fval: -|
         ^(complement+~&l,~&r); ~&l&& -|
            ^(~&l,complement+~&r); ~&r&& not+ ~&llZrB?/(("notp","notq"). "notp"?/"notp" "notq") ~&rlZrB?(
               ("notp","notq"). ^("notp",~&); ~&l?/~&l ~(~&NiX ~&r "notq"),
               ("notp","notq"). ^("notp",~&); ~&l?/~&l "notq"+~&r),
            ("notp","q"). "notp"?/0! "q"|-,
         ("p","q"). "p"?/"q" ! 0|-,         # luckily the general case can be defined without self reference
      help: 'conjunction'],
   pnode[mnemonic: 'D',fval: distribute^,help: 'left distribution'],
   pnode[mnemonic: 'E',fval: compare^,help: 'comparison'],
   pnode[
      mnemonic: 'G',
      fval: ~&lrlPXlrrPXX++ ^,
      pval: ^lrlPXlrrPXX/~&l ~&r; ~&alrB^?/~&a ~&alrY?\(&l,&r)! ~&al?(~&falPR; ~~ ~&iNX,~&farPR; ~~ ~&NiX),
      help: 'pairwise distribution'],
   pnode[mnemonic: 'H',fval: (recur&^J\~&r ~&l; ~&a;)^,help: 'function application'],
   pnode[
      mnemonic: 'I',
      fval: ~&I++ ^,
      pval: -+
         ~~ ~&al^& ~&allrY?\~&ar ~&fallPrXlrPrXXPW,
         ^lrlPXlrrPXX/~&l ~&r; ~&alrB^?/~&a ~&alrY?\(&l,&r)! ~&al?(~&falPR; ~~ ~&iNX,~&farPR; ~~ ~&NiX)+-,
      help: 'pairwise relative addressing'],
   pnode[
      mnemonic: 'M',
      fval: (both ~&lZrB)?/mapcur+embedded_pointer_reduction+~&br (mapcur&)^,
      help: 'mapped recursion'],
   pnode[mnemonic: 'O',fval: ||compose -&both ~&lZrB,~+ pointer_composition+ ~&br&-,help: 'functional composition'],
   pnode[
      mnemonic: 'P',
      pval: refer conditional( # for the sake of a non-circular definition of ~&al^& ~&allrY?\~&ar ~&fallPrXlrPrXXPW,
         field(0,(&,0)),
         conditional(
            conditional(field(0,((&,0),0)),constant &,field(0,((0,&),0))),
            couple(recur((&,0),(0,(((&,0),0),(0,&)))),recur((&,0),(0,(((0,&),0),(0,&))))),
            field(0,(0,&))),
         constant 0),
      pfval: ~&al==(&l,&r)^?/(~~+ ~&ar) ~&all?(
         ~&alr?(^^(~&fallPrXPR,~&falrPrXPR),~&l;+ ~&fallPrXPR),
         ~&alr?\~&ar ~&r;+ ~&falrPrXPR),
      fval: ++~&rlX,
      help: 'relative addressing'],
   pnode[
      mnemonic: 'R',
      fval: (both ~&lZrB)?/recur+embedded_pointer_reduction+~&br (recur&)^,
      help: 'recursion'],
   pnode[mnemonic: 'T',fval: cat^,help: 'concatenation'],
   pnode[
      mnemonic: 'U',
      fval: (~&al^?\~&ar ~&ar?\~&al ==+~&abh?/~&alh2fabt2RC lleq?abh/~&alh2faltPrXPRC ~&arh2falrtPXPRC)^,
      help: 'union of sets'],
   pnode[
      mnemonic: 'W',
      fval: (both ~&lZrB)?(
         (^+ (recur+ pointer_composition)^~(~&/&falPJ,~&/&farPJ))+ embedded_pointer_reduction+ ~&br,
         (^/~&falPR ~&farPR)^),
      help: 'pairwise recursion'],
   pnode[
      mnemonic: 'Y',
      fval: -|
         ^(complement+~&l,~&r); ~&l&& -|
            ^(~&l,complement+~&r); ~&r&& not+ ("notp","notq"). "notp"?/"notq" 0!,
            ~&llZrB?/(("notp","q"). "notp"?/"q" &!) ~&rlZrB?(
               ("notp","q"). ^("notp",~&); ~&l?/~(~&NiX ~&r "q") &!,
               ("notp","q"). ^("notp",~&); ~&l?/"q"+~&r &!)|-,
         ~&llZrB?/(("p","q"). "p"?/"p" "q") ~&rlZrB?(
            ("p","q"). ^("p",~&); ~&l?/~&l ~(~&NiX ~&r "q"),
            ("p","q"). ^("p",~&); ~&l?/~&l "q"+~&r)|-,
      help: 'disjunction']>

#library+

escapes = # these are invoked as K0, K1, etc.. More can be added ad infinitum but don't change the order

decoupled ^A(~mnemonic,~&)* (&r.mnemonic:=r ~&l)* num <
   pnode[fval: cross^,help: 'cartesian product',arity: 2],
   pnode[fval: all_same,help: 'all-same predicate',arity: 1],
   pnode[
      fval: ~&x++ |=+ compare++ ~&lZrB?\fan ~&r; ~+ pointer_reduction+ "p". (&l."p",&r."p"),
      help: 'partition by comparison',
      arity: 1],
   pnode[fval: substring^,help: 'substring predicate',arity: 2],
   pnode[fval: ([=)^,help: 'prefix predicate',arity: 2],
   pnode[fval: std-suffix^,help: 'suffix predicate',arity: 2],
   pnode[fval: ~&drPvHo+,help: 'tree evaluation by &drPvHo',arity: 1],
   pnode[fval: transpose+,help: 'transpose',arity: 1],
   pnode[fval: ! mtwist..u_enum,help: 'random draw from a list'],
   pnode[
      fval: |\,
      help: 'triangle combinator',
      arity: 1],
   pnode[fval: gint+ compare^|,help: 'generalized intersection by comparison',arity: 2],
   pnode[fval: gint,help: 'generalized intersection combinator',arity: 1],
   pnode[fval: gdif+ compare^|,help: 'generalized difference by comparison',arity: 2],
   pnode[fval: gdif,help: 'generalized difference combinator',arity: 1],
   pnode[fval: *|+ compare^|,help: 'distributing bipartition by comparison',arity: 2],
   pnode[fval: *|,help: 'distributing bipartition combinator',arity: 1],
   pnode[fval: ~|+ compare^|,help: 'distributing filter by comparison',arity: 2],
   pnode[fval: ~|,help: 'distributing filter combinator',arity: 1],
   pnode[fval: subset^,help: 'subset predicate',arity: 2],
   pnode[fval: (~=&& subset)^,help: 'proper subset predicate',arity: 2],
   pnode[fval: !=,help: 'bipartition combinator',arity: 1],
   pnode[fval: :-0,help: 'reduction with empty default',arity: 1],
   pnode[fval: ! ~&i&& ~&iNXS+ ~&rSxaahPNfatPRXfatPRNXQaaXq2S+ zipp0*ziD+ iol,help: 'address enumeration'],
   pnode[fval: =:+,help: 'address map',arity: 1],
   pnode[fval: -:+,help: 'partial reification',arity: 1],
   pnode[fval: -$^,help: 'unzipped partial reification',arity: 2],
   pnode[fval: ("f","g"). ?^(\/-=+ ~&lS+ "f",~&\"g"+ -:+ "f"),help: 'total reification',arity: 2],
   pnode[fval: ! ~&aitB^?\~&a ~&ahPfatt2RC,help: 'alternate items of a list including the head'],
   pnode[fval: ! ~&aitB^& ~&ath2fatt2RC,help: 'alternate items of a list excluding the head'],
   pnode[fval: (~&B^?a\~&Y@ar ~&alh2arh2fabt2RCC)^,help: 'merge of lists',arity: 2],
   pnode[fval: ! ~&lS+ zipt^/~& ~&aitB^& ~&ahthPNCCPfatt2RC,help: 'first half of a list'],
   pnode[fval: ! ~&lSx+ zipt^/~&x ~&a^& ~&at?\~&aNC ~&ahthPNCCPfatt2RC,help: 'second half of a list'],
   pnode[fval: ("f","g"). ~&a^& ^C/"f"@ah ~&at&& ^C/"g"@ath ~&fatt2R,help: 'map functions to alternate list items',arity: 2],
   pnode[fval: ~&?=/~&iiDlS! "f". ~&i&& @tiNCX ~&l->rx ^/~&lt ^C\~&r "f"@rh,help: 'triangle squared',arity: 1],
   pnode[fval: (depth_first visiting_leaves no_order)^,help: 'depth first tree leaf tagging',arity: 2],
   pnode[fval: (depth_first visiting_trunks preorder)^,help: 'preorder tree trunk tagging',arity: 2],
   pnode[fval: (depth_first visiting_leaves preorder)^,help: 'preorder tree tagging',arity: 2],
   pnode[fval: (depth_first visiting_trunks postorder)^,help: 'postorder tree trunk tagging',arity: 2],
   pnode[fval: (depth_first visiting_leaves postorder)^,help: 'postorder tree tagging',arity: 2],
   pnode[fval: (depth_first visiting_trunks in_order)^,help: 'inorder tree trunk tagging',arity: 2],
   pnode[fval: (depth_first visiting_leaves in_order)^,help: 'inorder tree tagging',arity: 2],
   pnode[fval: (breadth_first leaf_levels)^,help: 'level order tree leaf tagging',arity: 2],
   pnode[fval: (breadth_first root_levels)^,help: 'level order tree trunk tagging',arity: 2],
   pnode[fval: (breadth_first all_levels)^,help: 'level order tree tagging',arity: 2]>

pnodes = decoupled triples-- functionals-- soloists-- binaries-- ^A(~mnemonic,~&)* pnode$[mnemonic: ~&iNC]* '0123456789'

------------------------------------------- tree tagging functions ----------------------------------------------------------

#library-

(# These functions are used to construct tree tagging functions accessible by ~&K34 through ~&K43, which facilitate
applications needing to label or number the nodes in a tree uniquely. Each such function zips a list to a tree, resulting in
a similar tree having some or all nodes paired with an item from the list. The functions vary by their traversal order and by
whether they include terminal nodes, non-terminals, or both. The four traversal orders are preorder, postorder, inorder, and
level order, but the first three are indistinguishable if non-terminal nodes are excluded, resulting in ten
alternatives. Empty subtrees are skipped, but otherwise the list length must match the number of relevant nodes. #)

breadth_first = # applies to one of the levels functions

guard\<'bad tag'>!+ -+
   //+ @NiX ~&r->lh ~&rh?\~&lrhPNCTrtPX ^\~&rt ^rrPlrlx2VNCT/~&rhd @rhv2lX ~&alParh2fabt2RXlrlPCrrPXPNarPXq,
   @NlrNCXX+ ~&rr->rlPNiQl+-

all_levels  = ~&rrh?/~&rlhPrhd2XrhvNS3VPlCrltPrtPrhv2TXPX ~&NlCrlrtPXPX
root_levels = ~&rrhivB?\~&rrh2lCrlrtPXPX ~&rlhPrhd2XrhvNS3VPlCrltPrtPrhv2TXPX
leaf_levels = ~&rrh?\~&rrh2lCrlrtPXPX ~&rrhv?/~&rrhd2rhvNS3VPlCrlrtPrhv2TXPX ~&rlhPrhd2XNVPlCrltPrtPrhv2TXPX

depth_first = guard\<'bad tag'>!+ ~&rNiQl++ ~&ar^?\~&arlX+ ~&arv? # composes with one of the visiting functions

visiting_trunks = ~&\~&arlX                # applies to one of the order functions
visiting_leaves = ~&\~&alhPrdPXrvPVltPX    # applies to one of the order functions

no_order  = ^lrlPVrrPX/~&ard @falrvPXPJ descent
postorder = ^rrh2lXrlPVrrt2X/~&ard @falrvPXPJ descent
preorder  = ^lrlPVrrPX/~&alhPrdPX @faltPrvPXPJ descent
descent   = ~&aar^?\~&aarlX ~&lrlPCrrPX^|Jaall3fafalrPrXPJPRX/~& ^J/~&f ^/~&falrhPXPR ~&art  # visits its caller on subtrees

in_order =

~&arvt?(
   (^lrlrlPCPVrrr2X/~&ard ^/~&arvh descent@falrvt2XPJ)^J/~&f ^rlrt3rlrh3lXrllPrCPVX/~&ard ^/~&falrvh2XPR ~&arvt,
   ^rrh2lXrlPNCVrrt2X/~&ard ~&falrvh2XPR)

--------------------------------------- functions used in optimization ------------------------------------------------------

#library+
#optimize+

complement = # takes a predicate to its complement if a smaller one can be found

~&a^& -|
   ~&a; -&~&B,~&lr==0!,~&r==&!,~&ll&-|| ~&lrZB&& ~&llZ&& !+ ~&lrZ,
   -&~&alrZB,~&allrB,~&fall2Ralr2X; ~&l&& ~&l==~&?/~&r +&-,
   -&~&alrB,~&allrB,~&all2falrPrXPWX; ~&rlrB&& ?&-|-

decoupled = #  optimizes fval's of the form h^ to check for pairs of operands of the form ~f

* &m.(pval,fval):= ~&m.(pval,fval); optimization~~+ ^/~&l ~&r; ||~& -&
   -&~&,~&rZ,~&llrB,~&ll==(+)&-&& ~&lr; -&~&B,~&llrZB,~&ll; ~&lrZB&& ~&llZrB,~&r==(^)&-,
   &lrr:= ! ||(^) -&~&,~&B,both ~&lZrB,~+ embedded_pointer_reduction+ ~&br&-&-

------------------------------------------------ the pointer interpreter ----------------------------------------------------

percolation = # takes a list of pointer constructors to a pair (pointer,function), with at most one non-empty

~&?\(&,0)! ~&h.mnemonic-=(~&iNCS '0123456789')?/<'pointer underflow'>!% -+
   _pnode%LMk; ~&NiX; ^(pointer_reduction+~&l,optimization+~&r)+ ~&rlitBPY->lh ~&r?(~&,~&\<pnodes-P>+ ~&l); -+
      ^\~&rt :^\~&ll ~&lrlg?(
         ~pval?rh/^HNX(~&rh.pval,~&=>+ ~&lrlS) ~pfval?rh(
            ^NlrHX/~&rh.pfval ~&=>+ ~&lrlS; :^/~&h ~&t; * ~,
            ~fval?rh(
               _pnode%LtfZXLWwXMk; ^NlrHX/~&rh.fval ~&=>+ ~&lrlS; * ~,
               % ~&iNC+ 'misused pseudo-pointer at '--+ ~&rh.mnemonic; %sI?/~& ~&h+ %nP)),
         -&~&lrhl,~&rh.pfval&-?/(^NlrHX/~&rh.pfval ~&lr; ~&=>+ :^/~&hl ~&t; * ~&l?/~+~&l ~&r) ~fval?rh(
            ^NlrHX/~&rh.fval ~&lr; ~&=>+ * ~&l?/~+~&l ~&r,
            % ~&iNC+ 'misused pseudo-pointer at '--+ ~&rh.mnemonic; %sI?/~& ~&h+ %nP)),
      _pnode%LtfZXLWwXMk^\~&r -+
         ~&r->l ~&ll?\<'pointer underflow'>!% ^/~&lltPlhPrCX predecessor+ ~&r,
         ^(~&lNX,~&rh.arity); ~&ll?/~& 2?=r(~&/(<(&r,0),(&l,0)>,0)+ ~&r,1?=r\~& ~&/(<(&,0)>,0)+ ~&r)+-+-,
   *= (~&h.mnemonic-= ~&iNCS '0123456789')?\~& ~mnemonic*=; ~&iNC; ~&lS+ ~&D/pnodes-P+ iota+ ~reader type_constructors-n,
   ~&aitB^?\~&a ~&ahh.escaping?\~&ahPfatPRC :^\~&fatt2R -+
      ~&l?/~&lNC % ~&iNC+ 'unrecognized escape code: '--+ ~&h+ %nP+ ~&r,
      ^HrX/~&ahh.escaping (~&athh.mnemonic-= ~&iNCS '0123456789')?(
         ~&ath; ~mnemonic*=; ~&iNC; ~reader type_constructors-n,
         ~&athh.mnemonic)+-,
   rlc both ~mnemonic-= ~&iNCS '0123456789'+-
