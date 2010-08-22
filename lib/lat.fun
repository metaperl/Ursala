
#import std
#import nat

#comment -[
This module contains some operations on lattices. Most depend on the
assumption that the lattice has a single root.

Copyright (C) 2007-2010 Dennis Furey]-

#library+
#optimize+

--------------------------------------- construction and deconstruction of lattices -----------------------------------------

edges   = ~&/<&>; ~&xS+ ~&ar^& ~&rnSPlfPrmvPSLs3lart3XRX+ ~&iarhPlDrNrXlHAS2X
levels  = ~&NliNXSPNNNCCTXrNXHdS^*p/edges ~&
lnodes  = ~&L+ levels

grid = # takes a specification (<<v..>..>,<e..>) where each e is an adjacency relational predicate, to a %G type

~&l&& -+
   * ^|H(:=^/~&l !+ ~&r,~&)=>[]+ ~&lrrlDPD; * ^/~&rrl ^V/~&rrr ^HlS\~&rrlX ~|+ ~&br;+ ~&l,
   zipp(0!)^/~&r ~&l; ~&tytpBzNXNCT+ * ~&/<<&>>; -&leql,not eql&-->~&llTrX; zipt^\~&r ~&NlDrlXSPNrDT:-0+ ~&l,
   ~&alh^?\&! ~&alt?\~&alhNCPNX ^bbI/~&abh ^R/~&f ^\~&artiY :^\~&altt ^H\~&althPhX gint+ ~&rlX;+ ~&arh,
   (any %fI; ~&a^& ||~&favPMik -&~&adl=='library',~&avhdrNHl=='mtwist'&-)?r\~& -+
      %sLfLXMk+ ^/~&l ~&rlytplrK0S2p; * %fcWLXMk; lsm^H\~&r *~+ ~&l,
      ~&alt^?\~&alNX ~&abh2faltPrtiYPXPRXbbI+-+-

sever = # takes an argument of type t%G to one of type t%GG by replacing each node with the lattice rooted on it

^lxSPrp(edges,~&); %aLsaLXNoUXLMk; ~&a^& ~&at?(
   :^\~&fatPR (~&lrPllPrpX; ~&r->l ^\~&rt ^H\~&l :=^/(~&rhl; .\&d) !+ ~&rhr)^/~&ahlrX -+
      * :^/~&r ~&rrPlX; ~&ar^& ~&iarhPlDrNrXlHAS2X; :^\~&lfPrmvPSLs3lart3XR ~&r; ~&Hl\0+ :=+ ~&lNXSNNNCCTNrSXNXX,
      ~&atrSPhNliNXSPNNNCCTXrNXHPD+-,
   ~&ah; %aLsaLXNXMk; ~&liNXSPNNNCCTrNXX; ~&HlPNC\0+ :=^/~&l !+ ~&NlXrHdNCvVNCS)

------------------------------------- generalizations of list combinators to lattices ---------------------------------------

ldis = ^H\~&r lmap+ ^\~&+ !+ ~&l  # distributes a value to every node

ldiz = # takes a list of values and a grid, and distributes a value to each level

~&/<&>; ~&arr^& ~&iarlh2rrh2lDrNrXlHASPDrnPlrmd2Xrmv2VAS2X; :^\~&lfPrmvPSLs3larbt4XR ~&Hl\0+ :=+ ~&rlNXSNNNCCTNrSXNXX

lzip = # zips a couple of similarly shaped lattices together

^(edges,~&)~~; ~&llPrlPE?(
   ~&blrplNliNXSPNNNCCTXrNXHXS2lrp; ~&Hl\0+* :=+ ~&lliNXS2NNNCCTNlrdS2rrdS2prrvS2pXNXX,
   <'bad lzip'>!%)

lmap = # applies a function to every node in a lattice

"f". ~&/<&>; ~&ar^& -+
   :^\~&lfPrmvPSLs3lart3XR ^H(:=^/~&ll !+ ~&lr,~&r)=>0+ ~&r; * ^A/~&n ^V\~&mv "f"+ ~&md,
   ^/~& ~&arhPlDrNrXlHAS+-

lfold = # applies a function to a node and a list of the results from the subtrees in a lattice

"f". ~&i&& ~&/<&>; <:~&iarhPlDrNrXlHAS2X -+
   ~&Hl\0+ :=+ ~&liNXSPNNNCCTNrXNXX,
   ^/~&rnS "f"*+ ~&mvPk?r\~&rmS ~&lfPrmvPSLs3lart3XRrD; * ^V/~&rmd ~&lrmv2DNrXlHS+-

------------------------------------------------- induction patterns --------------------------------------------------------

bwi = # takes a function mapping an ordinary tree to a new root and performs backward induction on a lattice

"f". ~&i&& ~&/<&>; ~&r+ ~&ar^& ~&iallNiNXSNNNCCTXPrhPNXHpPX; ~&lart?(
   ~&rlfPrmvPSLs3lart3XRX; ^rlPrrPlCX/~&rr -+
      (~~ ~&Hl\0+ :=)^G/~&liNXSNNNCCT !~~+ ~&r,
      ^pllPSlrPSlrd2rVSXX\~&lmvPS ~&rlPlD; ^p/~&rnPS * ^V("f",~&v)+ ^V/~&rmd ~&lrmv2DNrXlHS+-,
   ~&iiNCX+ (~&Hl\0+ :=^/~&liNXSPNNNCCT !+ ~&r)^/~&rnS ~&rmS; * ^V/"f" ~&v)

fwi = # operand takes (<inheritance..>,tree) to (root,<bequest..>); result is a lattice transformation

"f". ~&NiX; ~&r&& ^lrrPXNCrlPX(~&l,~&r; ^/~& lfold ~&); ~&/<&>; <:~&ialNliNXSPNNNCCTXrrh2NXHpPX ~&larrt?(
   (:^/~&rr ^R/~&llf ^/~&rlnS ^/~&rlmS ~&llarrt)^/~& -+
      ^\-+~&Hl\0+ :=+ ~&liNXSPNNNCCTNrXNXX,^/~&rnPS ~&llPrmv2XS+- -+
         |=hlmr3rlPShrr2XXS&lmr+ *= ~&x+ psort<lleq+ ~&bln,~&blml; not nleq>,
         |=&lmr+ *= ^p\~&lr ^D/~&rn num+ ~&rmr+-,
      ^p\~&r ~&larl; * ^("f",~&rv); -&~&l,eql@lrPrX&-?/~&llPlrPrpX <'bad forward inducer'>!%+-,
   (~&H\0+ :=+ ~&liNXSPNNNCCTNrXNXX)^/~&rnS ~&larl; * "f"; ~&irZB?/~& <'bad boundary'>!%)

fswi = # operand takes ((<inheritance..>,<sibling..>),tree) to (root,<bequest..>); result is a lattice transformation

-+
   "f". @NiX ~&r&& ^lrrPXNCrlPX(~&l,~&r; ^/~& lfold ~&); ~&/<&>; <:~&ialNliNXSPNNNCCTXrrh2NXHpPX ~&larrt?(
      (:^/~&rr (~&rl; any ~&m)?\~&llarrt ^R/~&llf ^/~&rlnS ^/~&rlmS ~&llarrt)^/~& -+
         ~&i&& ^\-+~&Hl\0+ :=+ ~&liNXSPNNNCCTNrXNXX,^/~&rnPS ~&llPrmv2XS+- -+
            |=hlmr3rlPShrr2XXS&lmr+ *= ~&x+ psort<lleq+ ~&bln,~&blml; not nleq>,
            |=&lmr+ *= ^p\~&lr ^D/~&rn num+ ~&rmr+-,
         ^llrpB\~&r ~&rrlPSPlarl3D; * ~&rlPlXrrPX; ^("f",~&rv); eql?lrPrX/~&llPlrPrpX <'bad forward inducer'>!%+-,
      (~&H\0+ :=+ ~&liNXSPNNNCCTNrXNXX)^/~&rnS ~&rrlPSPlarl3D; * ~&rlPlXrrPX; "f"; ~&rZ?/~& <'bad boundary'>!%),
   ||(^/~&rd 0!*+ ~&rv)+-

swi = "f". fswi ^("f"+ ~&lrPrdPX,0!*+ ~&rv)  # f maps only (<sibling..>,root) to new root
