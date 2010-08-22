
#comment -[
This module contains general purpose operations that are frequently
used in the language.

Copyright (C) 2007-2010 Dennis Furey]-

#import nat
#library+
#export+
#import cor

characters = -<& %cI*~ upto 8
letters    = -- (take/26)^~(skip/97,skip/65) characters
digits     = '0123456789'

gpl = # takes a version number as a character string

-[This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; version -[.~&?\'3'! ~&iNC]-.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software Foundation,
Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA]-

#optimize+

command_line   :: files _file%L options _option%L
file           :: stamp %sbU path %sL preamble %sL contents %sLxU
option         :: position %n longform %b keyword %s parameters %sL
invocation     :: command _command_line environs %sm

# first order

choices         = ^(iota@r,~&l); leql@a^& ~&al?\&! ~&arh2fabt2RDfalrtPXPRT
closure         = ^= ^Ts\~& *=iiD ^D/~&rl @rlX ~&r*+ ~| ~&lrPrlPE
cross           = -**=+ *-
cuts            = @rlX ~&al^?\~&arrNCNCB ^|Darl2falrrPXPRDSL/~& ^|D/predecessor @NiXNC ~&hr->txtlxPrXS ~&hrhPlCrtPXPiC
enum            = ~&ddvDlrdPErvPrNCQSL2Vo+ %-U:-0+ %-u*
eql             = ~&alParPfabt2RBarZPq
gcp             = ~&al^&~&arPalhPrhPEPalh2fabt2RCBB
indexable       = ~&l&&~&all2alr2fallPrXPRfalrPrXPRBarPfabl2RBQalr2arPfabr2RBalPQq
intersecting    = ~&ar^& ~&arhPlw!| ~&falrtPXPR
iol             = ~&NiX; ~&r->lx ^\~&rt ~&l; :^\~& ~&i&& successor+ ~&h
leql            = ~&alZ^!~&arPfabt2RB
lleq            = ~&alParPallPrlPEPfabr2Rfabl2RQNQNNXq
num             = ^p\~& iol
permutations    = ~&itB^?a\~&aNC @ahPfatPRD *= refer ^C/~&a ~&ar&& ~&arh2falrtPXPRD
powerset        = -<&+ ~&rFlSPS+ zipp0^*D/~& iota+ ~&NSNNXNCT
singly_branched = ~&aalParPNfalPRQfarPRQNNXq
skip            = ~&alrB^?\~&ar ^R/~&f ^/~&ahPatPNatPCBNNXfatPRCq+~&al ~&art
subset          = *-; all -=
substring       = ^!~&arPfalrtPXPRB [=+ ~&a
suffix          = [=+~&bx
take            = ~&alrB^& :^/~&arh ^R/~&f ^\~&art ~&ahPatPNatPCBNNXfatPRCq+ ~&al
upto            = ~&\<<0>>; ~&l->xrLPO ^/~&ahPatPNatPCBNNXfatPRCq+~&l ^lLPrC\~&r cross*rrxPp
zip             = ~&alrB^?/~&abh2fabt2RC ~&alrY&& <'bad zip'>!%
zipt            = ~&alrB^&~&abh2fabt2RC

# second order

all            = ~&a^?\&!+ &&~&fatPR+ ~&ah;
all_same       = ~&aatPBZ^!~&ahthPEPfatPRB++ *
any            = ~&a^&+ !|~&fatPR+ ~&ah;
arc            = choice+ !*
associate_left = ~&i&&+ ~&t?\~&h+ ~&x;+ <:~&ahPatt2fatPRath2QX+ ~&rlX;
border         = +^|(~&,*)=>+ (^CihNCT\~&+ @h)*+ (*)|\x+ 0!!*+ iota
both           = ~&B++ ~~
case           = gcase ==
cases          = gcase -=
choice         = ^H\~&+ mtwist..u_enum++ !
dot            = "s". "f". * file$[stamp: &!,path: ~&iNC+ --(:/`. "s")+ ~&n,contents: "f"+ ~&m]
either         = ~&Y++ ~~
fused          = +^/~& ~&iNH; //~&; //+ ~&al^?\~&arlrY ~&fallPrbl2XlrPrbr2XXPW+ ~&falPbrlYPalrGPOXJ # record constructor
gang           = (^)=>0!
gdif           = ~&rlD;+ ~&r*++ *~+ not+ ~&rlD;+ any
gint           = ~&rlD;+ ~&r*++ *~+ ~&rlD;+ any
gldif "r"      = ~&al^& ~&alPfarPRT^J/~&f ~&a; ~&ar^?\~&alhPNCltPrXX "r"?abh/~&Nabt2X ~&rlPrrl2lrrr2CXXarh2falrtPXPRXO
glimit         = "f". ~&iNC; ~&htwZ->h ^("f"+ ~&h,~&); :^/~&l ^(weight+~&l,~&r); ~| nleq^\~&l weight+ ~&r
glint "r"      = ~&al^& ~&alPfarPRT^J/~&f ~&a; ~&ar^?\~&NaltPrXPX "r"?abh/~&alhPNCbtPX ~&rlPrrl2lrrr2CXXarh2falrtPXPRXO
lesser         = "r". "r"?/~&l ~&r
mat            = ~&i&&+ ~&t++ *=+ //:
neither        = ~&lNrZQ++ ~~
not            = ~&\&!+ ~&\0!
ordered        = ~&aatPBZ^!+ &&~&fatPR+ ~&ahthPX;
pad            = "p". ~&i&& ~&rSS+ zipp"p"^*D\~& leql$^
psort          = ~&?\~&! -<+ ~&at^?\~&ah +^(~&rlrE?\~&rl+ ~&l;+ ~&fatPR,^/~&+ ~&irlXX;+ ~~+ ~&ah)
rlc            = ~&a^&+ ~&at?\~&aNC+ ~&ahthPX;; \/? ~&/~&lrhPCrtPCahPfatPRXO ~&ahPNCfatPRC
sep            = ~&a^?\&!+ \/?=ah ~&/~&NfatPRC ~&lrhPCrtPCahPfatPRXO
skipwhile      = ->~&t+ ~&i&&+ ~&h;
stochasm       = ^H\~&+ mtwist..w_enum++ !+ * ^/~&m ~&n; %nI?\~& math..strtod+ ~&h+ %nP
takewhile      = ~&a^&+ &&~&ahPfatPRC+ ~&ah;
words          = "n". "a". ~&rlrK0liNCSPQ=>0 "a"!* iota"n"
zipp           = "p". ~&al^?(~&ar?/~&abh2fabt2RC *-"p"+ ~&al,~&ar&& "p"-*+ ~&ar)

block =

iota7?<(
   iota; ~&t?\~&iNCS! ~&a!*; ~&NiC|\; ^?^/-&&- ~&\~&aaNCB+ ^^(gang+ .\*&h,recur/&f+ ~&z),
   ~&a^&+ ~&alPfarPRC^J/~&f+ ~&a;+ //~&alrBPlrlPCrrPXarh2fabt2RXONarPXq+ 0!*+ iota)

rep "n" = 

nleq$-+ <.
   "f". -++- "f"!* iota "n",
   "f". ~&/(0!* iota "n"); ~&l->r ^|\"f" ~&lt,
   "f". ~&/"n"; ~&l->r ^|\"f" ~&ahPatPNatPCBNNXfatPRCq>

swin = # takes a number n to a function enumerating all length n sublists of a list

iota8?< ~&\("n". ~&r->lx~&lht2rhPNCTlCrtPX+ ~&lNrXX/"n"; ~&lrrPB->rlxPNCrX ^|/~&ahPatPNatPCBNNXfatPRCq ~&rhPlCrtPX) -+
   +^(~&xSNX;+ ~&K7x++ ~+ --<0,0>+ ~&all2arlrPXPNfalrPrXPRXqNX*arPNfarPRXaNXqSxp,~&NiX;+ ~+ ~&=>&l+ ~&NiXS),
   ~&NNXiX; ~&r->lxt ^|/~&NhCiC ~&ahPatPNatPCBNNXfatPRCq+-

next =

~&?(
   ~&ahPatPNatPCBNNXfatPRCq; "n". "f". "x". ~&x (rep"n" :^\~& "f"+ ~&h) <"x">,
   ! "f". "x". ~&wZ->tx(:^/"f"+~&h ~&) <"x">)

lsm = # takes a set to its logarithmic-time membership predicate

~&?\0!! ^w/~&+ @NiX (leql/8+ length)^?ar\!@ar (&&^|\~& ~)=>^lrNCT(~&alryPlj,?^/~@alrz ~&fallrTPrGPW)^|J/~& -+
   ^(^|/~&l ~&a^& :/&+ ~&l?a/~&falPRiNXS ~&farPRNiXS,^H\~&lr !=+ ~@r),
   ^/~& @r (nleq+ weight~~)$-+ ^HZ(all_same+ ~@r,~&l)~|^/~& @alrBPfabbIPWNqK21 ~&a^?\<&>! ~&WliNXSPrNiXSPT+-

# higher order

gcase = # generalized case statement, takes a recognizing predicate to a case statement constructor

~&lZrB?^(
   ~&al^?\~&ar++ ?^\^(~&alhr,~&faltPrXPR)++ ~&alhl;++ !;++ ///+ ^;+ //+,
   ^\~&;+ ;;+ ;+ ~&al^?\-+~&r;,~&ar+-+ ?^\^(~&r;+ ~&alhr,~&faltPrXPR)+ ~&alhl;+ !;+ ~&/~&l;+ ^;+ //+)
