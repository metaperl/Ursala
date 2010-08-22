
#import std

#comment -[
This file contains compatible replacements for most of the core virtual
machine combinators defined in cor.fun, expressed only in terms of
constant, conditional, compose, couple, field, and recur. This
information may be useful for abstract interpretation. The source
is distributed with both the Ursala compiler and the avram virtual
machine emulator but the compiler is needed to compile it.

Copyright (C) 2007-2010 Dennis Furey]-

#optimize+

successor  = ~&aahPNfatPRCNNXatPCQNNXNCq
sum        = ~&al^?\~&ar ~&ar?\~&al ~&alh?(~&arh?(successor+ ~&NNXfabt2RC,~&NNXfabt2RC),~&arh?(~&NNXfabt2RC,~&Nfabt2RC))
replace    = ~&ar^?\~&falNNXXPR ~&alll? ~&allr?~~/(~&falbr3falbl2rXPRXR,~&falllPrXPrlPXPRarr2X) (~&arl2fallrPrXPrrPXPRX,~&alr)

#library+  # those expressed in terms of the refer combinator will require further rewriting but will still terminate

profile    = ~&l
guard      = ~&l
note       = ~&l
refer      = //~&R
iterate    = ^?^/-+~&a;,~&l+- ~&\~&a+ ^R/~&f+ ~&a;+ ~&r
reduce     = ~&?^\!+~&r ~&h++ iterate/~&t+ ~&aitB^?\~&a+ ^\~&fatt2R+ ~&ahthPX;+ ~&l
sort       = ~&iNCS;+ reduce\0+ ~&al^?\~&ar+ ~&ar?\~&al+ ~&abh;; \/? ~&/~&alh2faltPrXPRC ~&arh2falrtPXPRC
transfer   = +^\-+//~&,~&iNH+- ~&l&&+ cat^/~&lr+ ~&llPrX;+ (refer+ //+ ~&rrrPlfPrlPlaritB3XRTB)+ ~&alrihBPX;; ^/~&
map        = ~&a^&+ ^\~&fatPR+ ~&ah;
filter     = ~&a^&+ ?\(~&ahPfatPRC,~&fatPR)+ ~&ah;
fan        = ~&lrNCC;+ ~&hthPX++ map
compare    = ~&alParPfabl2Rfabr2RBBarZPq
reverse    = ~&NiXarPfarhPlCrtPXPRaql
distribute = ~&arPalrhPXPfalrtPXPRCNq
member     = ~&ar^& !|~&falrtPXPR compare+ ~&alrhPX
cat        = ~&alPalh2faltPrXPRCarPq
transpose  = ~&ah^& :^(map~&h+ ~&a,^R/~&f map~&t+ ~&a)
weight     = ~&a^& successor+ sum+ ~&W
assign     = replace++ ^\~&+ ^^/!+~&l ~&r
mapcur     = (map ~&R)++ distribute++ ~
recur      = ~&R++ ~

#library-

u = %+ !+ ~&iNC+ 'unrecognized combinator (code '--+ --')'+ ~&h+ %nP
i = %+ !+ ~&iNC+ 'irreducible combinator (code '--+ --')'+ ~&h+ %nP


#comment-

#output * file$[
   stamp: &!,
   path: ~&iNC+ --'.c'+ ~&n,
   contents: ~&m; -+
      //-- ~&NiC --<''> <
         '/* This is the virtual machine code expressed as a c formatted character',
         '   constant for a function that takes a virtual machine program to an equivalent',
         '   program by translating the top level combinator into more primitive',
         '   combinators if possible. */'>,
      --<''>+ ^lrNCT(~&y; * --'\',~&z)+ ~&a^& ^alPfarPRC/~&f ~&a; ^(take/79,skip/79); ->~&lyPlzPrCX ~&l&& ~&lz==`\,
      'char *interpreter_code = "'--+ --'";'+ `\?=(~&iiNCC,~&iNC)*=+ ~&xttx+ ~&tt+ ~=` *~+ ~&L+ %xP+-]

#library+

rewrite = # used as the interpreter code in apply.c, in the virtual machine emulator source code

~&l?\(~&r?/i0 compare!) ~&r?(
   ~&ll?/(~&lr?/i1 i2) ~&lr?/i3 ~&r; ~&l?\(~&r?\cat! ~&r; ~&l?(~&r?/iterate filter+ ~&l,~&r?/transfer+~&r reverse!)) ~&r?(
      ~&ll?(
         ~&lr?(&?=r/i4 u0,&?=r/sort+~&ll -&~&ll==&,~&lrZ,~&rrZ,~&rl,~&rllZ&-?/i5 u1),
         ~&lr?/(&?=r/fan+~&lr u2) ~&r; ~&l?/(~&r?/i6 mapcur+ ~&l) ~&r?(
            ~&r; ~&l?(~&r?/u3 ~&l; ~&l?/profile i7,~&r?\weight! ~&r; ~&l?/note u4),
            transpose!)),
      ~&l; ~&l?/reduce ~&r?/map+~&r member!),
   ~&l; ~&l?\i8 ~&r?/i9 ~&l; ~&l?(
      ~&r?\refer+~&l guard(replace,<'invalid deconstruction'>?=\~& <'invalid assignment'>!)++ ^\~&+ ^^/!+~&l ~&r,
      ~&r?/recur+~&r distribute!))
