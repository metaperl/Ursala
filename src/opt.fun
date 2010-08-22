
#import std
#import nat

#comment -[
This module contains a few helpful code optimizing functions.

Copyright (C) 2007-2010 Dennis Furey]-

profile = +^(-=/'trace'?\~&l! ! guard^|/~& ^C\~&+ !,-=/'profile'?\~&! ! ^\~&r std-profile) __switches

#library+

mtv       = {('',~&)^: <>,('',0!)^: <>}  # disassembled representations of nil
reference = ('(reference)',0)^: <>
disint    = (*^ 'compose'?=dl\~& ^V/~&d ~&v; *= 'compose'?=dl/~&v ~&iNC) disassembly ~&c # disassembled intersection

#optimize+

---------------------------------------------------------- operations on pointers --------------------------------------------

all_points = ~&i&& ~&al^?(~&ar?/~&WlrT ~&falPRiNXS,~&ar?\~&aNC ~&farPRNiXS)
distinct   = |=&; ~&tkZ&& ~&hS; cross+~&iiX; ~&EZF; all ~&alrB^& ~&allPrlPB?/~&fabl2R ~&alrPrrPB?/~&fabr2R ~&a; neither ==&
split_p    = ~&a^& ~&alrY?\(&l,&r)! ~&alrB?/~&a ~&al?/~&falPRbiNX ~&farPRbNiX # takes a pointer to an equivalent pointer pair

pointer_reduction = # takes a pointer to an equivalent smaller pointer if possible

~&i&& ~&al^?(
   ~&ar?\~&falPRNX ~&W; -&~&allPrlPB,~&alrPrrPYZ&-^?/~&fabl2RNX -&~&alrPrrPB,~&allPrlPYZ&-?\~&a ~&Nfabr2RX,
   ~&ar?\&! ~&NfarPRX)

embedded_pointer_reduction = # usable only on pointers already inside of a function

^= ~&i&& ~&al^?(
   ~&ar?\~&falPRNX (&l,&r)?=(&!,~&)+ ~&W; -&~&llPrlPB,~&lrPrrPYZ&-^?a/~&fabl2RNX -&~&lrPrrPB,~&llPrlPYZ&-?a\~&a ~&Nfabr2RX,
   ~&ar?\&! ~&NfarPRX)

pointer_composition = # takes p and q to r such that ~r = ~p+~q

embedded_pointer_reduction+ ~&rlX; ~&all^?(
   ~&alr?(~&arl?(~&arr?/~&falrGPW ~&fabl2R,~&arr?/~&fabr2R ~&al),~&\0+ ~&fallPrXPR),
   ~&alr?\~&ar ~&/0+ ~&falrPrXPR)

allcur = +^\~&NrX ~&aaZ^!+ &&~&fafatPJPR+ ~&afahPR;+ ~&l # takes(f,p) to a function equivalent to (all f)+ mapcur p
anycur = +^\~&NrX ~&aa^&+ !|~&fafatPJPR+ ~&afahPR;+ ~&l  # takes(f,p) to a function equivalent to (any f)+ mapcur p

front_points = # returns all argument facing pointers from a function if possible

-&
   ~&a^& cases~&adl\0! {
      {'constant','version','have'}: &!,
      {'compose'}: ~&av&& ~&favz2R,
      {'couple','conditional'}: ~&av&& ~&favPMig,
      {'guard','note','profile'}: ~&av&& ~&favh2R,
      {'field','recur','mapcur'}: -&~&av,~&avtZ,concrete+ ~&a&-},
   all_points*=+ ~&a^& cases~&adl\0! {
      {'compose'}: ~&favz2R,
      {'couple','conditional'}: ~&favPML,
      {'guard','note','profile'}: ~&favh2R,
      {'field','recur','mapcur'}: ~&avhdrPvHo3NC}&-

pointing = # takes (p,f) where f has computable front_points to h such that f+g = h+ ~p+ g

%tsoXTXMk; ^(embedded_pointer_reduction+~&l,~&r); ~&ar^& cases~&ardl\~&ar {
   {'compose'}: ~&vzPiB+ ~&ard2arvy3falrvz2XPRNCTV,
   {'couple','conditional'}: ~&vigPiB+ ~&ard2falrvPDPMV,
   {'guard','note','profile'}: ~&vhPiB+ ~&ard2falrvh2XPRarvt3CV,
   {'field','recur','mapcur'}: (~&r&& ^V/~&l ~&iNV\<>+ ~&/0+ !+ ~&r)^/~&ard -+
      %tMk+ -&~&,$- nleq+ weight~~&-+ embedded_pointer_reduction*+ &^?=ar/~&alNC ~&all?(
         ~&alr?/~&fallPrXlrPrXXPWlrBbhPNCB ~&arlrZB?/~&fabl2R ~&arlrB&& ~&falrGPWliNXSPrNiXSPT,
         ~&alr?\~&alrE&&1! ~&arlZrB?/~&fabr2R ~&arlrB&& ~&falrGPWliNXSPrNiXSPT),
      ^\~&al ~&arvhdrPvHo; ~&a^& ~&al?(~&ar?/~&W ~&falPRlrBlNXrNXXiNXQ,~&ar?\&! ~&farPRlrBNlXNrXXNiXQ)+-}

----------------------------------------------- operations on functions ------------------------------------------------------

(# disassembly takes a program code to a tree of constructors the form %sfXT that can be reassembled by ~&drPvHo, or to nil if
the argument isn't valid program code. The string field is just for documentation. The semantic fields for couples and
compositions are adjusted to allow for more than two subtrees so the tree can be partly flattened that way but still
reassembled according to the same convention. #)

disassembly =

-+
   ~&i&& *^ ^V\~&v ^/~&dl ~&dl?\-+!,~&dr+- case~&dr(
      {conditional: ! ~&hthPXtth2X,compose: ! (+)=>,couple: ! (^)=>},
      ~&v?(~&vt?(~&hthPX;+ ~&dr,~&h;+ ~&dr),!+ ~&dr)),
   ~&a^& ~&al?(
      ~&ar?(
         ~&all?(
            ~&alr?(
               -&~&g,~&V/('conditional',conditional)&-+ <.~&fall2R,~&falr2R,~&farPR>,
               -&~&g,~&V/('couple',couple)&-+ <.~&fall2R,~&farPR>),
            ~&alr?(
               -&~&g,~&V/('guard',guard)&-+ <.~&falr2R,~&farPR>,
               ~&farPJ; ~&al?(
                  ~&ar?(
                     ~&all?(
                        ~&alr?(
                           (~&ar==&)&& %sWI+~&al&& ~&V/('library',library)+ <.~&V\<>+ ~&/0+ ~&al>,
                           ~&ar==&?(
                              -&~&h,~&V/('sort',sort)&-+ <.~&fall2R>,
                              (~&all==&)&& ~&alrZ&& ~&farPJ; -&~&arZ,~&al,~&allZ&-&& -+
                                 -&~&h,~&V/('interact',interact)&-,
                                 <.~&falr2R>+-)),
                        ~&alr?(
                           -|
                              (~&ar==&)&& -&~&h,~&V/('fan',fan)&-+ <.~&falr2R>,
                              ~&arlZrB&& %sWI+~&abr&& ~&V/('have',have)+ <.~&V\<>+ ~&/0+ ~&abr>|-,
                           ~&farPJ; ~&al?(
                              ~&ar?(
                                 -&~&g,~&V/('race',race)&-+ <.~&falPR,~&farPR>,
                                 ~&V/('mapcur',mapcur)+ :\<>+ ~&V\<>+ ~&/0+ ~&al),
                              ~&ar?(
                                 ~&farPJ; ~&al?(
                                    ~&arZ&& ~&falPJ; ~&al?(
                                       -&~&h,~&V/('profile',std-profile)&-+ <.~&falPR,~&V\<>+ ~&/0+ ~&ar>,
                                       ! ~&V/('version',version) <>),
                                    ~&ar?(
                                       ~&farPJ; ~&al&& -&~&h,~&V/('note',note)&-+ <.~&falPR,~&V\<>+ ~&/0+ ~&ar>,
                                       ! ~&V/('weight',weight) <>)),
                                 ! ~&V/('transpose',transpose) <>)))),
                     ~&falPJ; ~&al?(
                        -&~&h,~&V/('reduce',reduce)&-+ <.~&falPR,~&V\<>+ ~&/0+ ~&ar>,
                        ~&ar?(-&~&h,~&V/('map',map)&-+ <.~&farPR>,! ~&V/('member',member) <>))),
                  ~&ar?(
                     ~&farPJ; ~&al?(
                        ~&ar?(
                           -&~&g,~&V/('iterate',iterate)&-+ <.~&falPR,~&farPR>,
                           -&~&h,~&V/('filter',filter)&-+ <.~&falPR>),
                        ~&ar?(-&~&h,~&V/('transfer',transfer)&-+ <.~&farPR>,! ~&V/('reverse',reverse) <>)),
                     ! ~&V/('cat',cat) <>)))),
         ~&falPJ; ~&al?(
            ~&ar?(
               -&~&g,~&V/('compose',compose)&-+ :^/~&falPR :\<>+ ~&farPR,
               ~&falPJ; ~&al?(
                  ~&ar?(
                     -&~&th,~&V/('assign',assign)&-+ :^(~&V\<>+ ~&/0+ ~&al,:\<>+ ~&farPR),
                     -&~&h,~&V/('refer',refer)&-+ :\<>+ ~&falPR),
                  ~&ar?(~&V/('recur',recur)+ :\<>+ ~&V\<>+ ~&/0+ ~&ar,! ~&V/('distribute',distribute) <>))),
            ~&V/('constant',!)+ :\<>+ ~&V\<>+ ~&/0+ ~&ar)),
      ~&ar?(~&V/('field',~)+ :\<>+ ~&V\<>+ ~&/0+ ~&ar,! ~&V/('compare',compare) <>))+-

form = # takes n to a function that takes f to a function like abstract_interpretation/f applicable to an n+1-tuple

-+
   //+ (%gfZXTMk; abstract_disassembly); ~&a^& ~&adr?\~&adl ^V^/!@ad gang@favPM,
   \/(%fgfZXTXMk; abstract_interpretation)+ %gfZXTMk+ ('tuple',~&hthPX)^:@lrNCC=>+ ~&NiX|\NiXNXNVS+ --<&>+ &l!*+ iota+-

optimization = profile\'code optimization' ||~& disassembly; ~&i&& ~&drPvHo+ abstract_optimization

--------------------------------------------- predicates on disassembled functions -------------------------------------------

concrete = profile\'concrete' ~&i&& ~&drPvigPBo&& not *^& !|~&vik ~&dl=='interact'

decomposable = # characteristic of a function that doesn't refer to the same field in its argument more than once

profile\'decomposable' -&
   ~&a^& {'guard','note','profile'}?<adl/~&favihB2R 'compose'?=adl/~&favizB2R concrete+ ~&a,
   distinct+ all_points*=+ ~&a^& -?
      :~&favz2R ~&adl=='compose'&& ~&av,
      :~&favh2R ~&adl-={'guard','note','profile'}&& ~&av,
      ^T\~&favPML &&~&avhdrPvHo3NC ~&adl-= {'field','recur','mapcur'}?-&-

------------------------------------------ binary operations on disassembled functions ---------------------------------------

(# abstract_interpretation takes a function and a disassembled possibly symbolic argument to a dissassembled result in terms
of the argument if possible, which requires that the function being interpreted doesn't deconstruct the symbolic parts of the
argument. If the original function hangs or crashes, abstract interpretation also will, but otherwise if it deconstructs the
subtrees corresponding to the the symbolic parts of the disassembled argument, abstract interpretation will return an empty
result without crashing.  Symbolic parts of the argument are represented as trees with empty &dr semantic fields. The
combinator replacement functions defined in com.fun are used and are assumed not to deconstruct their arguments. An example
of how a partly symbolic disassembled function might arise is shown in lam.fun. #)

abstract_interpretation = symbolic_abstract_interpretation^/disassembly+~&l ~&r

symbolic_abstract_interpretation = # same as above but taking an already disassembled left argument

^(~&l,~&r; *^0 &dl:= :/`"+ ~&dl); (&dl:= ~&dl; `"?=ihB/~&t ~&)*^0+ %sfZXTWMk; ~&alrB^& case~&aldl(
   {'constant': -&~&alv,~&alvh&-}|{
      'refer': ~&alv&& ^R/~&f ^/~&alvh ~&V/('tuple',~&hthPX)+ ~&alvh2rNCC,
      'couple': -&~&alvitB,~&farlvPDrlXS2M; ~&g&& ^V\~& ~&/'tuple'+ ~&tt?\~&hthPX! ! ~&=>&-,
      'compose': ~&alvitB&& %sfZXTMk^arPfaRB/~&f %sfZXTWMk^/~&alvh ~&alvtt?/~&faldvtPVPrXPR %sfZXTMk+ ~&falvth3rXPR,
      'conditional': -&
         ~&alv; -&~&,~&t,~&tt,~&tttZ&-,
         -+concrete+~&r&& ~&rdrPvHo?/~&lfalvth3rXPR ~&lfalvtth4rXPR,^/~& ^R/~&f %sfOXTWMk+ ~&alvh2rX+-&-,
      'recur': %osfZXTWXMk; -+
         ~&aivB&& -&
            ~&adl=='tuple'!| ~&adr-={~&,~&=>,~&hthPX},
            ^R/~&f %sfZXTWMk^\~&a ~&avh; *^0 ^V\~&v ~&d+ -&~&vZ,~&dr-={0!,~&}&-?\~& &dl:= 0!&-,
         ^J/~&f %sfXTMk^R/~&f %sfXTWMk^\~&ar ~&V/('field',~+~&h)+ ~&alv+-,
      'field': -&~&alv,concrete+~&alvh&-&& ~&alvhdrPvHo3rX; ~&l&& %tsfZXTXCRk refer ~&all?(
         ~&alr?/(%fOtsfZXTXXMk; ~&fallPrXlrPrXXPWlrBiB; %sfOZXTWMk; ~&i&& ~&V/('tuple',~&hthPX)+ ~&lrNCC) -|
            -&~&ardl=='tuple'!| ~&ardr-={~&,~&=>,~&hthPX},~&arv,~&fallPrvh2XPR&-,
            %otsfZXTXXMk; -&concrete+~&ar,~&iNV+ ~&NiX+ !+ ^H/~+~&al ~&ardrPvHo&-|-,
         ~&alr?\~&ar -|
            -&~&ardr==~&,~&arv,~&falrPrdvtPVPXPR&-,
            -&~&ardl=='tuple'!| ~&ardr-={~&=>,~&hthPX},~&arvitB&-&& ~&arvtt?/~&falrPrdvtPVPXPR ~&falrPrvth3XPR,
            %otsfZXTXXMk; -&concrete+~&ar,~&iNV+ ~&NiX+ !+ ^H/~+~&al ~&ardrPvHo&-|-),
      'tuple': mtv?<alvh/(^R/~&f ^\~&ar ~&V/('field',~&NhX)+ ~&alvt) ~&alvhdl=='tuple'&& mtv?<alvth(
         mtv?<alvhvh/(^R/~&f ^\~&ar ~&V/('constant',~&NhXNX)+ ~&alvhvt) mtv?<alvhvth(
            ~&alvhvhdl=='tuple'&& ^R/~&f ^\~&ar mtv?<alvhvhvh(
               ~&V/('recur',~&NhXNXNX)+ ~&alvhvhvt,
               ~&V/('refer',~&hNXNXNX)+ ~&alvhvhvhNC),
            ^R/~&f ^\~&ar ~&V/('compose',~&hthPXNX)+ ~&alvhv),
         ^R/~&f ^\~&ar mtv?<alvhvth(
            ~&V/('couple',~&hNXthPX)+ ~&alvhvh3vtPC,
            ~&V/('conditional',~&hthPXtth2X)+ ~&alvhvh3vhvth4vtPCC))},
   {~&=>,~&hthPX}?<aldr/(^R/~&f ^\~&ar ^V\~&alv ~&/'tuple'+ ~&aldr) -&~&alvZ,concrete+~&al&-?(
      -+~&lal2rEZ&& ~&lfPrlar2XR,^/~& disassembly+ ~&aldrPvHo+-,
      ||-&~&a; both concrete,~&iNV+ ~&NiX+ !+ ~&HabdrPvHo2O&- -+
         ~&r&& ^R/~&lf ^\~&lar ~&lalv?\disassembly+~&r ^R/~&lf ^(
            disassembly+~&r,
            ~&lalvt?\~&lalvh ~&V/('tuple',~&=>)+ ~&lalv),
         ^/~& ~&aldl; -:0! ~&n~<{'refer','recur'}*~ gint~&EbnPO -|%QI,~&|-~~/com cor+-))

decomposition = # takes a pair of composed functions to a single equivalent function assuming the left is decomposable

refer cases~&aldl\0! (* ^A/~&n ("s","f"). profile/"f" (~&z "s")--' decomposition') {
   {'constant','have'}: ~&al,
   {'couple','conditional'}: ~&ald2farlvPDrlXS2MVvigPiB,
   {'compose'}: ~&alvitB&& ^rzPlrVB/~&ald ^lrNCT/~&alvy ~&falvz2rXPR,
   {'guard','note','profile'}: ~&alvitB&& ~&ald2falvh2rXPRalvt3CVvhPiB,
   {'map','fan'}: ~&Eabdl3O&& ^V/~&ald ~&VNC/('compose',(+)=>)+ ~&Tabv2O,
   {'filter'}: ~&ardl=='filter'&& ^V/~&ald ~&VNC/('conditional',~&hthPXtth2X)+ <.~&arvh,~&alvh,! disassembly 0!>,
   {'transpose'}: ~&ardl=='transpose'&& ! disassembly ~&,
   {'reverse'}: -|
      ~&ardl=='reverse'&& ! disassembly ~&,
      -&~&ardl=='couple',~&arvizB== disassembly 0!,~&ardvyxPzNCTPV&-|-,
   {'member'}: -&
      (~&ar; -&~&dl=='couple',~&v,~&vt,~&vttZ&-)&& ~&arvth; ~&dl=='constant'&& ~&vh; -!
         -&~&dl=='tuple',~&v,~&vt,~&vttZ,concrete+~&vth,~&vthdrPvHoZ&-,
         concrete&& ~&drPvHoitZB!-,
      ~&V/('compose',(+)=>)+ ~&lrNCC/(disassembly ==)+ ~&ar+ &arvt:= ~&VNC/('!+~&hlrh',~&hNlrh2XNX)+ ~&arvt&-,
   {'field'}: -+
      ~&i&& ~&ardl=='field'^?/(concrete+~&ar&& &arvhdr:=ar !+ pointer_composition+ ~&alrdrPvHor2X) ?(
         -&~&ardl=='constant',concrete+~&ar,indexable^/~&al ~&ardrPvHolr&-,
         ~&/(%tsfOXTXJMk; &arvhdr:=ar !+ ^H\~&ardrPvHolr ~+ ~&al) ~&all?(
            ~&alr?(
               ~&rigPlrVB/('couple',(^)=>)+ ~&fallPrXlrPrXXPWlrNCC,
               -&~&ardl=='couple',~&arv,~&arvt; all concrete,~&fallPrvh2XPR&-),
            ~&alr?\~&ar -&~&ardl=='couple',~&arv,concrete+~&arvh,~&arvt,~&arvtt?/~&falrPrdvtPVPXPR ~&falrPrvth3XPR&-)),
      concrete+~&al&& ~&aldrPvHor2rX+-,
   {'recur','mapcur'}: concrete+~&al&& -|
      (~&r&& ~&l+ &lvhdr:= !+ ~&r)^/~&al -+
         ~&ardl=='field'^?/-&concrete+~&ar,pointer_composition+~&alrdrPvHor2X&- ~&all?(
            -&~&alrZ,~&ardl=='couple',~&arv,~&fallPrvh2XPR&-,
            -&~&alr,~&ardl=='couple',~&arv,~&arvt,~&arvtt?/~&falrPrdvtPVPXPR ~&falrPrvth3XPR&-),
         ~&alvhdrPvHo3rX+-,
      (~&al== disassembly ~&R)&& -| 
         ~&ardl=='couple'&& -&
            -&~&arv,~&arvt,~&arvh; -&~&dl=='constant',~&v&-&-,
            -&not *^0 ~&vik!| ==reference,~&i&-^R/~&f ^/abstract_disassembly+~&arvhvh &arvh:=ar reference!&-,
         ~&arPfaRB^J/~&f ^/~&al -&
            ~&ardl=='constant'&& concrete+ ~&ar,
            ~&ardrPvHoNH; ~&i&& ~&V/('couple',(^)=>)+ ~&lrNCC+ ~~ ~&V/('constant',!+~&h)+ ~&iNVNC+ ~&/''+ !&-|-|-}

left_residue = # takes (f,g+f) to g if possible

profile\'left residue' ~&ar^& ~&alrE?/(! disassembly ~&) cases~&ardl\0! {
   {'constant'}: ~&ar,
   {'couple','conditional'}: ~&vigPiB+ ~&ard2falrvPDPMV,
   {'compose'}: ~&alrvz2E?(~&arvtt?/~&ardvyPV ~&arvh,^rzPlrVB/~&ard ^lrNCT/~&arvy ~&falrvz2XPR),
   {'field'}: -&~&aldl=='field',~&a; both concrete&-&& -+
      ~&i&& ~&V/('field',~&NhX)+ ~&NiXNVNC+ !,
      ~&abdrPvHor; ~&al^& ~&allrY?\~&ar ~&arllrBZPB&& ~&all?/~&fabl2R ~&fabr2R+-}

right_residue = # takes (g,g+f) to f if possible

~&ar^& ~&alrE?/(! disassembly ~&) case~&ardl\0! {
   'conditional': ~&av&& ~&vigPiB+ ~&ard2arvh3falrvt2DPMCV,
   'compose': ~&alrvh2E?(~&arvtt?/~&ardvtPV ~&arvz,^rhPlrVB/~&ard :^/~&falrvh2XPR ~&arvt)}

unused_result_preemption = # takes a pair (f,g) to a function equivalent to f+g with parts of g not needed by f removed

concrete+~&r&& -&~=,~&r,nleq+ weight~~+ ~&rlX,('compose',(+)=>)^:+ ~&rlrNCC&-^/~& (~&r&& ^liB\~&rr pointing+ ~&rlPlX)^/~&l -+
   %tsoXTXCk %tsoXTXMk+ ~&al^& &?=al/~&a -&~&dl=='couple',~&v,~&vt&-?ar\~&NNXarPX ~&all?(
      ~&alr?\~&fallPrvh2XPRlNXrX ~&fallPrXlrPrXXPW; ^/~&bl ~&V/('couple',(^)=>)+ ~&lrPrrPNCC,
      ~&falrPrvtt2dvtPVvth2QPXPRNlXrX),
   ^\~&r %tMk+ ~&ilrYiBB+ embedded_pointer_reduction+ ~&=>+ %tLMk+ ~&x+ -<&+ ~&l; front_points; %tLMk; ~&s; ^= -+
      %tLLMk; ~&t!=; ^T\~&rhS ~&l; * ~&a~=&^&~&afaWB+ $- nleq+ weight~~,
      |= ~&alrB^& -!~&a-={(&l,&r),(&r,&l)},~&al==&,~&ar==&,~&allPrlPBlrPrrPYZBPfabl2RB,~&arlPrrPBllPrlPYZBPfabr2RB!-+-+-

------------------------------ semantics altering transformations on disassembled functions ----------------------------------

left_multicompositor = # takes g+f to g if possible and g occurs more than once and isn't a deconstructor

^EZrB/~& -&~&g,~&itB,all_same~&,~&h&-+ refer case~&adl\~&aNC {
   'field': &!,
   'compose': ~&av&& ~&favh2R,
   'conditional': ||~&aNC ~&av&& ~&favt2ML; ~&g&& &&~& all_same~&,
   'guard': -&~&av,~&avh== disassembly compose(compare,constant 0)&-?/0! ~&aNC}

right_multicompositor = # takes g+f to f if possible and f occurs more than once and isn't a deconstructor

^EZrB/~& -&~&g,~&itB,all_same~&,~&h&-+ refer cases~&adl\~&aNC {
   {'field'}: &!,
   {'constant','have'}: 0!,
   {'compose'}: ~&av&& ~&favz2R,
   {'couple','conditional'}: ||~&aNC ~&favPML; ~&g&& &&~& all_same~&}

right_compositor = # same as above except f doesn't have to occur more than once

^EZrB/~& -&~&g,all_same~&,~&ihB&-+ refer cases~&adl\~&aNC {
   {'constant','have'}: 0!,
   {'compose'}: ~&av&& ~&favz2R,
   {'couple','conditional'}: ||~&aNC ~&favPML; ~&g&& &&~&ihNCB all_same~&}

predicate_transform = # optimizations applicable to functions whose result is only tested for non-emptiness

~&a^& -|
   -&~&adl=='map',! disassembly ~&i&-,
   -&~&a== disint,! disassembly intersecting&-,
   -&~&adl=='compose',~&av=] ~&v disint&-&& ~&V/('compose',(+)=>)+ -+
      //: disassembly intersecting,
      ~&av; //skip length ~&v disint+-,
   (~&a; -&~&dl=='conditional',~&v,~&vt,~&vtt,~&vtttZ&-)&& -|
      ~&a; ~&vhthPE&& &vth:= ! disassembly &!,
      ~&a; ~&vhtth2E&& &vtth:= ! disassembly 0!,
      ~&a; -&~&vth== disassembly &!,~&vtth== disassembly 0!,~&vh&-,
      ^vtPiB/~&ad :^/~&avh ~&avt2favt2Mp; ~&hrPthr2YrlYSB|-,
   -&~&adl-={'compose','guard','note','profile'},~&av,~&adPfavh2Ravt2CVvhPiB&-|-

conjoiner = # takes all(p) to p if possible

~&i&& -&~&dl=='refer',~&v&-&& ~&vh; ~&i&& -&
   -&~&dl=='conditional',~&v,~&vt,~&vtt,~&vtttZ&-,
   ~&vh== disassembly ~&a,
   ~&vtth== disassembly &!,
   ~&vth; -&~&dl=='conditional',~&v,~&vt,~&vtt,~&vtttZ&-&& -+
      //left_residue disassembly ~&ah,
      -&~&vth== disassembly ~&fatPR,~&vtth== disassembly 0!,~&vh&-|| -&
         -&~&vtth== disassembly ~&fatPR,~&vth== disassembly 0!&-,
         ~&V/('conditional',~&hthPXtth2X)+ :\(disassembly* <0!,&!>)+ ~&vh&-+-&-

disjoiner = # takes any(p) to p if possible

~&i&& -&~&dl=='refer',~&v&-&& ~&vh; ~&i&& -&
   -&~&dl=='conditional',~&v,~&vt,~&vtt,~&vtttZ&-,
   ~&vh== disassembly ~&a,
   ~&vtth== disassembly 0!,
   ~&vth; -&~&dl=='conditional',~&v,~&vt,~&vtt,~&vtttZ&-&& -+
      //left_residue disassembly ~&ah,
      -&~&vth== disassembly &!,~&vtth== disassembly ~&fatPR,~&vh&-|| -&
         -&~&vtth== disassembly &!,~&vth== disassembly ~&fatPR&-,
         ~&V/('conditional',~&hthPXtth2X)+ :\(disassembly* <0!,&!>)+ ~&vh&-+-&-

complement = # takes a disassembled program representing a predicate to the complement thereof if found

~&a^& -|
   (~&i&& form0 all)^R/~&f disjoiner+ ~&a,
   (~&i&& form0 any)^R/~&f conjoiner+ ~&a,
   -&~&adl=='compose',~&av,~&vhPiB+ ~&adPfavh2Ravt2CV&-,
   -&~&adl=='constant',~&av,concrete+~&a,~&a+ &avhdr:= !+ ~&avhdrPvHo3Z&-,
   (~&a; -&~&dl=='conditional',~&v,~&vt,~&vtt,~&vtttZ&-)&& -|
      ~&a; -&~&vth== disassembly 0!,~&vtth== disassembly &!,~&vh&-,
      ^rtPigPlrVB/~&ad :^/~&avh ~&favt2M|-|-

------------------------------ semantics preserving transformations on disassembled functions --------------------------------

decoupling = # simplifies couples appearing in a disassembled program if possible

*^ ||~& ~&dl=='couple'&& -|
   ^rrtPlrVrhPQB/~&d ~&v; -|
      ~&dl=='field'~-; ~&ritB&& ^lrNCT/~&l ~&r; ~&h+ &hv:= ~&VNC/('tuple',~&=>)+ * ~&V/('~&hr',~&hr)+ ~&iNC,
      ~&dl=='constant'~-; ~&ritB&& ^lrNCT/~&l ~&r; ~&h+ &hv:= ~&VNC/('tuple',~&=>)+ * ~&V/('~&hlr',~&hlr)+ ~&iNC|-,
   ~&vx; ^(~&,right_compositor)*; -+
      ~&ritB&& ~&rrk&& (~&r; not all ~&rZ!| ~&r==disassembly~&)&& %soXTWLWMk; -+
         ~&rigPrtPlrVrhPQB/('couple',(^)=>),
         ^T/~&llS -+
            //~&rigPlrVBNC ~&/'compose' (+)=>,
            %soXTWLWCk :^\~&rrFhrNC ~&rigPlrVB/('couple',(^)=>)+ left_residue*+ ~&rrlXS+-+-,
      %soXTWLWMk+ ~&rxPlX+ ~&NiX; ^= ?(
         -&~&r,~&rh; ~&r!| ~&dl=='constant',-!~&lZ,~&rhldl=='constant',~&Ebhr2O!-&-,
         ~&/~&rhPlCrtPX ~&)+-|-

deconditioning = # simplifies conditional forms appearing in disassembled programs if possible

*^ ||~& -&~&dl=='conditional',~&v,~&vt,~&vtt,~&vtttZ&-&& -|
   -&~&vh== disassembly 0!,~&vtth&-,
   ~&vhPiB+ &vh:= predicate_transform+ ~&vh,
   &&~&vth -!
      ~&vththPX; ==!| -&~&Ebdl2O,both concrete,==+ ~&bdrPvHo&-,
      ~&vh; -&~&dl=='constant',concrete,~&iNH+ ~&drPvHo&-!-,
   -&~&vth== disassembly 0!,~&vtth== disassembly &!,complement+ ~&vh&-,
   -&~&vth; -&~&dl=='conditional',~&v,~&vt,~&vtt,~&vtttZ&-,~&vhPvthvh4E,&vth:= ~&vthvth&-,
   ^rhPlrVB/~&d <.~&vh; ^(complement,~&); &&~&l ~&l&& weight~~; ~&EZ&& nleq,~&vtth,~&vth>,
   (@vhPvtth3X both -&~&dl=='conditional',~&v,~&vt,~&vtt,~&vtttZ&-)&& @v -&
      -&~&hvtth== disassembly 0!,^E/~&hvh ~&tthvh,^E/~&hvh ~&tthvth,^E/~&hvth ~&tthvtth&-,
      ^V/~&hd <.~&hvh,^V/~&hd <.~&hvth,~&th,~&hvh>,~&hvth>&-,
   ~&v; ^(right_compositor,~&)*; -&~&lF; -&all_same~&l,~&,~&hl~= disassembly~&i&-,~&lZF; all ~&rdl=='constant'&-&& -+
      //~&vigPlrVB ~&/'compose' (+)=>,
      :^\~&lFhlNC ~&vigPlrVB/('conditional',~&hthPXtth2X)+ left_residue*+-|-

abstract_disassembly = # rearranges an already disassembled tree representing a function to convert tuples to combinators

%sgUoXTMk; -+
   ~&E^?ar/~&arl ~&YlrEB?arbdl/~&arld3falrlvPrvPpPDPMV ~&arldl?/~&alrlvhdrPvHo4H -+
      ~&arlrE^?/(~&NiXNV+ !@arl) ~&arllPrlPB?(
         ~&arlrPrrPB?(('tuple',~&hthPX)^:@falrbl2rbr2XGPWlrNCC,('~&hNX',~&hNX)^:@falrbl2XPRNC),
         ~&arlrPrrPB?\~&alrllr3H ('~&NhX',~&NhX)^:@falrbr2XPRNC),
      ~&alrbdrPvHo2X+-,
   %fsoXTWXMk^/=:@rrlXS -+
      %soXTWMk+ ~~ disassembly+ ~&drPvHo+ ~&ar^& ~&ardr?/~&ard2falrvPDPMV ~&alrH,
      %fsoXTXWMk+ ~&brlX^G/~&l @r -:~~+ %sfZXTWLWMk^(* ^|/~& ~&NiXNV+ !+ !,* ^|/~& ~&NiXNV+ !+ (~)+ ~&NiX)+-,
   ^/~& %sgUoXTtXLMk+ ~&iiK22pB@aadr2favPMLPaNCQNqs+-

(# abstract_optimization takes a disassembled program to a smaller or faster equivalent one if found. Most of the code
generated by the compiler funnels through here, so modifying it ineptly could lobotomize the compiler within one or two
generations of bootstrapping. #)

abstract_optimization =

~&i&& glimit -++- (* ("n","f"). profile/"f" 'optimization form '--(~&h %nP "n")) num <
   *^ ||~& -&~&dl=='map',~&v,~&vh== disassembly ~&,~&vh&-,
   *^ ||~& -&~&dl-={'filter','iterate'},~&v,~&vhPiB+ &vh:= predicate_transform+ ~&vh&-,
   *^ ||~& -&~&dl=='fan',~&v,~&vhdl== 'field',~&vhvitZB,^V/~&vhd ~&VNC/('~&hiNXNiXX',~&hiNXNiXX)+ ~&vhv&-,
   *^ -&~&dl-={'field','assign','recur','mapcur'},concrete&-?\~& &vh:= ~&NiXNV+ !+ embedded_pointer_reduction+ ~&vhdrPvHo,
   *^ ||~& -&~&dl=='sort',~&v&-&& (~&vhPiB+ &vh:= predicate_transform+ ~&vh)|| -+
      ~&r&& ~&V/('compose',(+)=>)+ ~&lrNCC/(disassembly ~&x)+ ~&ldPrNCV,
      ^/~& ~&vh; ^(complement,~&); &&~&l ~&l&& weight~~; ~&EZ&& nleq+-,
   deconditioning+ *^ ||~& ^(left_multicompositor,~&); ~&vth2iB+ ~&V/('compose',(+)=>)+ <.~&l,right_residue>,
   decoupling+ *^ 'couple'?=dl\~& ^V/~&d ~&v; ||~& -&~&,~&t,~&ttZ,~&thdl=='couple',~&hthv2C&-,
   *^ ||~& ~&dl=='compose'&& -&~&,~&t,~&tt&-^?av\~&a -|
      (~&avh== disassembly ~&R)&& ~&a; -+
         ~&r&& decomposition,
         ^/~&vh (~&i&& decoupling)+ decomposition^/~&vth ~&vttt?/~&dvtt2V ~&vtth+-,
      ~&avh2fadvtPVPRX; 'compose'?=rdl/~&rdPlrvPCV ~&V/('compose',(+)=>)+ ~&lrNCC|-,
   *^ 'compose'?=dl\~& ^rtPlrVrhPQ/~&d ~&v; ~&aitB^?\~&a ^rlfPrlatt3CRlahPfatPRCPQ/~& ~&ahthPX; -|
      -&both ~&dl=='sort',==,~&l&-,
      -&~&rdl=='couple',~&rvitB,unused_result_preemption&-,
      profile\'identity form' &&~&l (~&r== disassembly ~&)!| ~&r; -&~&dl=='field',concrete,~&drPvHo== ~&i&-,
      -&~&rdl=='map',~&rv; ~&itZB&& ~&hdl=='field'&-&& -&
         -&~&ldl=='couple',~&lv; ~&itB&& all -&~&dl=='map',~&v,~&vhdl=='field'&-&-,
         ^V/~&ld ~&rvh2lvPD; * ^lrNCV/~&rd ('compose',(+)=>)^:+ ~&rvPlNCT&-,
      (~&r== disassembly ~&?(~&,&!))&& -&
         ~&l; -&~&dl=='conditional',~&v,~&vt,~&vtt,~&vtttZ,~&vh== disassembly ~&i&-,
         ~&V/('compose',(+)=>)+ ~&lvth3rNCC&-,
      (~&l== disassembly ~&l?(~&l,~&r))&& -&
         ~&r; -&~&dl=='couple',~&v,~&vt,~&vtt!| ~&vth~= disassembly ~&i&-,
         ~&V/('compose',(+)=>)+ <.
            &lvtth:=l ~&V/('compose',(+)=>)+ <.~&rvtt?/~&rdvtPV ~&rvth,! disassembly ~&r>,
            &rvt:=r ! ~&iNC disassembly ~&>&-,
      (~&l== disassembly ~&r?(~&r,~&l))&& -&
         ~&r; -&~&dl=='couple',~&v,~&vt,~&vtt!| ~&vth~= disassembly ~&i&-,
         ~&V/('compose',(+)=>)+ <.
            &lvtth:=l ~&V/('compose',(+)=>)+ <.~&rvh,! disassembly ~&l>,
            &rvh:=r ! disassembly ~&>&-,
      -||- ~&H\<(conjoiner,all,allcur,&),(disjoiner,any,anycur,0)> * ("j","a","c","k"). ^("j"@l,~&); ~&l&& -|
         &&~&rl ~&rrdl-={'sort','reverse'}!| ~&rr== ~&vh disassembly ~&s,
         ~&lrrPX; -|
            -&~&rdl=='map',~&rv,~&rvh,(form0 "a")+ ~&V/('compose',(+)=>)+ ~&lrvh2NCC&-,
            -&~&rdl=='mapcur',concrete+ ~&r,(~&r&& form2 "c")^/~&l split_p+~&rdrPvHorrl; ~&i&& ~~ ~&NiXNV+ !&-,
            -&~&rdl=='filter',~&rv,~&rvh&-&& -+
               (form0 "a")+ ~&V/('conditional',~&hthPXtth2X),
               <.~&rvh,~&l,! disassembly "k"!>+-|-|-,
      decomposable?l/decomposition ~&rdl=='field'&& -+
         &&~&l -!nleq+ weight~~,^(~&l,~&V/('compose',(+)=>)+ ~&rlrNCC); (both concrete)&& nleq+ weight~~+ ~&bdrPvHo!-,
         ^\~& decomposition+-|-,
   *^ 'compose'?=dl\~& ^V/~&d ~&v; *= 'compose'?=dl/~&v ~&iNC>
