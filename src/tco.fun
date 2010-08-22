
#import std
#import nat
#import ext
#import opt
#import tag

#comment -[
This module contains the tables specifying type constructors used
in type expressions.

Copyright (C) 2007-2010 Dennis Furey]-

profile = +^(-=/'trace'?\~&l! ! guard^|/~& ^C\~&+ !,-=/'profile'?\~&! ! ^\~&r std-profile) __switches

# nugatory constants defined here to avoid needing a virtual machine with math libraries to build the compiler

fzero     = -{wgfzg]ftVjBg=f]fB]\}-
fnzero    = -{wgfzg]ftVjBg=g]g]\<}-
cxzero    = -{wgfzg]ftVjBg]ftVjBg]ftVjBg]ftVhBfBdVB<}-
mpfr_zero = -{{gxbuBjBgCfbBe]e]b=bUbUbUbUbUbUbU`<}-
mptwenty  = -{{vuZtLg`gBjBdC<\}-
mpten     = -{{vuVtNjNhVtV\X><}-

#library+
#export+

primitive_types =

(* ^A(~mnemonic,~&)+ (microcode,printer,recognizer):= ~&/~&rhPNVlCrtPX+ (~&r;)^~/~printer ~recognizer) <
   type_constructor[
      mnemonic: 't',
      recognizer: &!,
      help: 'push primitive transparent type',
      generator: ! &?=/&! nleq/25?(25!,~&); rand_raw,
      printer: ~&iNC+ ~&a^?\'0'! &?=a/'&'! :/`(+ --')'+ ~&W; ^T/~&l :/`,+ ~&r],
   type_constructor[
      mnemonic: 'b',
      recognizer: -={0,&},
      initializer: ! ~&i&& &!,
      generator: ! -!==&,~&i&& 50%~!-,
      help: 'push primitive boolean type',
      printer: <.~&?/'true'! 'false'!>],
   type_constructor[
      mnemonic: 'e',
      recognizer: length==8&& all %cI,
      initializer: ! ~&?/~& ! fzero,
      help: 'push primitive floating point type',
      reader: ~&L; math..strtod,
      generator: ! math..sub\10.0+ mtwist..u_cont+ 20.0!,
      printer: <.math..asprintf/'%0.6e'>],
   type_constructor[
      mnemonic: 'E',
      recognizer: -&
         -&~&,~&l,~&ll; %nI&& ~<iota2,~&lr; -&~&,%bI+ ~&l,%nI+ ~&r&-,~&r,~&rl; -&~&,%bI+ ~&l,%nI+ ~&r&-,~&rr; all %cI&-,
         nleq^\length+~&rr ~&itB+ ~&itB+ ~&itB+ ~&ll&-,
      initializer: ! ~&?/~& ! mpfr_zero,
      help: 'push primitive arbitrary precision floating point type',
      generator: ! mpfr..sub\mpten+ mpfr..mul/mptwenty+ mpfr..urandomb+ 160!,
      reader: ~&L; (#-&mpfr..equal_p,~=&-^(~&,mpfr..shrink\1)->(mpfr..shrink\1)+#) mpfr..str2mp^\~& -+
         nleq?\160! quotient\3+ ~&r,                               # 160 bit precision unless input is longer
         ~&/480+ tenfold+ length+ -='0123456789'*~+ ~&l+ ~=`E-~+-,
      printer: ~&iNC+ mpfr..mp2str; ~=`.-~; ^|T/~& ~=`E-~; ^|T\~& take/7],
   type_constructor[
      mnemonic: 'j',
      recognizer: length==16&& all %cI,
      initializer: ! ~&?/~& ! cxzero,
      help: 'push primitive complex floating point type',
      generator: ! complex..create+ (math..sub\10.)~~+ mtwist..u_cont~~+ ! ~&iiX 20.0,
      reader: @L complex..create+ -='ij'*~?(
        ~<'ij'*~; rlc-!~&r~<'+-',~&l-='eE'!-; ~~ththPXNhXQ ~&?/math..strtod fzero!,
        ~&\0.+ math..strtod),
      printer: -+
         ^TNC(~&rl,--'j'+ ~&l?\~&rr :/`++ ~&rr)^(
            -&math..islessequal/fzero,~=fnzero&-+ ~&r,
            ~~ math..asprintf/'%0.3e'),
         ^/complex..creal complex..cimag+-],
   type_constructor[
      mnemonic: 'a',
      initializer: ! ~&?/~& 0:0!,
      generator: ! ~=(&)&& mtwist..u_path+ ~&iNX+ ~&||1!,
      recognizer: ~&i&& ~&aZ^! -!~&alZ&& ~&farPR,~&arZ&& ~&falPR!-,
      printer: ~&?\<'bad address'>!% ^TNC(~&l,:/`:+ ~&r)+ (~~ ~&h+ %nP)^(
         predecessor+ weight,
         ~&x+ skipwhile~&Z+ ~&ar^?(:/&+ ~&farPR,~&al&& :/0+ ~&falPR)),
      help: 'push primitive address type'],
   type_constructor[
      mnemonic: 's',
      generator: ! rand_str,
      recognizer: all -=(take/95 skip/32 characters),
      help: 'push primitive character string type',
      reader: ~&L; ~&i&& ~&h=='`'?\<'bad string'>!% ~&t; ~&a^?\<'bad string'>!% ~&ah==`'?(
         ~&at&& ~&ahPfatt2RC,
         ~&ahPfatPRC),
      printer: ~&iNC+ :/`'+ --''''+ *= `'?=/<.~&,~&> ~&iNC],
   type_constructor[
      mnemonic: 'o',
      recognizer: &!,
      generator: ! rand_raw,
      help: 'push primitive opaque type',
      printer: ~&iNC+ --'%oi&'+ ~&h+ %nP+ weight],
   type_constructor[
      mnemonic: 'f',
      generator: ! rand_fun,
      initializer: ! ~&?/~& <'empty function'>!%,
      recognizer: disassembly,
      printer: -&~&,disassembly&-; ~&?\<'not a function'>!% ~&adl^?(
         ~&av?\~&adlNC -?
            -&~&adl-={'compose','couple'},~&avtt&-: ~&fadvhPdvtPVNCVPR, 
            ~&adl-={'have','library'}: ('('?<rhh/~&lrhPTrtPC :^\~&rt ^T/~&l :/` + ~&rh)^/~&adl ~&avhdrPvH; %sWI?/%sWP %xP,
            ~&adl-={'field','recur','mapcur'}: ('(<-'?<rhh/~&lrhPTrtPC :^\~&rt ^T/~&l :/` + ~&rh)^/~&adl %tP+ ~&avhdrPvH,
            (-&~&adl=='assign',~&av&-?\~&adl2favPMX ^/~&adl :^\~&favt2M %tP+ ~&avhdrPvH); ~&rt?(
               (~&r; ~&tZg&& ~&itZB!| short+ ~&hSL)?(
                  ^TNC/~&l ~&r; :/`(+ --')'+ mat`,+ ~&hS,
                  :^/(--'('+ ~&l) ~&r; (* '   '--)^T(~&y; *= ^lrNCT/~&y --','+ ~&z,~&z; ^lrNCT/~&y --')'+ ~&z)),
            ~&lrhPX; '('?<rhh/~&lrhPTrtPC :^\~&rt ^T/~&l :/` + ~&rh)?-,
         ~&adrPvH; -|
            -|%nI&& %nP,&&<'&'>! ==&,%sI&& %sP,%nLI&& %nLP,%sLI&& %sLP,%sI+~&iNC&& %cP,%zI&& %zP,%sWI&& %sWP|-,
            -|%eI&& %eP,%eLI&& %eLP,%eWI&& %eWP|-,
            -|%jI&& %jP,%jLI&& %jLP,%jWI&& %jWP|-,
            -|%EI&& %EP,%ELI&& %ELP,%EWI&& %EWP|-,
            -|(nleq\512+ weight)&& %gP,%xP|-|-),
      help: 'push primitive function type'],
   type_constructor[
      mnemonic: 'q',
      precognizer: _type_constructor%TLqoUXMk; @r ~&i&& %zI@l&& @r ~&i&& %nI,
      generator: ! &?=/&! leql/512?(512!,~&); rand_rat,
      recognizer: -&~&irB,%zI@l,%nI@r,~&l?(==1+ gcd^|\~& ~&z?/~& ~&y,~&r==1)&-,
      initializer: ! guard\<'irrational'>! ~&?\(0,1)! -+
         ^|rlPlTrrPX/~& nat-quotient^~brlXPlrGO/gcd ~&,
         ~&ZzY?l/~&NiX ~&NNXlyPrXX+-,
      help: 'push primitive rational type',
      reader: guard\<'irrational'>! @L `-?=h(~&lrtPX/<0>,~&NiX); -+
         ^|rlPlTrrPX/~& nat-quotient^~brlXPlrGO/gcd ~&,
         ^|/~& %np~~biNC+ -=/`/?(~&lrtPX+ ~=`/-~,~&\'1')+-,
      printer: ^|TNC(~&,:/`/)+ ~&bh+ %zP~~],
   type_constructor[
      mnemonic: 'n',
      recognizer: ~&iZ!| ~&z&& all -={0,&},
      generator: ! rand_nat,
      reader: ~&L; -+
         ~&NiX; ~&r->l ^\~&rt sum^/~&rh ~&l; ~&i&& sum^/~&NiC <0,0,0>--,
         `+?=ihB(~&t,~&); * '0123456789'?<\<'non-numeric character'>!% '0123456789'-$iota10+-,
      printer: ~&iNC+ ~&H\~&(~&a^?\<1>! 9?=ah/~&NfatPRC :^\~&at ~&ah; -: ~&ytp iota 10) "f". -+
         ||'0'! ~&x+ * iota10-$'0123456789',
         ~&xNX; ~&l->r (~&lh?\~&ltPrX ^/~&lt "f"+ ~&r)^/~&l ~&r; ~&a^& :^(
            ~&ah; iota10-$<0,2,4,6,8,0,2,4,6,8>,
            iota5?<ah/~&fatPR "f"+ ~&fatPR)+-,
      help: 'push primitive natural number type'],
   type_constructor[
      mnemonic: 'z',
      recognizer: ~&iZ!| ~&z?/%nI @y ~&i&& %nI,
      generator: ! ~=(&)&& -&~&,50%~&-?(~&\<0>+ predecessor,~&\<>); ^|T/rand_nat ~&,
      reader: `-?=ihihBPB(@htPtC ~&\<0>,~&\<>); ^|rlrTlQ\~& %np,
      printer: ~&?\<'0'>! ~&z?(~&/'',@y ~&/'-'); ^|lrhPTrtPC/~& %nP,
      help: 'push primitive signed integer type'],
   type_constructor[
      mnemonic: 'v',
      recognizer: -&~&,~&l-={0,&},@r ~&Z!| ~&z&& all \/-= iota10&-,
      generator: ! rand_bcd,
      reader: @L `-?=h(~&NNXtX,~&NiX); `_?=z(~&y,~&); ^|rlBrX/~& ~&ihZB->x~&t+ * digits-$iota10,
      printer: ^|TNC(~&i&& '-'!,--'_'+ ||'0'! *x iota10-$digits),
      help: 'push primitive signed BCD integer type'],
   type_constructor[
      mnemonic: 'x',
      recognizer: &!,
      generator: ! rand_raw,
      reader: (~&L; ~=` *~; ||<'bad raw format'>!% -&~&,~&h==`-,~&t,~&th==`{,~&yz==`},~&z==`-,~&tt,~&tty,~&ttyy&-); -+
         (any ~&)&& -+
            ~&at^& ^W/~&f (~~ takewhile ~&)+ ~&lSrSX+ ~&a; ~&al^?\~&NarPD -+
               :^/~&al ^R/~&f ^\~&ar ~&all; ~&iiT+ ~&F,
               ^J/~&f ^\~&art ~&alrhPX; ~&al^?\~&NarPC ^lrlPCrrPX/~&arh ~&fabt2R+-,
            ~&/<&>; ~&al^& -+
               :^/~&al ^R/~&f ^\~&ar ~&al; ~&iiT+ ~&F,
               ^J/~&f ~&a; ~&al^?\~&NarPC ~&ar?\<'bad raw constant'>!% ^lrlPCrrPX/~&arh ~&fabt2R+-+-,
         *= ~&H(
            ?^(~&l; \/-=,~&\<.'bad character in raw constant: '-- ~&iNC>%+ -:+ ~&p),
            ~&/(take/64 skip/60 characters) (* ~&x+ take/6+ --(0!* iota 6)) iota 64)+-,
       printer: -+
         leql/iota40?(:/'-{'+ (* '   '--)+ (~&zitZB?\~& ~&x+ ~&x; ~&thPhTttPC)+ block48+ --'}-',~&iNC+ '-{'--+ --'}-'),
         (* ~&ar^?\~&al ~&arh?\~&fallPrtPXPR ~&falrPrtPXPR)+ -+
            ~&D/(~&:-0 take/64 skip/60 characters)+ ^lrNCT/~&y ~&z; take/6+ --(0!* iota 6),
            block6+ ~&NiNCX; ^=lx ^/~&rxPlT ~&lrNCCSL+ ~&riF+-+-,
      help: 'push primitive raw data type'],
   type_constructor[
      mnemonic: 'g',
      recognizer: &!,
      generator: ! rand_gen,
      printer: ||(%xP) -+
         ~&i&& 'L'^?=aldl(
            ~&falvh2rDPM; -&~&tZg,~&itZB!| short+ ~&hSL&-?(
               ~&iNC+ :/`<+ --'>'+ mat`,+ ~&hS,
               :/'<'+ (* '   '--)^T(~&y; *= ^lrNCT/~&y --','+ ~&z,~&z; ^lrNCT/~&y --'>'+ ~&z)),
            'X'?=aldl\~&aldrh3rH -+
               -&~&tZg,~&itZB!| short+ ~&hSL&-?(
                  ~&iNC+ :/`(+ --')'+ mat`,+ ~&hS,
                  :/'('+ (* '   '--)^T(~&y; *= ^lrNCT/~&y --','+ ~&z,~&z; ^lrNCT/~&y --')'+ ~&z)),
               ^M/~&f ~&alvPrX; ~&alt^?\~&alhPrXNC :^/~&alhPrlPX ~&faltPrrPXPR+-),
         ~&NiX; (nleq\9+ ~&al)^& -+
            ~&r?/~&NrXNVlar2X -|
               ~&l; -+
                  ~&g&& ^liB\~&rS ~&lS; ~&rlrNCVB/('L',<>)+ :-0 ~&alrB^& ~&aldl2rdl2E&& ~&aldl?(
                     eql+~&alvPrvPX&& ~&ald2falvPrvPpPMV; &&~& ~&v; all ~&,
                     ~&aldl2ldr2rdr2cXNV; &&~& ~&dr),
                  ^M/~&f ^D\~&ar successor+ ~&al+-,
               ~&l; ^W(~&f,^G\~&ar successor+ ~&al); ~&lrB&& ^\~&br ~&bl; ~&V/('X',<>)+ 'X'?=rdl/~&lrvPC ~&lrNCC|-,
            ^/~& ~&ar; ~&F+ <.
               %nI&& %nP!,
               %sI&& %sP!,
               (-={0,&})&& ! ~&?/<'&'>! <'0'>!,
               %eI&& <.math..asprintf/'%0.6e'>!,
               ~&iNC; %sI&& %cP!,
               %zI&& %zP!>+-+-,
      help: 'push primitive general data type'],
   type_constructor[
      mnemonic: 'c',
      generator: ! case~&\arc(characters) ^(~&,"n". arc weight=="n"*~ characters)* (~&ttt iota 8),
      recognizer: ~&w\~&H(
         block4+~&L; * -+
            ~&l+ ~&ah^?\~&NatPX ~&ffatPRJ; ^lrlPXrrPX/~&al ~&farPR,
            ~&xL+ * -: ~&p/'0123456789abcdef' (* take/4+ --<0,0,0,0>) iota 16+-,
         <
            '04d50135053504b50475027504f5004d014d054d154d134d0b4d074d04cd14cd',  # can use the same data in c
            '02cd12cd0acd11cd09cd012d052d152d0d2d032d132d0b2d072d04ad14ad0cad',  # the virtual machine needs to know
            '12ad11ad09ad046d146d026d126d0a6d116d096d10ed08ed04ed011d051d151d',
            '131d0b1d009d049d149d0c9d029d129d0a9d119d099d059d045d145d025d125d',
            '0a5d115d095d10dd08dd043d143d023d123d0a3d113d093d10bd08bd107d087d',
            '001300530153055315530b53075304d302d312d30ad306d301d311d309d305d3',
            '03d301330533153313330b3300b304b314b30cb302b312b30ab311b309b305b3',
            '04731473027312730a731173097310f308f301f3004b054b154b034b134b0b4b',
            '04cb14cb02cb12cb0acb11cb09cb012b052b152b0d2b132b0b2b04ab14ab0cab',
            '12ab11ab046b126b116b10eb011b051b151b0d1b131b0b1b049b149b129b119b',
            '045b145b0c5b125b115b10db043b123b113b10bb107b00470147054715470d47',
            '034713470b47074704c714c702c712c70ac711c709c70127052715270d270b27',
            '04a714a712a711a7046714671267116710e70117051715170d1713170b170497',
            '149712971197045714570c571257115710d7043714370c371237113710b71077',
            '010f050f150f0d0f030f130f0b0f070f048f148f128f118f044f144f124f114f',
            '10cf042f142f0c2f122f112f10af106f041f141f0c1f121f111f109f105f103f'>),
      help: 'push primitive character type',
      reader: ~&L; ||<'bad character format'>!% -&~&i,~&t,~&ttZ,~&h==``,~&th&-,
      printer: ~&iNC+ ``?=h(~&,--'%cOi&')+ -:(~&lrNCC/``) ^(~&r,~&h+ %nP+ ~&l)^*j(~&,take/95+ skip/32) num characters]>

unary_types = # pertaining to a single subtype

^A(~mnemonic,~&)* (* arity:=1!+ microcode:= ! ~&rhPlhPNCVltPCrtPX+ ~&l?/~& ~&/<~&V/primitive_types-g <>>+ ~&r) <
   type_constructor[
      mnemonic: 'W',
      help: 'transform top type to a pair',
      generator: rand_double+ ~&h,
      initializer: ~&l; (~&l?\~&r +)\(~&?/~& &!)+ ~&ihB&& fan+~&h,
      recognizer: ~&r&& ^G(~&lhvh2iC,~&r); both ^H/~&lhd.recognizer ~&,
      precognizer: ~&r&& ^G(~&lhvh2iC,~&r); both ^H\~& ~&lhd; ~precognizer|| ~recognizer,
      printer: ~&r?\<'()'>! pretty_pair''+ ^G(~&lhvh2iC,~&r); ~&lrNCC+ ~~ ^H/~&lhd.printer ~&],
   type_constructor[
      mnemonic: 'J',
      help: 'transform top type to job thereof',
      generator: rand_pair/rand_fun+ ~&h,
      initializer: ~&l; (~&l?\~&r +)\(~&?/~& &!)+ ~&ihB&& ~&h; "f". ^J/~&f "f"+ ~&a,
      recognizer: -&~&r,^(~&lhvh2iC,~&ra); ^H/~&lhd.recognizer ~&,~&rf; %fI&-,
      precognizer: -&~&r,^(~&lhvh2iC,~&ra); ^H\~& ~&lhd; ~precognizer|| ~recognizer,~&rf; %fI&-,
      printer: ^(~&lhvh2iC,~&r); ^lrhPTrtPC(~&rf; '~&J/'--+ --'%fOi& '+ ~&h+ %nP+ weight,^H/~&lhd.printer ~&lraPX)],
   type_constructor[
      mnemonic: 'Z',
      generator: -!==&,~&i&& 50%~!-&&+ ~&h,
      recognizer: ~&rZ!| ^(~&lhvh2iC,~&r); ^H/~&lhd.recognizer ~&,
      precognizer: ~&rZ!| ^(~&lhvh2iC,~&r); ^H\~& ~&lhd; ~precognizer|| ~recognizer,
      initializer: ~&l; ~&ihB&& ~&h; ~&i&&,
      printer: ~&r?(
         ^(~&lhvh2iC,~&r); ^H/~&lhd.printer ~&,
         ~&iNC+ cases~&lhd.mnemonic/{{'N','B'}: '[]'!,{'L','m','G'}: '<>'!,{'T'}: '~&V()'!,{'S'}: '{}'!} '()'!),
      help: 'replace top type with union with empty instance'],
   type_constructor[
      mnemonic: 'O',
      generator: ~&h,
      recognizer: ^(~&lhvh2iC,~&r); ^H/~&lhd.recognizer ~&,
      precognizer: ^(~&lhvh2iC,~&r); ^H\~& ~&lhd; ~precognizer|| ~recognizer,
      initializer: ~&l; ~&ihB,
      printer: ^(~&lhvh2iC,~&r); ~&iNC+ ~mnemonic=='B'?lhd(     # assuming record printers map 0 to the record identifier
         :/`(+ --')%i&'+ ^T(~&h+ %nP+ weight+ ~&r,',_'--+ ~&iNH+ ~&lhd.printer),
         ^|rlT(:/`%+ --'i&'+ ||'o'! ~&h; -&~&,--'O'&-+ *^0 ~&vig&& -&~&izB~<'Bu',~&i&-^T/~&vL ~&d.mnemonic,~&h+ %nP+ weight)),
      help: 'make top type printed as opaque'],
   type_constructor[
      mnemonic: 'L',
      initializer: ~&l; ~&ihB&& ~&h; *,
      help: 'transform top type to list thereof',
      generator: rand_list+ ~&h,
      recognizer: ^D(~&lhvh2iC,~&r); all ^H/~&lhd.recognizer ~&,
      precognizer: ^D(~&lhvh2iC,~&r); all ^H\~& ~&lhd; ~precognizer|| ~recognizer,
      printer: ^D(~&lhvh2iC,~&r);  (* ^H/~&lhd.printer ~&); -&~&tZg,~&itZB!| short+ ~&hSL&-?(
         ~&iNC+ :/`<+ --'>'+ mat`,+ ~&hS,
         :/'<'+ (* '   '--)^T(~&y; *= ^lrNCT/~&y --','+ ~&z,~&z; ^lrNCT/~&y --'>'+ ~&z))],
   type_constructor[
      mnemonic: 'S',
      help: 'transform top type to set thereof',
      initializer: ~&l; ~&h?\~&s! ~&s++ *+ ~&h,
      generator: ~&s++ rand_list+ ~&h,
      recognizer: ^E(~&r,~&rs)&& ^D(~&lhvh2iC,~&r); all ^H/~&lhd.recognizer ~&,
      precognizer: ^D(~&lhvh2iC,~&r); all ^H\~& ~&lhd; ~precognizer|| ~recognizer,
      printer: ^D(~&lhvh2iC,~&r);  (* ^H/~&lhd.printer ~&); -&~&tZg,~&itZB!| short+ ~&hSL&-?(
         ~&iNC+ :/`{+ --'}'+ mat`,+ ~&hS,
         :/'{'+ (* '   '--)^T(~&y; *= ^lrNCT/~&y --','+ ~&z,~&z; ^lrNCT/~&y --'}'+ ~&z))],
   type_constructor[
      mnemonic: 'm',
      help: 'transform top type to list of assignments of strings thereto',
      initializer: ~&l; ~&ihB&& ~&h; "f". * ^A/~&n "f"+ ~&m,
      generator: rand_list+ rand_pair/rand_str+ ~&h,
      recognizer: -&all~&+ ~&r,^D(~&lhvh2iC,~&rmS); all ^H/~&lhd.recognizer ~&,~&rnS; all %sI&-,
      precognizer: -&all~&+ ~&r,^D(~&lhvh2iC,~&rmS); all ^H\~& ~&lhd; ~precognizer|| ~recognizer,~&rnS; all %sI&-,
      printer: ^D(~&lhvh2iC,~&r); -+
         -&~&tZg,~&itZB!| short+ ~&hSL&-?(
            ~&iNC+ :/`<+ --'>'+ mat`,+ ~&hS,
            :/'<'+ (* '   '--)^T(~&y; *= ^lrNCT/~&y --','+ ~&z,~&z; ^lrNCT/~&y --'>'+ ~&z)),
         * ^lrhPTrtPC(~&rn; :/`'+  --''': '+ *= `'?=/<.~&,~&> ~&iNC,^H/~&lhd.printer ~&lrmPX)+-],
   type_constructor[
      mnemonic: 'T',
      help: 'transform top type to a tree thereof',
      generator: rand_tree+ ~&hhX,
      initializer: ~&l; ~&ihB&& ~&h; "f". *^0 ^V\~&v "f"+ ~&d,
      recognizer: ^(~&lhvh2iC,~&r); ~&arZ^! -&~&alrdPX; ^H/~&lhd.recognizer ~&,all~&+ ~&falrvPDPM&-,
      precognizer: ^(~&lhvh2iC,~&r); ~&arZ^! -&~&alrdPX; ^H\~& ~&lhd; ~precognizer|| ~recognizer,all~&+ ~&falrvPDPM&-,
      printer: ^(~&lhvh2iC,~&r); ~&ar^?\<'~&V()'>! -+
         -!~&lt,not short+ ~&lhPrhPT!-?(
            -&~&rtZ,~&rhh=='<>'!| short+ ~&lhPrhPT&-?(
               -!~&lt,~&lh; -!~&h==`~,~&w/` !-!-?(
                  :^\~&lt ^T('<>'?=rhh/'^:<>'! '^:'--+ ~&rh; -!~&h==`~,-=/` !-?\~& :/`(+ --')',:/` + ~&lh),
                  ~&iNC+ ^T('^:'--+ ~&rh; parenthetic?\~& :/`(+ --')',:/` + ~&lh)),
               :/'^: ('+ ^T(~&l; ^lrNCT/~&y --','+ ~&z,~&r; ^lrNCT/~&y --')'+ ~&z)+ ~~ * '   '--),
            :^\~&rt ^T\~&rh --'^: '+ ~&lh; parenthetic?\~& :/`(+ --')'),
         ^/~&l ~&r; -&~&tZg,~&itZB!| short+ ~&hSL&-?(
            ~&iNC+ :/`<+ --'>'+ mat`,+ ~&hS,
            :/'<'+ (* '   '--)^T(~&y; *= ^lrNCT/~&y --','+ ~&z,~&z; ^lrNCT/~&y --'>'+ ~&z)),
         ^\~&falrvPDPM ~&alrdPX; ^H/~&lhd.printer ~&+-],
   type_constructor[
      mnemonic: 'N',
      help: 'transform top type to balanced tree thereof',
      recognizer: ~&rZ!| ~&Nlhvh2iCPrNCXX; ~&lZrrPB->l ^(
         ~&rlrD; all ^H/~&lhd.recognizer ~&,
         ^/~&rl ~&rr; ~&g&& ~&lrNCCSLiF),
      precognizer: ~&rZ!| ~&Nlhvh2iCPrNCXX; ~&lZrrPB->l ^(
         ~&rlrD; all ^H\~& ~&lhd; ~precognizer|| ~recognizer,
         ^/~&rl ~&rr; ~&g&& ~&lrNCCSLiF),
      initializer: _type_constructor%TLfOLwXMk; ~&lihB&& -+
         ("i","r"). -+
            (* ^A/~&n "i"+ ~&m); =>0 ^H\~&r :=^(~&aahPNfatPRXfatPRNXQaaXq+ ~&alPNfalPRCarPNNXfarPRCBqx+ ~&ln,!+ ~&lm),
            ~&i&& ~&NNXiANC; (not all "r"+ ~&m)-> ~&mF+ *= <.^A\~&ml ~&nNX,^A\~&mr ~&NnX>+-,
         ^/~&lh (/)^\~&rhvh2iC ~&rhvhd; -|~precognizer,~recognizer,! ! &|-+-,
      generator: ~=(&)&&+ ~&r++ rand_bal+ ~&h,
      printer: ||<'[]'>! ~&r&& ~&Nlhvh2iCPNNXrXNCXX; -+
         ~&i&& -&~&tZg,~&itZB!| short+ ~&hSL&-?(
            ~&iNC+ :/`[+ --']'+ mat`,+ ~&hS,
            :/'['+ (* '   '--)^T(~&y; *= ^lrNCT/~&y --','+ ~&z,~&z; ^lrNCT/~&y --']'+ ~&z)),
         * :^(^T(--':'+ ~&l,:/` + ~&rh),~&rt)+ ^(
            ~&rl; ^T(~&l,:/`:+ ~&r)+ (~~ ~&h+ %nP)^(
               predecessor+ weight,
               ~&x+ skipwhile~&Z+ ~&x+ ~&ar^?/~&NNXfarPRC ~&alPNfalPRCB),
            ~&lrrPX; ^H/~&lhd.printer ~&),
         ~&lZrrPB->rlPlD ^(
            &&~&rr ~&rlrrSPD; all ^H/~&lhd.recognizer ~&,
            ^/~&rl ~&rr; ~&g&& ~&rF+ *= <.~&lNXrlPX,~&NlXrrPX>)+-],
   type_constructor[
      mnemonic: 'G',
      help: 'transform top type to recombining grid thereof',
      generator: ~&h; "f". ~&i&& ~=(&)&& -+
         %naLsaLXNLXXMk; :^\~&rr ^lrxPV\-+-<&,~&rl+- "f"+ (nleq?/0! difference)^/predecessor+~&l weight+ ~&r,
         ^lrihlPBrSXPX/~& ^NiX(||~& skip^\~& ~&itBitB+ length,~&); %aLsaLXNXLMk+ ~&rr->lt %aLsaLXNXLnWXMk+ -+
            ^/~&l ^/~&rl (nleq?/0! difference)^/~&rr successor+ weight+ ~&lhr,
            %aLsaLXNXLnWXMk^\~&lr -+
               ~&t?\~& %aLsaLXNXLMk; :^\~&t ^/~&hl -+
                  ^H\~&l ~&r; //=> %aaLXsaLXNXMk; %saLXNMk^H\~&r :=^(~&ll; .\&v,!+ ~&lr),
                  %aaLXLsaLXNXMk^\~&r ~&l; |=hlPrSXS&l; * ^lrxPX/~&l -<&+ ~&r,
                  ^\~&hr ~&hthPXl; -+
                     nleq^(product+ length~~+ ~&r,~&l)?/cross+~&r ^(iota+~&l,~&NrbiiX2X); ~&l->rlx -+
                        ~&rllrw2lrlrPrXPXltPrllrCPrll2lll2NCjrlr2Xrrl2llr2NCjrrr2XXXPXQ,
                        ^/~&l ~&r; ~&rblK8P2lXrX+ -+
                           (subset^\~&l cross+ ~&rbl)?/~&lrbrrX2X ~&,
                           ~&lrllPrlPilrrrXPXQrlPlrrXPrXbrrXPQQPX+-+-,
                     ^\~& length~~; sum^(lesser not nleq,mtwist..u_disc+ ||1! ~&itB+ product)+-+-,
               :^\~&ll ~&r; rand_bal ~&iNV+ "f"+ ~&i&& predecessor+-,
            %aLsaLXNXLnWXnXMk^/~& sum^/~&rlt mtwist..u_disc+ ||1! ~&rlt+-+-,
      initializer: ~&lihB&& -+
         ("i","t"). ~&i&& decombination/"t"; ~&NrX; ~&rl->lx %saLXNLasaLXXLsaLXNLXXMk+ ^(
            :^\~&l ~&rl; %asaLXXLMk; (* ^/~&l ^\~&rr "i"+ ~&rl); =>0 ^H\~&r :=^/~&ll !+ ~&lr,
            ~&r; ^\~&ritB ~&r&& ~&rhPlrrPSLs3DrNrXlHXS),
         ^/~&lh ~&r; -+
            * *^ &d.(reader,(mnemonic,printer),(microcode,arity),(help,target)):= (0,&,&,&)!,
            &hvhd.recognizer:= ~&hvhd; ~precognizer|| ~recognizer+-+-,
      (recognizer,precognizer): ~&H(
         ~~ "f". ~&rZ!| ~&Nlhvh2iCPNNXrhPXNCrtPXXX; ~&lZrrl2B->lNNXB -+
            ^\~&rrl2rrr2lXX &&~&rl ~&rrlPlXPlX; ~&ilrrrPSL3ZB+ ~&ar^?\~&a -&
               ~&allPrhPXlrrrPSLs4D; %osaLANXaXLMk; ~&i&& -&
                  all indexable+~&rlrPX&& ~&llPNrXlrPHX; -&
                     ~&r&& ~&rv; -&all_same weight,all %aI&-,
                     ^H/~&lhd.recognizer ~&lrdPX&-,
                  ~&rShlr2X; %aLsaLANXMk; ^E/~&r ^H(:=^/~&ll !+ ~&lr,~&r)=>0+ ^p/~&l ^H\~&r gang+ ~&lNiXS&-,
               ^R/~&f ^\~&art ^/~&all %asaLXALMk+ ~&arhPlrrrPSLs4DrNrXlHXS&-,
            ^/~&rrr ~&lrlPrrl2XX; ~&lZrrPB-> ^(
               &&~&rr ~&rlrrSPD; all -&~&r&& ~&rv; -&all_same weight,all %aI&-,^H/"f" ~&lrdPX&-,
               ^/~&rl ~&rr; (all~&r)&& -<&l+ ~&rF+ *= <.~&lNXrlPX,~&NlXrrPX>)+-,
         (~&lhd.recognizer,~&lhd; ~precognizer|| ~recognizer)),
      printer: ~&r?\<'<>'>! decombination; _type_constructor%TLasaLXXLsaLXNLXXMk; ~&rl?\<'bad grid'>!% (&rl:= -<&l+ ~&rl); -+
         -&~&tZg,~&itZB!| short+ ~&hSL&-?(
            ~&iNC+ :/`<+ --'>'+ mat`,+ ~&hS,
            :/'<'+ ('   '--)^*T(~&y; *= ^lrNCT/~&y --','+ ~&z,~&z; ^lrNCT/~&y --'>'+ ~&z)),
         ~&NiX; ~&r->lx ^(
            :^\~&l ~&r; -+
               %sLLC -&~&tZg,~&itZB!| short+ ~&hSL&-?(
                  ~&iNC+ :/`[+ --']'+ mat`,+ ~&hS,
                  :/'['+ ('   '--)^*T(~&y; *= ^lrNCT/~&y --','+ ~&z,~&z; ^lrNCT/~&y --']'+ ~&z)),
               ~&lrlPD; * _type_constructor%TLasaLXXXMk; :^(^T(--':'+ ~&l,:/` + ~&rh),~&rt)+ ^/(~&h+ %aP+ ~&rl) -+
                  -&~&tZg,short+ ~&hSL&-?(
                     ^TNC\~&thh --'^: '+ ~&hh; -!~&ihB==`~,-=/` !-?\~& :/`(+ --')',
                     -&~&tht,~&htZ,short+ ~&hh&-?(
                        :^(
                           ^T\~&thh ~&hh;  --'^: '+ -!~&ihB==`~,-=/` !-?\~& :/`(+ --')',
                           ~&tht; * '   '--),
                        -&~&thtZ,~&thh=='<>'!| short+~&hSL&-?(
                           ~&ht?(
                              :^\~&ht ^T('<>'?=thh/'^:<>'! '^:'--+ ~&thh,:/` + ~&hh),
                              '<>'?=thh(
                                 ~&iNC+ ~&hh; -!~&h==`~,-=/` !-?('^:<> '--,--'^: <>'),
                                 ^TNC\~&thh --'^:'+ ~&hh; -!~&h==`~,-=/` !-?\~& :/`(+ --')')),
                           :/'^: ('+ ('   '--)^*T(~&y; *= ^lrNCT/~&y --','+ ~&z,~&z; ^lrNCT/~&y --')'+ ~&z)))),
                  ^lrNCC/(~&lrrd2X; ^H/~&lhd.printer ~&) %aLP+ ~&rrv+-+-,
            ~&r; ~&rr&& ^/~&l ^\~&rrt ~&rrh2rlrrPSLs4DrNrXlHXS)+-]>

binary_types = # pertaining to a pair of subtypes

^A(~mnemonic,~&)* (arity:=2!)* (microcode:= ~microcode|| binary_reduction+ ~mnemonic)* <
   type_constructor[
      mnemonic: 'U',
      generator: &?=^\choice !+ ~&g+ ~&iNNXH+ gang,
      initializer: _type_constructor%TLfOLwXMk; -+
         -??-+ ~&yzrPNCT,
         ^p\-+* ~&|| ! ~&,~&l+- ~&rihvPDrlCS; * (/)^\~& ~&hd; -|~precognizer,~recognizer,! ! &|-+-,
      help: 'replace top two types with free union thereof',  # r%oU distributes over fields of record r
      microcode: binary_reduction'U'; ^\~&r :^\~&lt ~&lh; -+
         ?(
            -&~&d.mnemonic=='U',~&v; all ~&d.mnemonic=='u'&-,
            ~&\~& &d.(precognizer,recognizer):= ~&iiX+ ~&r;+ \/-=+ ~&v; * ~&iNHNH+ ~&d.initializer),
         ^?(
            -&~&a,~&ad.mnemonic=='U',~&av,~&avt,~&avttZ,~&avthd.mnemonic=='o',~&avhd.mnemonic=='B'&-,
            ~&\~&a ^V/~&ad :^\~&avt ^V/~&avhd ^M/~&f (~&rd.mnemonic=='o'?/~&r ~&ldPrlvt2CV)*+ ~&a; ^D/~& ~&vhv)+-,
      recognizer: ^D(~&r,~&lihvPDrlCS); any ^H/~&rhd.recognizer ~&rlX,
      precognizer: ^D(~&r,~&lihvPDrlCS); any ^H\~&rlX ~&rhd; ~precognizer|| ~recognizer,
      printer: ^D(~&r,~&lihvPDrlCS); -|
         ~&a^& (~&ah; ^H/~&rhd.recognizer ~&rlX)?\~&fatPR ~&ahrlX; ^H/~&lhd.printer ~&,
         <'unprintable union'>!%|-],
   type_constructor[
      mnemonic: 'A',
      generator: rand_pair+ ~&hthPX,
      help: 'transform top two types type to an assignment',
      initializer: ~&l; (~&?=l/~&r +)^(
         couple(field(&,0),field(0,&))?=(~&!,~&)+ -+
            (||couple -&both ~&lrZB,~&Ebll2O,~&blr==(~&l,~&r),fan+~&lll&-)=>,
            (~&l?\~&r +)^*p/~& (^TNiXS\~&zNC .\&l+ ~&y)+ ~&NiX|\+ &!*+-,
         filler+ (^T\~&zNC .\&l+ ~&y)+ ~&NiX|\+ &!*),
      recognizer: ^(~&lihvPDrlCS,~&r); ~&al^?\~&arZ ~&alt?(
         &&~&faltPrrPXPR ~&ar&& ~&alhPrlPX; ^H/~&lhd.recognizer ~&,
         ~&alhPrX; ^H/~&lhd.recognizer ~&),
      precognizer: ^(~&lihvPDrlCS,~&r); ~&al^?\~&arZ ~&alt?(
         &&~&faltPrrPXPR ~&ar&& ~&alhPrlPX; ^H\~& ~&lhd; ~precognizer|| ~recognizer,
         ~&alhPrX; ^H\~& ~&lhd; ~precognizer|| ~recognizer),
      printer: ~&r?\<'~&A()'>! -+
         -&~&,~&t,~&htZ,~&hhh~=`~&-?\pretty_pair'~&A' ^lrhPTrtPC(--': '+ @hh parenthetic?\~& :/`(+ --')',pretty_pair''+ ~&t),
         ^(~&rlCS+ ~&lihvPD,~&r); ~&alt^?(
            :^\~&faltPrrPXPR ^H(~&lhd.printer,~&)+ ~&alhPrlPX,
            ~&alhPrX; ^HNC/~&lhd.printer ~&)+-],
   type_constructor[
      mnemonic: 'X',
      generator: rand_pair+ ~&hthPX,
      help: 'transform top two types type to a pair', 
      initializer: @l (~&?=l/~&r +)^(
         couple(field(&,0),field(0,&))?=(~&!,~&)+ -+
            (||couple -&both ~&lrZB,~&Ebll2O,~&blr==(~&l,~&r),fan+~&lll&-)=>,
            (~&l?\~&r +)^*p/~& (^TNiXS\~&zNC .\&l+ ~&y)+ ~&NiX|\+ &!*+-,
         filler+ (^T\~&zNC .\&l+ ~&y)+ ~&NiX|\+ &!*),
      recognizer: ^(~&lihvPDrlCS,~&r); ~&al^?\~&arZ ~&alt?(
         &&~&faltPrrPXPR ~&ar&& ~&alhPrlPX; ^H/~&lhd.recognizer ~&,
         ~&alhPrX; ^H/~&lhd.recognizer ~&),
      precognizer: ^(~&lihvPDrlCS,~&r); ~&al^?\~&arZ ~&alt?(
         &&~&faltPrrPXPR ~&ar&& ~&alhPrlPX; ^H\~& @lhd ~precognizer|| ~recognizer,
         ~&alhPrX; ^H\~& @lhd ~precognizer|| ~recognizer),
      printer: ~&r?\<'()'>! pretty_pair''+ ^(~&lihvPDrlCS,~&r); ~&alt^?(
         :^\~&faltPrrPXPR ^H(~&lhd.printer,~&)+ ~&alhPrlPX,
         @alhPrX ^HNC/~&lhd.printer ~&)],
   type_constructor[
      mnemonic: 'D',
      generator: rand_tree+ ~&hthPX,
      initializer: ~&l; -&~&,~&t,~&ttZ&-&& -|
         ~&hthPB&& ~&hthPX; ("r","v"). ~&a^& ^V\~&favPM ~&av?/"r"+~&ad "v"+~&ad,
         ~&h&& ~&h; "r". ~&a^& ^V\~&favPM ~&av?/"r"+~&ad ~&ad,
         ~&th&& ~&th; "v".  ~&a^& ^V\~&favPM ~&av?/~&ad "v"+~&ad|-,
      recognizer:  ^(^/~&lhvh2iC ~&lhvth3iC,~&r); ~&arZ^! -&
         ~&arv?(~&allPrdPX,~&alrPrdPX); ^H/~&lhd.recognizer ~&,
         all~&+ ~&falrvPDPM&-,
      precognizer:  ^(^/~&lhvh2iC ~&lhvth3iC,~&r); ~&arZ^! -&
         ~&arv?(~&allPrdPX,~&alrPrdPX); ^H\~& ~&lhd; ~precognizer|| ~recognizer,
         all~&+ ~&falrvPDPM&-,
      printer: ^(^/~&lhvh2iC ~&lhvth3iC,~&r); ~&ar^?\<'~&V()'>! -+
         -!~&lt,not short+ ~&lhPrhPT!-?(
            -&~&rtZ,~&rhh=='<>'!| short+ ~&lhPrhPT&-?(
               -!~&lt,~&lh; -!~&h==`~,-=/` !-!-?(
                  :^\~&lt ^T('<>'?=rhh/'^:<>'! '^:'--+ ~&rh; -!~&h==`~,-=/` !-?\~& :/`(+ --')',:/` + ~&lh),
                  ~&iNC+ ^T('^:'--+ ~&rh; parenthetic?\~& :/`(+ --')',:/` + ~&lh)),
               :/'^: ('+ ^T(~&l; ^lrNCT/~&y --','+ ~&z,~&r; ^lrNCT/~&y --')'+ ~&z)+ ~~ * '   '--),
            :^\~&rt ^T\~&rh --'^: '+ ~&lh; parenthetic?\~& :/`(+ --')'),
         ^/~&l ~&r; -&~&tZg,~&itZB!| short+ ~&hSL&-?(
            ~&iNC+ :/`<+ --'>'+ mat`,+ ~&hS,
            :/'<'+ (* '   '--)^T(~&y; *= ^lrNCT/~&y --','+ ~&z,~&z; ^lrNCT/~&y --'>'+ ~&z)),
         ~&arv?(^\~&falrvPDPM ~&allPrdPX; ^H/~&lhd.printer ~&,~&\<>+ ~&alrPrdPX; ^H/~&lhd.printer ~&)+-,
      help: 'replace top two types with dual type tree']>

stacking_types = # for manipulating compile time and run-time stacks

^A(~mnemonic,~&)*  (* arity:= ~arity|| 1!) <
   type_constructor[
      arity: 2,
      mnemonic: 'w',
      microcode: ~&litB?/~&lthPhttPCCPrtPX <'type w underflow'>!%,
      help: 'swap the top two operands on the stack'],
   type_constructor[
      mnemonic: 'd',
      microcode: ~&l?/~&lhiCPrtPX <'type d underflow'>!%,
      help: 'duplicate the operand on the top of the stack'],
   type_constructor[
      mnemonic: 'l',
      microcode: ~&l?/~&lhlPtCPrtPX <'type l underflow'>!%,
      help: 'replace the top operand on the stack with its left side'],
   type_constructor[
      mnemonic: 'r',
      microcode: ~&l?/~&lhrPtCPrtPX <'type r underflow'>!%,
      help: 'replace the top operand on the stack with its right side'],
   type_constructor[
      mnemonic: 'h',
      help: 'push recursive type or raise the top one',
      microcode: ^\~&rt ~&llhd2rhPEB?/~&rhPlhPNCVltPC ~&rhPNVlC,
      recognizer: ~&lt?\<'bad recursive type'>!% ^H(~&lhd.recognizer,~&)+ ~&lhv?/~&lhvh2ttPCPrX ~&ltPrX,
      precognizer: ~&lt?\<'bad recursive type'>!% ^H(~&lhd; ~precognizer|| ~recognizer,~&)+ ~&lhv?/~&lhvh2ttPCPrX ~&ltPrX,
      printer: ~&lt?\<'bad recursive type'>!% ^H(~&lhd.printer,~&)+ ~&lhv?/~&lhvh2ttPCPrX ~&ltPrX]>

atypical_types = # may require something other than a type expression on top of the stack

^A(~mnemonic,~&)* (* arity:= ~arity|| 1!) <
   type_constructor[
      mnemonic: 'u',
      microcode: ~&l?\<'bad unit type'>!% ^\~&rt :^\~&lt ~&V\<>+ ~&rh+ assign(
         &rh.((generator,initializer),printer,recognizer),
         ^(^("x". ! &?=/&! "x"!,!+ !),^/(!+ %gP) ~&r==)+ ~&lh),
      help: 'transform top constant to unit type'],
   type_constructor[
      mnemonic: 'Q',
      initializer: ~&l; ~&ihB&& ~&h; "f". compress0+ "f"+ extract,
      generator: ~&h; (&?=l/~&r compress0+ ~&r)^/~&,
      microcode: ~&lrtPY?(
         ~&l?(
            -&~&rtZ,~&ltZ,%nI+ ~&lh,not ~&lh&& _type_constructor%TI+ ~&lh&-?(
               ^\~&rt ~&rhNVNC+ &rh.target:= compress+ ~&lh,
               ~&rhPlhPNCVltPCrtPX),
            ^\~&rt :^\~&l ~&V\<~&V/primitive_types-g <>>+ ~&rh),
         ^\~&rt ~&rhNVNC+ &rh.target:= ! compress 0),
      recognizer: extractable+~&r&& ^(~&lhvh2iC,extract+~&r); &?=l(~&rlY,~&l)+ ^\~&r ^H/~&lhd.recognizer ~&,
      precognizer: extractable+~&r&& -+
          &?=l(~&rlY,~&l)+ ^\~&r ^H\~& ~&lhd; ~precognizer|| ~recognizer,
         ^/~&lhvh2iC extract+ ~&r+-,
      printer: -+
         ~&t?(:^\~&t '%Q '--+ ~&h,~&iNC+ ~&h; '([{<'?<h('%Q'--,'%Q('--+ --')')),
         ^(~&lhvh2iC,extract+~&r); ^H/~&lhd.printer ~&+-,
      help: 'transform top type to compressed version'],
   type_constructor[
      mnemonic: 'B',
      microcode: ~&l?\<'bad record type'>!% ^\~&rt :^\~&lt ^V\~&lhtmS ~&rh+ assign(
         &rh.(generator,(initializer,printer),(precognizer,recognizer)),
         ~&/(rand_pair:- 0!)+ ~&lh; ^(
            ^/(!+ ~&?(~&,&!);+ ~&hm) ~&?^\(!+ ~&hn) &?=^/(!+ ~&tnS) -+
               (("x","p"). ~&lrhPTrtPC/"x"+ "p")^/~&l ~&r; "a". -+
                  -&~&tZg,~&itZB!| short+ ~&hSL&-?(
                     ~&iNC+ :/`[+ --']'+ mat`,+ ~&hS,
                     :/'['+ (* '   '--)^T(~&y; *= ^lrNCT/~&y --','+ ~&z,~&z; ^lrNCT/~&y --']'+ ~&z)),
                  (* :^\~&rt ^T\~&rh --': '+ ~&l; `~?=h\~& :/`(+ --')')+ -+
                     *~ not ~&r; ~&tZ&& ~&hx; =]']['&& ~&tt; ~&Z (#~&cZ/'~&/ (,)'#),
                     ~&rlPFlrrPXS+ ~&p/(~&rS "a")+ * ^/~&r ^H/~&lhd.printer ~&+-,
                  ^p(~&lihvPDrlCS,~&r; (~&lS "a")*-; * ^H\~&r ~+ ~&l)+-,
               ^/~&hn ~&t; ~&i&& ^p\~&nS ~&liNXSPrNiXSPT:-<&>+ <&>!*+-,
            ^(
               -&.
                  ~&t; ("a". (all indexable+ ~&rlX)+ ~&D\"a"+ ~&r)+ ~&liNXSPrNiXSPT:-<&>+ <&>!*,
                  -+
                     "a". (all ^H\~& ~&lhd; ~precognizer|| ~recognizer)+ ^p(~&lihvPDrlCS,~&r; "a"*-; * ^H\~&r ~+ ~&l),
                     ~&t; ~&liNXSPrNiXSPT:-<&>+ <&>!*+-&-,
               -&.
                  ~&t; ("a". (all indexable+ ~&rlX)+ ~&D\"a"+ ~&r)+ ~&liNXSPrNiXSPT:-<&>+ <&>!*,
                  -+
                     "a". (all ^H/~&lhd.recognizer ~&)+ ^p(~&lihvPDrlCS,~&r; "a"*-; * ^H\~&r ~+ ~&l),
                     ~&t; ~&liNXSPrNiXSPT:-<&>+ <&>!*+-,
                  ~&hm; "r". ~&r; ^E/"r" ~&i&-))),
      help: 'construct a record type from a module']> # ~&lh of the form <'rec': initializer,'field': subtype,...>

type_operators = # transform a type into something other than a type

^A(~mnemonic,~&)* (:^/~&h ~&t; * arity:= ~arity|| 1!) <
   type_constructor[
      mnemonic: 'y',
      microcode: ~&rhPNVlCrtPX,
      generator: ! ^lrPllPrHH(~&l,-&nleq+ ~&rlX,difference&-^/~&r weight+ ~&iNH+ ~&lr)^\~& ^(generator_of,%-Y)+ rand_type,
      recognizer: ~&r&& -&
         ~&rl; extractable&& extract; (0,_type_constructor)%dluwrXsUTMk; *^0 &&~&vig -!
            ~&dlZ&& ~&dr; -&_type_constructor%I,~mnemonic-= ~&nS atypical_types&-,
            ~&d-= :/'y' :/'h' :/'Q' ~&nS ~&L <primitive_types,unary_types,binary_types>!-,
         ^H(~&lhd.recognizer,~&)+ ^\~&rr <.^H\~&rl type_decompression+ ~&lhd>&-,
      printer: ^H(~&lhd.printer,~&)+ ^\~&r :^\~&l -+
         //~&V type_constructor[printer: ~printer binary_types-X,recognizer: ~recognizer binary_types-X],
         //: ~&V\<> type_constructor[printer: ~printer primitive_types-x,recognizer: &!],
         ^HNC\~&rl type_decompression+ ~&lhd+-,
      help: 'push primitive self-describing type'],
   type_constructor[
      mnemonic: 'R',
      microcode: <'bad R type expression'>!%,
      help: 'qualify C or V with recursive attribute'],
   type_constructor[
      mnemonic: 'k',
      microcode: ^\~&rt ~&rhNVNC+ &rh.target:= ~&!,
      help: 'transform top type or function to identity function'],
   type_constructor[
      mnemonic: 'i',
      arity: 2,
      microcode: ~&litB?(
         ^\~&rt &rh.target:=rhNVNC -|
            -&
               -&~&lh,~&lhd,~&lhd.mnemonic=='O',~&lth-=iota256&-&& ~&lhvihB; -&~&idB.mnemonic=='c',~&vZ&-,
               &?=\(~generator.&iNH primitive_types-c)+ !+ ~&ihB+ skip\characters+ ~&lth&-,
            +^(||<'bad i type'>!% generator_of+ ~&lh,!+ ~&lth)|-,
         <'bad i type'>!%),
      help: 'transform top type to random instance generator'],
   type_constructor[
      mnemonic: 'p',
      microcode: -+
         -&~&l,~&lh,~&lhd.reader&-?(^\~&rt ~&rhNVNC+ &rh.target:= ~&lhd.reader,<'parser not defined'>!%),
         ~&l?/~& ~&/<~&V/primitive_types-g <>>+ ~&r+-,
      help: 'transform top type to parsing function'],
   type_constructor[
      mnemonic: 'Y',
      microcode: -+
         ~&lh?\<'bad Y type'>!% ^\~&rt ~&rhNVNC+ &rh.target:= ~&lh; -+
            "t". ~&/"t",
            compress0+ *^ ^V\~&t (~&d.mnemonic-= ~&nS atypical_types)?(
               &d.(generator,(reader,initializer),(microcode,arity),(help,target)):=NdX (0,&,&,&)!,
               ~&d.mnemonic)+-,
         ~&l?/~& ~&/<~&V/primitive_types-g <>>+ ~&r+-,
      help: 'transform top type to self-describing formatter'],
   type_constructor[
      mnemonic: 'M',
      microcode: (~&l?/~& ~&/<~&V/primitive_types-g <>>+ ~&r); -&~&lh,~&lhd.printer&-?(
         ^\~&rt ~&rhNVNC+ &rh.target:= -+
            (% ~&)++ ~&l-=(~&nS primitive_types)?(~&NiX;+ ~&rd.printer,~&r; "t". ~&/<"t">; ^H/~&lhd.printer ~&),
            ~&lh; ^/~&d.mnemonic -+
               *^ ^V\~&v ~&d+ &d.(generator,(reader,initializer),(microcode,arity),(help,target)):= (0,&,&,&)!,
               ~&a^& (&d.mnemonic:= ''!)+ ^V/~&ad (~&a; -&~&d.mnemonic=='O',~&v&-)?\~&favPM ~&adPfavPMV*+ ~&favPD,
               -!~&d.mnemonic-={'U','N','G','y'},any~&+ ~&v!-*^?/~& *^ ^V\~&v ~&d+ &d.(precognizer,recognizer):= &!+-+-,
         <'bad M type'>!%),
      help: 'transform top type to error messenger'],
   type_constructor[
      mnemonic: 'P',
      microcode: (~&l?/~& ~&/<~&V/primitive_types-g <>>+ ~&r); -&~&lh,~&lhd.printer&-?(
         ^\~&rt ~&rhNVNC+ &rh.target:= -+
            (~&nS primitive_types)?<l(~&NiX;+ ~&rd.printer,~&r; "t". ~&/<"t">; ^H/~&lhd.printer ~&),
            ~&lh; ^/~&d.mnemonic -+
               *^ ^V\~&v ~&d+ &d.(generator,(reader,initializer),(microcode,arity),(help,target)):= (0,&,&,&)!,
               ~&a^& (&d.mnemonic:= ''!)+ ^V/~&ad (~&a; -&~&d.mnemonic=='O',~&v&-)?\~&favPM ~&adPfavPMV*+ ~&favPD,
               -!~&d.mnemonic-={'U','N','G','y'},any~&+ ~&v!-*^?/~& *^ ^V\~&v ~&d+ &d.(precognizer,recognizer):= &!+-+-,
         <'bad P type'>!%),
      help: 'transform top type to printing function'],
   type_constructor[
      mnemonic: 'I',
      microcode: (~&l?/~& ~&/<~&V/primitive_types-g <>>+ ~&r); -&~&lh,~&lhd.recognizer&-?(
         ^\~&rt ~&rhNVNC+ &rh.target:= -+
            (~&nS primitive_types)?<l(~&NiX;+ ~&rd.recognizer,~&r; "t". ~&/<"t">; ^H/~&lhd.recognizer ~&),
            ~&lh; ^/~&d.mnemonic *^ ^V\~&v ~&d+ assign(
               &d.(generator,(reader,initializer),(mnemonic,printer),(microcode,arity),(help,target)),
               (0,&,&,&,&)!)+-,
         <'bad I type'>!%),
      help: 'transform top type to instance recognizer'],
   type_constructor[
      mnemonic: 'C',
      arity: 1,
      microcode: (~&l?/~& ~&/<~&V/primitive_types-g <>>+ ~&r); -&~&lh,~&lhd.printer&-?(
         ^\-+~&i&& ~mnemonic=='R'?h/~&t ~&,~&rt+- ~&rhNVNC+ &rh.target:= -+
            ~&l?\~&r ~&r; "c". disassembly; -+
               ~&?\<'R type operator used with non-recursive function'>!% ~&drPvH*^,
               ~&aavPB^& ~&adl=='refer'?(
                  ~&a; ^V/~&d :^\~&vt ~&vh; ^V\~&v ^/~&dl "c"++ ~&dr,
                  -&all~&+ ~&v,~&i&-+ ~&adPfavh2Ravt2CV)+-,
            ^/~&l -+
               --<`-!* iota 80>+; ~&h;; ^T\~&t; \/guard; ; ^H\~&+ //guard; ; //--+ ~&iNC,
               (~&nS primitive_types)?<rl(
                  ~&l?/~&rrd.printer ~&NiX;+ ~&rrd.printer,
                  ~&l?(~&rr; "t". ~&a; ~&/<"t">; ^H/~&lhd.printer ~&,~&rr; "t". ~&/<"t">; ^H/~&lhd.printer ~&))+-,
            ^/-&~&rt,~&rth.mnemonic=='R'&- ~&lh; -+
               ^/~&d.mnemonic *^ ^V\~&v ~&d+ assign(
                  &d.(reader,(generator,initializer),(microcode,arity),(help,target)),
                  (0,&,&,&)!),
               -!~&d.mnemonic-={'U','N','G','y'},any~&+ ~&v!-*^?/~& *^ ^V\~&v ~&d+ &d.(precognizer,recognizer):= &!+-+-,
         <'bad C type'>!%),
      help: 'transform top type to exceptional input printing wrapper'],
   type_constructor[
      arity: 2,
      mnemonic: 'V',
      microcode: -&~&l,~&lt,~&lhthPX; both ~&i&& ~&d&& ~&d.printer&& ~&d.recognizer&-?(
         -&~&,~&h.mnemonic=='R'&-?rt(
            ^\~&rtt ~&rhNVNC+ &rh.target:= -+
               "v". disassembly; -+
                  ~&?\<'R type operator used with non-recursive function'>!% ~&drPvH*^,
                  ~&aavPB^& ~&adl=='refer'?(
                     ~&a; ^V/~&d :^\~&vt ~&vh; ^V\~&v ^/~&dl "v"++ ~&dr,
                     -&all~&+ ~&v,~&i&-+ ~&adPfavh2Ravt2CV)+-,
               ~&lthPhX; ("i","o"). "f". (~&a; ~&/<"i">; ^H/~&lhd.recognizer ~&)?(
                  ~&H(
                     ~&H(
                        --<`-!* iota 80>+; ~&h;; ^T\~&t; \/guard; ; ^H\~&+ //guard; ; //--+ ~&iNC,
                        ~&a; ~&/<"i">; ^H/~&lhd.printer ~&),
                     "f"; (~&/<"o">; ^H/~&lhd.recognizer ~&)?/~& <'bad output type'>!%),
                  <'bad input type'>!%)+-,
            ^\~&rt ~&rhNVNC+ &rh.target:= ~&lthPhX; ("i","o"). "f". (~&/<"i">; ^H/~&lhd.recognizer ~&)?(
               ~&H(
                  ~&H(
                     --<`-!* iota 80>+; ~&h;; ^T\~&t; \/guard; ; ^H\~&+ //guard; ; //--+ ~&iNC,
                     ~&/<"i">; ^H/~&lhd.printer ~&),
                  "f"; (~&/<"o">; ^H/~&lhd.recognizer ~&)?/~& <'bad output type'>!%),
               <'bad input type'>!%)),
         <'bad V type'>!%),
      help: 'transform top types to i/o validation wrapper generator']>

numbers = # can allow sequences of X's to be abbreviated; not currently used

^A(~mnemonic,~&)* ~&H\'0123456789' * type_constructor$[
   mnemonic: ~&iNC,
   help: ~&iNC; "k". 'numeric value '--"k"--' for '--"k"--'-tuple type constructors',
   microcode: ! ^/~&l ~&r; -+
      ^T\~&r ~&l; ~&lS+ ~&D/binary_types-X+ iota+ %np+ ~&iNC+ ~mnemonic*=,
      _type_constructor%LWMk+ -~ -=(~&iNCS '0123456789')+ ~mnemonic+-]

type_constructors = # contains all the other tables, remaining unused letters are F,H,K,v

type_optimization primitive_types-- type_operators-- type_validation ~&L <
   unary_types,
   binary_types,
   stacking_types,
   atypical_types,
   ## numbers>
