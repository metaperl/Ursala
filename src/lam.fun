
#import std
#import nat
#import opt
#import lag
#import ogl

#comment -[
This module contains some functions in support of lambda abstraction.

Copyright (C) 2007-2010 Dennis Furey]-

profile = +^(-=/'trace'?\~&l! ! guard^|/~& ^C\~&+ !,-=/'profile'?\~&! ! ^\~&r std-profile) __switches

#library+

lambda_constant = ~&d preprocess ogl-token_forms <operator[mnemonic: '(lambda constant)',meanings: mode[postfix: constant]]>
csem            = ~semantics lambda_constant

#optimize+

reducible_form = # allows simplified combinator semantic fields by imposing a fixed branching pattern in disassembled trees

~&i&& -+
   ^?(
      -&~&adl=='tuple',~&adr-={~&hthPX,~&=>},~&av,~&avt&-,
      ~&\~&adPfavPMV (~&V/('tuple',~&hthPX)+ ~&lrNCC)=>+ ~&favPM),
   ^?(
      -&~&adl=='couple',~&adr-={~&hNXthPX,(^)=>},~&av,~&avt&-,
      ~&\~&adPfavPMV (~&V/('couple',~&hNXthPX)+ ~&lrNCC)=>+ ~&favPM),
   ^?(
      -&~&adl=='compose',~&adr-={~&hthPXNX,(+)=>},~&av,~&avt&-,
      ~&\~&adPfavPMV (~&V/('compose',~&hthPXNX)+ ~&lrNCC)=>+ ~&favPM)+-

beta_reduction = # takes a lambda concretion ("x",f "x") and a tuple of trees y to f y provided y matches "x"

~&larPalrHPard2falrvPDPMVYNqB+ %fOZsoXTXMk^\~&lr -+
   -&~&g,-:0!&-+ %soXTWZLMk+ * %gsoXTtXXMk; indexable+~&rrPlX&& ~&rlPNrrPXlHX; &&~& _token%TswUfZXTI+ ~&r,
   ^D/~&r ~&NNXllPX; %soXTtXLMk+ ~&arv^?\~&arlXNC ~&falrvh2Xlrvth3XXPWllrNXXSPrlNrXXSPT+-

lambda_concretion = # takes a disassembled function of the form "x". f "x" to ("x",f "x") if possible

~&ilrBBiB+ -+
   ^H\~&l ~&r; ("apply","argument"). -+
      ^/~&l %soXTWCRk ~&ar^& "apply"?=ardl\("argument"?=ardl/~&al ~&ard2falrvPDPMV) -+
         ~&all^?(~&alr?\~&fallPrvh2XPR ~&V/('tuple',~&hthPX)+ ~&fallPrXlrPrXXPWlrNCC,~&alr?\~&ar ~&falrPrvth3XPR),
         %tsoXTXMk+ ~&arvhdrPvHor4lX+-,
      ^\~& -+
         ~&r+ ~&ar^?(
            ^(~&rl,~&V/('tuple',~&hthPX)+ ~&lrrPNCC)+ ^rrPlfPrlPlarr3XRX/~& ~&falrlPXPR,
            ^rlCrNXNVX/~&al ~&NNalPXX; ~&rl+ ~&rlZ-> -+
               ~&rlrr2w?\~&llPrlrr2XX ^/successor+~&ll ~&lr,
               ^/~& :/`a+ ~&h+ %nP+ ~&l+-),
         ^/~&dlPvLPCo ~&iNH+ -++-+ -+
            * "p". indexable/"p"?/~& "p":= 0!,
            all_points*=+ ~&vhdrPvHo2S+ ~&a^& "apply"?=adl/~&avhNC ~&favPML+-+-,
      %soXTMk; ~&\(~&V/("argument",0) <>); %soXTWCRk ~&al^& case~&aldl\0! {
         'constant': ~&alvihB,
         'tuple': ^R/~&f ^\~&ar %sfZXTMk+ abstract_disassembly+ ~&al,
         'refer': ~&alv&& ^R/~&f ^/~&alvh ~&V/('tuple',~&hthPX)+ ~&alvh2rNCC,
         'couple': -&~&alvitB,~&farlvPDrlXS2M; ~&g&& ^V\~& ~&/'tuple'+ ~&tt?\~&hthPX! ! ~&=>&-,
         'compose': ~&alvitB&& -|
            %sfZXTMk^arPfaRB/~&f %sfZXTWMk^/~&alvh ~&alvtt?/~&faldvtPVPrXPR %sfZXTMk+ ~&falvth3rXPR,
            ^lal2rENlfPrlar2XRQ/~& abstract_optimization+ ~&al|-,
         'conditional': -&
            ~&alv; -&~&,~&t,~&tt,~&tttZ&-,
            -+concrete+~&r&& ~&rdrPvHo?/~&lfalvth3rXPR ~&lfalvtth4rXPR,^/~& ^R/~&f %sfOXTWMk+ ~&alvh2rX+-&-,
         'recur': %osfZXTWXMk; -+
            ~&aivB&& -&
               ~&adl=='tuple'!| ~&adr-={~&,~&=>,~&hthPX},
               ^R/~&f %sfZXTWMk^\~&a ~&avh; *^0 ^V\~&v ~&d+ -&~&vZ,~&dr-={0!,~&}&-?\~& &dl:= 0!&-,
            ^J/~&f %sfXTMk^R/~&f %sfXTWMk^\~&ar ~&V/('field',~+~&h)+ ~&alv+-,
         'field': -&~&alv,concrete+~&alvh&-&& -|
            ~&alvhdrPvHo3rX; ~&l&& %tsfZXTXCRk refer ~&all?(
               ~&alr?/(%fOtsfZXTXXMk; ~&fallPrXlrPrXXPWlrBiB; %sfOZXTWMk; ~&i&& ~&V/('tuple',~&hthPX)+ ~&lrNCC) -|
                  -&~&ardl=='tuple'!| ~&ardr-={~&,~&=>,~&hthPX},~&arv,~&fallPrvh2XPR&-,
                  %otsfZXTXXMk; concrete+~&ar&& ~&iNV+ ~&NiX+ !+ ^H/~+~&al ~&ardrPvHo|-,
               ~&alr?\~&ar -|
                  -&~&ardr==~&,~&arv,~&falrPrdvtPVPXPR&-,
                  -&~&ardl=='tuple'!| ~&ardr-={~&=>,~&hthPX},~&arvitB&-&& ~&arvtt?/~&falrPrdvtPVPXPR ~&falrPrvth3XPR,
                  %otsfZXTXXMk; concrete+~&ar&& ~&iNV+ ~&NiX+ !+ ^H/~+~&al ~&ardrPvHo|-),
            ~&ardl=="argument"&& ~&V/("apply",0)+ ~&alrNCC|-}+-,
   ^/~& (~~ ~&l+ ~&w->~&llzPNCTrX)+ %ssSXWMk+ ~&brlX+ ~&G\('apply','argument')+ ~&dlPvLPCo+-

optimizing_inverse_concretion = # takes a lambda concretion ("x",f "x") to an optimized f, where f "x" is a function

%soXTMk+ -+
   (refer+ //+ -|reducible_form+ abstract_optimization+ abstract_disassembly,~&|-) beta_reduction^\~&ar ^/~&all -+
      ~&aa^& ~&fafPaal2aard3fafalrvPDPDPMVXJJ; ~&aardl2lw?/~&aar ~&aarv?(
         (all ~&dl=='constant')?aarv/~&aarvhd2dvvhPSPVNCV ~&afarPJ; -|
            ~&a; ~&dl=='tuple'&& (~&V/('couple',~&hNXthPX)+ ~&lrNCC)=>+ ~&v,
            ^alPfaRB/~&f %soXTWZsoXTLXMk^\~&av ^rlrldrlNCBPvLPTo2cZrBB/~&adrlNCBPvLPTo lambda_concretion+ %fI+ ~&adr,
            ~&a; ^V\~&v ~&NiX+ +^(//++ ~&dr,(^^)=>0!!+ (~)*+ ~&NiC|\+ &h!*+ ~&v)|-,
         ~&V/('constant',~&NhXNX)+ ~&aarNC),
      ~&falldrZlNCBPvLPToPrX2J+-,
   %soXTdWoXMk^/(^/~&l reducible_form+ ~&r; ||~& abstract_optimization+ abstract_disassembly) ~&NNXlX; ~&ardr^?(
      -&~&ardl=='tuple',~&arv,~&arvt,~&arvttZ,^WlrBiB/~&f %tsoXTXWMk+ ~&a; ^(^\~&rvh .\&l+ ~&l,^\~&rvth .\&r+ ~&l)&-,
      ~&V/('field',~&NhX)+ ~&NiXNVNC+ !+ ~&al)+-

lambda_optimization = # takes a parse tree and cleans up some of the code generated by lambda abstraction

profile\'source optimization' ~&i&& ||~& -+
   ~&ar^& ^V\~&falrvPDPM ~&ard+ &ard.(filename,location):= ^(
      -|~&ard.filename,~&al.filename|-,
      -|~&ard.location,~&al.location|-),
   ^/~&d -+
      (~&rZ&& ~&l; *^0 ~&vig&& ~&d.semantics&& not ~&d.lexeme.&ihB==`"&& ~&d.semantics; ~&rZlilZBPBZ)?(
         ~&l; -+
            ~&V\<>+ token$[lexeme: '(evaluated)'!,semantics: !+ !]+ optimization+ evaluation,
            ~&a^& ~(lexeme,semantics)==('(lambda constant)',csem)?ad/~&a ~&adPfavPMV; &d.postprocessors:= 0!+-,
         _token%TMk+ -+
            ~&i&& _token%TswUfOZXTMk; *^0 ~&dr?\~&dl ^V\~&v token$[lexeme: :/`(+ --')'+ ~&dl,semantics: !+ ~&dr],
            ~&l?\-+_token%TswUfOZXTCk reducible_form,abstract_optimization,_token%TswUfOZXTMk+ ~&r+- -+
               ~&l?(~&l->r ^/~&lt optimizing_inverse_concretion+ ~&lhPrX,reducible_form+ abstract_optimization+ ~&r),
               ~&lNrXX; ~&l->r _token%TswUfOZXTdLwXnwXMk+ ^/predecessor+~&l ~&r; ||~& ^rrlPlCrrPXB/~&l -+
                  ~&i&& ^riB/~&l abstract_disassembly+ ~&r,
                  _token%TswUfOZXTWZMk+ lambda_concretion+ _token%TswUfOZXTMk+ ~&r+-+-,
            _token%TswUfOZXTnwXMk^/~&r ~&l; _token%TMk; -+
               abstract_disassembly+ ~&r+ evaluation,
               ~&a^& ^V\~&favPM ~&ad+ &ad.(postprocessors,semantics):= ~&NiX+ !+ ?(
                  ~&a; ~&d.semantics&& not ~&d.lexeme.&ihB==`"&& ~&d.semantics; ~&rZlilZBPBZ,
                  ~&\(~&iNX++ !+ ~&a) -+
                     ("d","s"). ^(~&V/"d"+ ~&lS,abstract_interpretation/"s"+ ~&V/('',~&)+ * ~&r|| ~&lNXNV),
                     ~&ad; ^/~& ~&H+ ~/semantics lag-suffix+-)+-+-),
      ^/~& length+ ~&l+ (("o". =="o"!| -&~&,~&rZ,~&llrB,~&ll=="o"&-) optimization)-~+ ~&d.postprocessors+-+-

lambda_abstraction = # takes the application token to a preprocessor for the . operator when used for lambda abstraction

((filename,previous),lexeme,location):=(&,&)!; "a". ^V(~&d,preprocess*+ ~&v); -+
   (&rd.postprocessors:=r ~&l)^/~&rd.postprocessors ~&ar^& ~&arv?\~&alrdPH -+
      ||~&r ?(
         ~&rv; (* &d.(filename,location):= &!); all -&
            ~&d== lambda_constant,
            &!! ~&v; ~&itZB&& ~&h; ~&i&& not ~&vZ&& ~&d.semantics.&Z!| ~&d.lexeme.&ihB==`"&& ~&d.semantics; ~&rZlilZBPBZ&-,
         ~&/(~&rvhd3lNCV; &d.(filename,location):= ~&vhd.(filename,location)) -&
            ~&ld; =="a"+ ((filename,previous),lexeme,location):= (&,&)!,
            ~&rvhd; ((filename,location):= &!)== lambda_constant,
            -+
               &d.(filename,location):=~&vthd.(filename,location),
               ~&rvhvh2tC; //~&V ~&d preprocess ogl-token_forms ~&iNC operator[
                  ogl-mnemonic: '(lambda composition)',
                  meanings: mode[infix: compose]]+-&-),
      ^/~&ar ^V\~&falrvPDPM ~&ard+ &ard.((preprocessor,lag-suffix),semantics):= ~&/&+ !+ ~&ar; -|
         -&~&v,~&vt,~&vttZ&-&& -+
            ~&hthPH?=(! ~&hthPX; ^; //+ ~&H,-&~&,~&rZ,~&l,~&ll,~&lr== ~&hthPX,~&hthPX;+ ^;+ //++ ~&ll&-),
            ~&H+ ~&d.(semantics,lag-suffix)+-,
         -&~&v,~&vtZ&-&& -&~&,~&rZ,~&l,~&ll,~&lr== ~&h,~&h;+ //++ ~&ll&-+ ~&H+ ~&d.(semantics,lag-suffix),
         +^(//++ ~&H+ ~&d.(semantics,lag-suffix),(^^)=>0!!+ (~)*+ ~&NiC|\+ &h!*+ ~&v)|-+-,
   ^\~&vth ~&vh; -+
      ?^/(~lexeme-=+ ~&lS) -+
         \/~& -+
            &d.(filename,location):= ~&vhd.(filename,location),
            ~&VNC\<>; //~&V lambda_constant+-,
         ~&V\<>++ (lexeme,semantics):=+ ^/~lexeme.&t+ ~lexeme;+ -:+ ^p/~&lS ~&rS; * !+ !+-,
      ~&rNlXXS+ ~&/&; refer -?
         -&~&ard.lexeme==':',~&arv,~&arvt&-: ~&llNXrXSPrNlXrXSPT+ ~&falrvhPvth2XPGPW,
         -&~&ard.lexeme=='(',~&arv&-: ~&arvt?\~&falrvh2XPR ~&llNXrXSPrNlXrXSPT+ ~&falrvhPdvtPVXPGPW,
         -&~&ard.lexeme=='<',~&arv&-: ~&arvt?\~&falNXrvh2XPR ~&llNXrXSPrNlXrXSPT+ ~&falrvhPdvtPVXPGPW,
         (~&ard.lexeme; ~&i&& ~&h==`"): ^iNC/~&al ~&ard.lexeme,
         <'invalid abstraction'>!%?-+-+-

