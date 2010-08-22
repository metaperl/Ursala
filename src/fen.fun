
#import std
#import nat
#import pag
#import lag
#import dir
#import ogl
#import apt

#comment -[
This module combines most of the code for the front end of the compiler.

Copyright (C) 2007-2010 Dennis Furey]-

#library+
#optimize+

directive_inference = # puts directives into matching nested pairs by filling in the missing ones

"d". _token%LLMk; num; _token%LnwXLMk; -**=; _token%nwXLMk; ~&rSS+ rlc~&llPrlPE+ -+
   ~&NiX; ~&ar^?\~&alx ~&arhr.lexeme;-&~&h==`#,~&t,~&th~=`#&-?(
      ~&arhr.lexeme.&z==`+?/~&farhPlCrtPXPR ?(
         -&~&arhr.lexeme.&z==`-,~&al,==+ ~&y~~+ ~&abhr.lexeme&-,
         ~&/~&fabt2R ~&alxPrhPNCTPfNart2XRT),
      ~&alxPrhPNCTPfNart2XRT),
   ^= -+
      ~&/<<>>; ~&ar^?\~&alhrS (~&arhhr.lexeme; -&~&h==`#,not ~&z-='-#'&-)?(
         ((~&arhhr.lexeme.&t; ~&z==`+?/~&y ~&)-= ~dir-mnemonic* ~nestable*~ "d")?(
            _token%nwXddLwXLLwLLXowXMk; -+
               ^T/~&rrSx ^T/~&larh ^T/~&rlSx2L ^R/~&lf ^/~&rlal2C ^T\~&lart -&
                  -&~&r,~&rhlt,~&lart,~&larthhr.lexeme; ~&h~=`#&& ~='(separation)'&-,
                  ~&NlrHXNCNC\separation+ location:=+ !+ ~&larhhr.location&-,
               ^/~& ~&alh; _token%nwXdLwXLMk+ *~ not (~&hlr.lexeme.&t; ~&z==`+?/~&y ~&)-= ~dir-mnemonic* ~blockable*~ "d"+-,
            ^T/~&arh ^R/~&f ^\~&art :^\~&alt :^\~&alh ^/~&arh -+
               &r.((preprocessor,semantics),lexeme):= ~&/&+ --'-'+ ~&r.lexeme; ~&z==`+?/~&y ~&,
               ~&arhh+-),
         (~&arhhr.lexeme; -&~&h==`#,~&z==`-&-)?\~&arh2falrtPXPRT (~&arhhr.lexeme.&ty-= ~dir-mnemonic* ~nestable*~ "d")?(
            ^T/~&alhrS ^T/~&arh ^T(
               ~&alt&& ~&alth; ~&lSxL+ *~ not (~&hlr.lexeme.&t; ~&z==`+?/~&y ~&)-= ~dir-mnemonic* ~blockable*~ "d",
               ^R/~&f _token%nwXddLwXLLwLLXMk+ ^/~&altNNXY ^rlrTB(
                  -&~&alt,~&alth,~&althhlt,~&NlrHXNCNC\separation+ location:=+ !+ ~&arhhr.location&-,
                  -&~&alt,~&alth,~&art,~&arthhr.lexeme=='(separation)'&-?/~&artt ~&art)),
            (^w/~&arhhr.lexeme ~&r.lexeme*+ ~&alhrS)?\~&falrtPXPR -+
               ^T/~&rlrSx3larh3TrllS2LPT ^R/~&lf ^(
                  ~&rlxPrtPTPlalt3C,
                  -&~&rl,~&rlhltZ,~&lart,~&larthhr.lexeme=='(separation)'&-?/~&lartt ~&lart),
               ^/~& ^(~&arhhr.lexeme,~&Nalh2X); ~&r+ _token%nwXdLwXLWswXMk+ ->~&lrrhPlCrtPXPX ^EZ/~&l ~&rrhrr.lexeme+-)),
      _token%nwXLLMk+ rlc not -!
         ~&lr.lexeme; =='(separation)'!| -&~&h==`#,~&z-='+-'&-,
         ~&rr.lexeme; =='(separation)'!| -&~&h==`#,~&t,~&th~=`#&-!-+-+-

#optimize-

(# lexer takes a list of operators and a list of directives to a lexical analyzer that inserts separators by hand between
declarations and removes white space by hand before closing aggregate operators so as to work with the kind of parser defined
below. #)

lexer =

("o","d"). ^H\~&r ("f". guard/"f"+ (("s". :^\~&t "s"--+ ~&h)+ --':'+ ~&l)) -+
   ->~&t ~&i&& ~&hZ!| ~&htZ&& ~&hh.lexeme=='(separation)',
   directive_inference"d"; ~&LS+ rlc ~&rh.lexeme; -!\/-= :/']-]-' ~&F ~match* "o",~&h==`#&& ~&z==`-!-,
   ~&rSS+ rlc~&llPrlPE+ ~&/<>; ~&r->lx ||~&rhPlCrtPX ~&rhr.lexeme-={'=','::'}&& ~&l&& -+
      -&
         ~&lr; -&~&,~&hr.lexeme; not =='(separation)'!| -&~&h==`#,~&z-='+'&-&-,
         ^\~&rt :^/~&rh ^T/~&llx _token%nwXLMk+ -+
            -&~&,~&t,~&thr.lexeme=='##'&-?\~& -&~&,~&hr.lexeme; -&~&h==`#,~&z-='+'&-&-?tt/~&t ~&thPhttPCC,
            (&hr.location:= ~&thr.location)+ :/(~&/0 separation)+ ~&lr+-&-,
      ^\~&r ~&l; ~&lrSPrX+ ~&/<>; _token%nwXdswXLwLXMk+ -> (
         ~&r&& -!
            -!~&lZ,~&lhl,~&lhrr.lexeme.&h==`",~&rhr2lhrr3X.location; ~&B&& ==+~&bl&& ~&br; ^|E/successor ~&!-,
            ~&l; all ~&rr.lexeme; ~&c/'"<(,)>'!-,
         ^\~&rt :^\~&l ^\~&rh -+-&~&lh-='<(',~&r&-?/~&rt ~&r,^/~&rhr.lexeme ^T/~&llhl2B ~&rhr.lexeme; &&~& -={')','>'}+-)+-,
   -**=+ num+ tokenizer ~&L <
      <lag-directives dir-token_forms"o" "d",built_ins ogl-token_forms "o">,
      <raw_data,markup,numbers,quoted_variables/`" `",nested_quotes/`' `'>,
      <identifiers :/`_ letters,quoted_characters>,
      <line_comments,nested_comments,non_terminating_comments,smart_comments>>+-

parser = # takes a set of operator precedence rules and a list of operators to a parser

("p","o"). -+
   ~&l|| ~&r; ~&i&& -|skipwhile ~&hzNCC=='()'+ ~lexeme,~&|-; % ^TNC(
      ^T(~&h.filename; ~&i&& --':',^T(~&l,:/`:+ ~&r)+ ~&h.location; ~~ ~&h+ %nP),
      ': can''t parse; error near '--+ --'...'+ take/12+ ~&h.lexeme; ==','?/'comma'! ~&),
   pag-parser syntax[
      pag-parameterless: -!
         # ~lexeme; -&~&h==`#,not ~&z-='+-'&-,
         ~lexeme-= :/']-]-' (~&F ~match* "o")-- ~ogl-mnemonic* ~meanings.ogl-solo*~ "o"!-,
      pag-prefix: -!
         ~lexeme; -&~&h==`#,~&z~=`-&-,
         ~lexeme-= :/'-[-[' ~ogl-mnemonic* (~meanings; ~ogl-prefix!|~aggregate)*~ "o"!-,
      pag-infix: ~lexeme-= ~&T(
         <',',']--[','(separation)','(juxtaposition)','(application)','(tight application)'>,
         ~ogl-mnemonic* ~meanings.ogl-infix*~ "o"),
      pag-postfix: -!
         ~lexeme; ~&i&& ~&h==`#&& ~&z==`-,
         ~lexeme-= :/']-]-' ^T(~&F+ ~match*,~ogl-mnemonic*+ ~meanings.ogl-postfix*~) "o"!-,
      pag-rules: ~&H\"p" -|~&,! &|-; ~~ -|~&,! &|-; ~~ "r". ~&b.lexeme; -!
         -&~&lh==`#,~&lt,~&lth~=`#&-,
         -&~&l=='(separation)',~&r~='(separation)',not -&~&rh==`#,~&rt,~&rth~=`#&-&-,
         lsm ~&Ls <
            (~&iiXS <',',']--[','(separation)'>)-- (~&D/'##' ~ogl-mnemonic* ~loose*~ "o")-- cross/<']--[',','> <'##'>,
            ~&irlXST :/('-[-[',']-]-') ~(ogl-mnemonic,match)* ~meanings.aggregate*~ "o",
            '(tight application)'-*(~ogl-mnemonic* ~tight*~ "o"),
            *-'(tight application)' ~&j(<'##',',',']--['>-- ~ogl-mnemonic* "o",~ogl-mnemonic* ~tight*~ "o"),
            cross/(<']--[',',','##'>-- ~ogl-mnemonic* ~loose*~ "o") ~&T(
               <'(tight application)','(juxtaposition)','(application)'>,
               :/'-[-[' ~ogl-mnemonic* ~meanings.aggregate.&Z*~ "o"),
            cross ~&llrTX/<'(juxtaposition)','(application)'> :/'(tight application)' ~&j(
               :/'-[-[' ~ogl-mnemonic* ~meanings.aggregate.&Z*~ "o",
               <']--[',','>-- ~ogl-mnemonic* ~loose*~ "o"),
            cross(
               :/'-[-[' :/']-]-' (~ogl-mnemonic* ~meanings.aggregate*~ "o")--(~&F ~match* "o"),
               <',','##',']--[','(juxtaposition)','(application)','(tight application)'>-- ~ogl-mnemonic* ~loose.&Z*~ "o"),
            (gdif ~&rlG; either -!~&E,~&rZ,~&rh-='#('!-)/"r" ~&T(
               (ogl-mnemonic* ~loose*~ "o")-- <',','-[-[',']--[',']-]-','##'>,
               ~&T(~&F ~match* "o",~ogl-mnemonic* ~meanings.aggregate*~ "o"))>!-,
      pag-juxtaposition: ?(
         -!~&rd.lexeme; ~&h==`#&& ~&t&& ~&th~=`#,~&l; ~&vitBhZB->~&vth; ~&d.lexeme; ~&h==`#&& ~&z==`-!-,
         ~&H\separation+ (filename,location):=+ !+ ~&rd.(filename,location),
         ~&H\apt-juxtaposition+ (filename,location):=+ !+ ~&rd; ^/~filename ~location; ~&i&& ^/~&l ~&r; ~&i&& predecessor),
      pag-concatenation: ?(
         -!~&rd.lexeme; ~&h==`#&& ~&t&& ~&th~=`#,~&l; ~&vitBhZB->~&vth; ~&d.lexeme; ~&h==`#&& ~&z==`-!-,
         ~&H\separation+ (filename,location):=+ !+ ~&rd.(filename,location),
         ~&H\application"o"+ (lexeme,filename,location):=+ !+ ~&/'(tight application)'+ ~&rd.(filename,location))]+-
