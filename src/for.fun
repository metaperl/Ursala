
#import std
#import nat
#import ogl
#import ops
#import apt
#import eto
#import xfm
#import dir
#import lag
#import fen
#import mul

#comment -[
This module defines the data structure specifying command line options
to the compiler and some supporting functions.

Copyright (C) 2007-2010 Dennis Furey]-

#export+
#library+

------------------------------------------------------ data structures ------------------------------------------------------

version_number   = '0.7.1'--' ['--__source_time_stamp--']'
maintainer_email = 'ursala-users@freelists.org'

#optimize+

formulator ::  # specifies a command line option to the compiler

mnemonic   %s  # full name of the formulator as it appears on the command line
filial     %b  # true if it takes a file parameter
formula    %fO # a function taking ((<parameter..>,file%Z),formulation) to a new formulation
extras     %sL # allowable parameters for the option, currently used only for online documentation
requisites %sL # required parameters for the option, currently used only for online documentation
favorite   %n  # disambiguation precedence, more is higher
help       %s  # a one line description for on-line help

---------------------------------- functions supporting automatically generated formulators ----------------------------------

direct_all = # puts a named directive around all the symbols in all the source files, given as token streams

"m". (("o","d"),"t"). * -+
   &hh.(filename,location):= ! ~&/'command-line' &,
   //: <~&h dir-token_forms"o" (~dir-mnemonic== "m")*~ "d">,
   "t"--+ ^T(
      ~&H\"t" ~&?\<>!! ! ~&ahh.lexeme~='(separation)'&& -+
         ~&iNC+ ~&iNC+ ~&H\apt-separation,
         (filename,location):=+ !+ ~&ahh.(filename,location)+-,
      ^lrNCT/~&y ~&z; -+
         ^lrNCT/~&y ~&z; (filename,location):= ('command-line',&)!,
         --<~&th dir-token_forms"o" (~dir-mnemonic== "m")*~ "d">+-)+-

direct_symbol = # puts a named directive around a symbol

"m". (("o","d"),"t","s"). * ~&a^& ~lexeme;-&~&h==`#,~&t,~&th~=`#,~&z~=`-&-?ahh/~&ahPfatPRC ?(
   ~&a; ~&a^& -!
      ~&ah; any ~preprocessor.&Z&& ~lexeme=="s",
      &&~&fatPR ~&ah; all ~preprocessor&& not ~lexeme; -!
         -&~&h==`#,~&t,~&th~=`#&-,
         -= :/'(separation)' ~ogl-mnemonic* ~loose*~ "o"!-!-,
   (&hh.(filename,location):= ||-&~&ht,~&hth.(filename,location)&- ! ~&/'command-line' &)+ -+
      //: <~&h dir-token_forms"o" (~dir-mnemonic== "m")*~ "d">,
      "t"--+ ^T(
         ~&H\"t" ~&?\<>!! ! ~&ahh.lexeme~='(separation)'&& -+
            ~&iNC+ ~&iNC+ ~&H\apt-separation,
            (filename,location):=+ !+ ~&ahh.(filename,location)+-,
         ~&a; ~&a^& (~&ah; any ~lexeme; -&~&h==`#,~&t,~&th~=`#&-)?(
            :^\~&at ~&ah; -+
               ^T/~&l ~&r; -+
                  :^\~&t ~&h; (filename,location):= ('command-line',&)!,
                  //: ~&th dir-token_forms"o" (~dir-mnemonic== "m")*~ "d"+-,
               ~- ~lexeme; -&~&h==`#,~&t,~&th~=`#&-+-,
            -!~&atZ,~&athh.lexeme=='(separation)'!-?(
               :^\~&at ~&ah; -+
                  ^lrNCT/~&y ~&z; (filename,location):= ('command-line',&)!,
                  --<~&th dir-token_forms"o" (~dir-mnemonic== "m")*~ "d">+-,
               -&~&aht,~&ahz.lexeme=='(separation)'&-?\~&ahPfatPRC ^T\~&at :^\~&ahzNCNC ~&ahy; -+
                  ^lrNCT/~&y ~&z; (filename,location):= ('command-line',&)!,
                  --<~&th dir-token_forms"o" (~dir-mnemonic== "m")*~ "d">+-)))+-,
   (-&~&l,~&lzh.lexeme=='(separation)',~&r,~&rhh.lexeme; -&~&h==`#,~&t,~&th~=`#&-&-?/~&lyPrT --)^alPfarPRX/~&f ~&NaX; -+
      ~&r?\~&lxPrX ^\~&rt ~&x+ ~&rhPlC,
      ->~&rhPlCrtPX ~&r&& ~&rh; not any ~lexeme; =='(separation)'!| -&~&h==`#,~&t,~&th~=`#,~&z~=`-&-+-)

direct_last = # puts a named directive around the last declaration in the last source file

"m". (("o","d"),"t"). ~&?(
   ^T/~&y ~&z; ^H\~&iNC -+
      direct_symbol"m"/("o","d")+ ~&/"t"+ -+
         ~&i&& ~&h.lexeme,
         skipwhile ~lexeme; not all \/-= :/`_ letters+-,
      ~&Lx; skipwhile not ~lexeme-= ~ogl-mnemonic* ~loose*~ "o"+-,
   <' source files necessary for --'--"m"--' were not supplied'>!%)

directive_based_formulators = # takes a list of directives to formulators that allow them to be invoked on the command line

~nestable.&Z*~; (* direction:= ~direction; ~&i&& \/guard * 'usage: #'%= 'usage: --'); * formulator$[
   mnemonic: ~dir-mnemonic,
   favorite: ~dir-favorite,
   extras: <'symbol-name'>!,
   formula: ~parameterized?(
      ~(dir-mnemonic,dir-parameter); ("m","p"). -+
         ~&r+ &r.token_filter:= +^\-|~&r.token_filter,! ~&|- -+
            ~&rr?\direct_last"m"+~&lrlPX ~&rr=='all'?/direct_all"m"+~&lrlPX direct_symbol "m",
            ~(&r.(operators,directives),&l)+-,
         ^\~&r -+
            ~&ll?(
               ^\~&lr -+
                  * * filename:= 'command-line'!,
                  ^lrNCH\-+mat`,,~&ll+- ~&/'command-line';+ ~&r.(operators,directives); ?(
                     ==(extra_tabular default_operators,default_directives),
                     ~&\fen-lexer ! fen-lexer\default_directives extra_tabular default_operators)+-,
               "p"!?(
                  ~&/<<token[lexeme: '(default '--"m"--' parameter)',filename: 'command-line',semantics: "p"!!]>>+ ~&lr,
                  <' usage: --'--"m"--' "expression"[,symbol-name|all]'>!%)),
            ^\~&r ~&ll; ?(
               ~&itB&& ~&z; -&~&,~&h~=`_,all \/-= :/`_ letters&-,
               ~&/~&yzX ~&iNX)+-+-,
      ~dir-mnemonic; "m". ~&r+ &r.token_filter:= +^\-|~&r.token_filter,! ~&|- -+
         ~&rr?\direct_last"m"+~&lrlPX (~&rr; any =='all')?(
            direct_all"m"+ ~&lrlPX,
            _token%LLLMk++ ~&arr^?\~&! +^\~&falrlrtPXPXPR ~&alrlrhPXPX; direct_symbol "m"),
         ~(&r.(operators,directives),&lrlX)+-),
   requisites: ~&iiNCB+ ~parameterized,
   help: 'invoke the #'--+ --' directive (see --help directives)'+ ~dir-mnemonic]

help_formulator = # takes a table of help topics as defined in def.fun

formulator$[
   mnemonic: 'help'!,
   favorite: 1!,
   formula: ~&r++ &r.(source_filter,target_filter):=+ ~&/<>!++ !++ ~&iNC++ file$$[
      contents: :/''++ --<'',''>++ ||(~&iNC+ 'no help available for '--+ mat`,+ ~&ll)+ -??-+ -+
         \/~&T <
            ~&/(^D(~&llihB,~mnemonic*+ ~&r.formulators); any ~&l&& [=) -+
               ^T/~&rhthPNCC [=~|+ ~&lrtt2X,
               ^/('--'--+ ~&llh) ~&r.formulators; -+
                  (* ^T/~&l :/` + ~&r)^p\~&rS ~&lS; (* ~&rS+ zipp` )^D\~& leql$^,
                  //-- ~&lrNCC ~&bbI ^(~&,`-!*)~~ ('option','effect'),
                  -<&l+ * ^(^T('--'--+ ~mnemonic,-!~filial,~extras,~requisites!-&& ' ...'!),~help)+-+-,
            ~&r.formulators; -+
               //-- <
                  'fun version '--version_number,
                  '   compiler for the Ursala programming language',
                  '   Please send feedback to '--maintainer_email--'.',
                  '',
                  'usage:',
                  '   fun [<file>[.fun|.avm] | <option>]*',
                  '',
                  'options:'>,
               -<&+ :/'   --phase <0|1|2|3>'+ -+
                  * (~&B?\~&T ^T/~&l :/` + ~&r)^(
                     ^T/('   --'--+ ~mnemonic) -&~&,:/` &-+ (~&B?\~&T ^T/~&l :^/~&rh :/`,+ ~&rt)^(
                        ~requisites; ~&i&& '<'--+ --'>'+ mat`|,
                        ~extras; ~&i&& '['--+ --']'+ mat`|),
                     ~filial&& '<configuration-file>'!),
                  ~&a^& -+
                     :^(~&lah+ &lah.extras:= ~&rlx,^R/~&lf ^T\~&lat ~&rr&& ~&lahNC+ &lah.extras:= ~&rr),
                     ^/~& ~&ah.extras; ~&NiX; ->~&rhPlCrtPX ~&r&& leql\iota48+ ~&llLPT+-+-+->,
         * ("q","x"). ~&/(~&ll; ~&i&& ~&h[="q") "x"+ ~&llPrX+-],
   extras: ~&nS,
   help: 'show information about options and features'!]
