
# this file provides the command line interface to the compiler

#import std
#import nat
#import fen
#import pru
#import for
#import mul
#import def
#import con

#comment --<'Copyright (C) 2007-2010 Dennis Furey'> ~&H(
   ~&ziyQ+ ~&h.contents+ ~&iNH+ ~target_filter+ \/~&H ~&/& default_formulation default_formulators,
   ~formula help_formulator default_help_topics)

profile = +^(-=/'trace'?\~&l! ! guard^|/~& ^C\~&+ !,-=/'profile'?\~&! ! ^\~&r std-profile) __switches

#optimize+

report_errors_with = # takes a command name and a function and supplements the error messages

("s","f"). guard/"f" :^(("s"--':')--+ ~&h,~&t)+ ~&?(
   %sLI?/~& :/' (garbled message)'+ * %snWXI?/^|T(~&,:/` + ~&h+ %nWP) * (skip/32 take/127 characters)?</~& `?!,
   <' undiagnosed error :('>!)

#executable (<'parameterized'>,<'std.avm','nat.avm'>)

fun = # takes an invocation record to a list of target files

profile\'overhead' ~command; -+
   ~std-options?(
      -+
         ^H\~&rr report_errors_with^/~&rl.command_name ~&l?(
            ^H\~&rl core_dumper+ -&~&,%np+ ~&iNC&-+ ~&c/'0123456789'+ ~&l,
            compiler+ ~&rl),
         ^/(~std-parameters*==+ ~keyword=='phase'*~+ ~std-options) report_errors_with/'fun' -+
            //customized (help_topics:= default_help_topics!) default_formulation default_formulators,
            std-options:= ~keyword~='phase'*~+ ~std-options+-+-,
      report_errors_with/'fun' -|
         ~files; compiler default_formulation default_formulators,
         ! <file[contents: <'fun: warning: no output generating directives were specified',''>]>|-),
   ~files!|~std-options?/~& ! command_line[std-options: <std-option[std-keyword: 'help']>]+-
