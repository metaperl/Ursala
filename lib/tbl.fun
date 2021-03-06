
#import std
#import nat

#comment -[
This module contains some functions for generating tables in LaTeX
format.

Copyright (C) 2007-2010 Dennis Furey]-

#optimize+

headings = # takes a list of trees of lists of strings to the latex code for some table headings

%sLMk+ -+
   (~&aatPB^?\~&a ~&ath=='&'?/~&fahthPTttPCPR ~&ahPfatPRC)+ *= =]'\cmid'?\~&iNC sep` ,
   ~&NiX; ~&ly+ %sLnsLXTLXMk+ ~&rdrPk-> ^(
      ^T\~&l (~&r; *= ~&a^& ~&av?/~&favPML ~&adNC); %nsLXLMk; ^T(
         ^lrNCT(~&y,--'\\'+ ~&z)+ mat'&'+ * ~&i&& -+
            1?=l/~&r ~&rZ?/(~&iiNCB+ `&!*+ ~&t+ iota+ ~&l) ^lrhPTrtPC(
               '\multicolumn{'--+ --'}{c}'+ ~&h+ %nP+ ~&l,
               :^(:/`{+ ~&h,~&t)+ ^lrNCT/~&ry --'}'+ ~&rz),
            ^/~&l ~&r; ~&i&& ~&t?\~& :/'\begin{tabular}{c}'+ --<'\end{tabular}$\!\!\!\!$'>+ ^T(~&y; * --'\\',~&zNC)+-,
         ~&iNC+ mat` + ~&rFlS+ ^p\~&rS ~&lS; (* '\cmidrule'--)+ -+
            (~&titB?\~& :^/~&h ~&t; ^T\~&zNC ~&y; * '(lr)'--)+ :^('(r)'--+ ~&h,~&t)+ ^lrNCT(~&y,'(l)'--+ ~&z),
            * :/`{+ --'}'+ ^T(~&l,:/`-+ ~&r)+ ~~ ~&h+ %nP,
            :/0; ~&ar^& :^(^/successor+~&al sum+~&alrhPX,^R/~&f ^/sum+~&alrhPX ~&art)+-),
      ~&r; * ~&a^& ~&av?\~&adlPNXNV ^V/~&ad ~&favPM; &&~& any~&dr),
   %nsLXTLMk+ * ~&a^& ~&av?\-+~&V\<>+ ~&/1+ ~&ad+- ~&adPfavPMV; ^V\~&v ^\~&d sum:-0+ ~&vdlPS+-

body = # takes a list of string lists or float lists to a latex table body

"d". -+
   (* --'\\')+ (* :-0 ^|T/~& ' & '--)+ transpose+ (~&rS+ zipp '')^*D\~& leql$^,
   * scientific_notation*+ %sLI?/~& * -+
      ==` -~; ^T/~&l ~&r; -!~&h~=`-,~&c/'123456789'!-?/~& :/` + ~&t,
      =='inf'?/'$\infty$'! =='-inf'?/'$-\infty$'! ~&,
      //(library/'math' 'asprintf') '%0.'-- --'f' ~&h %nP "d"+-+-

#library+

vwrap "n" = # takes a table argument and splits it n ways side by side, eliminating repeated columns

-+
   ^|\~& ~&dvihBPCoS; (rlc eql); *= ~&aht^?\~&a ^JalSPfarSPMp/~&f ~&hhPtSXS+ rlc~&EbhPO+ ~&a,
   (~&rSlSrSX+ nleq-<&l+ |=hS&r+ num)^lvdvDiNCQoSL2rp/(~&DlSL\iota"n"+ ~&l) ~&rSS+ zipp0^*D(leql$^,~&)^HK7L(
      *+ block+ ~&r?(~&l,predecessor+ ~&l)+ division\"n"+ sum/"n"+ nleq$^+ length*+ ~&r,
      ~&r; ~&rSS+ zipp0^*D\~& leql$^)+-

scientific_notation = # changes a floating point string of the form d.dE+d to d.d x 10^d in LaTeX format

-=/`$?/~& ~&aitB^?\~&a ?(
   -&~&ah-='eE',~&ath-='+-',~&att; ~&i&& all -=\'0123456789'&-,
   ~&\~&ahPfatPRC '$\times 10^{'--+ --'}$'+ ^T/-&~&ath==`-,~&athNC&- ~&att; ||('0'!) ->~&t ~&i&& ~&h==`0)

table = # takes the number of decimal places to a function taking (headings,<column..>) of type %sLTLeLsLULX

"d". :^/('\begin{tabular}{'--+ --'}'+ `r!*+ ~&r) --<'\end{tabular}',''>+ :/'\toprule'+ --<'\bottomrule'>+ ^|T(
   --<'\midrule'>+ headings,
   body "d")

sectioned_table = # takes the number of decimal places to a function taking (headings,<<column..>..>) of type %sLTLeLsLULLX

"d". :^(
   '\begin{tabular}{'--+ --'}'+ `r!*+ ~&rihB,
   --<'\end{tabular}',''>+ :/'\toprule'+ --<'\bottomrule'>+ ^|T(--<'\midrule'>+ headings,mat'\midrule'+ * body "d"))

elongation = # takes a caption to a function changing a table generated by the table function to longtable format

^rlPlrrPNCTCNNCT(~&tyy,~&hyzPX; ~~ 'tabular'%='longtable')++ -+.
   ~&?(
      "c". :^/~&h ~&t; ~='\midrule'-~; ~&lrhPNCTrtPX; ^T\~&r ~&l; ^T(
         :/('\caption{'--"c"--'}\\')+ --<'\endfirsthead'>,
         :/('\caption{'--"c"--' (continued)}\\')+ --<'\endhead','\bottomrule','\endfoot'>),
      ! ~&a^& '\midrule'?=ah\~&ahPfatPRC <'\midrule','\endhead','\bottomrule','\endfoot'>--+ ~&at),
   ! *~ ~='\bottomrule'+-

label = # takes a label to a function that adds a label to the result of an elongation

('\label{'--+ --'}'); "s". *= '\endfoot'?=\~&iNC :\<"s">

