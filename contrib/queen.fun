#import std
#import nat

#comment -[
solves the general case of the 8 queens problem;
invoke as queens -n, where n is a digit > 3]-

#executable <'par',''>
#optimize+

queens =

%np+~command.options.&h.keyword.&iNC; -+
   ~&iNC+ file$[contents: --<''>+ %nLP*=]+ ~&rSSs+ nleq-<&l*rFlhthPXPSPS,
   ~&i&& ~&lNrNCXX; ~&rr->rl ^/~&l ~&lrrhrSiF4E?/~&rrlPlCrtPX @r ^|/~& ^|T\~& -+
      -<&l^|*DlrTS/~& ~&iiDlSzyCK9hlPNNXXtCS,
      ^jrX/~& @rZK20lrpblPOlrEkPK13lhPK2 ~&i&& nleq$-&lh+-,
   ^/~&NNXS+iota -<&l+ ~&plll2llr2lrPrNCCCCNXS*=irSxPSp+ ^H/block iota; *iiK0 ^/~& sum+-
