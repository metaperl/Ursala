
#import std
#import nat
#import flo

#comment -[
This module contains functions and data structures for solving linear
programming problems by way of a more convenient interface than direct
invocation of the virtual machine's library functions, because it
allows symbolic names for variables, positive and negative solutions,
and costs proportional to magnitudes. A few matrix operations are also
included. Replacement functions implemented in virtual code are
provided in case the virtual machine doesn't have the required
libraries (lapack, umf, and pcx or glpk) but performance and memory
efficiency will suffer considerably.

Copyright (C) 2007-2010 Dennis Furey]-

#library+
#optimize+

------------------------------------------------ data structures -----------------------------------------------------------
linear_system ::

lower_bounds  %geAS      # the minimum allowed value for each variable in the solution
upper_bounds  %geAS      # the maximum allowed value for each variable in the solution
costs         %geAS      # the proportional contribution of each variable to the objective function to be minimized
taxes         %geAS      # the proportional contribution of the magnitude of each variable to the objective function
equations     %egXSeXS   # the equations to be satisfied in the form <(<(coefficient,name)..>,total)..>
integers      %gS        # the variables constrained to integer values
binaries      %gS        # the variables constrained to binary values
derivations   %egXSm     # <name: <(coefficient,name)..>> original variables expressed in terms of standardized variables

------------------------------------------- general operations on matrices -------------------------------------------------

mmult = iprod*rlD*rK7lD   # matrix multiplication

#library-

upper_triangular = # takes a matrix and transforms it to upper triangular form by row reductions

~&a^& (~&aitB?\~&a ^rlhPlthS2rpCB/~&a ~&fattS2R)^J/~&f ~&a; (not fleq+ abs~~)-<&h; (fleq/eps+ abs+ ~&hh)&& -+
   :^/~&h ~&htPtD; * :/0.+ minus^*p/~&rt times*+ ~&rhPlD,
   :^\~&t ~&h; :/1.+ vid*+ ~&htD+-

#library+

msolve = # takes a square matrix and a vector to a vector using gauss jordan elimination with pivoting

lapack.|dgesvx -+
   ~&i&& ~&xzS+ ~&a^& :^(~&ah,^p/~&athS ~&fattS2R)^J/~&f ~&a; :^/~&h ~&htD; * minus^*p/~&r times*+ ~&rhPlD,
   ~&plrNCTS; ~&iyxPzNCTSxPB+ upper_triangular+-

minverse = ~&K7+ msolve^*D/~& ^DlSzyCK9\~& :/1.+ 0.!*+ ~&t

sparso = # storage efficient solution of systems of linear equations in sparse matrix form 

%nWeXLeLXMk; umf.|di_a_trp msolve^\~&r ^DrlHS/iol+~&r ~&l; |=&ll; nleq-<&hll; * *+ -:0.!+ ~&lrPrXS

------------------------------------------- arbitrary precision versions ---------------------------------------------------

mp_solve = # same as msolve but a lot slower and for mpfr (arbitrary precision) numbers

-+
   ~&i&& ~&xzS+ ~&a^& :^(~&ah,^p/~&athS ~&fattS2R)^J/~&f ~&a; :^/~&h ~&htD; * mpfr..sub^*p/~&r mpfr..mul*rhPlD,
   ~&plrNCTS; ~&iyxPzNCTSxPB+ ~&a^& -+
      ~&aitB?\~&a ^rlhPlthS2rpCB/~&a ~&fattS2R,
      ^J/~&f ~&a; (not mpfr..lessequal_p+ mpfr..abs~~)-<&h; (mpfr..lessequal_p/1E-16+ mpfr..abs+ ~&hh)&& -+
         :^/~&h ~&htPtD; * :/0E0+ mpfr..sub^*p/~&rt mpfr..mul*rhPlD,
         :^\~&t ~&h; :/1E0+ mpfr..vid*+ ~&htD+-+-+-

mp_sparso = # replacement function for sparso with mpfr numbers, but no advantage in storage efficiency

%nWEXLELXMk; mp_solve^\~&r ^DrlHS/iol+~&r ~&l; |=&ll; nleq-<&hll; * *+ -:0E0!+ ~&lrPrXS

------------------------------------------------- linear programming functions ---------------------------------------------

standard_form = # removes finite and negative bounds and unsigned costs from linear systems by variable substitutions

-+
   linear_system$l[
      taxes: <>!,
      upper_bounds: <>!,
      lower_bounds: :0.^*js\~&rlnS --+ ~/&rlmrSPSL &l.equations.&lrSPSL,
      costs: -+
         ^A(~&hn,plus:-0.+ ~&mS)*+ |=&n+ ^T(
            ~&l; *= ||~&lNC ~&lmPrD; * ^A/~&rr times+~&lrlPX,
            ~&r; *= ||~&lNC ~&lmPrD; * ^A/~&rr times^/~&l abs+~&rl),
         %seAesXLXLWMk^H\~&l.(costs,taxes) ~*+ ^/~&+ ~&n;+ -:0!+ ~&rl+-,
      equations: (^\~&r ~&l~<{0.,-0.}*~+ ~&l)^*T\~&rr -+
         * %esXLeXMk+ ^\~&rr ~&lrlPDlrHS; %esXLMk+ *= ||~&lNC ~&llPrD; * ^\~&rr times+~&lrlPX,
         ^D\~&l.equations ^/~&+ ~&r;+ -:0!+ ~&rl+-,
      derivations: --+ ~/&l.derivations &rl],
   ^/~& -+
      %esXLmesXLeXLXMk+ ~&lSLPrSLPX+ * -?
         ~&rml;fleq/0.: ~&NiX+ ~&L+ <.
            ~&rml~=0.&& ^iNC\~&rml ^H/(:^/~&h+ ~&t;+ ~&l) <.~&/1.,~&/-1.+ --'_bloat'>+ ~&rn,
            ~&rmr~=inf&& ^iNC\~&rmr ^H/(:^/~&h+ ~&t;+ ~&l) <.~&/1.,~&/1.+ --'_headroom'>+ ~&rn>,
         ~&rmr;fleq\0.: ^/(^ANC/~&rn ^H/~&l ~&iNC/-1.+ --'_complement'+ ~&rn) ~&L+ <.
            ~&rmr~=0.&& ^iNC\negative+~&rmr ^H/~&l <.~&/1.,~&/-1.+ --'_bloat'>+ --'_complement'+ ~&rn,
            ~&rml~=ninf&& ^iNC\negative+~&rml ^H/~&l <.~&/1.,~&/1.+ --'_headroom'>+ --'_complement'+ ~&rn>,
         ^/(^ANC/~&rn ^H/~&l <.~&/1.+ --'_credit',~&/-1.+ --'_debit'>+ ~&rn) ~&L+ <.
            ~&rml~=ninf&& ^iNC\~&rml ^H/~&l <.~&/1.+ --'_credit',~&/-1.+ --'_debit',~&/-1.+ --'_bloat'>+ ~&rn,
            ~&rmr~=inf&& ^iNC\~&rmr ^H/~&l <.~&/1.+ --'_credit',~&/-1.+ --'_debit',~&/1.+ --'_headroom'>+ ~&rn>?-,
      %fOseWAXLMk^D((~&?\~&! *+ !; ^\~&; //+ ~&rrPlw->r &rr:= :/``+ ~&rr)+ ~&lrlPU; *~ -=/`_,~&rr)^(
         ~derivations.&nmrSPCSLs,
         ^H\~equations.&lrSPSLs ^/~&+ (*+ ^llPlrPrXA)^\-:inf!+~upper_bounds ^/~&+ -:ninf!+ ~lower_bounds)+-,
   upper_bounds:= ^Ts(~&DrlAS/1.+ ~binaries,^niK12/~upper_bounds ~binaries),
   lower_bounds:= ^Ts(~&DrlAS/0.+ ~binaries,^niK12/~lower_bounds ~binaries)+-

solution = # takes a linear system to a result of type %em

gint~&lnPrE^\~equations.&lSLrS standard_form; -+
   %emMk^T\~&r ~&m~<{0.,-0.}*~+ ^DrnPlrmPHAS\~&l %fMk+ plus:-0.++ *+ times^/~&l+ ~&r;+ -:0.!+ ~&r,
   %esXLmemXMk^/~&l.derivations %emMk^DlrlPHrrPAS/~&rrr %neXLMk+ mip_solver^(
      %nLWMk^H/~*@rrl ~&l.(binaries,integers),
      %eLnWeXLeLXXMk^(
         %eLMk+ (#:/0.+#) ~&rS+ %neXLMk+ (nleq-<&l)^DlrnPHrmPXS/~&rrl %emMk^T(~&r,gdif~&EbnPO)^\~&l.costs ~&A\*0.+ ~&rl,
         ^\%eLMk+~&l.equations.&rS %nWeXLMk+ ~&DSLlrlPXrrPXS+ num+ nleq-<&l*+ ~&DlrrPHrlPXSPS^D/~&rrl ~&l.equations.&lS)),
   _linear_system%sSfOWXXMk^/~& ~equations.&lSLrSs; ^/~& -:0!~~+ ~&rlXSiX+ num+-

mip_solver = # takes an argument ((b,i),c,m,y) of type %nLWeLnWeXLeLXXX to a result of type %neXL

~&Y?l\lp_solver@r ~&ll?\lpsolve..iform@lrPrX ~&lr?\lpsolve..bform@llPrX lpsolve..biform

lp_solver = # lower level interface, takes an argument (c,m,y) of type %eLnWeXLeLXX to a result of type %neXL

lpsolve.|stdform glpk.|simplex glpk.|interior replacement_lp_solver

replacement_lp_solver = # solves it the hard way without calling an external library function

^|(num,~&); -+
   %fnWeXLLneXLXXnLLXMk; @NiX ~&rr->lilB ^\~&rlrtPXP @lrlrhPXPX %neXLeXZfnWeXLLneXLXXnLXXCk -+
      ~&r?\~&l ~&l?\~&r %neXLeXZWMk; lesser fleq@br,
      ^/~&l (%fneXLXMk; ~&r&& ^/~&r plus:-0.+ times*DlrlPHrrPXS)^/~&rll -+
         eql+~&llPrX&& eql+~&lrlrPSs3rX&& %nLnWeXLXneXLXMk; -+
            %neXLMk+ -&~&r; ~&i&& all fleq/0.,~&p&-^|/~& sparso,
            %nLnWeXLeLXXMk^/~&ll ^\~&rrS ^H\~&lr @rlSPllPX *+ ^\~&r+ ~&l;+ ^|+ ~~ -$^/~& iol+-,
         (^/~&l ~&rlrPX; gint~&llPrll2E)^\~&rlrr ~&rrPrlrl3X; %nLnWeXLXMk^/~&l ~&L+ ~&rhlr3lw~|+-+-,
   ^(^/-:+~&l ^\num+~&rr |=&lr+ ~&rl,leql?rrPlX\<'bad linear program'>!% %nLLMk+ choices^/~&llS length+ ~&rr)+-
