
#import std
#import nat
#import flo
#import tbl

#comment -[graph plotting functions, Copyright (C) 2007-2010 Dennis Furey]-

#optimize+

------------------------------------------------------- data structures ----------------------------------------------------

linear      = -+all \/fleq times/100. eps,abs*,nth_diff2+-
logarithmic = (not any zeroid)&& -+all \/fleq times/1e3 eps,abs*,nth_diff1,div*,~&typ+-

#library+

curve ::

points       %ssXLesXLseXLeeXLUUU     # a list of pairs of strings or floats describing a function of one variable
peg          %seU                     # value that's constant along this curve if it's a function of two variables
attributes   %sm                      # passed through as \psset{attribute=value,..} for each curve
decorations  %seUWsLXL                # LaTeX code fragments pasted onto the graph at the given point coordinates
scattered    %b                       # points are plotted without being connected
discrete     %b                       # points are plotted on top of vertical lines
ordinate     %a &?=(&h!,~&)+~ordinate # index with respect to the ordinates indicating the placer to use for plotting

axis :: 

variable     %s       # written near the axis on the plot
alias        %eW      # an absolute displacement in points to move the label away from its default position if necessary

hatches      %eLsLU   # a list of numbers or strings to be printed along the axis

-|~hatches,~hats; ~&i&& strtod*; &&~& not all zeroid|-

rotation     %e       # a number of degrees whereby the number or strings along the axis are turned for display purposes
intercept    %esUL    # the coordinates of origin of the axis with respect to the other axes

hats         %sL      # strings to be printed along the axis

~hats|| ~hatches; %sLI?/~& -&linear,abs*; all zeroid!| -&fleq/0.01,fleq\1.e5&-&-?(
   printf/*'%0.2f',
   scientific_notation*+ printf/*'%0.2e')

placer       %fOZ     # takes a string or number to a number between 0 and 1 indicating its position along the axis

~placer|| ~hatches; ~&itB&& ~&hzEZ&& %eLI&& -!ordered fleq,ordered not fleq!-&& -|
   linear&& ~&hzX; ("l","h"). div\minus("h","l")+ minus\"l",
   logarithmic&& ~&hzX; ln~~; ("l","h"). div\minus("h","l")+ minus\"l"+ ln,
   ~&itB&& (^/~&rr div^/float+~&rl ~&l)^*D(float+ length+ ~&t,num); -+
      (~&av^?\~&Nadr2XNV ~&avhdlrl6NXfavPMV); "t". ^H\~& ~&/"t"; ~&aldl^?\~&aldr fleq?arldl2X/~&falvh2rXPR ~&falvth3rXPR,
      ~&ldll3rdlr3XNXlrNCCV:-0+ ^piNVS/(~&at^& :^/~&ahthPX ~&fatPR) ~&aitB^& :^\~&fatPR -+
         (("x1","y1"),("x2","y2")). plus/"y1"+ times/minus("y2","y1")+ div\minus("x2","x1")+ minus\"x1",
         ~&ahthPX+-+-|-

visualization :: 

abscissa     _axis    # the axis for the first independent variable

~&r+ -+
   -!~&r.intercept,not all~hatches+ ~&l!-?/~& &r.intercept:= ~hatches.&h*+ ~&l,
   ^/(^T/~pegaxis.&iiNCB ~ordinates) ~abscissa;-&~hatches,~placer&-?/~abscissa -+
       -&~&%eLLI,all -!ordered fleq,ordered not fleq!-&-?r(
         axis$l[hatches: ~&l.hatches|| ~&rL; ~&i&& ari6^/fleq$- fleq$^],
         axis$l[hatches: ~&l.hatches|| ~&r; ^H\~& satch+ ~&itBitBitB+ length,placer: place+ ~&r]^/~&l merge+ ~&r),
      ^(~abscissa,~&lSS+ ~points*+ ~curves)+-+-

pegaxis      _axis%Z  # the axis for the second independent variable if any

~&r+ -+
   -!~&rZ,~&r.intercept,not all~hatches+ ~&l!-?/~& &r.intercept:= ~hatches.&h*+ ~&l,
   ^/(:^/~abscissa ~ordinates) ||~pegaxis -&any~peg+ ~curves,~pegaxis; not -&~&,~hatches,~placer&-&-&& -+
      -&%eLI,-!ordered fleq,ordered not fleq!-&-?r(
         axis$l[hatches: ~&l.hatches|| ~&r; ari6^/fleq$- fleq$^],
         axis$l[hatches: ~&l.hatches|| ~&r; ^H\~& satch+ ~&itBitBitB+ length,placer: ~&l.placer|| place+ ~&r]),
      ^(~pegaxis||axis&!,~peg*+ ~curves)+-+-

ordinates    _axis%L  # the axes of the dependent variables

(~&l?\~&r ~&ar^& :^\~&falttiQPrtPXPR ~&abh; &r.intercept:=r ~&r.intercept||~&l)^(
   -+
      ~&g&& ~&rlrPllPQS^*DlrpS/~& (~&rS+ zipp0)^*D(0!*+ ~&z,~&)+ iota+ --<&>+ 0!*,
      ~hatches.&ihzXB*+ :^/~abscissa ~pegaxis.&iiNCB+-,
   -+
      ~&rS+ nleq-<&l+ ^T\~&r gdif~&EblPO,
      ^/~&l ~&r; (_axis%nwX,_curve%L)%XLMk; * ^/~&ll (fused axis)^/~&lr -+
         ~&B?/<'conflicting axis types'>!% -|
            ~&l&& axis$[hatches: ~&lL; ari6^/fleq$- fleq$^],
            ~&r&& axis$[hatches: ^H\~& satch+ ~&itBitBitB+ length,placer: place]+ merge+ ~&r|-,
         %eLI!=+ ~&rSS+ ~points*+ ~&r+-,
      ^/~&l |=hrPlSXSlF&r+ -*; * ^/~&r ~&l&& ~(&r.ordinate,&l); ~&l?\~&rh indexable&& ~&NlXrH,
      ^\~curves num+ ~ordinates||<axis&>!+-)


curves        _curve%L ~curves; * ~ordinate==&?\~& ordinate:= %eI+~points.&ihBr?/&h! &th!
picture_frame %eWW     ~picture_frame; ^|(^({0,0.}?<l/300.! ~&l,{0,0.}?<r/200.! ~&r),~~ {0,0.}?</-32.5! ~&)
headroom      %eZ      ~headroom|| 25.!
margin        %eZ      ~margin|| ~ordinates.&itB?/30.! 10.!
viewport      %eWZ     -&~margin,~headroom,~viewport.&Z&-?\~viewport minus^~bbI(plus~~+ ~picture_frame.&bbI,~/margin headroom)
boxed         %b

----------------------------------------------------------- plotting functions ---------------------------------------------
#library-

satch"n" = ~&i&& ~&hSztzNCBPT+ ~&t?\~&iNC ^H\~& block+~&lihBPrizBPYirB+ (nleq/"n")!=&r+ (*~ not remainder)^D/length ~&itB+iol
place    = ?^(\/-=+ ~&lS,~&\<'bad coordinate'>!%+ -:)+ (^/~&rr div+~&rlPlX)^*D/float+length+~&t num; * ^\~&r float+ ~&l
merge    = ~&hS+ rlc~&E+ :-0 ~&al^?\~&ar ~&ar?\~&al ~&alhPrhPE?/~&alh2fabt2RC ~&alhPrw?/~&arh2falrtPXPRC ~&alh2faltPrXPRC

left_axis =

-+
   :/'% left axis'+ :^(
      -+
         '\put'--+ ^|T(:/`(+ --')'+ ^|T(~&,:/`,)+ printf/$'%0.2f','{\makebox(0,0)[l]{'--+ --'}}'),
         ~&lrlPX; ^\~&l.ordinates.&h.variable plus^~bbI/~&l.ordinates.&h.alias ^(
            minus\10.+ ~&r,
            plus/20.+ ~&l.viewport.&r)+-,
      ~&rlrD; :^y(
         '\psline{->}'--+ ~&hzXblrlPX; --+ ~~ :/`(+ --')'+ ^|T(printf/'%0.2f',:/`,),
         *= <.
            '\put'--+ ^T(~&lrlPX; :/`(+ --')'+ ^|T(printf/'%0.2f'+ minus\10.,:/`,),~&rr; :/`{+ --'}'),
            '\put'--+ ^T(:/`(+ --')'+ ^T(printf/'%0.2f'+ ~&l,:/`,+ ~&rl),! '{\psline{-}(0,0)(-5,0)}')>)),
   ^/~& ^(
      ^H\~ordinates.&h.intercept.&h +^\~abscissa.placer //times+ minus^\~margin plus+ ~picture_frame.&bl,
      ^p(printf/*'%0.2f'+ ^H/ari+length+~&r ~&/0.+ ~&l,~&r)^/~viewport.&r ~ordinates.&h; -+
         * '\begin{rotate}'--+ --'\end{rotate}'+ ^|T(:/`{+ --'}','\makebox(0,0)[r]{'--+ --'}'),
         ^D(
            printf/'%0.2f'+ ~rotation,
            ~hats|| ~hatches; %sLI?/~& -&linear,any fleq/1.&-?(printf/*'%0.2f',printf/*'%0.2e'))+-)+-

right_axis = # the intercept is ignored

~ordinates.&itB&& -+
   ~&r&& :/'% right axis'+ :^(
      -+
         '\put'--+ ^|T(:/`(+ --')'+ ^|T(~&,:/`,)+ printf/$'%0.2f','{\makebox(0,0)[r]{'--+ --'}}'),
         ~&l; ^\~ordinates.&th.variable plus^~bbI/~ordinates.&h.alias ^|(plus/10.,plus/20.)+ ~viewport+-,
      :^y(
         '\psline{->}'--+ ^G(printf/'%0.2f'+ ~&l.viewport.&l,~&rhzXbl); --+ ~~ :/`(+ --')'+ ^|T/~& :/`,,
         -*+~(&l.viewport.&l,&r); ~&lrlPXrrPXS; *= <.
            '\put'--+ ^|T(^|T(:/`(+ printf/'%0.2f'+ plus/10.,:/`,+ --')'),:/`{+ --'}'),
            ^|T('\put('--+ printf/'%0.2f',:/`,+ --'){\psline{-}(0,0)(5,0)}')+ ~&l>)),
   ^/~& ^p(printf/*'%0.2f'+ ^H/ari+length+~&r ~&/0.+ ~&l,~&r)^/~viewport.&r ~ordinates.&th; -+
      * '\begin{rotate}'--+ --'\end{rotate}'+ ^|T(:/`{+ --'}','\makebox(0,0)[l]{'--+ --'}'),
      ^D(printf/'%0.2f'+ ~rotation,~hats|| ~hatches; %sLI?/~& -&linear,any fleq/1.&-?(printf/*'%0.2f',printf/*'%0.2e'))+-+-

bottom_axis =

-+
   :/'% bottom axis'+ :^(
      -+
         '\put'--+ ^|T(:/`(+ --')'+ ^|T(~&,:/`,)+ printf/$'%0.2f','{\makebox(0,0)[t]{'--+ --'}}'),
         ~&l; ^\~abscissa.variable plus^~bbI/~abscissa.alias ~&\-25.+ div\2.+ ~viewport.&l+-,
      -+
         -!~ordinates.&itB,~curves; any ~discrete!-?ll(
            :^\~&rr ~&rlPlrPX; %ssWLXMk; '\psline{-}'--+ ~&lrhzXbl3G; --+ ~~ '('--+ --')'+ ^T/~&r :/`,+ ~&l,
            :^y\~&rr ~&rlPlrPX; %ssWLXMk; '\psline{->}'--+ ~&lrhzXbl3G; --+ ~~ '('--+ --')'+ ^T/~&r :/`,+ ~&l),
         ^/~& -+
            ('0.00'?=l/~& ~&lritBitB2X)^/(printf/'%0.2f'+ ~&l) -+
               %soULMk+ *= <.
                  '\put'--+ ^T('('--+ --')'+ ^T/~&rl :/`,+ ~&l,:/`{+ --'}'+ ~&rr),
                  '\put('--+ --'){\psline{-}(0,5)(0,10)}'+ ^T/~&rl :/`,+ ~&l>,
               ^D\~&r printf/'%0.2f'+ %eoUMk+ minus\10.+ ~&l+-,
            ^\~&r ~&l; times^/~viewport.&r ^H/~ordinates.&h.placer ~abscissa.intercept.&h+-+-),
   ^/~& %sWLMk^p(printf/*'%0.2f'+ ^H/ari+length+~&r ~&/0.+ ~&l,~&r)^/~viewport.&l ~abscissa; -+
      * '\begin{rotate}'--+ --'\end{rotate}'+ ^T/(~&l; :/`{+ --'}'+ printf/'%0.2f') ^|T(
         '\makebox(0,0)['--+ --']'+ fleq/30.?/'tr'! fleq\-30.?/'tl'! 't'!,
         :/`{+ --'}'),
      ^D(~rotation,~hats|| ~hatches; %sLI?/~& -&linear,any fleq/1.&-?(printf/*'%0.2f',printf/*'%0.2e'))+-+-

surface =

:/'% curves'+ -+
   *== <.
      ~&r.attributes; ~&i&& ~&iNC+ '\psset{'--+ --'}'+ mat`,+ * ^T/~&l :/`=+ ~&r,
      ^D(~&lr,~&rF+ ~&r.decorations); *= ^lrhPTrtPC(
         '\put'--+ ~&lrlPH; :/`(+ --')'+ ^|T/~& :/`,,
         :^(:/`{+ ~&h,~&t)+ ^lrNCT(~&y,--'}'+ ~&z)+ ~&rr),
      ~&r.discrete?(
         ^H(~&lr; -+*+ //+ '\psline{-*}'--+ --+ ~~ :/`(+ --')'+ ^|T/~& :/`,,~&rlPlXrX;+ ~~+-,-*+ ~/&ll &r.points),
         :^(
            ~&r.scattered?/'\psdots%'! '\psline{-}%'!,
            (* '   '--)+ ~&LS+ ~&lrPrX; block4^|H\~points *+ :/`(++ --')'++ //+ ^|T/~& :/`,))>,
   ~&r.points*~^p\~curves ^D/~abscissa.intercept.&h (^|; //+ printf/$'%6.2f')^*D(
      +^\~abscissa.placer //times+ minus^\~margin plus+ ~picture_frame.&bl,
      +^*D(//times+ minus^\~headroom plus+ ~picture_frame.&br,~placer^*DNrXlHS/~ordinates ~ordinate*+ ~curves))+-

#library+

plot = # takes a visualization to a LaTeX fragment

_visualization%Mk; ~&rhPlrtPCC/'\psset{unit=1pt}'+ :^(
   ~picture_frame; '\begin{picture}'--+ --+ ~~ printf/$'%0.2f'; :/`(+ --')'+ ^T/~&l :/`,+ ~&r,
   --<'\end{picture}'>+ ^T/(~&L+ <.left_axis,right_axis,bottom_axis,surface>) ~boxed&& ~picture_frame; -+
      :/'% bounding box'+ ~&iNC+ '\put'--+ ^T/~&r '{\dashbox'--+ --'{}}'+ ~&l,
      ~~ printf/$'%0.2f'; :/`(+ --')'+ ^|T/~& :/`,+-)

------------------------------------------------- file formatting functions --------------------------------------------------

latex_document = # wraps the argument in LaTeX front matter suitable for a free standing document

--<'\end{document}',''>+ //~&T ~&tittt2BS -[
   \documentclass{article}
   \usepackage{pstricks}
   \usepackage{pspicture}
   \usepackage{rotating}
   \usepackage{booktabs}
   \usepackage{longtable}
   \addtolength{\oddsidemargin}{-50pt}
   \addtolength{\evensidemargin}{-50pt}
   \addtolength{\topmargin}{-100pt}
   \addtolength{\textheight}{140pt}
   \addtolength{\textwidth}{120pt}
   \begin{document}
   \setlength{\arrowlength}{5pt}
   \psset{linewidth=0.5pt,arrowinset=0,arrowscale=1.1,showpoints=false}]-
