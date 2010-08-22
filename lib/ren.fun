
#import std
#import nat
#import flo
#import plo

#comment -[
These are some functions for rendering functions of two variables as a
surface. 

The main one is the rendering function, which takes an argument of the
form ((observer,eccentricty),visualization) to a rendering of the
surface expressed in a LaTeX picture enviornment with pstricks
commands.

The observer can be a list of floating point numbers <x,y,z> giving
the coordinates of the focal point for the image, using a coordinate
system wherein the surface is inscribed in the cube in the first
octant bounded by the origin and <1,1,1>.  Alternatively, the observer
can be a string of the form (i|o)(l|m|h)(e|n|w|s)(+|-) specifying the
distance (in or out), the elevation (low, medium or high), and the
azimuth (north, south, east or west, with + or - for a slight positive
or negative angular displacement, respectively) assuming the north
direction coincides with the positive y axis and east with the
positive x axis.

The eccentricity can be empty or can be a pair of floating point
numbers (x,y) specifying an elongation in the x and y directions of
the cube in 3-space in which the surface is inscribed. Equal values
greater than one specify a pizza box shape, and less than one specify
a tower. Unequal values specify a rectangular prism. Observer
coordinates are automatically displaced consistently with the
eccentricity.

The visualization contains a family of curves specifying the surface,
with equally many points on each one. The peg fields and pegaxis
should be initialized with the y values and the abscissa with the x
values. True perspective is obtained only when a square picture frame
or at least a square viewport are specified, but the image will be
scaled to fit any given viewport. Displacements and rotations may
be specified for the axis labels and are supported.

Another useful function in this module is drafts, which takes an
eccentricity and a visualization, as above, and generates 48 different
views in a free standing LaTeX document.

Copyright (C) 2007-2010 Dennis Furey]-

----------------------------------------------------- constants -------------------------------------------------------------

corners     = %eLLPk ~&r?(1.!,0.!)** zipp0^*D(~&y,iota) 8

diffusion   = 25. # determines light attenuation with distance; set to 0 for a point source or infinity for an overcast sky

low_horizon = 20. # vertical angular displacements used for recommended observation points
mid_horizon = 35.
hi_horizon  = 50.
plus_angle  = 35. # horizontal angular displacements used for recommended observation points
minus_angle = 55.

#library+

recommended_observers = # a list of pairs (c,<x,y,z>) where c is a string of the form (i|o)(l|m|h)(e|n|w|s)(+|-)

(\/~&H ~&/<low_horizon,mid_horizon,hi_horizon> plus* ~&rlDSL <plus_angle,minus_angle>-* ari4/0. 270.) -+
   ~&TblrDlrlPCrrPXS2O+ ~&bbI/(`i,`o)+ ~~ ~&p/*'lmh'; //~&plrDSrlPlCrrPXSSL block2 'e+n-n+w-w+s-s+e-',
   %eLLLWMk+ plus/***$.5+ ^(times/***2.,times/***3.5)+ * *-; * ^T\~&lt times*+ ~&lhPrD,
   -*+ ~* times/pi; div\180.; ^lrNCC/cos sin+-

#library-
------------------------------------------------ geometric functions --------------------------------------------------------

#optimize+

observer    = -:~& recommended_observers
coterminal  = %eLWWMk; ~&G; either ~&rlG; either ==
unit        = vid^*D\~& sqrt+ plus:-0.+ times*+ ~&iiXS
edges       = %eLMk; %eLWSMk+ ~&hthPXSs+ -<&*+ ~&lrNCCS+ ~&plrEZFitZB*~+ ~&HiiK0\corners+ *+ times*++ //~&p+ div\*.5

far_corners = # takes (observer,center) to (near corner,far corner)

%eLWMk; %eLWMk+ -+
   ~&bl+ (^ ^($-,$^) fleq+ ~&br)+ * ^/~&r iprod+ ~&iiX+ minus*+ ~&p,
   ^D/~&l ~&H\corners+ *+ times*++ //~&p+ div\*.5+ ~&r+-

view = # takes (observer,center) to a perspective map to the unit square

%eLWMk; %fMk+ -+
   (("f","g","h"). <."g"+ ~&h,"h"+ ~&th>+ "f")^/~&r -+
      ^G(bus~~; lesser not fleq,~&bl); ~~ ("s","l"). div\"s"+ minus\"l",
      ^(fleq$-,fleq$^)^~HhSthPSX(*+ ~&r,~&H\corners+ *+ times*++ //~&p+ div\*.5+ ~&l)+-,
   ^/~&r -+
      ("o","u","r","l"). vid^*D(iprod/"l",<.iprod/"r",iprod/"u">)+ minus*+ ~&p\"o",
      ^/~&l ^(unit+ oprod,~&)^(unit+ oprod\<0.,0.,1.>,~&)+ minus*+ ~&rlp+-+-

left_light = # takes (observer,center) and selects a light source over the observer's left shoulder

plus^*p/~&r minus*p; ^lrNCT(
   ~&lrNCC+ ~&thPhX; times^~G/math..hypot ^(cos,sin)+ math..atan2; //plus div\180. times/pi -60.,
   times/1.2+ abs+ ~&z)

right_light = # takes (observer,center) and selects a light source over the observer's right shoulder

plus^*p/~&r minus*p; ^lrNCT(
   ~&lrNCC+ ~&thPhX; times^~G/math..hypot ^(cos,sin)+ math..atan2; //plus div\180. times/pi 60.,
   times/1.2+ abs+ ~&z)

back_light = # selects a light source position facing the observer slightly from the left and closer to the horizon

plus^*p/~&r minus*p; ^lrNCT(
   ~&lrNCC+ ~&thPhX; times^~G/math..hypot ^(cos,sin)+ math..atan2; //plus div\180. times/pi -120.,
   times/.75+ abs+ ~&z)

--------------------------------------------------- axis rendering functions ------------------------------------------------

rear_edges = # takes (observer,center) and a viewport

:/'% rear edges'+ ^H(~&r,coterminal~|^\edges+~&lr ~&rrX+ far_corners+ ~&l)^/~&l -+
   *+ //+ '\psline[linestyle=dotted,linewidth=0.9pt,linecolor=black,fillstyle=none]{-}'--+ --,
   ~~+ (:/`(+ --')'+ ^T/~&h :/`,+ ~&th)++ printf/*'%6.2f'++ +^\view+~&l <..~&h;+ //times+ ~&rl,~&th;+ //times+ ~&rr>+-

side_edges = # takes observer location and a viewport

:/'% side edges'+ ^H(~&r,(not coterminal)~|^\edges+~&lr far_corners+ ~&l)^/~&l -+
   *+ //+ '\psline[linestyle=dotted,linewidth=0.9pt,linecolor=black,fillstyle=none]{-}'--+ --,
   ~~+ (:/`(+ --')'+ ^T/~&h :/`,+ ~&th)++ printf/*'%6.2f'++ +^\view+~&l <..~&h;+ //times+ ~&rl,~&th;+ //times+ ~&rr>+-

front_edges = # takes observer location and a viewport

:/'% front edges'+ ^H(~&r,coterminal~|^\edges+~&lr ~&llX+ far_corners+ ~&l)^/~&l -+
   *+ //+ '\psline[linestyle=dotted,linewidth=0.9pt,linecolor=black,fillstyle=none]{-}'--+ --,
   ~~+ (:/`(+ --')'+ ^T/~&h :/`,+ ~&th)++ printf/*'%6.2f'++ +^\view+~&l <..~&h;+ //times+ ~&rl,~&th;+ //times+ ~&rr>+-

axes = # takes ((observer,center),viewport,<x axis,y axis,z axis>)

_axis%LeLWweWwXXMk; -+
   ~&pL/<'% x axis','% y axis','% z axis'>+ * -+
      %sLMk+ ^lrNCT(
         ~&lrtPD; *= _axis%seseLWXXXXMk; %sLMk+ ^lrNCC(
            '\put'--+ ^T(
               :/`(+ --')'+ ^T(~&h,:/`,+ ~&th)+ printf/*'%6.2f'+ ~&rrrrr,
               :/`{+ --'}'+ '\begin{rotate}'--+ --'\end{rotate}'+ ^T(
                  :/`{+ --'}'+ printf/'%0.3f'+ _axis%seseLWXXXXMk; -+
                     div\pi+ times/180.+ math..atan2+ (both fleq\0.)?/abs~~ fleq\0.?r/negative~~ ~&,
                     ~&thPhX+ minus*+ ~&rrrrlrp+-,
                  ^T/('\makebox(0,0)['--+ --']'+ ~&rl) :/`{+ --'}'+ ^T(
                     '\scalebox{'--+ --'}'+ printf/'%0.3f'+ ~&rrl,
                     :/`{+ --'}'+ ~&rrrl))),
            '\put('--+ --'){\pscircle*{1.5pt}}'+ ^T(~&h,:/`,+ ~&th)+ printf/*'%6.2f'+ ~&rrrrl),
         '\put'--+ ^|T(:/`(+ --')',:/`{+ --'}')^(
            ^T(~&l,:/`,+ ~&r)+ printf/$'%6.2f'+ plus^~lhPrlPXlth2rrPXX\~&l.alias plus^*p(~&rl,times*+ ~&lrrPD)^(
               times/.4+ sqrt+ iprod+ ~&iiX+ minus*+ ~&p+ ~&rthzXbrrrl,
               ~&rhrrr; ^/~&l unit+ minus*+ ~&rlp),
            '\begin{rotate}'--+ --'\end{rotate}'+ ^T(
               :/`{+ --'}'+ printf/'%0.3f'+ ~&l.rotation,
               ^T('\makebox(0,0)['--+ --']'+ ~&rhl,:/`{+ --'}'+ ~&rhrrl)))),
      _axis%seseLWXXXLXMk^/~&l ~&r; ^D\~& ~&lzrr+ (fleq+~&lrlPX)~-+ -+
         -*+ \/~& ~&p\<'l','lb','rb','r','rt','lt','l'> :/-180. ari6/-150. 150.,
         div\pi+ times/180.+ math..atan2+ ~&thPhX+ minus*+ ~&p+ mean~*+ ~&rrPSlSrSXbiK7+-+-,
   _axis%eseLWXXLXLMk^p/~&rr -+
      %eseLWXXLLMk+ (-*; * ^\~&rr div+~&lrlPX)^*D\~& fleq$-+ ~&lSSL,
      %eseLWXXLLLMk; %eseLWXXLLMk+ $^ fleq+ ~~ ~&thPzXSbrrr3S; fleq$-+ * iprod+ ~&iiX+ minus*+ ~&p,
      * -*; * -*; * %fOWseWLXXMk; %eseLWXXMk+ ^/~&llPrrrS2H ^/~&rl ^H/~&lr ~&rr; ^\~&rS * ~&l,
      ^D/^(~&ll; sqrt++ iprod++ ~&iiX++ minus*++ //~&p,~~+ +^\view+~&l <..~&h;+ //times+ ~&rll,~&th;+ //times+ ~&rlr>) -+
         * -*; * ~&lrrSPK7iK1SPXrD; -+
            * ^/~&rl ~&llPlrPrrPpD; * ~&rl?\~&rrrX ^/~&rr ~&rrPlX; fleq/eps?l/plus minus,
            %eWtLXseLXXLMk; %etLXseLXXLMk+ ~&hllrPrXPrXPtlllPrXPrXSPC+-,
         ^D/(^(~&,times/8.)+ div/10.+ ~&rl; div\2.+ plus) -+
            %seLXLLLMk+ * ~&p; * ^lrK7p/~&llS ~&lrSPrlrpPD; * ~&rlrE?/~&rlPlDlS ~&l,
            %seXLLeLWLXLMk^D(
               ~&lrPrrPp; * :^(~/&r.variable &l,^p/~&r.hats ^H/ari+length+~&r.hats ~&/0.+ times/2.+ ~&l),
               ~&l; -+
                  %eLWLLMk; * ~&x+ -< leql+ ~~ ==-~+ ~&p,
                  (coterminal|=*tttPB)*~+ choices\3+ (not coterminal)~|^\edges+~&r far_corners+-)+-+-+-+-

------------------------------------------- surface rendering functions -----------------------------------------------------

surface = # takes ((observer,center),light source,visualization), simulates attenuation due to distance and angle of incidence

_visualization%eLWweLwXXMk; :/'% surface'+ -+
   :/'\psset{fillstyle=solid,linewidth=0.2pt,linecolor=darkgray}',
   ^T/(~&rr.curves; ~attributes*=; ~&i&& ~&s; |=hS&n; ~&iNC+ '\psset{'--+ --'}'+ mat`,+ * ^|T/~& :/`=) -+
      * ^|T('\newgray{shade}{'--+ --'}\psset{fillcolor=shade}','\pspolygon'--)^|(
         printf/'%0.4f'+ times^/~&l minus/1.+ div\pi+ math..acos+ ~&r,
         printf/**'%6.2f'; ~&thPhttPCC; *= :/`(+ --')'+ ^T/~&h :/`,+ ~&th),
      ((^\~&rr ^\~&rlr div+ ~&rll2lX)^*D\~& fleq$^+ ~&llPS)+ * ^\~&rr ^(
         div/1.+ plus/diffusion+ iprod+ ~&iiX+ minus*+ ~&lrlh2p,
         iprod+ unit^~/minus*+~&lrlh2p oprod+ minus~*+ ~&blrpPrlthththPXPG3O),
      ^D/~&rl -+
         %eLLWLMk+ ~&xrS+ fleq-<&l+ * ^\~&r iprod+ ~&iiX+ minus*+ ~&lrlh2p,
         ^D/~&ll %eLLWLMk+ ^(:^\~&l mean*+ ~&lK7,~&r)^*HytpSK7ytpSLllPlrPrlPrrPNCCCCSlSrSXS(
            ^(~&l,~viewport+~&rr); %eLeWXMk; *+ *+ ^/~&+ +^\view+~&l <..~&h;+ //times+ ~&rl,~&th;+ //times+ ~&rr>,
            %eLLLMk+ ^H\(~&rr.curves; * %eeWXLMk+ -*+ ~/peg points) -+
               *+ *+ <..~&rl;+ times^^/!+~&lh ~&rh,~&l;+ times^^/!+~&lth ~&rth,~&rr;+ times^^/!+~&ltth ~&rtth>,
               ^(div\*.5+ ~&lr,~&rr; ~placer*+ <.~abscissa,~pegaxis,~ordinates.&h>)+-)+-+-+-

-------------------------------------------- file formatting functions -----------------------------------------------------

lit_rendering = # a light source to a function taking ((observer,eccentricty),visualization) to a LaTeX fragment

"l". _visualization%seLUeWZXwXMk; ~&rhPlrtPCC/'\psset{unit=1pt}'+ -+
   -&~pegaxis,~ordinates,~curves; all~peg&& all_same length+ ~points&-?r\<'invalid surface'>!% :^(
      ~&r.picture_frame; '\begin{picture}'--+ --+ ~~ printf/$'%0.2f'; :/`(+ --')'+ ^|T/~& :/`,,
      --<'\end{picture}'>+ ~&L+ <.
         rear_edges+ ~/&l &r.viewport,
         side_edges+ ~/&l &r.viewport,
         axes^/~&l ~&r; ^/~viewport <.~abscissa,~pegaxis,~ordinates.&h>,
         surface^/~&l ^|\~& "l",
         front_edges+ ~/&l &r.viewport,
         ~&r; ~boxed&& ~picture_frame; -+
            :/'% bounding box'+ ~&iNC+ '\put'--+ ^T/~&r '{\dashbox'--+ --'{}}'+ ~&l,
            ~~ printf/$'%0.2f'; :/`(+ --')'+ ^|T/~& :/`,+->),
   _visualization%eLWwXMk^|(
      %eLWMk+ -+
         ((all -&fleq/0.+ ~&l,fleq&-)^p/~&l times/*2.+ ~&r)?/<'invalid observation point'>!% ~&,
         eql?r\<'misspecified observer'>!% ^\~&rr ~&lrlPE?/~&l times^*p/~&rl div\*.5+ ~&rr,
         ^/~&l ^/observer+~&l ~&r; ||(0.5!* 7)! ~&i&& --<0.5>+ ~&lrNCC+ times/$.5+-,
      _visualization%Mk+ ?(
         ~(picture_frame,margin,headroom)== ~(picture_frame,margin,headroom) visualization&,
         ~&\~& visualization+ (picture_frame,margin,headroom,viewport):= (((400.,400.),(-50.,-50.)),50.,50.,(300.,300.))!))+-

#library+

rendering           = lit_rendering 50%~?/left_light right_light
left_lit_rendering  = lit_rendering left_light
right_lit_rendering = lit_rendering right_light
back_lit_rendering  = lit_rendering back_light

drafts = # renders all recommended views of a visualization for a given eccentricity into a free standing LaTeX document

_visualization%eWZwXMk; latex_document+ mat0+ -+
   * ^T(<'\mbox{}','\vfill'>--+ ~&llNC,:/''+ --<'\vfill','\pagebreak'>+ rendering),
   ^Drll2lXrrPXS/~&l recommended_observers*-+ boxed:=&!+ ~&r+-
