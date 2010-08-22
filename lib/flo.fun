
#import std
#import nat

#comment -[
This module contains some floating point functions and constants.

Copyright (C) 2007-2010 Dennis Furey]-

#library+

eps         = 5e-16
inf         = -{wgfzg]ftVjBk=hTZd@L\}-
nan         = -{wgfzg]ftVjBk=hTY<PP<}-
ninf        = -{wgfzg]ftVjBk=hT[<AA<}-
pi          = 3.14159265358979323846

#optimize+

abs         = math..fabs
ari         = ~&?\0!! "n". ("l","h"). plus/*"l" times^(~&l,float@r)* -*iota"n" div(minus/"h" "l",float predecessor "n")
acos        = math..acos
asin        = math..asin
atan        = math..atan
atanh       = math..atanh
bus         = math..bus
correlation = div^/covariance times+ stdev~~
cos         = math..cos
covariance  = mean+ (* times+ minus~~)^DbbIS/mean~~ ~&p
cu_prod     = :/1.; ~&ar^& ^rlfPrlart3XRC/~& times+~&alrhPX
cu_sum      = :/0.; ~&ar^& ^rlfPrlart3XRC/~& plus+~&alrhPX
derivative  = // gsldif..central
div         = math..div
eudist      = sqrt+ iprod+ ~&iiX+ minus*p
exp         = math..exp
fleq        = math..islessequal
float       = ~&/(0.,1.); ~&r->ll ^\~&rt ^\-+times/2.,~&lr+- ~&rh?/plus+~&l ~&ll
floatz      = ~&?\0.! ~&z?(~&NiX,~&NNXyX); (~&l?\~&r negative@r)^|/~& float
geo         = exp*++ ln~~;+ ari
integral    = "f". ("a","b"). gslint..qagx ("f","a","b")
iprod       = plus:-0.+ times*p
levin_sum   = ~&l+ gslevu..utrunc
levin_limit = plus^/~&h levin_sum+ minus*typ
ln          = math..log
max         = fleq?/~&r ~&l
mean        = div^/plus:-0. float+ length
min         = fleq?/~&l ~&r
minus       = math..sub
N           = rmath..pnorm\(0.,1.,&,0)
negative    = minus/0.
nth_deriv   = "n". -++- (* "t". // gsldif..t_central\"t") (times/2.)|\x (pow/1.0e-8 div/1. float "n")!* iota "n"
nth_diff    = "n". rep"n" minus*typ
oprod       = @pbaatPahPfatPRDCaqPO minus*lihBPrrlXPrQS+ num+ iprod~~+* ~&lyPrtPXltPryPXX
plus        = math..add
pow         = math..pow
printf      = math..asprintf
Q           = rmath..qnorm\(0.,1.,&,0)
rand        = mtwist..u_cont+ 0!
sgn         = 0.?=/~& fleq/0.?/1.! -1.!
sin         = math..sin
sqr         = times+ ~&iiX
sqrt        = math..sqrt
stdev       = sqrt+ variance
strtod      = math..strtod
tan         = math..tan
tanh        = math..tanh
times       = math..mul
variance    = mean+ (sqr+ minus)^*D/mean ~&
vid         = math..vid
Z           = rand; rmath..qnorm\(0.,1.,&,0)
zeroid      = math..iszero

root_finder = # takes ((lower bound,upper bound),function,tolerance)

^(^bbI/~&l ~&H~~+~&rlPlG,~&r); (fleq^/~&rr abs+ minus+ ~&lbl)->lll ^\~&r -+
   (==+ sgn~~)?rrPlllr3X/~&rllr2X ~&lll2rX,
   ^/~& ^rlrHX/~&rl div\2.+ plus+ ~&lbl+-
