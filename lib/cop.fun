
#import std
#import nat
#import flo

#comment -[
These functions may be useful in conjunction with non-linear
optimization by the minpack and kinsol libraries.

Copyright (C) 2007-2010 Dennis Furey]-

#library+
#optimize+

------------------------------------------------------- jacobians -----------------------------------------------------------

(# These construct jacobian functions numerically using the gsl differentiation library functions, which might be better than
a finite difference method but not as good as an analytical form. jacobian_row is useful for solvers that require only one
row of the jacobian matrix at a time. #)

t_derivative  = // \/gsldif..t_central

jacobian = # takes (n,m) to a function mapping f: R^m -> R^n to j: R^m -> R^(n x m)

+^\(gang+ (//+)*+ ~&t;|\+ ~&h!*+ iota+ ~&l) gang++ *+ ~&r; gang++ gang+ iota; * "n". "f". "x". ~&H(
   derivative "f"+ take("n","x")--+ \/~&lritBPC skip/"n" "x",
   ~&h skip/"n" "x")

jacobian_row = # takes n to a function mapping f: R^m -> R^n to j: ({0..n-1} x R^m) -> R^m

iota; \/-*; gang++ //+ * ("f","i"). ("j","x"). ~&H(
   derivative ~&h+ skip/"j"+ "f"+ take("i","x")--+ \/~&lritBPC skip/"i" "x",
   ~&h skip/"i" "x")

------------------------------------------------------ changes of variables -------------------------------------------------

(# half_line smoothly maps negatives to the interval 0..1 and positives to 1..inf, with a fixed point at infinity. The
constant appearing in the formula is the empirically determined maximum value consistent with monotonic convergence (within
machine precision). under takes a number to a function that maps the real line to the half line under that number. over takes
a number to a function that maps the real line to the half line over that number. Between takes a pair of numbers to a
function that maps the real line to the interval between the numbers, with unit slope and a fixed point at the center. The
lesser number should be on the left. chov takes a list of pairs of numbers to a function that maps a list of numbers to a list
of numbers between the corresponding intervals. #)

half_line = times^(div\2.+ plus/1.+ math..tanh+ div\2.60080714,math..hypot/2.)

under = "r". minus/"r"+ half_line+ plus/"r"+ negative
over  = "l". plus/"l"+ half_line+ minus\"l"

between =

ninf?=l/(inf?=r/~&! under+~&r) inf?=r/over+~&l -+
   ("c","w"). plus/"c"+ times/"w"+ math..tanh+ div\"w"+ minus\"c",
   (div\2.)^~/plus abs+ minus+-

chov = gang+ ~&t;|\+ ~&h;+* between
