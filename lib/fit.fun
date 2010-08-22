
#import std
#import nat
#import flo
#import lin

#comment -[some curve fitting functions, Copyright (C) 2007-2010 Dennis Furey]-

#library+
#optimize+

---------------------------------------------- interpolating function generators -------------------------------------------

# each of these takes a list of points <(x,y)..> and returns a function defined for intermediate values of x

one_piece_polynomial = # takes a list of points to a naive polynomial interpolation function

-+
   "c". ~&\1.; ~&\"c"; ~&ar^?\0.! plus^/times+~&alrPrhPX ^R/~&f ^\~&art ^/~&all times+~&al,
   ~&x+ msolve^\~&rS ~&lSiiDlSK7tS; * =><1.> :^\~&r times+ ~&lrhPX+-

mp_one_piece_polynomial = # takes a list of points in mpfr format to a naive polynomial interpolation function

-+
   "c". ~&\1E0; ~&\"c"; ~&ar^?\0E0! mpfr..add^/mpfr..mul+~&alrPrhPX ^R/~&f ^\~&art ^/~&all mpfr..mul+~&al,
   ~&x+ mp_solve^\~&rS ~&lSiiDlSK7tS; * =><1E0> :^\~&r mpfr..mul+ ~&lrhPX+-

sinusoid = # takes a list of points to a sinusoidal interpolation function, best behaved for equally spaced x values

plus:-0.++ gang+ (+^\~&l //times+ ~&r)^*p\~&rS ~&lSiiDrlXS; * -+
   %fMk+ chord_fit0; //+ zeroid?/1.! div^/sin ~&,
   %eWLMk+ ^(~&r,times/pi+ ~&l)^*T\~&r ~&ltx; * ^\~&r negative+ ~&l,
   %eeLXMk; fleq*|; ~&NrxPClX; ~~ num; * ^\~&r float+ ~&l+-

mp_sinusoid = # same as above for mpfr numbers

mpfr..add:-0E0++ gang+ (+^\~&l //mpfr..mul+ ~&r)^*p\~&rS ~&lSiiDrlXS; * -+
   %fMk+ mp_chord_fit0; //+ mpfr..zero_p?/1E0! mpfr..div^/mpfr..sin ~&,
   %EWLMk+ ^(~&r,mpfr..mul^/~&l mpfr..pi+ mpfr..prec+ ~&r)^*T\~&r ~&ltx; * ^\~&r mpfr..mul/-1E0+ ~&l,
   %EZWLWMk+ %EELXMk; mpfr..lessequal_p*|; %ELWMk; ~&NrxPClX; ~~ num; * ^\~&r mpfr..nat2mp+ ~&l+-

plin = # takes a list of points <(x,y)..> to a piecewise linear interpolating function

~&itB?\<'bad plin spec'>!% fleq-<&l; -+
   ~&r+ :-0.! ^/~&ll ?^\~&br \/fleq+ ~&rl,
   *ytpbbIS ^/~&ll +^(//plus+ ~&rl,+^(//times+ vid+ bus~~,\/minus+ ~&ll))+-

--------------------------------- functions returning interpolating function generators ------------------------------------

(# chord_fit returns a function taking a list of data points to a piecewise polynomial interpolation function with higher
order polynomials for the inner intervals so that the slope at each data point is parallel to the chord intersecting the two
neighboring points, the concavity is proportional to second difference, etc. limited by n. The n = 0 corresponds to a cubic
polynomial. Values of n greater than 3 are usually unstable. #)

chord_fit =

successor; "n". %eWLMk; -+
   "t". ~&\"t"; ~&arv^?(
      fleq?alrdPX/~&falrvh2XPR ~&falrvth3XPR,
      ^(~&\1.+ ~&al,~&ard); ~&ar^?\0.! plus^/times+~&alrPrhPX ^R/~&f ^\~&art ^/~&all times+~&al),
   (%eeLDMk+ ~&r+ ~&lll2rlr2Xllr2lrPrrPNCCVX:-0+ ~&rliNVSPp)^\~&lSytp -+
      %eWeLXWLMk; %eLLMk+ * msolve+ ^(length+ --,~&); -+
         %eLLeLXMk^\~&rrPS ~&lrlPXS; * *-; * (times^/~&rl pow+ ~&lrrPX)^/~&r float~~+ ~&l,
         --+ zipt^~G\~&rbhhlPrDC ~&l; ~&iiDlShyCK9+iota; ^pxlrpS\~&x ~&hxPzSDrlXS; product:-1*+* take^*Dx/~&l ~&rrDlStK9+-,
      ^pytp/~& ~&NlrNCXSX; ->ltxK7iFS (
         ~&rrk&& leql\iota"n"+ ~&l,
         ^rrihBPSPlCrX/~&l ~&r; ~&lrithNCBBPXS+ ~&aititBPB^?\~&a :^/~&ah ~&Bahtth2Xr2O?(
            ^R/~&f :^\~&att &athr:=ath :^\~&athr div+ minus~~+ ~&bbIatth2hXrtthPBhYPlX2O,
            ~&fatPR))+-+-

mp_chord_fit = # similar to above but uses mpfr numbers for greater stability; compatibility will require type conversions

successor; "n". %EWLMk; -+
   "t". ~&\"t"; ~&arv^?(
      mpfr..lessequal_p?alrdPX/~&falrvh2XPR ~&falrvth3XPR,
      ^(~&\1E0+ ~&al,~&ard); ~&ar^?\0E0! mpfr..add^/mpfr..mul+~&alrPrhPX ^R/~&f ^\~&art ^/~&all mpfr..mul+~&al),
   (%EELDMk+ ~&r+ ~&lll2rlr2Xllr2lrPrrPNCCVX:-0+ ~&rliNVSPp)^\~&lSytp -+
      %EWELXWLMk; %ELLMk+ * mp_solve+ ^(length+ --,~&); %ELLELXMk+ -+
         --; ^\~&rrPS ~&lrlPXS; * *-; * ~&rlX; mpfr..mul^(mpfr..nat2mp+ ~&rl,mpfr..pow_ui+ ~&lrrPX),
         zipt^~G\~&rbhhlPrDC ~&l; ~&iiDlShyCK9+iota; ^pxlrpS\~&x ~&hxPzSDrlXS; product:-1*+* take^*Dx/~&l ~&rrDlStK9+-,
      ^pytp/~& ~&NlrNCXSX; ->ltxK7iFS (
         ~&rrk&& leql\iota"n"+ ~&l,
         ^rrihBPSPlCrX/~&l ~&r; ~&lrithNCBBPXS+ ~&aititBPB^?\~&a :^/~&ah ~&Bahtth2Xr2O?(
            ^R/~&f :^\~&att &athr:=ath :^\~&athr mpfr..div+ mpfr..sub~~+ ~&bbIatth2hXrtthPBhYPlX2O,
            ~&fatPR))+-+-

(# multivariate takes an interpolating function generator such as any of those above and returns an interpolating function
generator for functions of many variables. The function returned by multivariate will take an argument of the form
<<x0..xn,y>..> where the x's are inputs and the y's are outputs, and will return a function that takes an input of the form
<x0..xn> to the corresponding or interpolated y value. #)

multivariate =

"f". ~&ahtt^?\-+~&h;,"f"+ ~&ahthPXS+- -+
   "t". -+
      ^H\~&lh "f"+ ^p/~&rlS ~&rlHS+ ~&ltPrrSPD,
      ^/~& ~&h; ~&/"t"; ~&aldl^?\~&aldr fleq?arldl2X/~&falvh2rXPR ~&falvth3rXPR+-,
   %efOXLMk; -+
      %eZefOXLXTMk+ ~&ldll3rdlr3XNXlrNCCV:-0; ~&av^?\~&Nadr2XNV ~&avhdlr5NXfavPMV,
      ^VNX(~&thlPthl2X,~&)*+ %efOXLLMk+ ||~&iNC (*~ leql/iota4)+ ~&a^& :^\~&fatPR take/4+ ~&a+-,
   ~&alPfarPMp^J/~&f ~&a; ~&lSrSX+ fleq-<&h; |=&h; ~&hhPtSXS+-

----------------------------------------------- other relevant functions ---------------------------------------------------

(# poly_dif takes a number n to a function that takes a polynomial interpolation function returned by one of the above
functions to its nth derivative by modifying the virtual machine code. It should work on functions generated by either
version of one_piece_polynomial and chord_fit, but not sinusoid. #)

poly_dif "n" =

rep"n" -|
   ^EZrB/~& ~&a^& -&%eeLDI,~&d&-?a\~&W ~&a; %eeLDdVRk *^0 ~&v?/~& ^V\~&v ||<0.>! ~&t+num+~&d; * times^/float+~&l ~&r,
   ^EZrB/~& ~&a^& -&%EELDI,~&d&-?a\~&W ~&a; *^0 ~&v?/~& ^V\~&v ||<0E0>! ~&t+num+~&d; * mpfr..mul^/mpfr..nat2mp+~&l ~&r,
   ~&a^& -&~&,%eLI&-?a\~&W ||<0.>! ~&t+num+~&a; * times^/float+~&l ~&r,
   ~&a^& -&~&,%ELI&-?a\~&W ||<0E0>! ~&t+num+~&a; * mpfr..mul^/mpfr..nat2mp+~&l ~&r|-
