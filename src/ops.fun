
#import std
#import nat
#import ext
#import opt
#import tag
#import tco
#import psp
#import lag
#import ogl

#comment -[
This module describes most of the operators in the language.

Copyright (C) 2007-2010 Dennis Furey]-

---------------------------------------------------- operator tables -------------------------------------------------------

prefix = ogl-prefix

#library+
#export+

aggregation = # operators that must occur in matched pairs

(* optimizers:= ~optimizers|| ! mode[aggregate: &]) (* match:= ~match|| ~&ixEZxB+ ~mnemonic) <
   operator[
      mnemonic: '-?',
      optimizers: mode[aggregate: <&>],
      meanings: mode[aggregate: ("f". ~&?/"f" "f"!) ^H\~&y ~&z; //=> (("p","f"),"g"). conditional("p","f","g")],
      help: mode[aggregate: 'cumulative conditional with default case last']],
   operator[
      mnemonic: '-+',
      optimizers: mode[aggregate: <&>],
      preprocessors: mode[aggregate: ||~& -&~&d.lag-suffix.&Z,~&v,~&vtZ,~&vh&-],
      meanings: mode[aggregate: ("f". ~&?/"f" "f"!) compose:-~&],
      help: mode[aggregate: 'cumulative functional composition']],
   operator[
      mnemonic: '-|',
      optimizers: mode[aggregate: <&>],
      preprocessors: mode[aggregate: ||~& -&~&d.lag-suffix.&Z,~&v,~&vtZ,~&vh&-],
      meanings: mode[aggregate: ("f". ~&?/"f" "f"!) :-0! ("p","q"). "p"||"q"],
      help: mode[aggregate: 'cumulative ||, short circuit functional disjunction']],
   operator[
      mnemonic: '-!',
      optimizers: mode[aggregate: <&>],
      preprocessors: mode[aggregate: ||~& -&~&d.lag-suffix.&Z,~&v,~&vtZ,~&vh&-],
      meanings: mode[aggregate: ("f". ~&?/"f" "f"!) :-0! ("p","q"). "p"!|"q"],
      help: mode[aggregate: 'cumulative !|, logical valued functional disjunction']],
   operator[
      mnemonic: '-&',
      optimizers: mode[aggregate: <&>],
      preprocessors: mode[aggregate: ||~& -&~&d.lag-suffix.&Z,~&v,~&vtZ,~&vh&-],
      meanings: mode[aggregate: ("f". ~&?/"f" "f"!) :-&! ("p","q"). "p"&&"q"],
      help: mode[aggregate: 'cumulative &&, short circuit functional conjunction']],
   operator[
      mnemonic: '[',
      match: ']',
      help: mode[aggregate: 'record delimiters'],
      meanings: mode[aggregate: =>0 ^H\~&r assign^/~&ln !+ ~&lm]],
   operator[
      mnemonic: '<',
      match: '>',
      meanings: mode[aggregate: ~&],
      help: mode[aggregate: 'list delimiters']],
   operator[
      mnemonic: '{',
      match: '}',
      meanings: mode[aggregate: (sort lleq); ~&aitB^?\~&a ~&ahthPE?/~&fatPR ~&ahPfatPRC],
      help: mode[aggregate: 'specifies sets as sorted lists with duplicates purged']],
   operator[
      mnemonic: '(',
      match: ')',
      meanings: mode[aggregate: ~&=>],
      preprocessors: mode[
         aggregate: ~&d.lag-suffix?/~& -&~&v,~&vtZ&-?/~&vh &d.semantics:= !+ ~&v?\0!! ~+ ~&=>+ triangle~&NiC+ &h!*+ ~&v],
      help: mode[aggregate: 'tuple delimiters']]>

manipulation = # operators used primarily as first order functions pertaining to lists and sets

(:^/~&h :^/~&th ~&tt&& *ttPizyCp &l.peer:=l ~&r.mnemonic) <
   operator[
      mnemonic: ':',
      dyadic: mode[prefix: &,postfix: &,solo: &],
      help: mode[
         infix: 'list construction operator, x0:<x1..xn> = <x0..xn>',
         postfix: 'assignment construction operator, n: m = ~&A(n,m)',
         prefix: 'assignment construction operator, :m n = ~&A(n,m)',
         solo: 'list construction operator, : (x0,<x1..xn>) = <x0..xn>'],
      meanings: mode[~&A/infix ~&C,~&A/solo ~&C,~&A/postfix //~&A,~&A/prefix \/~&A]],
   operator[
      mnemonic: '^:',
      dyadic: mode[prefix: &,postfix: &,solo: &],
      peer: ':',
      help: mode[
         infix: 'tree construction operator, d^:v = ~&V(d,v)',
         postfix: 'tree construction operator, d^: v = ~&V(d,v)',
         prefix: 'tree construction operator, ^:v d = ~&V(d,v)',
         solo: 'tree construction operator, ^: (d,v) = ~&V(d,v)'],
      meanings: mode[infix: ~&V,solo: ~&V,postfix: //~&V,prefix: \/~&V]],
   operator[
      mnemonic: '|',
      dyadic: mode[solo: &],
      help: mode$[infix: ~&,solo: ~&] 'union of a pair of sets',
      meanings: ~&H(
         mode$[infix: ~&,solo: ~&],
         ~&al^?\~&ar ~&ar?\~&al ==?abh/~&alh2fabt2RC lleq?abh/~&alh2faltPrXPRC ~&arh2falrtPXPRC)],
   operator[
      mnemonic: '--',
      dyadic: mode[prefix: &,postfix: &,solo: &],
      help: mode[
         infix: 'list concatenation, <x0..xn>--<y0..yn> = <x0..xn,y0..yn>',
         prefix: '--x is a function that appends x to its argument',
         postfix: 'x-- is a function that appends its argument to x',
         solo: 'list concatenation, -- (<x0..xn>,<y0..yn>) = <x0..xn,y0..yn>'],
      meanings: mode[infix: cat,prefix: "k". cat\"k",postfix: "k". cat/"k",solo: cat]],
   operator[
      mnemonic: '-*',
      dyadic: mode[prefix: &,postfix: &,solo: &],
      help: mode[
         infix: 'left distribution, x-*<y0..yn> = <(x,y0)..(x,yn)>',
         prefix: 'left distribution with fixed right side, (-*y) x = x-*y',
         postfix: 'left distribution with fixed left side, (x-*) y = x-*y',
         solo: 'left distribution, -* (x,<y0..yn>) = <(x,y0)..(x,yn)>'],
      meanings: mode[
         prefix: "k". distribute\"k",
         postfix: "k". distribute/"k",
         infix: distribute,
         solo: distribute]],
   operator[
      mnemonic: '*-',
      help: mode[
         infix: 'right distribution, <x0..xn>*-y = <(x0,y)..(xn,y)>',
         prefix: 'right distribution with fixed right side, (*-y) x = x*-y',
         postfix: 'right distribution with fixed left side, (x*-) y = x*-y',
         solo: 'right distribution, *- (<x0..xn>,y) = <(x0,y)..(xn,y)>'],
      meanings: mode[
         prefix: "k". ~&rlX*+ distribute/"k",
         postfix: "k". ~&rlX*+ distribute\"k",
         infix: ~&rlX*+ distribute+ ~&rlX,
         solo: ~&rlX*+ distribute+ ~&rlX]]>

(# These are some operators deriving functions combined with constants. Their preprocessors put a space between the root and
the left subtree so as not to inhibit optimization of the constants if they happen to be functions. That works because the
collect function defined in ogl.fun that's automatically incorporated into the preprocessor of every operator token stops
descending when a parent and its subtree have different postprocessors. #)

consternation = 

(:^/~&h ~&t; (optimizers:= mode[infix: <&>]!)*+ ~&izyCp; * &l.peer:=l ~&r.mnemonic) <
   operator[
      mnemonic: '!',
      help: mode[
         postfix: 'constant combinator, k! x = k for all x',
         solo: 'constant combinator, (! k) x = k for all x'],
      preprocessors: mode[postfix: ~lexeme=='(spacer)'?vhd/~& &vh:= ~&V/token[lexeme: '(spacer)',semantics: ~&h!]+ ~&v],
      meanings: mode[postfix: constant,solo: constant]],
   operator[
      mnemonic: '/',
      options: <'$': fan,'|': triangle,'*': map,';': filter>,
      opthelp: <'a $ applies to both of a pair, and a | triangulates over a list, ; filters, and * maps'>,
      dyadic: mode[solo: &],
      help: mode[
         infix: 'fixes the left argument to a function, f/k x = f(k,x)',
         solo: 'binary to unary combinator, (/ (f,k)) x = f(k,x)'],
      preprocessors: mode[infix: ~lexeme=='(spacer)'?vthd/~& &vth:= ~&V/token[lexeme: '(spacer)',semantics: ~&h!]+ ~&vt],
      meanings: mode[
         (infix,solo): ~&iiX (-++-+ ~&mSx); ~&?=(! +^(~&l,^^(!+ ~&r,~&!)),"h". "h"+ +^(~&l,^^(!+ ~&r,~&!)))]],
   operator[
      mnemonic: '\',
      dyadic: mode[solo: &],
      options: <'$': fan,'|': triangle,'*': map,';': filter>,
      opthelp: <'a $ applies to both of a pair, and a | triangulates over a list, ; filters, and * maps'>,
      help: mode[
         infix: 'fixes the right argument to a function, f\k x = f(x,k)',
         solo: 'reverse binary to unary combinator, (\ (f,k)) x = f(x,k)'],
      preprocessors: mode[infix: ~lexeme=='(spacer)'?vthd/~& &vth:= ~&V/token[lexeme: '(spacer)',semantics: ~&h!]+ ~&vt],
      meanings: mode[
         (infix,solo): ~&iiX (-++-+ ~&mSx); ~&?=(! +^(~&l,^^(~&!,!+ ~&r)),"h". "h"+ +^(~&l,^^(~&!,!+ ~&r)))]],
   operator[
      mnemonic: '/*',
      dyadic: mode[solo: &],
      help: mode[
         infix: 'mapping binary to unary combinator, f/*k x = (f/k)* x',
         solo: 'mapping binary to unary combinator, (/* (f,k)) x = (f/k)* x'],
      options: <'*': *,'=': ~&L+,'$': fan>,
      opthelp: <'* makes it a nested map, = flattens, and $ applies to both of a pair (order matters)'>,
      preprocessors: mode[infix: ~lexeme=='(spacer)'?vthd/~& &vth:= ~&V/token[lexeme: '(spacer)',semantics: ~&h!]+ ~&vt],
      meanings: mode[(infix,solo): ~&iiX (-++-+ ~&mSx); ~&?=(! ("f","k"). map "f"/"k","h". ("f","k"). "h" map "f"/"k")]],
   operator[
      mnemonic: '\*',
      dyadic: mode[solo: &],
      help: mode[
         infix: 'mapping binary to unary combinator, f\*k x = (f\k)* x',
         solo: 'mapping reverse binary to unary combinator, (\ (f,k)) x = (f\k)* x'],
      options: <'*': *,'=': ~&L+,'$': fan>,
      opthelp: <'* makes it a nested map, = flattens, and $ applies to both of a pair (order matters)'>,
      preprocessors: mode[infix: ~lexeme=='(spacer)'?vthd/~& &vth:= ~&V/token[lexeme: '(spacer)',semantics: ~&h!]+ ~&vt],
      meanings: mode[
         (infix,solo): ~&iiX (-++-+ ~&mSx); ~&?=(! ("f","k"). map "f"\"k","h". ("f","k"). "h" map "f"\"k")]]>

deconstruction = # operators making explicit use of pointers

<
   operator[
      mnemonic: '&',
      help: mode[solo: 'evaluates to the pointer determined by its suffix'],
      meanings: mode[solo: ~(0,0)?\(0,0)! (percolation+ * ~(0,(0,0))); ~((0,0),0)|| <'misused pseudo-pointer'>!%],
      opthelp: <
         'a pointer is given by the suffix, with pseudo-pointers allowed only',
         'when it''s the operand of a ~ operator'>,
      options: pnodes],
   operator[
      mnemonic: '@',
      peer: '*',
      help: mode[
         postfix: 'f@s is equivalent to f+ ~&s',
         solo: '@s f is equivalent to ~&s; f'],
      meanings: mode[(postfix,solo): ~&iiX ~&lNlXBrY+percolation@mS; ~&?=(! ~&,"d". "f". "f"+ "d")],
      opthelp: <'a pointer specifies a preprocessor for the operand'>,
      options: pnodes],
   operator[
      mnemonic: '.',
      help: mode[
         infix: 'pointer combinator, p.q addresses field q with respect to p',
         postfix: 'lambda abstraction, p. f returns f when argument matches p',
         solo: 'pointer combinator, . (p,q) addresses field q with respect to p'],
      meanings: mode$[infix: ~&,postfix: ! <'misused .'>!%,solo: ~&] ~&al^& ~&allrY?\~&ar ~&fallPrXlrPrXXPW],
   operator[
      mnemonic: '~',
      tight: &,
      preprocessors: (solo:= ~prefix) mode[
         prefix: ||~& ~&v&& ~&vhPiB+ ^V\propagation*v &d.(preprocessor,semantics):=d ~&NiX+ ~&hlNlXBrY!!],
      help: mode[
         prefix: 'deconstruction combinator, ~p = field(p)',
         solo: 'deconstruction combinator, (~ p) = field(p)'],
      meanings: mode[prefix: field,solo: field]],
   operator[
      mnemonic: ':=',
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      dyadic: mode[prefix: &,postfix: &,solo: &],
      options: pnodes,
      opthelp: <'a pointer expression specifies a postprocessor'>,
      excluder: -!~&ihB-= '0123456789',~&~<'!'-~; ~&r&& subset\'_abcdefghijklmnopqrstuvwxyz'+ ~&l!-,
      help: mode[
         solo: '(:= (p,f)) x replaces field(p) of x with (f x)',
         infix: '(p:=f) x replaces field(p) of x with (f x)',
         prefix: 'assignment of a fixed function, (:=f) p = p:=f',
         postfix: 'assignment to a fixed pointer, (p:=) f = p:=f'],
      meanings: mode[
         infix: ~&lNlXBrY+percolation+~&mS; ~&?=/assign! "d". "d"++ assign,
         prefix: ~&lNlXBrY+percolation+~&mS; ~&?=(! "f". assign\"f","d". "f". "d"++ assign\"f"),
         postfix: ~&lNlXBrY+percolation+~&mS; ~&?=(! "p". assign/"p","d". "p". "d"++ assign/"p"),
         solo: ~&lNlXBrY+percolation+~&mS; ~&?=/assign! "d". "d"++ assign]]>

predication = # operators concerned with logic

(* dyadic:= ~dyadic|| ! mode[prefix: &,postfix: &,solo: &]) (~&izyCp; * &l.peer:=l ~&r.mnemonic) <
   operator[
      mnemonic: '&&',
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      help: mode[
         infix: 'functional conjunction, f&&g x is (f x) if nil, (g x) otherwise',
         solo: 'functional conjunction, (&& (f,g)) x is (f x) if empty, else (g x)',
         postfix: 'conjunction with fixed left side, (p&&) q = p&&q',
         prefix: 'conjunction with fixed right side, (&&q) p = p&&q'],
      meanings: mode[
         infix: ("p","q"). "p"?/"q" 0!,
         prefix: "q". "p". "p"?/"q" 0!,
         postfix: "p". "q". "p"?/"q" 0!,
         solo: ("p","q"). "p"?/"q" 0!]],
   operator[
      mnemonic: '||',
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      help: mode[
         infix: 'disjunction, ((f||g) x) is (f x) if nonempty, else (g x)',
         prefix: 'disjunction with fixed right side, (||g) f = f||g',
         postfix: 'disjunction with fixed left side, (f||) g = f||g',
         solo: 'disjunction, (|| (f,g)) x is (f x) if nonempty, else (g x)'],
      meanings: mode[
         infix: ("p","q"). ^("p",~&); ~&l?/~&l "q"+~&r,
         prefix: "q". "p". ^("p",~&); ~&l?/~&l "q"+~&r,
         postfix: "p". "q". ^("p",~&); ~&l?/~&l "q"+~&r,
         solo: ("p","q"). ^("p",~&); ~&l?/~&l "q"+~&r]],
   operator[
      mnemonic: '!|',
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      help: mode[
         infix: 'f!|g x is true iff either (f x) or (g x) is nonempty',
         prefix: 'logical disjunction with fixed the right side, (!|g) f = f!|g',
         postfix: 'logical disjunction with fixed left side, (f!|) g = f!|g',
         solo: '(!| (f,g)) x is true iff either (f x) or (g x) is nonempty'],
      meanings: mode[
         infix: ("p","q"). "p"?/&! "q",
         prefix: "q". "p". "p"?/&! "q",
         postfix: "p". "q". "p"?/&! "q",
         solo:  ("p","q"). "p"?/&! "q"]],
   operator[
      mnemonic: '^&',
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      help: mode[
         infix: 'recursive conjunction, f^&g is equivalent to refer f&&g',
         prefix: 'recursive conjunction with fixed right side, (^&g) f = f^&g',
         postfix: 'recursive conjunction with fixed left side, (f^&) g = f^&g',
         solo: 'recursive conjunction, ^& (f,g) is equivalent to refer && (f,g)'],
      meanings: mode[
         infix: ("p","f"). refer "p"&&"f",
         prefix: "f". "p". refer "p"&&"f",
         postfix: refer++ ~&\0!;+ //?,      # equlvalent to "p". "f". refer "p"&&"f"
         solo: ("p","f"). refer "p"&&"f"]],
   operator[
      mnemonic: '^!',
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      help: mode[
         infix: 'recursive logical or, f^!g is equivalent to refer f!|g',
         prefix: 'recursive logical or with fixed right side, (^!g) f = f^!g',
         postfix: 'recursive logical or with fixed left side, (f^!) g = f^!g',
         solo: 'recursive logical or, ^! (f,g) is equivalent to refer !| (f,g)'],
      meanings: mode[
         infix: ("p","f"). refer "p"!|"f",
         prefix: "f". "p". refer "p"!|"f",
         postfix: "p". "f". refer "p"!|"f",
         solo: ("p","f"). refer "p"!|"f"]],
   operator[
      mnemonic: '-=',
      dyadic: mode[postfix: &],
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      preprocessors: mode[infix: ~lexeme=='(spacer)'?vthd/~& &vth:= ~&V/token[lexeme: '(spacer)',semantics: ~&h!]+ ~&vt],
      help: mode[
         infix: 'membership combinator, (f-=s) x <-> (f x) is a member of s',
         prefix: 'membership in a fixed constant, (-=s) x <-> x is in s',
         postfix: 'membership combinator with left side fixed, (f-=) s = f-=s',
         solo: 'membership predicate, -= (x,s) is true iff x is a member of s'],
      meanings: mode[
         infix: ("f","k"). "f"; \/ member "k",
         postfix: "f". "k". "f"; member\"k",
         prefix: "k". member\"k",
         solo: member]],
   operator[
      mnemonic: '==',
      dyadic: mode[postfix: &],
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      preprocessors: mode[infix: ~lexeme=='(spacer)'?vthd/~& &vth:= ~&V/token[lexeme: '(spacer)',semantics: ~&h!]+ ~&vt],
      help: mode[
         infix: 'comparison combinator, (f==k) x is true when (f x) = k',
         prefix: 'comparison to a fixed constant, (==k) x is true iff x = k',
         postfix: 'comparison combinator with left side fixed, (f==) k = f==k',
         solo: 'comparison predicate, == (x,y) is true if x = y, 0 otherwise'],
      meanings: mode[
         infix: ("f","k"). compare^("f",! "k"),
         postfix: "f". "k". "f"; compare/"k",
         prefix: "k". compare/"k",
         solo: compare]],
   operator[
      mnemonic: '~<',
      dyadic: mode[postfix: &],
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      preprocessors: mode[infix: ~lexeme=='(spacer)'?vthd/~& &vth:= ~&V/token[lexeme: '(spacer)',semantics: ~&h!]+ ~&vt],
      help: mode[
         infix: 'non-member combinator, (f~<s) x is false when (f x) is in s',
         prefix: 'non-member of a fixed set, (~<s) x is false iff x is in s',
         postfix: 'non-member combinator with left side fixed, (f~<) k = f~<k',
         solo: 'non-member predicate, ~< (x,s) is false if x is in s'],
      meanings: mode[
         infix: ("f","k"). (not member)^("f",! "k"),
         postfix: "f". "k". "f"; not member\"k",
         prefix: "k". not member\"k",
         solo: not member]],
   operator[
      mnemonic: '~=',
      dyadic: mode[postfix: &],
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      preprocessors: mode[infix: ~lexeme=='(spacer)'?vthd/~& &vth:= ~&V/token[lexeme: '(spacer)',semantics: ~&h!]+ ~&vt],
      help: mode[
         infix: 'unequal combinator, (f~=k) x is false when (f x) = k',
         prefix: 'unequal to a fixed constant, (~=k) x is false iff x = k',
         postfix: 'unequal combinator with left side fixed, (f~=) k = f~=k',
         solo: 'unequal predicate, ~= (x,y) is false if x = y'],
      meanings: mode[
         infix: ("f","k"). (not compare)^("f",! "k"),
         postfix: "f". "k". "f"; not compare/"k",
         prefix: "k". not compare/"k",
         solo: not compare]]>

serialization = # operators expressing computations whose results form the inputs to further computations

(dyadic:= ~dyadic|| mode[prefix: &,postfix: &,solo: &]!)* ^T(~&l,~&r; ~&i&& ~&izyCp; * &l.peer:=l ~&r.mnemonic) !=(peer) <
   operator[
      mnemonic: '->',
      peer: '-<',
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      options: pnodes,
      opthelp: <'a pointer expression specifies a postprocessor'>,
      help: mode[
         infix: 'p->f iterates f while p is true',
         prefix: 'iteration with a fixed function, (->f) p = p->f',
         postfix: 'iteration with a fixed predicate, (p->) f = p->f',
         solo: '(-> (p,f)) iterates f while p is true'],
      meanings: mode[
         infix: ~&lNlXBrY+percolation+~&mS; ~&?=/iterate! iterate;+ //+,
         prefix: ~&lNlXBrY+percolation+~&mS; ~&?=(! "f". iterate\"f","d". "f". "d"++ iterate\"f"),
         postfix: ~&lNlXBrY+percolation+~&mS; ~&?=(! "p". iterate/"p","d". "p". "d"++ iterate/"p"),
         solo: ~&lNlXBrY+percolation+~&mS; ~&?=/iterate! iterate;+ //+]],
   operator[
      mnemonic: '^=',
      dyadic: mode[],
      optimizers: mode[postfix: <&>,solo: <0,&>],
      options: <'=': 0>-- pnodes,
      opthelp: <'a pointer expression specifies a postprocessor; = specifies generalized limits'>,
      help: mode[
         postfix: 'f^= iterates f until a fixed point is detected',
         solo: '(^= f) iterates f until a fixed point is detected'],
      meanings: mode$[postfix: ~&,solo: ~&] ~&mS; ~&g?(
         ~&lNlXBrY+percolation; ~&?=/limit! limit;+ //+,
         ~&lNlXBrY+percolation+~&F; ~&?=/glimit! glimit;+ //+)],
   operator[
      mnemonic: '+',
      dyadic: mode[postfix: &,solo: &],
      optimizers: mode[infix: <&>,postfix: <&,&>,solo: <0,&>],
      options: <'*': *,'=': ~&L+,'.': *~,'$': fan>,
      opthelp: <
         '* maps, = flattens, $ fans, and . filters the resulting function',
         '(order matters)'>,
      preprocessors: mode[
         infix: -+
            &dvhd2X.postprocessors:= ~&iNX+ ^T/~&d.postprocessors ~&vhd.postprocessors.&itB,
            &vh:= preprocess+~&vh+-],
      help: mode[
         infix: 'functional composition, (f+g) x evaluates to f (g x)',
         postfix: 'functional composition with fixed left side, (f+) g = f+g',
         solo: 'functional composition, (+ (f,g)) x = f (g x)'],
      meanings: mode[
         postfix: ~&mSx; -++-; ~&?=(! "f". "g". compose("f","g"),"h". "f". "g". "h" compose("f","g")),
         infix: ~&mSx; -++-; ~&?=(! ("f","g"). compose("f","g"),"h". ("f","g").  "h" compose("f","g")),
         solo: ~&mSx; -++-; ~&?=(! ("f","g"). compose("f","g"),"h". ("f","g"). "h" compose("f","g"))]],
   operator[
      mnemonic: ';',
      dyadic: mode[postfix: &],
      options: <'*': *,'=': ~&L+,'.': *~,'$': fan>,
      opthelp: <
         '* maps, = flattens, $ fans, and . filters the resulting function',
         '(order matters)'>,
      optimizers: mode[infix: <&>,postfix: <&,&>,solo: <0,&>],
      preprocessors: mode[
         infix: -+
            &dvthd3X.postprocessors:= ~&iNX+ ^T/~&d.postprocessors ~&vthd.postprocessors.&itB,
            &vth:= preprocess+~&vth+-],
      help: mode[
         infix: 'sequential composition, (f;g) x = g (f x)',
         postfix: 'sequential composition with fixed left side, (f;) g = f;g',
         solo: 'sequential composiiton with fixed left side, (; f) g = f;g'],
      meanings: mode[
         infix: ~&?=(! compose+ ~&rlX,"h". "h"+ compose+ ~&rlX)+ -++-+ ~&mSx,
         postfix: ~&?=(! \/compose,"h". \/("h"+ compose))+ -++-+ ~&mSx,
         solo: ~&?=(! \/compose,"h". \/("h"+ compose))+ -++-+ ~&mSx]]>

tight_paralation = # high precedence operators expressing computations with trivial parallel decompositions

(:^/~&h ~&t; ~&izyCp; * &l.peer:=l ~&r.mnemonic) <
   operator[
      peer: '?',
      mnemonic: '|\',
      optimizers: mode[postfix: <&>,solo: <0,&>],
      options: pnodes,
      opthelp: <'a pointer expression specifies a postprocessor'>,
      help: mode[
         postfix: 'triangle combinator, f|\ <x0,x1,x2,x3..> = <x0,f x1,f f x2,f f f x3...>',
         solo: 'triangle combinator, (|\ f) <x0,x1,x2,x3..> = <x0,f x1,f f x2,f f f x3...>'],
      meanings: mode$[postfix: ~&,solo: ~&] ~&lNlXBrY+percolation+~&mS; ~&?=/triangle! "d". "d"++ triangle],
   operator[
      mnemonic: '~~',
      optimizers: mode[postfix: <&>,solo: <0,&>],
      options: pnodes,
      opthelp: <'a pointer expression specifies a preprocessor'>,
      help: mode[
         postfix: 'pairwise application operator, f~~ (x,y) evaluates to (f x,f y)',
         solo: 'pairwise application operator, (~~ f) (x,y) evaluates to (f x,f y)'],
      meanings: mode$[postfix: ~&,solo: ~&] ~&lNlXBrY+percolation+~&mS; ~&?=/fan! "d". "d";+ fan],
   operator[
      mnemonic: '$',
      optimizers: mode[postfix: <&,&>,solo: <0,&>],
      help: mode[
         postfix: 'raises the order of a record type constructor',
         solo: 'raises the order of a record type constructor'],
      meanings: mode[postfix: dollar+ ~&i&& ~&lNlXBrY+percolation+~&mS,solo: dollar+ ~&i&& ~&lNlXBrY+percolation+~&mS],
      opthelp: <
         'an optional pointer suffix indicates the location from which default field',
         'values are to be copied into the result'>,
      options: pnodes],
   operator[
      mnemonic: '~*',
      optimizers: mode[postfix: <&>,solo: <0,&>],
      options: pnodes,
      opthelp: <'a pointer expression specifies a preprocessor'>,
      help: mode[
         postfix: 'map to both, f~* (<x0..xn>,<y0..yn>) = (<f x0..f xn>,<f y0..f yn>)',
         solo: 'map to both, (~* f) (<x0..xn>,<y0..yn>) = (<f x0..f xn>,<f y0..f yn>)'],
      meanings: mode$[postfix: ~&,solo: ~&] ~&lNlXBrY+percolation+~&mS; ~&?=/(fan+ map)! "d". "d";+ fan+ map],
   operator[
      mnemonic: '*',
      optimizers: mode[postfix: <&>,solo: <0,&>],
      options: pnodes,
      opthelp: <'a pointer expression specifies a preprocessor'>,
      help: mode[
         postfix: 'map combinator, f* <x0..xn> = <f x0..f xn>',
         solo: 'map combinator, (* f) <x0..xn> = <f x0..f xn>'],
      meanings: mode$[postfix: ~&,solo: ~&] ~&lNlXBrY+percolation+~&mS; ~&?=/map! "d". "d";+ map],
   operator[
      mnemonic: '*=',
      optimizers: mode[postfix: <&>,infix: <&>,solo: <0,&>],
      options: <'*': *,'=': ~&L+>-- pnodes,
      opthelp: <
         '* nests maps, and = flattens further',
         '(order matters), and a pointer is a preprocessor'>,
      help: mode[
         postfix: 'flattening map, f*= is equivalent to reduce(cat,<>)+ map f',
         solo: 'flattening map, (*= f) is equivalent to reduce(cat,<>)+ map f'],
      meanings: mode$[postfix: ~&,solo: ~&] -+
         ~&?=l(~&r; "h". "f". "h" reduce(cat,<>)+ map "f",("d","h"). "f". "d"; "h" reduce(cat,<>)+ map "f"),
         ^|(~&lNlXBrY+ percolation,-++-+ ~&x)+ !=bmS ~&nh-= ~&nSL pnodes+-]>

loose_paralation = # low precedence operators expressing computations with trivial parallel decompositions

(~&izyCp; * &l.peer:=l ~&r.mnemonic) <
   operator[
      mnemonic: '^',
      dyadic: mode[postfix: &],
      optimizers: mode[postfix: <&,&>,infix: <&>,solo: <0,&>],
      help: mode[
         infix: 'composition after coupling, f^(g,h) x evaluates to f(g x,h x)',
         postfix: 'binary operator lifting, ((f^) (g,h)) x = f(g x,h x)',
         solo: 'coupling combinator, ((^) (f,g)) x evaluates to (f x,g x)'],
      meanings: mode[
         infix: ~&lNlXBrY+percolation+~&mS; ~&?=(! ++ couple/~&l couple+ ~&r,+++ couple/~&l+ couple+~&r;+ //+),
         postfix: ("f". ~&lNlXBrY+percolation+~&mS; ~&?=/"f"! "d". "d"++ "f") compose(
            compose,
            couple(constant compose,compose(couple,couple(constant,constant couple)))),
         solo: ~&lNlXBrY+percolation+~&mS; ~&?=/couple! "d". "d"++ couple],
      opthelp: <'a pointer expression specifies a postprocessor'>,
      options: pnodes],
   operator[
      mnemonic: '^~',
      dyadic: mode[postfix: &],
      optimizers: mode[infix: <&>,postfix: <&,&>,solo: <0,&>],
      help: mode[
         infix: 'couple, compose, and fan, f^~(g,h) x evaluates to (f g x,f h x)',
         postfix: 'couple, compose, and fan, ((f^~) (g,h)) x evaluates to (f g x,f h x)',
         solo: 'couple, compose, and fan, ((^~ f) (g,h)) x evaluates to (f g x,f h x)'],
      meanings: mode[
         infix: (~&nh-= ~&nSL pnodes)!=; ^(~&lNlXBrY+percolation+~&lmS,-++-+ ~&rmSx); ~&?=l(
            ("d","e"). ("f","gh"). ("e" fan "f")^("gh"),
            ("d","e"). ("f","gh"). ("d"; "e" fan "f")^("gh")),
         postfix: (~&nh-= ~&nSL pnodes)!=; ^(~&lNlXBrY+percolation+~&lmS,-++-+ ~&rmSx); ~&?=l(
            ("d","e"). "f". "gh". ("e" fan "f")^("gh"),
            ("d","e"). "f". "gh". ("d"; "e" fan "f")^("gh")),
         solo: (~&nh-= ~&nSL pnodes)!=; ^(~&lNlXBrY+percolation+~&lmS,-++-+ ~&rmSx); ~&?=l(
            ("d","e"). "f". "gh". ("e" fan "f")^("gh"),
            ("d","e"). "f". "gh". ("d"; "e" fan "f")^("gh"))],
      opthelp: <'* maps, = flattens, ~ filters, and a pointer expression specifies a postprocessor'>,
      options: <'*': *,'=': ~&L+,'~': *~>-- pnodes],
   operator[
      mnemonic: '^|',
      dyadic: mode[postfix: &],
      optimizers: mode[infix: <&>,postfix: <&,&>,solo: <0,&>],
      help: mode[
         infix: 'pairwise coupling, f^|(g,h) (x,y) evaluates to f(g x,h y)',
         postfix: 'pairwise coupling, ((f^|) (g,h)) (x,y) evaluates to f(g x,h y)',
         solo: 'pairwise coupling, ^|(g,h) (x,y) evaluates to (g x,h y)'],
      meanings: mode[
         infix: (~&nh-= ~&nSL pnodes)!=; ^(~&lNlXBrY+percolation+~&lmS,-++-+ ~&rmSx); ~&?=l(
            ("d","e"). ("f","g","h"). ("e" "f")^("g"+ ~&l,"h"+ ~&r),
            ("d","e"). ("f","g","h"). (("e" "f")+ "d")^("g"+ ~&l,"h"+ ~&r)),
         postfix: (~&nh-= ~&nSL pnodes)!=; ^(~&lNlXBrY+percolation+~&lmS,-++-+ ~&rmSx); ~&?=l(
            ("d","e"). "f". ("g","h"). ("e" "f")^("g"+ ~&l,"h"+ ~&r),
            ("d","e"). "f". ("g","h"). (("e" "f")+ "d")^("g"+ ~&l,"h"+ ~&r)),
         solo: (~&nh-= ~&nSL pnodes)!=; ^(~&lNlXBrY+percolation+~&lmS,-++-+ ~&rmSx); ~&?=l(
            ("d","e"). ("g","h"). ("e" ~&)^("g"+ ~&l,"h"+ ~&r),
            ("d","e"). ("g","h"). (("e" ~&)+ "d")^("g"+ ~&l,"h"+ ~&r))],
      opthelp: <'* maps, = flattens, ~ fans, and a pointer expression specifies a postprocessor'>,
      options: <'*': *,'=': ~&L+,'~': ~~>-- pnodes],
   operator[
      mnemonic: '^*',
      dyadic: mode[postfix: &],
      optimizers: mode[infix: <&>,postfix: <&,&>,solo: <0,&>],
      opthelp: <
         '* maps again, = flattens, ~ filters, and',
         'a pointer in a suffix is applied after the couple and before the mapped function'>,
      help: mode[
         infix: 'couple, compose, and map, f^*(g,h) is equivalent to f*+ ^(g,h)',
         postfix: 'couple, compose, and map, ((f^*) (g,h)) is equivalent to f*+ ^(g,h)',
         solo: 'couple, compose, and map, ((^* f) (g,h)) is equivalent to f*+ ^(g,h)'],
      meanings: mode[
         infix: (~&nh-= ~&nSL pnodes)!=; ^(~&lNlXBrY+percolation+~&lmS,-++-+ ~&rmSx); ~&?=l(
            ("d","e"). ("f","gh"). ("e" map "f")^("gh"),
            ("d","e"). ("f","gh"). ("d"; "e" map "f")^("gh")),
         postfix: (~&nh-= ~&nSL pnodes)!=; ^(~&lNlXBrY+percolation+~&lmS,-++-+ ~&rmSx); ~&?=l(
            ("d","e"). "f". "gh". ("e" map "f")^("gh"),
            ("d","e"). "f". "gh". ("d"; "e" map "f")^("gh")),
         solo: (~&nh-= ~&nSL pnodes)!=; ^(~&lNlXBrY+percolation+~&lmS,-++-+ ~&rmSx); ~&?=l(
            ("d","e"). "f". "gh". ("e" map "f")^("gh"),
            ("d","e"). "f". "gh". ("d"; "e" map "f")^("gh"))],
      options: <'*': *,'=': ~&L+,'~': ~~>-- pnodes]>

interrogation = # operators expressing explicit conditional forms

(~&izyCp; * &l.peer:=l ~&r.mnemonic) <
   operator[
      mnemonic: '?',
      optimizers: mode[postfix: <&,&>,solo: <0,&>],
      help: mode[
         postfix: 'conditional, ((p?) (f,g)) x is (f x) if p(x) is true, else g x',
         solo: 'conditional, ((?) (p,f,g)) x is (f x) if p(x) is true, else g x'],
      meanings: mode[
         postfix: ~&lNlXBrY+percolation+~&mS; conditional(==~&,! //conditional,"d". //conditional+ "d";),
         solo: ~&lNlXBrY+percolation+~&mS; conditional(==~&,conditional!,"d". conditional^\~&r "d";+ ~&l)],
      opthelp: <
         'an optional pointer in a suffix serves as a preprocessor',
         'to the predicate of the conditional form'>,
      options: pnodes],
   operator[
      mnemonic: '^?',
      optimizers: mode[postfix: <&,&>,solo: <0,&>],
      help: mode[
         postfix: 'recursive conditional, p^? (f,g) is equivalent to refer p? (f,g)',
         solo: 'recursive conditional, ^? (p,f,g) is equivalent to refer ? (p,f,g)'],
      options: <'<': \/-=,'=': //==,'$': =]>-- pnodes,
      meanings: mode[
         postfix: (~&nh-='<=[')!=; ^(~&lNlXBrY+percolation+~&rmS,-++-+ ~&lmSs); ~&?=l(
            ("d","e"). "p". "fg". refer ("e" "p")?("fg"),
            ("d","e"). "p". "fg". refer (("e" "p")+"d")?("fg")),
         solo: (~&nh-='<=[')!=; ^(~&lNlXBrY+percolation+~&rmS,-++-+ ~&lmSs); ~&?=l(
            ("d","e"). ("p","fg"). refer ("e" "p")?("fg"),
            ("d","e"). ("p","fg"). refer (("e" "p")+"d")?("fg"))],
      opthelp: <
         '$ takes a prefix to a starts-with test,',
         '< takes the predicate to be a membership test,',
         '= takes it as a test of equality, and an optional pointer is a preprocessor',
         'to the predicate'>],
   operator[
      mnemonic: '?=',
      optimizers: mode[postfix: <&,&>,solo: <0,&>],
      help: mode[
         postfix: 'comparing conditional, (x?= (f,g)) y is (f y) if x=y, else g y',
         solo: 'comparing conditional, (?= (x,f,g)) y is (f y) if x=y, else g y'],
      meanings: mode[
         postfix: ~&lNlXBrY+percolation+~&mS; conditional/(==~&) (
            ! "c". "fg". compare/"c"?("fg"),
            "d". "c". "fg". "d";compare/"c"?("fg")),
         solo: ~&lNlXBrY+percolation+~&mS; conditional/(==~&) (
            ! ("c","fg"). compare/"c"?("fg"),
            "d". ("c","fg"). ("d"; //compare "c")?("fg"))],
      opthelp: <
         'an optional pointer in a suffix serves as a preprocessor',
         'to the predicate of the conditional form'>,
      options: pnodes],
   operator[
      mnemonic: '?$',
      optimizers: mode[postfix: <&,&>,solo: <0,&>],
      help: mode[
         postfix: 'prefix conditional, (x?$ (f,g)) y is (f y) if =]x y, else g y',
         solo: 'prefix conditional, (?$ (x,f,g)) y is (f y) if =]x y, else g y'],
      meanings: mode[
         postfix: ~&lNlXBrY+percolation+~&mS; conditional/(==~&) (
            ! "c". "fg". =]"c"?("fg"),
            "d". "c". "fg". ("d"; =]"c")?("fg")),
         solo: ~&lNlXBrY+percolation+~&mS; conditional/(==~&) (
            ! ("c","fg"). =]"c"?("fg"),
            "d". ("c","fg"). ("d"; =]"c")?("fg"))],
      opthelp: <
         'an optional pointer in a suffix serves as a preprocessor',
         'to the predicate of the conditional form'>,
      options: pnodes],
   operator[
      mnemonic: '?<',
      optimizers: mode[postfix: <&,&>,solo: <0,&>],
      help: mode[
         postfix: '(s?< (f,g)) y is (f y) if y is a member of s, else g y',
         solo: '(?< (s,f,g)) y is (f y) if y is a member of s, else g y'],
      meanings: mode[
         postfix: ~&lNlXBrY+percolation+~&mS; ~&?=(
            ! "c". "fg". member\"c"?("fg"),
            "d". "c". "fg". "d";member\"c"?("fg")),
         solo: ~&lNlXBrY+percolation+~&mS; ~&?=(
            ! ("c","fg"). member\"c"?("fg"),
            "d". ("c","fg"). "d";member\"c"?("fg"))],
      opthelp: <
         'an optional pointer in a suffix serves as a preprocessor',
         'to the predicate of the conditional form'>,
      options: pnodes]>

recursion = # functional combinators expressing standardized forms of recursion over trees and lists

(~&izyCp; * &l.peer:=l ~&r.mnemonic) <
   operator[
      mnemonic: '=>',
      dyadic: mode[prefix: &,solo: &],
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&>,solo: <0,&>],
      preprocessors: mode[infix: ~lexeme=='(spacer)'?vthd/~& &vth:= ~&V/token[lexeme: '(spacer)',semantics: ~&h!]+ ~&vt],
      help: mode[
         infix: 'fold combinator, f=>k <x0..xn> = f(x0,f(..f(xn,k)))',
         prefix: 'fold with fixed vacuous case, (=>k f) <x0..xn> = f(x0,f(..f(xn,k)))',
         postfix: 'right association combinator, f=> <x0..xn> = f(x0,f(..xn))',
         solo: 'fold combinator, (=> (f,k)) <x0..xn> = f(x0,f(..f(xn,k)))'],
      meanings: mode[
         infix: refer+ ~&a?^\!+~&r ~&l; ; ^/~&ah ~&fatPR,
         prefix: "k". "f". (refer+ ~&a?^\!+~&r ~&l; ; ^/~&ah ~&fatPR)("f","k"),
         postfix: "f". ~&?\0! ~&t?\~&h refer "f"^/~&ah ~&att?\~&ath ~&fatPR,
         solo:  refer+ ~&a?^\!+~&r ~&l; ; ^/~&ah ~&fatPR]],
   operator[
      mnemonic: ':-',
      dyadic: mode[prefix: &,postfix: &,solo: &],
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      preprocessors: mode[infix: ~lexeme=='(spacer)'?vthd/~& &vth:= ~&V/token[lexeme: '(spacer)',semantics: ~&h!]+ ~&vt],
      help: mode[
         infix: 'f:-x is list reduction by binary operator f with vacuous case x',
         prefix: 'list reduction with fixed vacuous case, (:-x) f = f:-x',
         postfix: 'list reduction with fixed binary operator, (f:-) x = f:-x',
         solo: ':- (f,x) is list reduction by binary operator f with vacuous case x'],
      meanings: mode[infix: reduce,prefix: "k". reduce\"k",postfix: "f". reduce/"f",solo: reduce]],
   operator[
      mnemonic: '<:',
      dyadic: mode[prefix: &,postfix: &,solo: &],
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      help: mode[
         infix: 'recursive composition, f<:g is equivalent to refer f+g',
         prefix: 'recursive composition with fixed right side, (<:g) f = f<:g',
         postfix: 'recursive composition with fixed left side, (f<:) g = f<:g',
         solo: 'recursive composition, <: (f,g) is equivalent to refer + (f,g)'],
      meanings: mode[
         infix: ("p","f"). refer "p"+ "f",
         prefix: "f". "p". refer "p"+ "f",
         postfix: "p". "f". refer "p"+ "f",
         solo: ("p","f"). refer "p"+ "f"]],
   operator[
      mnemonic: '*^',
      dyadic: mode[prefix: &],
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&>,solo: <0,&>],
      options: <'*': *,'=': ~&L+,'.': *~>,
      opthelp: <'* maps, = flattens, and . filters the resulting function (order matters)'>,
      help: mode[
         infix: 'tree folding combinator, f*^x specifies vacuous case x',
         prefix: 'tree folding combinator with fixed vacuous case, (*^x) f = f*^x',
         postfix: 'tree folding combinator with no vacuous case',
         solo: 'tree folding combinator with no vacuous case'],
      meanings: mode[
         infix: ~&mSx; -++-; "h". ("l","r"). "h" refer conditional(~&a,("l")^V/~&ad mapcur&favPJ,"r"!),
         prefix: ~&mSx; -++-; "h". "r". "l". "h" refer conditional(~&a,("l")^V/~&ad mapcur&favPJ,"r"!),
         postfix: ~&mSx; -++-; "h". "h"+ refer+ ^V(~&ad,mapcur&favPJ);,
         solo: ~&mSx; -++-; "h". "h"+ refer+ ^V(~&ad,mapcur&favPJ);]]>

liberation = # operators concerned with table lookups, of relevance to library functions

(!=(peer); ^T/~&l ~&r&& ~&rizyCp; * &l.peer:=l ~&r.mnemonic) <
   operator[
      mnemonic: '-',
      peer: '..',
      tight: &,
      preprocessors: mode$[infix: ~&] ?(
         ~&vth; -!~&d.semantics&& ^EZ/~&d.semantics !+ !+ ~&d.lexeme,~&v!| not ~&d.lexeme; all \/-= :/`_ letters!-,
         ~&/<'misused dash operator'>!% &vthd.(preprocessor,semantics):= ~&NiX+ !+ !+ ~&vthd.lexeme),
      meanings: mode[
         infix: -+
            ^(~&l,~&lrnPE~|); ~&r?(
               ~&rh; ||~&m -&
                  -&~&n,~&nt,~&nh==`_,~&nth~=`_&-,
                  ~&m; extractable&& extract; *^0 (all~&+ ~&v)&& -!
                     ~&dlZ&& ~&dr; _type_constructor%I&& ~tag-mnemonic-= ~&nS atypical_types,
                     ~&d-= ~&nS type_constructors!-,
                  ~&m; type_decompression type_constructors-y&-,
               <.'unrecognized identifier: '--+ ~&l>%),
            ^/~&r ~&l; ~&inBF+ -&~&,not %soXLI,extractable&-?\~& extract+-],
      help: mode[infix: 'table lookup operator, <''n0'': m0, ... ''nk'': mk>-ni = mi']],
   operator[
      mnemonic: '..',
      peer: '-',
      tight: &,
      options: ~&iNCiAS '_0123456789'-- letters,
      opthelp: <'the suffix spells the recognizably truncated library function name in letters, digits, and underscores'>,
      preprocessors: mode$[postfix: ~&] ?(
         ~&vh; -!~&d.semantics&& ^EZ/~&d.semantics !+ !+ ~&d.lexeme,~&v!| not ~&d.lexeme; all \/-= :/`_ letters!-,
         ~&/<'misused .. (library) operator'>!% &vhd.(preprocessor,semantics):= ~&NiX+ !+ !+ ~&vhd.lexeme),
      meanings: mode[
         postfix: ~&mS; /// ~&rlX;  ||<'unrecognized library function'>!% ||-&~&B,%sWI,library&- -+
            (~&itZB&& library+ ~&h)+ -*; *= ^D/~&rl ~&l?\~&rr ~&lrrPX; ==~||| [=~|,
            %sssLXLXMk^/~&r (~&lrlPE~||| ~| [=+ ~&lrlPX)^/~&l ~&hlPrSXS+ |=&l+ have/'*' '*'+-,
         solo: ~&mS; ||<'unrecognized library function'>!% -+
            (~&itZB&& library+ ~&h)+ -*; *= ^D/~&rl ~&l?\~&rr ~&lrrPX; ==~||| [=~|,
            %sssLXLXMk^/~& ~&hlPrSXS+ |=&l+ have/'*' '*'+-],
      help: mode[
         solo: 'library combinator, ..func abbreviates library(''*'',''func..'')',
         postfix: 'library combinator, lib..func abbreviates library(''lib..'',''func..'')']],
   operator[
      mnemonic: '.|',
      peer: '$',
      dyadic: mode[postfix: &],
      options: ~&iNCiAS '_0123456789'-- letters,
      opthelp: <'the suffix spells the recognizably truncated library function name in letters, digits, and underscores'>,
      preprocessors: mode$[infix: ~&,postfix: ~&] ?(
         ~&vh; -!~&d.semantics&& ^EZ/~&d.semantics !+ !+ ~&d.lexeme,~&v!| not ~&d.lexeme; all \/-= :/`_ letters!-,
         ~&/<'misused .| (library) operator'>!% &vhd.(preprocessor,semantics):= ~&NiX+ !+ !+ ~&vhd.lexeme),
      meanings: mode[
         postfix: ~&mS; //\ ("l". have"l"?/library"l")+ %sWMk+ ||~& -+
            (~&itZB&& ~&h)+ -*; *= ^D/~&rl ~&l?\~&rr ~&lrrPX; ==~||| [=~|,
            %sssLXLXMk^/~&r (~&lrlPE~||| ~| [=+ ~&lrlPX)^/~&l ~&hlPrSXS+ |=&l+ have/'*' '*'+-,
         infix: ~&mS; /// ?^(have+~&l,^/library+~&l ~&r)^\~&rr ~&rlPlX; ||~& -+
            (~&itZB&& ~&h)+ -*; *= ^D/~&rl ~&l?\~&rr ~&lrrPX; ==~||| [=~|,
            %sssLXLXMk^/~&r (~&lrlPE~||| ~| [=+ ~&lrlPX)^/~&l ~&hlPrSXS+ |=&l+ have/'*' '*'+-,
         solo: ~&mS; (~&ilrBB?\<'unrecognized function name'>!% "l". have"l"?/library"l")+ ||~& -+
            %sWZMk+ (~&itZB&& ~&h)+ -*; *= ^D/~&rl ~&l?\~&rr ~&lrrPX; ==~||| [=~|,
            %sssLXLXMk^/~& ~&hlPrSXS+ |=&l+ have/'*' '*'+-],
      help: mode[
         solo: 'defaultable library function, .|func f defaults to f at run time',
         postfix: 'defaultable library function, (lib.|func) f defaults to f at run time',
         infix: 'defaultable library function, lib.|func f defaults to f at run time']],
   operator[
      mnemonic: '.!',
      peer: '$',
      dyadic: mode[postfix: &],
      options: ~&iNCiAS '_0123456789'-- letters,
      opthelp: <'the suffix spells the recognizably truncated library function name in letters, digits, and underscores'>,
      preprocessors: mode$[infix: ~&,postfix: ~&] ?(
         ~&vh; -!
            ~&d.semantics&& ^EZ/~&d.semantics !+ !+ ~&d.lexeme,
            ~&v!| not ~&d.lexeme; all \/-= :/`_ letters!-,
         ~&/<'misused .! (library) operator'>!% &vhd.(preprocessor,semantics):= ~&NiX+ !+ !+ ~&vhd.lexeme),
      meanings: mode[
         infix: ~&mS; /// ^Y\~&rr ~&rlPlX; -+
            (~&itZB&& library+ ~&h)+ -*; *= ^D/~&rl ~&l?\~&rr ~&lrrPX; ==~||| [=~|,
            %sssLXLXMk^/~&r (~&lrlPE~||| ~| [=+ ~&lrlPX)^/~&l ~&hlPrSXS+ |=&l+ have/'*' '*'+-,
         postfix: ~&mS; "f". "l". ~&?(!,~&!)+ -+
            (~&itZB&& library+ ~&h)+ -*; *= ^D/~&rl ~&l?\~&rr ~&lrrPX; ==~||| [=~|,
            ~&/"f"+ (~&lrlPE~||| ~| [=+ ~&lrlPX)/"l"+ ~&hlPrSXS+ |=&l+ have/'*' '*'+-,
         solo: ~&mS; ~&?(!,~&!)+ -+
            (~&itZB&& library+ ~&h)+ -*; *= ^D/~&rl ~&l?\~&rr ~&lrrPX; ==~||| [=~|,
            %sssLXLXMk^/~& ~&hlPrSXS+ |=&l+ have/'*' '*'+-],
      help: mode[
         solo: 'defaultable library function, .!func f defaults to f at compile time',
         postfix: 'defaultable library function, (lib.!func) f defaults to f at compile time',
         infix: 'defaultable library function, lib.!func f defaults to f at compile time']]>

classification = # operators concerned with pattern recognition and classification

(!=(peer); ^T/~&l ~&r&& ~&rizyCp; * &l.peer:=l ~&r.mnemonic) <
   operator[
      mnemonic: '%',
      peer: '^',
      help: mode$[postfix: ~&,solo: ~&] 'specifier of printing functions and exception handlers',
      meanings: mode[
         postfix: ~&mS; "s". "v". ~&H(
            ~&r?/execution ~&lh; ~&H\<>!++ //+ !; //guard compare+ <>!,
            ~&/<"v"> "s"),
         solo: (~&i&& all ~&n-= ~&iNCS '0123456789')?(
            \/guard+ \/--+ ~&nSLPNC,
            (~&r?/execution ! ~&H\<>!++ //+ !; //guard compare+ <>!)/<>+ ~&mS)],
      opthelp: <
         'a numeric suffix in the solo usage of the operator indicates an exception handler that prints the number;',
         'otherwise the suffix specifies a type expression or type related function'>,
      options: type_constructors-- ~&iNCNAS '0123456789'],
   operator[
      mnemonic: '%~',
      peer: '%',
      meanings: mode$[postfix: ~&,solo: ~&] mtwist..bern++ !+ -&~<{0.,.5},~&i&-+ math..div\100.+ -|
         %nI?(nleq\100&& math..strtod+ ~&h+ %nP,-&%eI,math..islessequal/0.,math..islessequal\100.,~&i&-),
         <'%~ operand out of range'>!%|-,
      help: mode[
         postfix: 'n%~ returns true n% of the time, for real or natural n',
         solo: '(%~ n) returns true n% of the time, for real or natural n']],
   operator[
      mnemonic: '%-',
      peer: '%',
      help: mode[solo: 'parameterized type expression constructor'],
      meanings: mode[solo: ~&mS; ~&?\<'misused %- operator'>!% "s". "v". execution/<"v"> "s"],
      opthelp: <'the suffix specifies a type expression or type related function'>,
      options: type_constructors],
   operator[
      mnemonic: '=:',
      optimizers: mode[postfix: <&>,solo: <0,&>],
      help: mode[
         postfix: 'address map, <(ai,yi)..>=: an = yn, where ai are addresses',
         solo: 'address map, (=: <(ai,yi)..>) an = yn, where ai are addresses'],
      meanings: mode[(postfix,solo): ~&iiX address_map]],
   operator[
      mnemonic: '-~',
      optimizers: mode[postfix: <&>,solo: <0,&>],
      options: pnodes,
      opthelp: -[a pointer expression specifies a postprocessor]-,
      help: mode[
         postfix: 'p-~ x = (l,r) where l--r = x and p is true of all members of l',
         solo: '(-~ p) x = (l,r) where l--r = x and p is true of all members of l'],
      meanings: mode$[postfix: ~&,solo: ~&] ~&lNlXBrY+percolation+~&mS; ~&?=(
         ! "p". ~&a^?\&! "p"?ah/~&ahPfatPRXlrlPCrrPX ~&NaX,
         "d". "p". "d"+ ~&a^?\&! "p"?ah/~&ahPfatPRXlrlPCrrPX ~&NaX)],
   operator[
      mnemonic: '~-',
      optimizers: mode[postfix: <&>,solo: <0,&>],
      options: pnodes,
      opthelp: -[a pointer expression specifies a postprocessor]-,
      help: mode[
         postfix: 'p~- x = (l,r) where l--r = x and p is true of all members of r',
         solo: '(~- p) x = (l,r) where l--r = x and p is true of all members of r'],
      meanings: mode$[postfix: ~&,solo: ~&] ~&lNlXBrY+percolation+~&mS; ~&?=(
         ! "p". ~&rlX+ (fan reverse)+ reverse; ~&a^?\&! "p"?ah/~&ahPfatPRXlrlPCrrPX ~&NaX,
         "d". "p". "d"+ ~&rlX+ (fan reverse)+ reverse; ~&a^?\&! "p"?ah/~&ahPfatPRXlrlPCrrPX ~&NaX)],
   operator[
      mnemonic: '*~',
      optimizers: mode[postfix: <&>,solo: <0,&>],
      preprocessors: mode[infix: ^V/(&d.preprocessor:=d 0!) :^/~&vh propagation*+ ~&vt],
      options: pnodes,
      opthelp: -[a pointer expression specifies a postprocessor]-,
      help: mode[
         postfix: 'filter combinator, p*~ <x0..xn> deletes x''s for which p is false',
         infix: 'filter combinator, p*~f <x0..xn> deletes x''s for which p+~f is false',
         solo: 'filter combinator, (*~ p) <x0..xn> deletes x''s for which p is false'],
      meanings: mode[
         infix: ~&lNlXBrY+percolation+~&mS; ~&?=(
            ! &?=rl/filter+~&l ~&rl?(~&lrlPX; ("p","f"). filter "p"+ field "f",~&lrrPX; ("p","f"). filter "p"+ "f"),
            "d". "d"++ &?=rl/filter+~&l ~&rl?(
               ~&lrlPX; ("p","f"). filter "p"+ field "f",
               ~&lrrPX; ("p","f"). filter "p"+ "f")),
         (postfix,solo): ~&iiX ~&lNlXBrY+percolation+~&mS; ~&?=/filter! "d". "d"++ filter]],
   operator[
      mnemonic: '!=',
      optimizers: mode[prefix: <&>,infix: <&>,postfix: <&>,solo: <0,&>],
      options: pnodes,
      opthelp: -[a pointer expression specifies a postprocessor]-,
      preprocessors: mode[
         prefix: ^V/(&d.preprocessor:=d 0!) propagation*+ ~&v,
         infix: ^V/(&d.preprocessor:=d 0!) :^/~&vh propagation*+ ~&vt],
      help: mode[
         infix: 'p!=f bipartitions a list or set by the predicate p+ field f',
         prefix: '!=f bipartitions a list or set by the predicate field f',
         postfix: 'bipartition, p!= <x0..xn> = (<xi..>,<xj..>) where p(xi) are true',
         solo: 'bipartition, (!= p) <x0..xn> = (<xi..>,<xj..>) where p(xi) are true'],
      meanings: mode[
         infix: ~&lNlXBrY+percolation+~&mS; ~&?=(
            ! &?=rl/bipartition+~&l ~&rl?(
               ~&lrlPX; ("p","f"). bipartition "p"+ field "f",
               ~&lrrPX; ("p","f"). bipartition "p"+ "f"),
            "d". "d"++ &?=rl/bipartition+~&l ~&rl?(
               ~&lrlPX; ("p","f"). bipartition "p"+ field "f",
               ~&lrrPX; ("p","f"). bipartition "p"+ "f")),
         prefix: ~&lNlXBrY+percolation+~&mS; ~&?=(
            ! ~&l?(~&l; "f". bipartition field "f",~&r; "f". bipartition "f"),
            "d". ~&l?(~&l; "f". "d"+ bipartition field "f",~&r; "f". "d"+ bipartition "f")),
         solo: ~&lNlXBrY+percolation+~&mS; ~&?=/bipartition! "d". "d"++ bipartition,
         postfix: ~&lNlXBrY+percolation+~&mS; ~&?=/bipartition! "d". "d"++ bipartition]],
   operator[
      mnemonic: '%=',
      dyadic: mode[prefix: &,postfix: &,solo: &],
      optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      options: <'*': *,'=': ~&L+,'-': ^=>,
      opthelp: <'* maps, - iterates, and = flattens (order matters)'>,
      help: mode[
         infix: 'string substitution, s%=t x replaces s with t in x',
         prefix: 'string substitution, (%=t s) x replaces s with t in x',
         postfix: 'string substitution, (s%= t) x replaces s with t in x',
         solo: 'string substitution, (%= (s,t)) x replaces s with t in x'],
      meanings: ~&rlH(
         ~&litZB?(
            ~&ritZB?(~&bh; ("a","b"). * "a"?=/"b"! ~&,~&lhPrX; ("a","b"). *= "a"?=/"b"! ~&iNC),
            ~&NiX; //~&; //+ %ssWXsXCRk ~&ar^?\~&alrlPlxPrrPQ ~&alrl?\~&alrr3falNlxPrrPXXPrXPRT ~&alrlh3rhPE?(
               ~&falrlh2lCrlt2rrPXXPrtPXPR,
               ~&all?/~&allz3falNlxPrlPTrrPXXPllyx3rTXPRC ~&arh2falrtPXPRC)),
         "sub". mode[
            infix: ~&mSx; -++-; ~&?=(! "sub","h". "h"+ "sub"),
            prefix: ~&mSx; -++-; ~&?=(! "t". "sub"\"t","h". "t". "h"+ "sub"\"t"),
            postfix: ~&mSx; -++-; ~&?=(! "s". "sub"/"s","h". "s". "h"+ "sub"/"s"),
            solo: ~&mSx; -++-; ~&?=(! "sub","h". "h"+ "sub")])],
   operator[
      mnemonic: '=]',
      dyadic: mode[postfix: &],
      optimizers: mode[prefix: <&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      help: mode[
         infix: 'startswith combinator, (f=]x) y is true if x is a prefix of (f y)',
         postfix: 'startswith combinator, (f=] x) y is true if x is a prefix of (f y)',
         prefix: 'startswith combinator, (=]x) y is true when x is a prefix of y',
         solo: 'startswith combinator, (=] x) y is true if x is a prefix of y'],
      meanings: mode[
         infix: ("f","x"). (~&a^?\&!! ?^(~&i&&+ ~&h==+ ~&ah,~&\0!+ ~&t;+ ~&fatPR))("x")+ "f",
         postfix: "f". "x". (~&a^?\&!! ?^(~&i&&+ ~&h==+ ~&ah,~&\0!+ ~&t;+ ~&fatPR))"x"+ "f",
         prefix: ~&a^?\&!! ?^(~&i&&+ ~&h==+ ~&ah,~&\0!+ ~&t;+ ~&fatPR),
         solo: ~&a^?\&!! ?^(~&i&&+ ~&h==+ ~&ah,~&\0!+ ~&t;+ ~&fatPR)]],
   operator[
      mnemonic: '[=',
      dyadic: mode[postfix: &],
      optimizers: mode[prefix: <&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      help: mode[
         infix: 'prefix combinator, (f[=x) y is true when (f y) is a prefix of x',
         postfix: 'prefix combinator, (f[= x) y is true when (f y) is a prefix of x',
         prefix: 'prefix combinator, ([=x) y is true when y is a prefix of x',
         solo: 'prefix predicate, [= (x,y) is true when x is a prefix of y'],
      meanings: mode[
         infix: ("f","x"). "f"; (~&alZ^!-&~&ar,==+~&abh,~&fabt2R&-)\"x",
         postfix: "f". "x". "f"; (~&alZ^!-&~&ar,==+~&abh,~&fabt2R&-)\"x",
         prefix: \/(~&alZ^!-&~&ar,==+~&abh,~&fabt2R&-),
         solo: ~&alZ^!-&~&ar,==+~&abh,~&fabt2R&-]],
   operator[
      mnemonic: '-$',
      peer: '*',
      dyadic: mode[prefix: &,postfix: &,solo: &],
      options: <'-': 0,'=': 0>,
      opthelp: <'- for fast code, = for small code'>,
      # optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      help: mode[
         prefix: 'unzipped partial reification, (-$<yi..> <xi..>) xn = yn',
         postfix: 'unzipped partial reification, (<xi..>-$ <yi..>) xn = yn',
         infix: 'unzipped partial reification, <xi..>-$<yi..> xn = yn',
         solo: 'unzipped partial reification, (-$ (<xi..>,<yi..>)) xn = yn'],
      meanings: ("o". mode[prefix: "o"; "f". "y". "f"\"y",postfix: "o"; "f". "x". "f"/"x",infix: "o",solo: "o"]) ~&?(
         ~&t?/<'ambiguous -$ suffix'>!% @p+ `=?=hnh/small_map! fast_map!,
         @p+ easy_map!)],
  operator[
      mnemonic: '-:',
      peer: '*',
      dyadic: mode[prefix: &,postfix: &],
      options: <'-': 0,'=': 0>,
      opthelp: <'- for fast code, = for small code'>,
      # optimizers: mode[prefix: <&,&>,infix: <&>,postfix: <&,&>,solo: <0,&>],
      preprocessors: mode[infix: ~lexeme=='(spacer)'?vthd/~& &vth:= ~&V/token[lexeme: '(spacer)',semantics: ~&h!]+ ~&vt],
      help: mode[
         prefix: 'total reification combinator, (-:d <(xi,yi)..>) xn = yn, else d',
         postfix: 'total reification combinator, (<(xi,yi)..>-: d) xn = yn, else d',
         infix: 'total reification combinator, <(xi,yi)..>-:d xn = yn, else d',
         solo: 'partial reification combinator, (-: <(xi,yi)..>) xn = yn'],
      meanings: ~&H(
         ("p","o"). mode[
            prefix: ("f". "d". "f"\"d")+ ?^^/"p" ^|\~&+ "o",
            postfix: ("f". "m". "f"/"m")+ ?^^/"p" ^|\~&+ "o",
            infix: ?^^/"p" ^|\~&+ "o",
            solo: "o"],
         ~&/(@llS+ ':'?=ihnPB\lsm! ! \/-=) ~&?(
            ~&t?/<'ambiguous -: suffix'>!% `=?=hnh/small_map! fast_map!,
            easy_map!))]>

stratification = # pattern recognition and classification making use of pointers or pseudo pointers

(^T/~&l ~&r&& ~&rizyCp; * &l.peer:=l ~&r.mnemonic) !=(peer) <
   operator[
      mnemonic: '$^',
      peer: '*',
      optimizers: mode[prefix: <&>,infix: <&>,postfix: <&>,solo: <0,&>],
      options: pnodes,
      opthelp: <'a pointer expression specifies a postprocessor'>,
      preprocessors: mode[
         prefix: ^V/(~&d+ &d.preprocessor:= 0!) propagation*+ ~&v,
         infix: ^V/(~&d+ &d.preprocessor:= 0!) :^/~&vh propagation*+ ~&vt],
      help: mode[
         infix: 'p$^f finds the maximum element w.r.t p of field f',
         postfix: 'p$^ finds the maximum element w.r.t predicate p',
         prefix: '$^f finds the longest length element by field f',
         solo: '$^ p finds the maximum element w.r.t predicate p'],
      meanings: mode[
         infix: ~&lNlXBrY+percolation+~&mS; ~&?=(
            ! &?=r/maximum+~&l ("p","f"). maximum "p"+ ~&l?(~&NlNXNlXXX,~~+ ~&r) "f",
            "d". "d"++ &?=r/maximum+~&l ("p","f"). maximum "p"+ ~&l?(~&NlNXNlXXX,~~+ ~&r) "f"),
         prefix: ~&lNlXBrY+percolation+~&mS; ~&?=(
            ! "f". maximum leql+ ~&l?(~&NlNXNlXXX,~~+ ~&r) "f",
            "d". "d"++ "f". maximum leql+ ~&l?(~&NlNXNlXXX,~~+ ~&r) "f"),
         postfix: ~&lNlXBrY+percolation+~&mS; ~&?=(maximum!,"d". "d"++ maximum),
         solo: ~&lNlXBrY+percolation+~&mS; ~&?=(maximum!,"d". "d"++ maximum)]],
   operator[
      mnemonic: '$-',
      peer: '*',
      optimizers: mode[prefix: <>,infix: <>,postfix: <>,solo: <>],
      options: pnodes,
      opthelp: <'a pointer expression specifies a postprocessor'>,
      preprocessors: mode[
         prefix: ^V/(~&d+ &d.preprocessor:= 0!) propagation*+ ~&v,
         infix: ^V/(~&d+ &d.preprocessor:= 0!) :^/~&vh propagation*+ ~&vt],
      help: mode[
         infix: 'p$-f finds the minimum element w.r.t p of field f',
         postfix: 'p$- finds the minimum element w.r.t predicate p',
         prefix: '$-f finds the shortest length element by field f',
         solo: '$- p finds the minimum element w.r.t predicate p'],
      meanings: mode[
         infix: ~&lNlXBrY+percolation+~&mS; ~&?=(
            ! &?=r/minimum+~&l ("p","f"). minimum "p"+ ~&l?(~&NlNXNlXXX,~~+ ~&r) "f",
            "d". "d"++ &?=r/minimum+~&l ("p","f"). minimum "p"+ ~&l?(~&NlNXNlXXX,~~+ ~&r) "f"),
         prefix: ~&lNlXBrY+percolation+~&mS; ~&?=(
            ! "f". minimum leql+ ~&l?(~&NlNXNlXXX,~~+ ~&r) "f",
            "d". "d"++ "f". minimum leql+ ~&l?(~&NlNXNlXXX,~~+ ~&r) "f"),
         postfix: ~&lNlXBrY+percolation+~&mS; ~&?=(minimum!,"d". "d"++ minimum),
         solo: ~&lNlXBrY+percolation+~&mS; ~&?=(minimum!,"d". "d"++ minimum)]],
   operator[
      mnemonic: '-<',
      optimizers: mode[prefix: <>,infix: <>,postfix: <>,solo: <>],
      options: pnodes,
      opthelp: <'a pointer expression specifies a postprocessor'>,
      preprocessors: mode[
         prefix: ^V/(~&d+ &d.preprocessor:= 0!) propagation*+ ~&v,
         infix: ^V/(~&d+ &d.preprocessor:= 0!) :^/~&vh propagation*+ ~&vt],
      help: mode[
         infix: 'p-<f sorts a list using p to compare field f in each item',
         postfix: 'p-< sorts a list using p to compare items',
         prefix: '-<f lexically sorts a list by field f',
         solo: '-< p sorts a list using p to compare items'],
      meanings: mode[
         infix: ~&lNlXBrY+percolation+~&mS; ~&?=(
            ! sort+ &?=rl/~&l +^/~&l ~&r; ~&l?/~&NlNXNlXXX ~~+ ~&r,
            "d". "d"++ sort+ &?=rl/~&l +^/~&l ~&r; ~&l?/~&NlNXNlXXX ~~+ ~&r),
         prefix: ~&lNlXBrY+percolation+~&mS; ~&?=(
            ! sort+ &?=l/lleq! lleq++ ~&l?/~&NlNXNlXXX ~~+ ~&r,
            "d". "d"++ sort+ &?=l/lleq! lleq++ ~&l?/~&NlNXNlXXX ~~+ ~&r),
         postfix: ~&lNlXBrY+percolation+~&mS; ~&?=(! sort,"d". "d"++ sort),
         solo: ~&lNlXBrY+percolation+~&mS; ~&?=(! sort,"d". "d"++ sort)]],
   operator[
      mnemonic: '*|',
      optimizers: mode[prefix: <&>,infix: <&>,postfix: <&>,solo: <0,&>],
      preprocessors: mode[
         prefix: ^V/(~&d+ &d.preprocessor:= 0!) propagation*+ ~&v,
         infix: ^V/(~&d+ &d.preprocessor:= 0!) :^/~&vh propagation*+ ~&vt],
      help: mode[
         postfix: 'distributing bipartition, p*| (x,y) is equivalent to ~&brS p!= x-*y',
         infix: 'distributing bipartition, p*|f (x,y) is equivalent to ~&brS p+~f!= x-*y',
         prefix: 'distributing bipartition, *|f (x,y) is equivalent to ~&brS ==+~f!= x-*y',
         solo: 'distributing bipartition, (*| p) (x,y) is equivalent to ~&brS p!= x-*y'],
      meanings: mode[
         postfix: ~&lNlXBrY+percolation@mS; ~&?=(! dipart,"d". "d"++ dipart),
         infix: -+
            ~&?=(! dipart+ +^/~&l ~&rlNlXBrY,"d". "d"++ dipart+ +^/~&l ~&rlNlXBrY),
            ~&lNlXBrY+ percolation@mS+-,
         prefix: -+
            ~&?=(! dipart+ compare++ ~&lNlXBrY,"d". "d"++ dipart+ compare++ ~&lNlXBrY),
            ~&lNlXBrY+ percolation@mS+-, 
         solo: ~&lNlXBrY+percolation@mS; ~&?=(! dipart,"d". "d"++ dipart)],
      opthelp: <'a pointer expression specifies a postprocessor'>,
      options: pnodes],
   operator[
      mnemonic: '~|',
      optimizers: mode[prefix: <&>,infix: <&>,postfix: <&>,solo: <0,&>],
      preprocessors: mode[
         prefix: ^V/(~&d+ &d.preprocessor:= 0!) propagation*+ ~&v,
         infix: ^V/(~&d+ &d.preprocessor:= 0!) :^/~&vh propagation*+ ~&vt],
      help: mode[
         postfix: 'distributing filter, p~| (x,y) is equivalent to ~&rS p*~ x-*y',
         prefix: 'distributing filter, ~|f (x,y) is equivalent to ~&rS (==+~f)*~ x-*y',
         infix: 'distributing filter, p~|f (x,y) is equivalent to ~&rS (p+~f)*~ x-*y',
         solo: 'distributing filter, (~| p) (x,y) is equivalent to ~&rS p*~ x-*y'],
      meanings: mode[
         postfix: ~&lNlXBrY+percolation+~&mS; ~&?=(! -*;+ ~&r*++ *~,"d". "d"++ -*;+ ~&r*++ *~),
         infix: -+
            ~&?=(! -*;+ ~&r*++ *~+ +^/~&l ~&rlNlXBrY,"d". "d"++ -*;+ ~&r*++ *~+ +^/~&l ~&rlNlXBrY),
            ~&lNlXBrY+ percolation+ ~&mS+-,
         prefix: -+
            ~&?=(! -*;+ ~&r*++ *~+ compare++ ~&lNlXBrY,"d". "d"++ -*;+ ~&r*++ *~+ compare++ ~&lNlXBrY),
            ~&lNlXBrY+ percolation+ ~&mS+-,
         solo: ~&lNlXBrY+percolation+~&mS; ~&?=(! -*;+ ~&r*++ *~,"d". "d"++ -*;+ ~&r*++ *~)],
      opthelp: <'a pointer expression specifies a postprocessor'>,
      options: pnodes],
   operator[
      mnemonic: '|=',
      optimizers: mode[prefix: <&>,infix: <&>,postfix: <&>,solo: <0,&>],
      options: <'*': 0,'=': 0>-- pnodes,
      opthelp: <
         '* partitions by the transitive closure of the relation,',
         '= partitions by the symmetric closure, and any pointer',
         'constant in a suffix is a postprocessor'>,
      excluder: ~&~<'-.'-~; ~&r&& subset\'_abcdefghijklmnopqrstuvwxyz'+ ~&l,
      help: mode[
         infix: 'p|=f partitions a list or set by the equivalence p+ fan field f',
         prefix: '|=f partitions a list or set by the equivalence compare+ fan field f',
         postfix: 'p|= partitions a list or set into equivalence classes w.r.t. p',
         solo: '(|= p) partitions a list or set into equivalence classes w.r.t. p'],
      preprocessors: mode[
         prefix: ^V/(~&d+ &d.preprocessor:= 0!) propagation*+ ~&v,
         infix: ^V/(~&d+ &d.preprocessor:= 0!) :^/~&vh propagation*+ ~&vt],
      meanings: mode[
         infix: -+
            case<.-=/'*'+ ~&rnS,~&l==~&,-=/'='+ ~&rnS>\0! {
               <0,0,0>: ~&l; "d". &?=rl/(("p","f"). "d"+ partition "p") ~&rl?(
                  ~&lrlPX; ("p","f"). "d"+ partition "p"+ fan field "f",
                  ~&lrrPX; ("p","f"). "d"+ partition "p"+ fan "f"),
               <0,0,&>: ~&l; "d". &?=rl/(("p","f"). "d"+ partition ~&irlXX; either "p") ~&rl?(
                  ~&lrlPX; ("p","f"). "d"+ partition ~&irlXX; either "p"+ fan field "f",
                  ~&lrrPX; ("p","f"). "d"+ partition ~&irlXX; either "p"+ fan "f"),
               <0,&,0>: ! &?=rl/partition+~&l ~&rl?(
                  ~&lrlPX; ("p","f"). partition "p"+ fan field "f",
                  ~&lrrPX; ("p","f"). partition "p"+ fan "f"),
               <0,&,&>: ! &?=rl/(partition+ ~&irlXX;+ either+ ~&l) ~&rl?(
                  ~&lrlPX; ("p","f"). partition ~&irlXX; either "p"+ fan field "f",
                  ~&lrrPX; ("p","f"). partition ~&irlXX; either "p"+ fan "f"),
               <&,0,0>: ~&l; "d". &?=rl/(("p","f"). "d"+ concom "p") ~&rl?(
                  ~&lrlPX; ("p","f"). "d"+ concom "p"+ fan field "f",
                  ~&lrrPX; ("p","f"). "d"+ concom "p"+ fan "f"),
               <&,0,&>: ~&l; "d". &?=rl/(("p","f"). "d"+ concom ~&irlXX; either "p") ~&rl?(
                  ~&lrlPX; ("p","f"). "d"+ concom ~&irlXX; either "p"+ fan field "f",
                  ~&lrrPX; ("p","f"). "d"+ concom ~&irlXX; either "p"+ fan "f"),
               <&,&,0>: ! &?=rl/concom+~&l ~&rl?(
                  ~&lrlPX; ("p","f"). concom "p"+ fan field "f",
                  ~&lrrPX; ("p","f"). concom "p"+ fan "f"),
               <&,&,&>: ! &?=rl/(concom+ ~&irlXX;+ either+ ~&l) ~&rl?(
                  ~&lrlPX; ("p","f"). concom ~&irlXX; either "p"+ fan field "f",
                  ~&lrrPX; ("p","f"). concom ~&irlXX; either "p"+ fan "f")},
            !=&m; ^/~&lNlXBrY+percolation+~&lmS ~&r+-,
         prefix: (~&lNlXBrY+ percolation+ ~&mS+ ~&m*~); ~&?=(
            ! &?=l/(! partition compare) ~&l?(
               ~&l; "f". partition compare+ fan field "f",
               ~&r; "f". partition compare+ fan "f"),
            "d". &?=l/(! "d"+ partition compare) ~&l?(
               ~&l; "f". "d"+ partition compare+ fan field "f",
               ~&r; "f". "d"+ partition compare+ fan "f")),
         (postfix,solo): ~&iiX -+
            -=/'*'?rnS(
               -=/'='?rnS(
                  ~&?=l/(! concom+ ~&irlXX;+ either) ~&l; "d". "d"++ concom+ ~&irlXX;+ either,
                  ~&?=l/concom! ~&l; "d". "d"++ concom),
               -=/'='?rnS(
                  ~&?=l/(! partition+ ~&irlXX;+ either) ~&l; "d". "d"++ partition+ ~&irlXX;+ either,
                  ~&?=l/partition! ~&l; "d". "d"++ partition)),
            !=&m; ^/~&lNlXBrY+percolation+~&lmS ~&r+-]]>

default_operators = 

~&H(
   * -+
      ~optimizers?\~& optimizers.(ogl-prefix,infix,postfix,solo,aggregate):= -+
         ~&=>+ * * ~&?/optimization! ~&,
         ~optimizers; <.~ogl-prefix,~infix,~postfix,~solo,~aggregate>+-,
      meanings.(ogl-prefix,infix,postfix,solo,aggregate):= -+
         ~&=>+ optimization*,
         ~meanings; <.~ogl-prefix,~infix,~postfix,~solo,~aggregate>+-+-,
   ~&L <
      aggregation,
      manipulation,
      consternation,
      deconstruction,
      predication,
      serialization,
      tight_paralation,
      loose_paralation,
      interrogation,
      recursion,
      liberation,
      classification,
      stratification>)
