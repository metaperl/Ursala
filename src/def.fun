
#import std
#import nat
#import opt
#import psp
#import ogl
#import ops
#import apt
#import eto
#import dir
#import lag
#import fen
#import ext
#import pru
#import for
#import mul

#comment -[
This module contains the tables of the default formulators and help topics
used by the compiler as defined in for.fun

Copyright (C) 2007-2010 Dennis Furey]-

profile = +^(-=/'trace'?\~&l! ! guard^|/~& ^C\~&+ !,-=/'profile'?\~&! ! ^\~&r std-profile) __switches

#library+

spell = # rewrites a string to make it a valid identifier; used on file names

~&l+ ==`_~-+ ~&r+ ==`_-~+ ~&hS+ (rlc both ==`_)+ *= -:~&iNC ~&p/'0123456789().,-;@% ' (:/`_+ --'_')* -- sep` ~~ (
   'zero one two three four five six seven eight nine',
   'paren thesis dot comma dash semi at percent space')

word_wrap = # takes a number to a function reformatting a list of strings to have at most n columns

-|~&,!1|-; "n". -+
   ~&NiX; ~&F+ ~&ar^& ^(~&,~=` -~+ ~&ar); length=="n"?rl/~&NrlPlfPNrritB2XRCC -+nleq/"n",length+-?rl(
      :^(take^\~&rl difference/"n"+ ~&lal,^lNrXR/~&lf ` ?=ihB(~&t,~&)^T\~&rr skip^\~&rl difference/"n"+ ~&lal),
      -+nleq/"n",sum^/~&lal length+~&rlitB+-?/~&NlfNarPXRPC -+
         ~&r?\~&lNC ~&rh?\~&lrtPC %ssLXMk; :^\~&rt ^T/~&l :/` + ~&rh,
         ^/~&rl ^R/~&lf ^\~&rritB sum^/~&lal length+~&NrlPC+-),
   mat` ; ~&x+ ~&ihB==` ->~&t+ ~&x+ ~&ihB==` ->~&t+ ~&aitB^?\~&a (` ,` )?=ahthPX/~&fatPR ~&ahPfatPRC+-

--------------------------------------------------- table of help topics -----------------------------------------------------

(# Each function takes (<parameter..>,formulation) to a help text. The code to generate the --help pointers listings is based
on the assumption that escaping pointer constructors, of which K is currently the only example, operate on a finite domain of
consecutive naturals starting from zero, and return an empty value for arguments outside the domain. The display may hang up
or crash if that's not the case. #)

default_help_topics = 

<
   'suffixes': ^(~&l,~opthelp*~+ ~&r.operators); -|~| ~&w+ ~\&l &r.ogl-mnemonic,~&r|-; -+
      //-- ~&lrNCC ^T(~&l,:/` + ~&r)~~ ^(~&,~~ `-!*)/'stem' 'suffixes',
      *= ~&TS+ zipp'     '+ ^(~&iNC+ take/5+ --'     '+ ~ogl-mnemonic,word_wrap74+ ~opthelp)+-,
   'prefix': (||~&r ^rlrTB/~&rhthPNCC [=~|+ ~&lrtt2X)^/(~&lt; -&~&,~&h,--' '+ ~&h&-) -+
      //-- :^(~&,~&iNC+ `-!*) 'prefix operators',
      (* ^T/~&l '  '--+ ~&r)^p\~&rS ~&lS; (* ~&rS+ zipp` )^D\~& leql$^,
      -&~&r,%sI+ ~&r&-*~+ ~(ogl-mnemonic,ogl-help.ogl-prefix)*+ ~&r.operators+-,
   'postfix': (||~&r ^rlrTB/~&rhthPNCC [=~|+ ~&lrtt2X)^/(~&lt; -&~&,~&h,--' '+ ~&h&-) -+
      //-- :^(~&,~&iNC+ `-!*) 'postfix operators',
      (* ^T/~&l '  '--+ ~&r)^p\~&rS ~&lS; (* ~&rS+ zipp` )^D\~& leql$^,
      -&~&r,%sI+ ~&r&-*~+ ~(ogl-mnemonic,ogl-help.ogl-postfix)*+ ~&r.operators+-,
   'infix': (||~&r ^rlrTB/~&rhthPNCC [=~|+ ~&lrtt2X)^/(~&lt; -&~&,~&h,--' '+ ~&h&-) -+
      //-- :^(~&,~&iNC+ `-!*) 'infix operators',
      (* ^T/~&l '  '--+ ~&r)^p\~&rS ~&lS; (* ~&rS+ zipp` )^D\~& leql$^,
      -&~&r,%sI+ ~&r&-*~+ ~(ogl-mnemonic,ogl-help.ogl-infix)*+ ~&r.operators+-,
   'solo': (||~&r ^rlrTB/~&rhthPNCC [=~|+ ~&lrtt2X)^/(~&lt; -&~&,~&h,--' '+ ~&h&-) -+
      //-- :^(~&,~&iNC+ `-!*) 'solo operators',
      (* ^T/~&l '  '--+ ~&r)^p\~&rS ~&lS; (* ~&rS+ zipp` )^D\~& leql$^,
      -&~&r,%sI+ ~&r&-*~+ ~(ogl-mnemonic,ogl-help.ogl-solo)*+ ~&r.operators+-,
   'libraries': -+
      ~&?\<'no library functions found'>! |=&l; -<&hl; -+
         (*= ^HlrTS\~&lNCrX zipp+ ` !*+ ~&l)^T(
            ~&rhthPNCC; \/~&plrNCXS ~&H\'functions' ^lrNCC/~& `-!*,
            ^p/~&rtt ^H\~&l *+ -<&;+ word_wrap+ difference/79+ length+ ~&rh),
         ^/~&rSS ~&hlPS;  --' '*+ take/*40+ ~&rSS+ zipp` ^*D(leql$^,~&)+ (~&H\'library' ^lrNCC/~& `-!*)--+-,
      ~&litB; ^(~&ihB,~&itBthPB); ||have('*','*') -+
         -*; *= ^D/~&rl ~&l?\~&rr ~&lrrPX; ==~||| [=~|,
         ^/~&r (~&lrlPE~||| ~| [=+ ~&lrlPX)^/~&l ~&hlPrSXS+ |=&l+ have/'*' '*'+-+-,
   'outfix': -+
      ||~&r ^rlrTB/~&rhthPNCC [=~|+ ~&lrtt2X,
      ^/(~&lt; -&~&,~&h,~&h; --'..'+ ~&itB?/~& :/` &-) -+
         //-- :^(~&,~&iNC+ `-!*) 'outfix operators',
         (* ^T/~&l '  '--+ ~&r)^p\~&rS ~&lS; (* ~&rS+ zipp` )^D\~& leql$^,
         * ^\~&r ~&l; ^T/(~&l; ~&itB?/~& :/` ) '..'--+ ~&r,
         -&~&r,%sI+ ~&r&-*~+ ~((ogl-mnemonic,ogl-match),ogl-help.ogl-aggregate)*+ ~&r.operators+-+-,
   'options': -+
      ||~&r ^rlrTB/~&rhthPNCC [=~|+ ~&lrtt2X,
      ^/(~&lt; -&~&,~&h,'--'--+ ~&h&-) ~&r.formulators; -+
         (* ^T/~&l :/` + ~&r)^p\~&rS ~&lS; (* ~&rS+ zipp` )^D\~& leql$^,
         //-- ~&lrNCC ~&bbI ^(~&,`-!*)~~ ('option','effect'),
         -<&l+ -+
            //: ~&/'--phase ...' 'disgorge the compiler''s run-time data structures',
            * ^(^T('--'--+ ~for-mnemonic,-!~filial,~extras,~requisites!-&& ' ...'!),~help)+-+-+-,
   'directives': -+
      ||~&r ^rlrTB/~&rhthPNCC (:/`# )*+ [=~|+ ~&lrtttS3X,
      ^/~&ltihB ~&r.directives; -+
         (* ^T/~&l :/` + ~&r)^p\~&rS ~&lS; (* ~&rS+ zipp` )^D\~& leql$^,
         //-- ~&lrNCC ~&bbI ^(~&,`-!*)~~ ('directive','effect'),
         -<&l+ * ^(^T(:/`#+ ~dir-mnemonic,~dir-parameterized.&Z&& '+'!),~dir-help)+-+-,
   'types': -+
      ||(mat''+ ~&r) -*; (~&itZB&& ~&h; ^T/~&rhthPNCC ~&lrtt2X; ~| [=)+ *~ ~&lrtt2D; any [=,
      ^(~&l,~&rS+ ||~&r ~| ~&lrlPE)+ ^/~&ltihB ~&r.operators; -+
         |=(tag-arity); nleq-<&h.tag-arity; * ^/(~&h+ %nP+ ~&h.tag-arity) ^T(
            :^(~&,~&iNC+ `-!*)+ 'type stack operators of arity '--+ ~&h+ %nP+ ~&h.tag-arity,
            -+* ^T/~&l '  '--+ ~&r,*~ not ~&l-= ~&iNCS '0123456789',-<&l+ * ~/tag-mnemonic tag-help+-),
         ~&mS+ ~&imBF+ ~&s+ ~ogl-options*=+ *~ ~ogl-options; //~&c tco-type_constructors+-+-,
   'pointers': -+
      ||(mat''+ ~&r) -*; (~&itZB&& ~&h; ^T/~&rhthPNCC ~&lrtt2X; ~| [=+ ~&lrttt3X)+ *~ ~&lrtt2D; any [=+ ~&lrttt3X,
      ^(~&l,~&rS+ ||~&r ~| ~&lrlPE)+ ^/~&ltihB ~&r.operators; -+
         |=(psp-arity); nleq-<&h.psp-arity; * ^/(~&h+ %nP+ ~&h.psp-arity) ^T(
            :^(~&,~&iNC+ `-!*)+ -+
               'pointer stack operators of arity '--+ --'  (*pseudo-pointer)',
               ~&h+ %nP+ ~&h.psp-arity+-,
            (* ^|T/~& '  '--)+ -+
               *~ not ~&l-= ('   '--+ --'  ')*iNCS '0123456789',
               psort<leql@bl,lleq@bl>; ^p\~&rS pad` @lS,
               * ^\~psp-help ^T\~psp-mnemonic ~psp-pval?/'   '! ' * '!+-),
         ~psp-help*~+ -+
            ~psp-escaping!=; ^T/~&T *=l (* &r.psp-mnemonic:=r ^|T/~& ~psp-mnemonic)^D/~psp-mnemonic -+
               @NiX ^=lx ^\~&r ^T\~&l ^HiiNCB/~&r length@l,
               (~&r&& &r.psp-mnemonic:=r ~&l)++ ^/(~&h+ %nP)+ ~psp-escaping+-,
            ~&smS+ (~&i&& ~&m; _pnode%I&& ~psp-mnemonic; ~&i&& %sI)*~+ ~ogl-options*=+-+-+->

--------------------------------------------------- tables of formulators ----------------------------------------------------
#library-

showing_formulators =

^A(~for-mnemonic,~&)* (help:= 'show '--+ ~help)* <
   formulator[
      for-mnemonic: 'version',
      formula: &r.(source_filter,target_filter):=r ! ~&/<>! ! ~&iNC file[
         contents: <'fun version '--version_number,''>],
      help: 'the main compiler version number'],
   formulator[
      for-mnemonic: 'warranty',
      formula: &r.(source_filter,target_filter):=r ! ~&/<>! ! ~&iNC file[
         contents: --<''> <
            'fun version '--version_number,
            'Copyright (C) 2007-2010 Dennis Furey. fun comes with NO WARRANTY, to the extent',
            'permitted by law. You may redistribute copies of fun under the terms of the',
            'GNU General Public License. For more information about these matters, see the',
            'files named COPYING.'>],
      help: 'a reminder about the lack of a warranty']>

customizing_formulators =

^A(~for-mnemonic,~&)* :^(~&h,~&t; :^/~&h ~&t; * help:= 'load '--+ --' from a file'+ ~help) <
   formulator[
      for-mnemonic: 'alias',
      formula: ~&llihB?\<' non-empty command name required'>!% &r.command_name:=r ~&llh,
      extras: <'command-name'>,
      help: 'use a specified command name in error messages'],
   formulator[
      for-mnemonic: 'switches',
      formula: &r.token_filter:=r +^\-|~&r.token_filter,! ~&|- ~&ll; "p". * * * ?(
         ~lexeme== '__switches',
         ~&\~& semantics:= !+ !+ "p"--+ ~&iNH+ ~&iNH+ -|~semantics,! ! <>|-),
      extras: <'switch-names'>,
      help: 'set application-specific compile-time switches'],
   formulator[
      for-mnemonic: 'precedence',
      filial: &,
      formula: ~&lr?\<' operator precedence configuration file required'>!% -+
         (~&lr.preamble&& %sWLWWI+ ~&lr.contents)?(
            &r.precedence:=r -+
               ~&ll?/~&lr (~~ ~&Ts~~+ ~&bbI)^bbI/~&lr ~&r.precedence,
               ^\~&r ^(~&ll; ~&ihB&& ~&h[='only',~&lr.contents)+-,
            % ~&iNC+ ' bad operator precedence configuration file format'--+ ~&lr.path.&ihB&& ' in '--+ ~&lr.path.&h),
         (~&lr.contents; &&extractable not %sWLWWI)?\~& &lr.contents:= extract+ ~&lr.contents+-,
      extras: <'only'>,
      help: 'operator precedence rules'],
   formulator[
      for-mnemonic: 'help-topics',
      filial: &,
      formula: ~&lr?\<' help topics configuration file required'>!% -+
         -&~preamble,%fmI+ ~contents&-?lr(
            &r.help_topics:=r -+
               ~&ll?/~&lr ^T/~&lr (gdif ==+ ~&bn)+ ~/&r.help_topics &lr,
               ^|\~& ^|\~contents ~&ihB&& ~&h[='only'+-,
            % ~&iNC+ ' bad help topics configuration file format'--+ ~&lr.path.&ihB&& ' in '--+ ~&lr.path.&h),
         (~&lr.contents; &&extractable not %fmI)?\~& &lr.contents:= extract+ ~&lr.contents+-,
      extras: <'only'>,
      help: 'interactive help topics'],
   formulator[
      for-mnemonic: 'operators',
      filial: &,
      formula: ~&lr?\<' operator configuration file required'>!% -+
         (~&lr.preamble&& ogl-_operator%LI+ ~&lr.contents)?(
            &r.operators:=r -+
               ~&ll?/~&lr ^T(
                  -*+~(&lr,&r.operators); * ||~&r ~&rlX; ~&ihB+ ~| ==+ ~&b.ogl-mnemonic,
                  (gdif ==+ ~&b.ogl-mnemonic)+ ~\&r.operators &lr),
               ^\~&r ^(~&ll; ~&ihB&& ~&h[='only',~&lr.contents)+-,
            % ~&iNC+ ' bad operator configuration file format'--+ ~&lr.path.&ihB&& ' in '--+ ~&lr.path.&h),
         (~&lr.contents; &&extractable not ogl-_operator%LI)?\~& &lr.contents:= extract+ ~&lr.contents+-,
      extras: <'only'>,
      help: 'operator semantics'],
   formulator[
      for-mnemonic: 'formulators',
      filial: &,
      formula: ~&lr?\<' formulator configuration file required'>!% -+
         (~&lr.preamble&& _formulator%LI+ ~&lr.contents)?(
            &r.formulators:=r -+
               ~&ll?/~&lr ^T/~&lr (gdif ==+ ~&b.for-mnemonic)+ ~/&r.formulators &lr,
               ^\~&r ^(~&ll; ~&ihB&& ~&h[='only',~&lr.contents)+-,
            % ~&iNC+ ' bad formulator configuration file format'--+ ~&lr.path.&ihB&& ' in '--+ ~&lr.path.&h),
         (~&lr.contents; &&extractable not _formulator%LI)?\~& &lr.contents:= extract+ ~&lr.contents+-,
      extras: <'only'>,
      help: 'command line semantics'],
   formulator[
      for-mnemonic: 'directives',
      filial: &,
      formula: ~&lr?\<' directive configuration file required'>!% -+
         (~&lr.preamble&& dir-_directive%LI+ ~&lr.contents)?(
            &r.(formulators,directives):=r -+
               ^\~&r (^T/~&r gdif ==+ ~&b.for-mnemonic)^/~&l directive_based_formulators+ ~&r,
               ^/~&r.formulators -+
                  ~&ll?/~&lr ^T/~&lr (gdif ==+ ~&b.for-mnemonic)+ ~/&r.directives &lr,
                  ^\~&r ^(~&ll; ~&ihB&& ~&h[='only',~&lr.contents)+-+-,
            % ~&iNC+ ' bad directive configuration file format'--+ ~&lr.path.&ihB&& ' in '--+ ~&lr.path.&h),
         (~&lr.contents; &&extractable not dir-_directive%LI)?\~& &lr.contents:= extract+ ~&lr.contents+-,
      extras: <'only'>,
      help: 'directive semantics'],
   formulator[
      for-mnemonic: 'types',
      filial: &,
      formula: ~&lr?\<' type configuration file required'>!% -+
         (~&lr.preamble&& tag-_type_constructor%LI+ ~&lr.contents)?(
            &r.operators:=r -+
               * ?(
                  ~&r.ogl-options; (~&m&& ~&nihB-= letters--digits)*~; ~&i&& tag-_type_constructor%mI,
                  ~&\~&r &r.ogl-options:=r ~&ll?(
                     ^lrrPT/~&lr ~&r.ogl-options; != ~&m&& ~&nihB-= letters--digits,
                     ^T/~&lr gdif~&lnPrnPE+ ~/&r.ogl-options &lr)),
               ^D\~&r.operators ^(~&ll; ~&ihB&& ~&h[='only',~&lr.contents; * ^A/~tag-mnemonic ~&)+-,
            % ~&iNC+ ' bad type configuration file format'--+ ~&lr.path.&ihB&& ' in '--+ ~&lr.path.&h),
         (~&lr.contents; &&extractable not tag-_type_constructor%LI)?\~& &lr.contents:= extract+ ~&lr.contents+-,
      extras: <'only'>,
      help: 'type expression semantics'],
   formulator[
      for-mnemonic: 'pointers',
      filial: &,
      formula: ~&lr?\<' pointer configuration file required'>!% -+
         (~&lr.preamble&& psp-_pnode%LI+ ~&lr.contents)?(
            &r.operators:=r -+
               * ?(
                  ~&r.ogl-options; (~&m&& ~&nihB-= letters--digits)*~; ~&i&& psp-_pnode%mI,
                  ~&\~&r &r.ogl-options:=r ~&ll?(
                     ^lrrPT/~&lr ~&r.ogl-options; != ~&m&& ~&nihB-= letters--digits,
                     ^T/~&lr gdif~&lnPrnPE+ ~/&r.ogl-options &lr)),
               ^D\~&r.operators ^(~&ll; ~&ihB&& ~&h[='only',~&lr.contents; * ^A/~psp-mnemonic ~&)+-,
            % ~&iNC+ ' bad pointer configuration file format'--+ ~&lr.path.&ihB&& ' in '--+ ~&lr.path.&h),
         (~&lr.contents; &&extractable not psp-_pnode%LI)?\~& &lr.contents:= extract+ ~&lr.contents+-,
      extras: <'only'>,
      help: 'pointer expression semantics']>

output_file_formulators =

^A(~for-mnemonic,~&)* <
   formulator[
      for-mnemonic: 'gpl',
      formula: &r.target_filter:=r +^\-|~&r.target_filter,! ~&|- -+
         "v".  * ~preamble?\~& preamble:= ~preamble; ?(
            -&~&h=]'!/bin/sh',~&z=]'exec avram',~&yzx=]'\'&-,
            (^T/~&yyNNCT ((* :/` ) gpl "v")--+ ~&yzPzNCC,--<''>+ --((* :/` ) gpl "v")+ ~&iNNCT)),
         ||'3'! ~&llihB+-,
      extras: <'version'>,
      help: 'include GPL notification in executables and libraries'],
   formulator[
      for-mnemonic: 'archive',
      for-favorite: 1,
      formula: &r.target_filter:=r +^\-|~&r.target_filter,! ~&|- *+ ~preamble?\~&+ -+
         //? ~preamble; -&~&h=]'!/bin/sh',~&z=]'exec avram',~&yzx=]'\'&-,
         ^(
            (preamble,contents):=+ -+
               //+ ^\~&rrl ^T/~&lyyNNCT ^T\~&lyzPzNCC ^C(
                  ' self-extracting with nominal granularity '--@h+ %nP@rrr,
                  weight~~rlrlPX; (both ~&iZ!| ~&z&& all -={0,&})?(
                     (#:/' (weights appear to be well defined)'+#) ^|TNC(' compressed from weight '--,' to '--)+ ~~ ~&h+ %nP,
                     %xWP; ^|C\~& ' pre- and/or post-compression weights are indeterminate: '--)),
               ^/~preamble+ ~contents;+ ^/~&+ ^^(self_extracting,!)+ @llihB -&~&,all \/-= '0123456789',%np+ ~&iNC&-+-,
            (preamble,contents):=+ -+
               //+ ^\~&r ^T/~&l -+
                  :\<''>+ ' compressed with granularity '--,
                  ~&r; ~&h+ %nP+ ||weight -&~&,minimum nleq&-+ weight*+ shared_subtrees+-,
               ^/~preamble+ ~contents;+ compress+ ~&llihB; -&~&i,all \/-= '0123456789',%np+ ~&iNC&-+-)+-,
      extras: <'number'>,
      help: 'compress binary output files and executables']>


input_file_formulators =

^A(~for-mnemonic,~&)* <
   formulator[
      for-mnemonic: 'implicit-imports',
      formula: &r.source_filter:=r -|~&r.source_filter,! ~&|-; //+ -+
         * ~&r.preamble?/~&r ~&r+ &r.contents:= --+ ~/&l &r.contents,
         ^D\~& -+* '#import '--+ ~&x+ ~path.&hxtttt,*~ ~preamble&& ~path; ~&i&& std-suffix/'.avm'+ ~&h+-+-,
      help: 'infer #import directives for command line libraries'],
   formulator[
      for-mnemonic: 'data',
      filial: &,
      formula: ~&lr?(
         &r.preformer:=r +^\-|~&r.preformer,! ~&|- \/--+ -+
            //~&lhPNlth2rNNCCVNCCVNC dir-token_forms(default_operators) <default_directives-export>,
            ~&t?\~&h ~&vtPivhPQ+ ~&V/apt-separation,
            //~&VNC ~&h ogl-token_forms <ez_declaration>,
            ~&iNVS+ (location:= &!)*+ ~&lr; <.
               token$[lexeme: spell+ ~path.&ihB,filename: ~path.&ihB],
               token$[lexeme: ~path.&ihB,filename: ~path.&ihB,semantics: !+ !+ ~contents]>+-,
         -&~&ihB,~&h; ~&cZ/'./'&-?ll\<' data file required'>!% % ~&iNC+ ' use ./'--+ --' syntax for file parameters'+ ~&llh),
      help: 'treat an input file as data instead of compiling it'],
   formulator[
      for-mnemonic: 'main',
      formula: &r.source_filter:=r +^\-|~&r.source_filter,! ~&|- -+
         //+ -+
            ^lrNCT(
               ~&ly; * ~preamble?/~& contents:= :/'#export+'+ ~contents,
               ~&rlzPX; ~&r+ &r.contents:= --+ ~/&l &r.contents),
            ^/~& -+* '#import '--+ spell+ ~&x+ ~path.&hxtttt,*~ ~preamble&& ~path; ~&i&& std-suffix/'.avm'+ ~&h+-+-,
         "m". ^T/~& <file[path: <'command-line'>,contents: <'#export+',"m",''>]>!,
         ^H\~&ll -+
            "l". mat`,; (any ~=` )?\<'main expression required'>!% ("l"; -!-=/'=',-=/'::',~&ihB&& ~&hh==`#!-)?/~& 'main= '--,
            ~lexeme**=++ ~&iNC;+ ~&/'command-line';+ ~&r.(operators,directives); ?(
               ==(extra_tabular default_operators,default_directives),
               ~&\fen-lexer ! fen-lexer\default_directives extra_tabular default_operators)+-+-,
      extras: <'expression'>,
      help: 'include the given declaration among those to be compiled']>

diagnostic_formulators = # useful for development and debugging

^A(~for-mnemonic,~&)* <
   formulator[
      for-mnemonic: 'trace',
      formula: ~&r,  # do nothing because it's detected by avram
      help: 'echo dialogs of the interact combinator'],
   formulator[
      for-mnemonic: 'no-warnings',
      formula: &r.target_filter:=r ~&r.target_filter; //+ -+
         ^T/~&l ~&r; (~contents; any ~&i&& not all ==` )*~+ * contents:= ~contents; *~ not =]'warning:',
         != ~path!| ~preamble+-,
      help: 'suppress all warning messages'],
   formulator[
      for-mnemonic: 'depend',
      formula: ^H\~& ~&r.operators; "o". &r.preformer:=r -|~&r.preformer,! ~&|-; //+ -+
         ~&iNC+ ~&iNV+ token$[location: &!,lexeme: '#(pretty printer)'!,semantics: !+ !+ ~&NiX+ ~&iNC],
         file$[contents: --<''>]+ *= ~&a^& ?(
            -&~&ad.lexeme=='#depend-',~&av&-&& ~&avh; -&~&,~&d.lexeme=='(separation)',~&v,~&vh&-,
            ~&\~&favPML ^T/-+~&i&& ~&iNC+ --':',~&ad.filename+- pretty"o"+ ~&avhvh)+-,
      help: 'display data from #depend directives'],
   formulator[
      for-mnemonic: 'no-core-dumps',
      formula: &r.target_filter:=r ~&r.target_filter; //+ -+
         ^T/~&rl ~&l~='0'&& ~&lrrPX; ~&r?(
            &rh.contents:=r ^T(
               ~&rh.contents; ~&izZB?/~&y ~&,
               :\<''>+ 'warning: core dump(s) of size '--+ --' suppressed'+ ~&l),
            ~&iNC+ file$[contents: :\<''>+ 'warning: core dump(s) of size '--+ --' suppressed'+ ~&l]),
         ^(~&h+ %nP+ sum:-0+ weight*+ ~contents*+ ~&l,~path!=+ ~&r)+ != ~preamble&& ~path== <'core'>+-,
      help: 'suppress all core dump files'],
   formulator[
      for-mnemonic: 'parse',
      for-favorite: 1,
      formula: ^H\~& ^(~&llihB,~&r.operators); 'all'?=l(
         ~&r; "o". &r.preformer:=r -|~&r.preformer,! ~&|-; //+ -+
            ~&iNC+ ~&iNV+ token$[location: &!,lexeme: '#(pretty printer)'!,semantics: !+ !+ ~&NiX+ ~&iNC],
            file$[contents: --<''>]+ profile(pretty"o",'pretty printing')+ -+
               ~&i&& ~&vtPivhPQ+ ~&V/apt-separation,
               *~ not *^0 -!~&d.location-={0,&},any~&+ ~&v!-+-+-,
         ("x","o"). &r.preformer:=r -|~&r.preformer,! ~&|-; //+ -+
            ~&iNC+ ~&iNV+ token$[location: &!,lexeme: '#(pretty printer)'!,semantics: !+ !+ ~&NiX+ ~&iNC],
            file$[contents: --<''>+ profile(pretty"o",'pretty printing')+ ~&i&& ~&vtPivhPQ+ ~&V/apt-separation]+ -|
               *= ~&a^& -&~&ad.lexeme-={'=','::'},~&av,~&avt,~&avttZ,~&avh; *^0 ~&vik|| ~&d.lexeme=="x"&-?\~&favPML ~&aNC,
               ~&izNCB+ -+
                  *= ~&a^& -&~&ad.lexeme=='=',~&av,~&avt,~&avttZ&-?\~&favPML ~&aNC,
                  *~ not *^0 !|~&vik ~&d.location-={0,&}+-|-+-),
      extras: <'symbol-name','all'>,
      help: 'parse and display code in fully parenthesized form'],
   formulator[
      for-mnemonic: 'decompile',
      for-favorite: 1,
      formula: ^H\~& ~&llihB; "x". &r.(target_filter,preformer):=r -+
         //~& *~ not ~path!| ~preamble,
         -|~&r.preformer,! ~&|-; "p". "p"; ?(
            any ~&/"x"; ~&ar^& -&~&ard.lexeme-={'=','::'},~&arv,~&arvh,~&arvhd.lexeme=="x"&-!| ~&k+ ~&falrvPDPM,
            * ~&/"x"; ~&ar^& ?(
               -&~&ard.lexeme-={'=','::'},~&arv,~&arvh,^E/~&al ~&arvhd.lexeme&-,
               ~&\~&ard2falrvPDPMV ~&ar; -+
                  //~&lhPNlth2rNNCCVNCCV dir-token_forms(default_operators) <default_directives-output>,
                  ~&vtPivhPQ+ ~&V/apt-separation,
                  ~&iNC; //: ~&V\<> token[
                     location: &,
                     lexeme: '(decompiler)',
                     semantics: ! ! ~&iNC+ file$[
                        contents: ~&i&& ~&z; -+
                           :^\~&mt ^T/~&n ' = '--+ ~&mh,
                           ^A/~&n ~&m; ||<'(not a function)'>! %fI&& %fP+-]]+-),
            ~&i&& ^lrNCT/~&y ~&z; ~&r+ ~&a^?\&! ~lexeme-={'=','::'}?ad(
               ~&a; ~&/&+ -+
                  //~&lhPNlth2rNNCCVNCCV dir-token_forms(default_operators) <default_directives-output>,
                  ~&vtPivhPQ+ ~&V/apt-separation,
                  ~&iNC; //: ~&V\<> token[
                     location: &,
                     lexeme: '(decompiler)',
                     semantics: ! ! ~&iNC+ file$[
                        contents: ~&i&& ~&z; (:^\~&mt ^T/~&n ' = '--+ ~&mh)^A/~&n ~&m; ||<'(not a function)'>! %fI&& %fP]]+-,
               ^rlPlad2rrPVX/~& ~&favx2J; ~&lrxPX+ ~&aa^?\&! -+
                  ~&rl?/~&rlPrrPlaat3CX ^rlPlrrPCX/~&laah ~&lfafatPJPR,
                  ^/~& ~&afahPR+-))+-,
      extras: <'symbol-name'>,
      help: 'suppress output files but display formatted virtual code']>

------------------------------------------- the main table of command line options ------------------------------------------
#library+

default_formulators = 

(&m.formula:= optimization+ ~&m.formula)* ~&hS |=&n :/('help': help_formulator default_help_topics) ~&L <
   showing_formulators,
   diagnostic_formulators,
   customizing_formulators,
   output_file_formulators,
   input_file_formulators,
   ^A(~for-mnemonic,~&)* directive_based_formulators ~&mS default_directives>
