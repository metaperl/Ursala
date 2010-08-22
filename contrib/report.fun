#import std
#import nat
#import flo

#executable (<'param'>,<'employees.txt','clients.txt','billrates.txt'>)

report = ~&iNC+ -+
   file$[stamp: &!,contents: 'rrr'%=*'lll'+ --<''>,path: <'report.tex'>!],
   ~command.files; ^H\~&z.contents -+
      <"e","c","b">. tbl-sectioned_table2+ -+
         //~& ~&iNCNVS <'Client','Employee','Date','Hours','Fee'>,
         * ^lrNCT/~&y ~&z; ~&t?\~& ^lrNCT/~& plus:-0.,
         ~&htNtCSPCK7S+ * *= ~&hthNttPCCSPC+ * ^/"c"+~&h :^/"e"+~&th :^(
            take/6+ ~&tttt+ stt-time_to_string+ %np+ ~&tthNC,
            ^lrNCC(~&r,times)^(
               %ep+ ~&iNC+ "b"+ ~&th,
               div\3.6e3+ float+ difference+~&thPhX+ %np*+ ~&ttiNCS)),
         |=hK2SthPhttPCCSSS&th+ sep` *+ ~&F+-,
      ~&y; * ~contents.&F; -:+ * sep` ; :^|/~& mat` +-+-
