#import std
#import nat
#import int

#comment -[
This module contains two functions for converting between natural
numbers expressing times in seconds since midnight January 1, 1970 and
strings of the form 'Fri Mar 18 1:58:31 2005 +0100'. The time zone
abbreviation is ignored, but time zones can be specified as +0500,
etc.. Days of the week are output correctly but ignored in the input.
Fields can be written in any order but must be separated by spaces.
Commas are optional.

Copyright (C) 2007-2009 Dennis Furey]-

#library+

one_time = 'Fri Mar 18 01:58:31 UTC 2005'

#library-

months = block3 'JanFebMarAprMayJunJulAugSepOctNovDec'

#optimize+

mlen = # the number of days in a given month in the range 0..4799, with 0 corresponding to January 1970

-: ^(~&,division\12; 1?=r(@l ||28! -&~&itB,~&hZthPB,~<{130,230,330},29!&-,{3,5,8,10}?<r/30! 31!))* iota 4800

mdiv = @NiX ^= zleq?r(^|/successor difference@rlX,~&lrrPX)^/~&l ^|/mlen ~&

# seconds and slots use a simpler algorithm for the first 128 years, during which leap years happen every 4 years

seconds = # takes a list like <2009,'Aug',13,20,27,37>

-+
   sum^|\~& division\4800; sum^|(product/12622780800,~&)^|/~& product/86400+ zleq/1536?(
      iota; sum:-0+ mlen*,
      division\48; sum^|/(product/1461) -: num ^NiC(~&h,~&ar^& ^rlfPrlart3XRC/~& sum@alrhPX) mlen* iota 48),
   ^(sum@hthPX,~&tth)^|C/(product/12+ difference\1970) ^|lrNCC(
      -:@rlXS (^T/num --+ (num^~ (*+ *)^~(~&K30K31piK26,~&K31K30piK26) letters)) months,
      sum:-0+ product*p/<86400,3600,60,1>+ ^|C/predecessor ~&)+-

slots = # takes a time in seconds to a list like <2009,'Aug',13,20,27,37>

division\12622780800; ^C(sum/1970+ sum^/~&rh product/400+ ~&l,~&rt)^|/~& -+
   ^|T\~& division\12; ^|lrNCC/~& -: num months,
   ^|T\~& ^|lrNCC(~&,successor)+ zleq/46752?/mdiv division\1461; ^(sum@lrlPX,~&rr)^|\mdiv product/48,
   division\86400; ^|C/~& division\3600; ^|lrlrNCCPC/~& division\60+-

#library+

time_to_string =

-+
   ^|(~&,%nP*=); ^|T/(^|T/~& :/` ) :/` + ^T\~&h --' UTC '+ @t ^|T(~&t?/~& :/` ,:/` + mat`:+ * ~&t?/~& :/`0),
   ^lrth2XrhttPCPX\slots quotient\86400; remainder\7; -: num block3'ThuFriSatSunMonTueWed'+-

string_to_time = # fields are allowed in any order; time zone abbreviations and day of week are ignored

guard\<'bad date format'>! ','%=' '; sep` ; seconds^T(
   <.eql/;15; ~&i&& %np,~&h+ *~ \/-= months,leql\;3; ~&i&& %np>,
   ^C(sum@lrhPX,~&rt)^/(-&~&,@hyy %zp@iNC+ `+?=h\~& ~&t&-+ *~ eql/31&& ~&ihB-='+-') %np*iNCS+ sep`:@ihB+ ~&w/;`:)
