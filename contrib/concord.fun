
#import std
#import nat

#comment -[invoke as $ concord file ... for a list words and the number of usages]-

#executable (<'parameterized'>,<>)

concord =

~command.files; ~&iNC+ file$[contents: ~&]+ ~contents*=; mat` ; sep` ; ~&F; -+
   ^(length,~&h)*; -<&r; --<''>+ * ^T(~&h+ %nP+ ~&l,:/` + ~&r),
   |=&+ * (* -:~& ~&p (take/26)^~(skip/65,skip/97) characters)+ *~ ~<'.,()''`\'+-
