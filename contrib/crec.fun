
#import std

#comment -[
Invoked with any combination of parameters or options,
this program pretty prints a representation of the command line
record to standard output.]-

#executable ('parameterized',<>)

#optimize+

crec = ~&iNC+ file$[contents: --<''>+ _command_line%P+ ~command]
