info([Message|Tail]) :- printInfo, write(Message), info(Tail).
info([]) :- printInfo, writeln('').
info(_) :- not(printInfo), true.
