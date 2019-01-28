# coqrep

This repository currently contains an old version of the coqrep library for computable analysis in coq.
The parts of the library that evolve around continuity only and not around computablity have been externalized, cleaned up and are now located in the "incone" repository that can also be found in my github account.
I am in the process of rebuilding coqrep as a code-extraction layer for incone, but that may take me a some time.

This is a repository containing what I have done so far to formalize results from computable analysis in coq.
I am aiming for it to be possible to use this as a library but I can not recommend using it yet.
If you came here for doing computation on the real numbers in coq, I'd point you to the CoRN library instead.
If you are looking for software for verified real arithmetic based on the ideas of computable analysis I'd recommend you check out iRRAM.
There is also RZ, which you might be intressted in.
If you still want to take a look at the content of this repository and maybe also use it, be advised that you have to be very carefull with your use of Axioms (as explained in more detail below).
I am thankful for any comments and any kind of support.

The library currently uses coq functions to simulate computability is ... tacky and has some serious disadvantages but also some advantages.
Unfortunately the list of disadvantages is long and I will probably at some point have to switch to a different system.
First off, Coq functions are always total and partial functions are necessary to appropriatelly handle divergent behaviour of certain algorithms.
This is handled in the usual way by modeling computation via an additional natural number argument and replacing the return value type by an option type.
To guarantee executability, the functions defined this way have to be Axiom free.
In principle it would be possible to use a self-reflection library to force this, but in the current state it is the responsibility of the user to guaratee this.
Be carefull with that, depending on the part of the library you use you it is easy to accidentally make all functions, or at least all continuous functions, computable.
There are some induction principles proven in the library, but they are very fragile.
If something that should not be opaque is opaque, for instance execution will take very long and result in a big term from which you can sometimes see what went wrong.
The advantage of doing it like this, of course, is that everything that has been proven in Coq can be reused.
Many things that have been proven constructively can directly be executed and used as algorithms.

I currently use Coq 8.8.2 to compile and I do not explicitly check compatibilty with any other versions.
To build the library you can try doing what I do:
You need to run "coq_makefile -f _CoqProject -o Makefile" once to generate a Makefile.
You might have to change some line endings depending on whether I last commited from Windows or Linux.
Then run make to compile the library.
Once you got it to run, the file "example_real_functions" is a good starting point for getting to know the library.
You may also find the other example files interesting and there are some explanations of what is going on scattered throughout the library.
