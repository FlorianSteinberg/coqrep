# coqrep

This is a repository containing what I have done so far to formalize results from computable analysis in coq.
I am aiming for it to be possible to use this as a library but I can not recommend using it yet.
If you came here for doing computation on the real numbers in coq, I'd point you to the CoRN library instead.
If you are looking for software for verified real arithmetic based on the ideas of computable analysis I'd recommend you check out iRRAM.
There is also RZ, which you might be intressted in.
If you still want to take a look at the content of this repository and maybe also use it, be advised that you have to be very carefull with your use of Axioms (as explained in more detail below).
I am thankful for any comments and any kind of support.
The notations of this library heavily use natural language in attempt to make it possible to read lemmas and statements out loud. To avoid blocking too many keywords, left recursive notations that use natural language start in a backslash.

The core Ideas this library pursues are the following:
- Each proof should lead to a program that is actually executable inside of Coq.
- It is ok to use classical reasoning to simplify proofs, eliminate assumptions and provide canonical constructions (the function space construction currently uses propositional extensionality and several parts use classical reasoning).
That is, of course, only where it does not break with the previous point.
- Programs extracted from abstract proofs are very slow.
For a given problem it is usually possible to do a lot better by providing a concrete algorithm and proving it correct.
The goal is to make this possible, if one is willing to invest the time.
- On the other hand, it should be possible to prove qualitative inefficiency.
On a computability level, I'll go for discontinuity.
I hope to be able to provide a similar thing on a complexity level, but it will take me some time to get to that part...

The executability inside of Coq has some serious advantages and some serious disadvantages.
The advantages are that everything that has been proven in Coq can be reused and many things that have been proven constructively can directly be executed and used as algorithms.
Unfortunately the list of disadvantages is long and I will probably at some point have to switch to a different system.
First off, Coq functions are always total and partial functions are necessary to appropriatelly handle divergent behaviour of certain algorithms.
This is handled in the usual way by modeling computation via an additional natural number argument and replacing the return value type by an option type.
Proofs of incomputability in a discrete sense are problematic since execution is done inside of Coq this is because of the possibility to asssume Axioms and has further consequences:
Depending on the part of the library you use you it is easy to accidentally make all functions computable or at least all continuous functions computable.
This does not mean that you should avoid Axioms completly.
The library is made for reasoning about structures like the real numbers and I recommend to reason classical about those.
The library uses sigma types for computability statements and if the Axioms you use are formulated in the right way, Coq should not allow you to use them inappropriatelly.
This is easy to get around though if you try and even if you don't try it does not always work reliably.
The best way to test whether everything is alright is executing.
To be able to execute you need to end proofs of computability with Defined instead of Qed.
This removes opacity and has consequences for performance, thus it should only be done in the places where it is really necessary.
If something that should not be opaque is opaque, for instance because it relies on an axiom, execution will take very long and result in a big term from which you can see what went wrong.


I currently use Coq 8.7.2 to compile and I do not provide any compatability with other versions.
To build the library you can try doing what I do:
You need to run "coq_makefile -f Make -o Makefile" once to generate a Makefile.
You might have to change the line endings of the file Make depending on whether I last commited from Windows or Linux.
Then run make to compile the library.
Once you got it to run, the file "example_real_functions" is a good starting point for getting to know the library.
You may also find the other example files interesting and there are some explanations of what is going on scattered throughout the library. 

I started this project in the course of my one year postdoc at INRIA in Sophia-Antipolis to become familiar with Coq.
There are a lot of parts that I have written myself and where it probably would have been better to rely on existing stuff.
I am looking into replacing such parts.
If you spot something that should be replaced feel free to tell me.

