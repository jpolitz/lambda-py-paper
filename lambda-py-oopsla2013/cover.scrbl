#lang scribble/base

@(require "bib.rkt")
@(define (lambda-py) (elem "λ" (subscript (larger "π"))))

@section{Reviewer 1}

@subsection{Response 1}

While we would have loved to have had the time to do a static analysis or other
tool-building, those are probably papers in their own right.  We think this
work lays the foundation for that in the future.

The style of semantics is very similar to that used in hundreds or thousands of
other papers, so we've reduced Python to something that is wholly familiar to
the broader PL research community. This is a matter of judgment, to be sure, so
we'd love feedback on things that strike you as bad about the semantics.

@subsection{Revision 1}

Thanks for pointing out that we say too late in section 4 that the CPS
translation is (at first) a failed effort. We have made that clear up front, in
prose and the section title.

@section{Reviewer 2}

@subsection{Response 2}

It is indeed true that one @bold{could} directly express the scope rules in the core
language. We believe that would have made the core not only bigger, but in our
judgment, far less amenable to many kinds of analysis, because the resulting
@(lambda-py) would be much closer to a dynamically-scoped scripting language
than, with some exceptions where it really does not apply, a statically-scoped
language.  The latter would be a highly nonstandard basis for building type
systems, static analyses, etc.

Nevertheless, these are matters of judgment---we did not claim this is a
@bold{canonical} core language for Python---and another group is welcome to try
doing things differently (we make our entire codebase public to ease
experimentation). Indeed, instead of starting from scratch, they can start with
our system, change just that one part, use the testing strategy to ensure they
have not altered the meaning of programs, and obtain a different semantics.
Users would then be free to choose between the systems.

@section{Reviewer 3}

@subsection{Response 3}

``the paper does not show that the generators can't be desugared to Python''
--- that is correct.  Given the richness of Python as a target language and of
our desugaring process, such a proof would be a technical result in its own
right (using something like Felleisen's
technique@~cite["felleisen:expressiveness"]).  We note that we said that the
translation is "inexpressible", and we have indeed failed to justify that
claim. We should not have said that, and will fix it.

On @tt{locals}:

We do not need to give up all hope. If a program only wants to read and
reflect on its locals, that can be just fine. Even modifying a local is
sometimes no different from a variable update in the source. If, however, a
programmer performs arbitrary mutations on @tt{locals}, then all bets may indeed be
off.

This is where it helps to consider the purpose of a semantics. If we are trying
to build a (purely) static reasoning system, such a system is unlikely to be
sound if the program modifies @tt{locals}, or uses it in a higher-order way.
Therefore, a reasonable restriction such a system might impose is that the
programs it types/analyzes/verifies cannot modify @tt{locals} (an easy
syntactic test). In such a case, a semantics that doesn't handle the full power
of locals is actually perfectly useful, and our semantics provided some useful
insight into what features a subset of Python should avoid to be amenable to
static reasoning.

As a rough point of comparison, it takes about 20 hours to run a similar
experimental semantics for JavaScript@~cite["politz:s5"] on a conformance
suite that takes around 10-15 minutes in a browser.

@subsection{Revision 3}

We have revised the text to: (a) make clear at the beginning of section 4 that
this is describing a failed attempt, and (b) changed the prose to simply make
clear that we have not found a desugaring, not to claim that one does not
exist.  The end of 4.1 now reads ``The straightforward CPS solution, which
avoids extending the number of concepts in the language, is incorrect in the
presence of Python’s mechanics of variable binding.''

We have added some of the above discussion about @tt{locals} in section 6.

@(generate-bib)
