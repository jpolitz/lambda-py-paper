#lang scribble/manual

@(require
  scriblib/footnote
  scriblib/figure
  scribble/core
  racket/base
  (only-in racket/string string-join)
  redex
  "../redex/lambdapy-core.rkt"
  "../redex/lambdapy-reduction.rkt"
  "../redex/lambdapy-prim.rkt"
  "typesetting.rkt"
  "bib.rkt")

@(define (pycode . stx)
  (nested #:style 'code-inset
   (verbatim (string-join stx ""))))
@(define (pyinline . stx)
  (tt (string-join stx "")))

@(define (lambda-py) (elem "λ" (subscript (larger "π"))))
@(define (lambda-js) (elem "λ" (subscript "JS")))
@(define (lambda-interp) (elem "λ" (subscript (larger "π↓"))))

@title{Python: The Even Fuller Monty}

@section[#:tag "s:appendix" #:style 'unnumbered]{Appendix 1: The Rest of @(lambda-py)}

The figures in this section show the rest of the @(lambda-py) semantics. We
proceed to briefly present each of them in turn.

@figure["f:E" (elem "Evaluation contexts") @(with-rewriters (lambda () (render-language λπ #:nts '(E Es))))]

@subsection{Contexts and Control Flow}

@figure["f:T" (elem "Contexts for try-except") @(with-rewriters (lambda () (render-language λπ #:nts '(T Ts))))]
@figure["f:H" (elem "Contexts for loops") @(with-rewriters (lambda () (render-language λπ #:nts '(H Hs))))]


@Figure-ref["f:E" "f:T" "f:H" "f:R"] show the different @emph{contexts} we use
to capture left-to-right, eager order of operations in @(lambda-py).  @(lp-term E)
is the usual @emph{evaluation context} that enforces left-to-right, eager
evaluation of expressions. @(lp-term T) is a context for the first expression
of a @(lp-term tryexcept) block, used to catch instances of @(lp-term raise).
Similarly, @(lp-term H) defines contexts for loops, detecting @(lp-term continue) and @(lp-term break),
and @(lp-term R) defines contexts for @(lp-term return) statements inside functions.
Each interacts with a few expression forms to handle non-local control flow.

@figure["f:R" (elem "Contexts for return statements") @(with-rewriters (lambda () (render-language λπ #:nts '(R Rs))))]
@figure["f:control" (elem "Control flow reductions")
  @(lp-reduction '(E-While E-LoopContinue E-LoopBreak E-LoopNext
                   E-TryDone E-TryCatch
                   E-Return E-FramePop
                   E-FinallyReturn E-FinallyBreak E-FinallyRaise E-FinallyContinue
                   E-IfTrue E-IfFalse E-Seq))]

@Figure-ref["f:control"] shows how these contexts interact with expressions.
For example, in first few rules, we see how we handle @(lp-term break) and
@(lp-term continue) in @(lp-term while) statements.  When @(lp-term while)
takes a step, it yields a @(lp-term loop) form that serves as the marker for
where internal @(lp-term break) and @(lp-term continue) statements should
collapse to.  It is for this reason that @(lp-term H) does @emph{not} descend
into nested @(lp-term loop) forms; it would be incorrect for a @(lp-term break)
in a nested loop to @(lp-term break) the outer loop.

One interesting feature of @pyinline{while} and @pyinline{tryexcept} in Python
is that they have distinguished ``else'' clauses.  For @pyinline{while} loops,
these else clauses run when the condition is @pyinline{False}, but @emph{not}
when the loop is broken out of.  For @pyinline{tryexcept}, the else clause is
only visited if @emph{no} exception was thrown while evaluating the body.  This
is reflected in E-TryDone and the else branch of the @(lp-term if) statement
produced by E-While.

We handle one feature of Python's exception raising imperfectly.  If a
programmer uses @pyinline{raise} without providing an explicit value to throw,
@emph{the exception bound in the most recent active catch block} is thrown
instead.  We have a limited solution that involves raising a special designated
``reraise'' value, but this fails to capture some subtle behavior of nested
catch blocks.  We believe a more sophisticated desugaring that uses a global
stack to keep track of entrances and exits to catch blocks will work, but have
yet to verify it.  We still pass a number of tests that use @pyinline{raise}
with no argument.

@subsection{Mutation}

@figure*["f:mutation" "Various operations on mutable variables and values"]{
  @(lp-reduction '(E-App E-LetLocal E-LetGlobal E-GetVar E-GetVar E-AssignLocal E-AssignGlobal
                   E-Alloc E-Fetch E-Set! E-SetFieldAdd E-SetFieldUpdate
                   E-DeleteLocal E-DeleteGlobal))
}

There are @emph{three} separate mutability operators in @(lambda-py), @(lp-term (set! e e)), which mutates the value stored in a reference value, @(lp-term (assign e := e)), which mutates variables, and @(lp-term (set-field e e e)), which updates and adds fields to objects.

@Figure-ref["f:mutation"] shows the several operators that allocate and
manipulate references in different ways.  We briefly categorize the purpose for
each type of mutation here:

@itemlist[

  @item{We use @(lp-term (set! e e)), @(lp-term (fetch e)) and @(lp-term (alloc e))
  to handle the update and creation of objects via the δ function, which
  reads but does not modify the store.  Thus, even the lowly @(lp-term +)
  operation needs to have its result re-allocated, since programmers only see
  references to numbers, not object values themselves.  We leave the pieces of
  object values immutable and use this general strategy for updating them,
  rather than defining separate mutability for each type (e.g., lists).}

  @item{We use @(lp-term (assign e := e)) for assignment to both local and
  global variables.  We discuss global variables more in the next section.
  Local variables are handled at binding time by allocating references and
  substituting the new references wherever the variable appears.  Local
  variable accesses and assignments thus work over references directly, since
  the variables have been substituted away by the time the actual assignment or
  access is reached.  Note also that E-AssignLocal can override potential
  @(lp-term (undefined-val)) store entries.}

  @item{We use @(lp-term (set-field e e e)) to update and add fields to
  objects' dictionaries.  We leave the fields of objects' dictionaries as
  references and not values to allow ourselves the ability to share references
  between object fields and variables.  We maintain a strict separation in our
  current semantics, with the exception of modules, and we expect that we'll
  continue to need it in the future to handle patterns of @pyinline{exec}.}

]

Finally, we show the E-Delete operators, which allow a Python program to revert
the value in the store at a particular location back to @(lp-term (undefined-val)), or to remove
a global binding.

@subsection{Global Scope}

@figure*["f:lazy-get" "Accessing fields on a class defined by an identifier"]{
  @(lp-reduction '(E-GetField-Class/Id))
  @(linebreak)
  @(lp-metafunction env-lookup #f)
}

While local variables are handled directly via substitution, we handle global
scope with an explicit environment @(lp-term ε) that follows the computation.
We do this for two main reasons.  First, because global scope in Python is
truly dynamic in ways that local scope is not (@pyinline{exec} can modify global
scope), and we want to be open to those
possibilities in the future.  Second, and more implementation-specific, we use
global scope to bootstrap some mutual dependencies in the object system, and
allow ourselves a touch of dynamism in the semantics.

For example, when computing booleans, @(lambda-py) needs to yield numbers from
the δ function that are real booleans (e.g., have the built-in @(lp-term (id %bool global))
object as their class).  However, we need booleans to set up if-tests while we
are bootstrapping the creation of the boolean class itself!  To handle this, we
allow global identifiers to appear in the class position of objects.  If we
look for the class of an object, and the
class position is an identifier, we look it up in the global environment.  We only
use identifiers with special %-prefixed names that aren't visible to Python in
this way.  It may be possible to remove this touch of dynamic scope from our
semantics, but we haven't yet found the desugaring strategy that lets us do so.
@Figure-ref["f:lazy-get"] shows the reduction rule for field lookup in this case.


@subsection{@pyinline{True}, @pyinline{False}, and @pyinline{None}}

The keywords @pyinline{True}, @pyinline{False}, and @pyinline{None} are all
singleton references in Python.  In @(lambda-py), we do not have a form for
@pyinline{True}, instead desugaring it to a variable reference bound in the
environment.  The same goes for @pyinline{None} and @pyinline{False}.  We
bind each to an allocation of an object:@centered{
@(lp-term
  (let (True global = (alloc (obj-val %bool (meta-num 1) ()))) in
  (let (False global = (alloc (obj-val %bool (meta-num 0) ()))) in
  (let (None global = (alloc (obj-val %none (meta-none) ()))) in
    e_prog))))
}
and these bindings happen before anything else.
This pattern ensures that all references to these identifiers in the desugared
program are truly to the same objects.  Note also that the boolean values are
represented simply as number-like values, but with the built-in @(lp-term
%bool) class, so they can be added and subtracted like numbers, but perform
method lookup on the @(lp-term %bool) class.  This reflects Python's semantics:

@pycode{
isinstance(True, int) # ==> True
}

@subsection{Variable-arity Functions}

@figure*["f:varargs" "Variable-arity functions"]{
  @(lp-reduction '(E-AppArity E-AppVarArgsArity E-AppVarArgs1 E-AppVarArgs2))
}

We implement Python's variable-arity functions directly in our core semantics,
with the reduction rules shown in @figure-ref["f:varargs"].  We show first the
two arity-mismatch cases in the semantics, where either no vararg is supplied
and the argument count is wrong, or where a vararg is supplied but the
count is too low.  If the count is higher than the number of parameters and a
vararg is present, a new tuple is allocated with the extra arguments, and
passed as the vararg.  Finally, the form @(lp-term (app e (e ...) e)) allows a
variable-length collection of arguments to be @emph{passed} to the function;
this mimics @pyinline{apply} in languages like Racket or JavaScript.

@subsection{Modules}

@figure*["f:modules" @elem{Simple modules in @(lambda-py)}]{
  @(lp-reduction '(E-ConstructModule E-ModuleDone))
  @(linebreak)
  @(lp-metafunction vars->fresh-env #f)
}

We model modules with the two rules in @figure-ref["f:modules"].
E-ConstructModule starts the evaluation of the module, which is represented by
a @(lp-term meta-code) structure.  A @(lp-term meta-code) contains a list of
global variables to bind for the module, a name for the module, and an
expression that holds the module's body.  To start evaluating the module, a new
location is allocated for each global variable used in the module, initialized
to @(lp-term (undefined-val)) in the store, and a new environment is created
mapping each of these new identifiers to the new locations.

Evaluation that proceeds inside the module, @emph{replacing} the global
environment ε with the newly-created environment.  The old environment is
stored with a new @(lp-term in-module) form that is left in the current
context.  This step also sets up an expression that will create a new module
object, whose fields hold the global variable references of the running module.

When the evaluation of the module is complete (the @(lp-term in-module) term
sees a value), the old global environment is reinstated.

To desugar to these core forms, we desugar the files to be imported, and
analyze their body to find all the global variables they use.  The desugared
expression and variables are combined with the filename to create the @(lp-term
meta-code) object.  This is roughly an implementation of Python's
@pyinline{compile}, and it should be straightforward to extend it to implement
@pyinline{exec}, though for now we've focused on specifically the module case.

