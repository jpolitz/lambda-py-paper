#lang scribble/sigplan @10pt @preprint

@(require scriblib/footnote scribble/manual scriblib/figure racket/base)
@(require redex)
@(require
  "../redex/lambdapy-core.rkt"
  "../redex/lambdapy-reduction.rkt"
  "../redex/lambdapy-prim.rkt"
  "typesetting.rkt")      

@(define (lambda-py) (elem "λ" (subscript (larger "π"))))

@title{Python: The Full Monty@(elem #:style "thanks" "Title credit Benjamin S.
Lerner")}
@authorinfo["Sumner Warren" "Brown University" "FILL"]
@authorinfo["Matthew Milano" "Brown University" "FILL"]
@authorinfo["Daniel Patterson" "Brown University" "FILL"]
@authorinfo["Alejandro Martinez" "" ""]
@authorinfo["Junsong Li" "" ""]
@authorinfo["Anand Chitipothu" "" ""]
@authorinfo["Joe Gibbs Politz" "Brown University" "joe@cs.brown.edu"]
@authorinfo["Shriram Krishnamurthi" "Brown University" "sk@cs.brown.edu"]

@abstract{Python is hard}

@section{Introduction}

@section{Contributions}

We tackled, for Python
3.2.3,@note{http://www.python.org/getit/releases/3.2.3/} (released April
2012), the semantics of:

@itemlist[
  @item{Object model}
  @item{Pythonic Patterns}
  @item{Scope}
  @item{Modules}
  @item{Generators}
  @item{Testing strategy & results}
]

@subsection{Outline} We first address Python's value and object model, whose
richness allows many of the other patterns we see in the language.  We then
show how many Pythonic patterns for iteration and overloading can be
implemented as straightforward expansions to patterns in this object model.
In this section we also introduce the concept of @emph{desugaring} the surface
language to the core.  Next, we tackle Python's unique treatment of scope for
variables and closures.  This notion of scope interacts with Python's module
system at the global and local level, so we discuss the module system next.
Finally, we show how generators, a complicated control-flow construct in
Python, interact with Python's scope and require a more subtle solution than
an obvious CPS transformation.

@figure["f:values" @elem{Values in @(lambda-py)}]{
  @(with-rewriters
    (lambda () (render-language λπ #:nts '(val mval εs ε ref))))
}

@section{Warmup: Pythonic Values and Objects}

An expressive object model is one of the core features of Python.  Pythons
object and class system has support for single and multiple inheritance, static
and instance members and methods, monkey-patching, proxying, and more.


@subsection{Built-in Values}

Python has a few commonly-used built-in datatypes with rich (but implicit)
interfaces.  Dictionaries, tuples, and lists are all supported directly in
Python syntax, and all implement their own overloading of common operations:

@verbatim{
s = "str"
d = { "dictionaries":  "with",
      0:               "or more ",
      "comp" + "uted": "keys" }
t = ("heter", 0, "geneous tuples")
l = ["heter", 0, "geneous lists"]
st = {"heter", 0, "geneous sets"}
assert(len(s) == len(d) == len(t)
    == len(l) == len(s) == 3)
assert(s[0] == "s")
assert(d[0] == "or more")
assert(t[0] == "heter")
assert(l[0] == "heter")
assert(st[0] == "heter")
}

All of these builtin values have special, builtin behavior that cannot be
completely emulated by programmers in Python.  We give these values
distinguished forms in our semantics.  However, these builtin values are
@emph{not} the values of the language themselves.  They only appear as part of
a larger object value.  Every value that the Python programmer sees truly is
an object: there is no such thing as a ``primitive string'' that a programmer
can directly get a reference to in Python.

@subsubsection{Creating Values}

@Figure-ref["f:values"] shows the representation of values in @(lambda-py).
Each @(lambda-py) object, written as a triple of the form @(lp-term (obj-val val mval ((string ref) ...))), has distinguished positions for its class, its primitive
content (if any), and the dictionary of string-indexed fields that it holds.
The class value is any other Python value, though non-objects may end up
throwing runtime errors.  The @emph{meta-val} position holds special kinds of
builtin data, of which there is one per builtin type that @(lambda-py) models.

As an example, we'll step through the various stages of constructing and using
a built-in list in @(lambda-py).  Lists are built with object expressions,
which have two pieces: the @emph{class} of the object being constructed, and
the @emph{meta-val}, if any, that stores primitive data.  The expression for
creating an empty list is:

@centered[
  @(lp-term (list (id %list localid) ()))
]

Where @(lp-term (id %list localid)) is expected to be bound to the built-in
list class.  In general, the first position of a list expression is the
@emph{class} of the list object to create.  This must part of the list
expression because programmers can subclass the builtin @code{list} class and
create values that can use all the built-in list primitives, but have their
own set of methods.  The second part of the expression is a list of
expressions that will evaluate to the elements of the list.  For example, a
list containing the numbers 1 and 3 is written:

@(define (lst1)
  (lp-term (list (id %list localid) ((object (id %int localid) (meta-num 1)) (object (id %int localid) (meta-num 3))))))

@centered[
  @(lst1)
]

The object creation expressions for numbers similarly indicate that the
@(lp-term %int) class should be used for their methods.  The rule for
evaluating list expressions themselves allocates a new location on the heap
for the resulting list, and constructs a value with the given class and a
list-typed @(lp-term mval) to hold its elements:

@centered[
  @(lp-reduction '("E-List"))
]

Here, the @"@" indicates a reference value, which is pointing to a new object
which is added to the store Σ.  This also shows the shape of reductions for
@(lambda-py), which is a small-step relation over triples of expressions
@(lp-term e), environment lists @(lp-term εs),@note{We discuss the need for a
list of environments, rather than just a single environment, in [REF].} and
stores @(lp-term Σ).  We define evaluation contexts @(lp-term E) in the usual
way to enforce an evaluation order on expressions.

In this style, to fully evaluate @(lst1), the reduction would
allocate 3 new references: one for each number, and one for the resulting
list:

@itemlist[
  @item{@(lp-term (Σ(ref_list))) = @(lp-term (obj-val %list (meta-list ((pointer-val ref_one) (pointer-val ref_three))) ()))}
  @item{@(lp-term (Σ(ref_one))) = @(lp-term (obj-val %int (meta-num 1) ()))}
  @item{@(lp-term (Σ(ref_three))) = @(lp-term (obj-val %int (meta-num 3) ()))}
]

And the reference value @(lp-term (pointer-val ref_list)) would be placed back
into the active context.  Similar rules for tuples, dictionaries, and sets are
shown in @figure-ref["f:steps-values"].

@figure["f:steps-values" (elem (lambda-py) " reduction rules for creating objects")]{
  @(lp-reduction '("E-Object" "E-Tuple" "E-Dict" "E-Set" "E-List"))
}

@subsubsection{Accessing Built-in Values}

Now that we've created a list, we should be able to perform some operations on
it, like look up its elements.  @(lambda-py) defines a number of builtin
primitives that model Python's internal operators for manipulating data, and
these are used to access the contents of a given object's @(lp-term mval).
We formalize these builtin primitives in a metafunction called δ.  A few
selected cases of the δ function are shown in @figure-ref["f:delta"].

@figure*["f:delta" (elem "A sample of " (lambda-py) " primitives")]{
  @(lp-metafunction δ '(0 1 2 3))
}

This lets us, for example, look up values on builtin lists:

@centered{
  @(lp-term (prim "list-getitem" ((obj-val %list (meta-list ((obj-val %str (meta-str "first-elt") ()))) ())
                                  (obj-val %int (meta-num 0) ()))))
  @(newline)
  @(lp-term ==>)
  @(lp-term (obj-val %str (meta-str "first-elt") ()))
}

Since δ works over object values themselves, and not over references, we need
a way to access the values in the store.  @(lambda-py) has the usual set of
operators for accessing and updating mutable references, shown in
@figure-ref["f:references"].

@figure["f:references" (elem (lambda-py) " reduction rules for references")]{
  @(lp-reduction '("E-Fetch" "E-Set!" "E-Alloc"))
}



The full language of expressions for @(lambda-py) is in
@figure-ref["f:exprs"].  We defer a full explanation of all the terms in that
semantics, and the full reduction relation, to the appendix [REF].  We
continue here by focusing on some of the cases in the semantics that are
unique to Python.

@figure["f:exprs" (elem (lambda-py) " expressions")]{
  @(with-rewriters
    (lambda () (render-language λπ #:nts '(e t))))
}


@subsection{First-class Functions}

Python has first-class functions that can close over their environment (in
interesting ways, see section [FILL]):

@verbatim{
def f():
  x = "to-be-closed-over"
  def g():
    return x
  return g

fun apply_twice(h): h()()

apply_twice(f) # evaluates to "to-be-closed-over"
}

Anonymous functions have syntactic restrictions on the kinds of expressions
that can appear in their body, but are also allowed:

@verbatim{
x = 10
f = lambda: x
f() # evaluates to 10
f = lambda: x = 42 # syntax error
}


We represent function values in the usual way, as abstractions that store an
environment:

@centered[
@(lp-term (fun-val εs (λ (x ...) e)))
]

Python also allows for variable-arity functions, which we explicitly support
in the semantics via an extra argument that holds all additional values passed
to the function beyond those in the list @(lp-term (x ...)):

@centered[
@(lp-term (fun-val εs (λ (x ...) x_var e)))
]

[FILL] functions as objects.

@subsection{Classes}





Python has a number of reflective operations on the values in its object
system.  These operations predominantly preserve @emph{integrity} while
compromising @emph{confidentiality}.  That is, the allow the user to observe
and copy values that are internal to objects, but not to change them if they
would affect the internals of the behavior of the object.

@section{Pythonic Patterns}

Pythonic objects can have a number of so-called @emph{magic fields} that allow
for overriding the behavior of built-in syntactic forms.  These magic fields
can be set anywhere in an object's inheritance hierarchy, and provide a lot of
the flexibility that Python is well-known for.

@section{Python, the Hard Parts}

Python's value and object model, and the desugaring of surface forms to it,
exhibit properties of good design: they are extensible, and provide
abstractions to the programmer.  This is reflected in their straightforward
and compositional desugaring.

Not all of Python has this a semantics this obvious.  To illustrate some of
the trickier features, we begin with an example of an analysis task, a
continuation-passing style transformation, that is difficult in Python.  This
description actually stems from our false start at implementing generators via
CPS that ran afoul of scoping issues.  By the end of the paper, we will make
clear all the pieces that go into solving this problem.

@subsection{The Semantics of Generators}

Python has a built-in notion of @emph{generators}, which provide a control-flow
construct, @code{yield}, that can implement lazy or generatives sequences and
coroutines.  The programmer interface for creating a generator in Python is
straightforward: any function definition that uses the @code{yield} keyword in
its body is automatically converted into an object with particular interface.
To illustrate the easy transition from function to generator, consider this
(perhaps foolish) program in Python:

@verbatim{
def f():
  x = 0
  while True:
    x += 1
    return x

f() # evaluates to 1
f() # evaluates to 1
# ...
}

This function, when called, always starts what would be an infinite loop if it
didn't immediately return @code{1}.  By changing the {\tt return} statement to a
@code{yield} statement, a generator is produced that can produce an arbitrary
number of such values:

@verbatim{
def f():
  x = 0
  while True:
    x += 1
    yield x

gen = f()
gen.next() # evaluates to 1
gen.next() # evaluates to 2
gen.next() # evaluates to 3
# ...
}

The application @code{f()} no longer immediately evaluates the body of the
function.  Instead, it creates an object with (at least) a @code{next} method.
When @code{next} is invoked, it evaluates up to the next {\tt yield} statement,
returns the value provided there, and stores its state for future @code{next}
calls.  The documentation of @code{yield} says as much (emphasis added):


...the execution proceeds to the first @code{yield} expression, where it is
suspended again, returning the value of [the @code{yield expression}] to the
generator's caller. By suspended we mean that @emph{all local state is retained,
including the current bindings of local variables, the instruction pointer, and
the internal evaluation stack}. When the execution is resumed by calling one of
the generator's methods, the function can proceed exactly as if the yield
expression was just another external
call.@note{http://docs.python.org/release/3.2.3/reference/expressions.html?highlight=generator#yield-expressions}

The emphasized English description of the retention of local state is quite
broad, and not entirely precise.  Is there any local state other than the local
variables' bindings, the instruction pointer, and the internal evaluation
stack?  If Python has new forms of local state added in the future, will those
be included in the stored local state?  Is it truly safe for, say, a program
analysis in an IDE to treat a @code{yield} statement as any other external call,
as the last line suggests?

One way that we might try to explain the semantics of generators and {\tt
yield} is by reducing them to other concepts.  For example, if we could express
Python generator expressions in terms of just function declarations and
objects, then the translation down to the simpler concepts would provide an
explanation of their behavior.  A traditional way to express the semantics of
control flow operators like @code{yield} is via continuations, whether as a
first-class construct in the language, or via a @emph{continuation-passing
style} (CPS) transformation of the source language.  In fact, CPS is a useful
tool for program analyses in general for making control flow explicit.  Can we
apply a CPS transformation to Python generators, and the @code{yield} operation
in particular, to both explain their semantics and provide a useful normal form
for analyses?

@subsection{CPS for Generators, a False Start}

The usual goal of a CPS transformation is to turn all control flow in the
language into function applications.  Functions with the appropriate future
behavior (the @emph{continuation} of the program) are bound at each expression
context that handles control flow, and the expression that causes an abnormal
flow of control calls the appropriate handler.  The expressions that use these
control-flow constructs need to be rewritten to construct the appropriate
continuation and pass it in.

For example, a @code{try/except} block can be changed from:

@verbatim{
try:
  raise Exception()
except e:
  print(e)
}

@verbatim{
def except_handler(e): print(e)
except_handler(Exception())
}

In the case of generators, a sketch of a solution for rewriting @code{yield}
with CPS would involve creating a handler that stores a function holding the
code for what to do next, and rewriting @code{yield} expressions to call that
handler:

@verbatim{
def f():
  x = 1
  yield x
  x += 1
  yield x

g = f()
g.__next__() # evaluates to 1
g.__next__() # evaluates to 2
g.__next__() # throws "StopIteration"
}

Would be rewritten to something like:@note{ This is a sketch, not
the true output of an automated process, so we've taken liberties
with the variable names and continuations' construction. We use a
dictionary for @code{__next__} to avoid verbose object
construction.} 

@verbatim{
def f():
  def done(): raise StopIteration()
  def start():
    x = 1
    def rest():
      x += 1
      return yielder(x, done)
    return yielder(x, rest)

  def yielder(val, rest_of_function):
    next.to_call_next = rest_of_function
    return val

  def next():
    return next.to_call_next()

  next.to_call_next = start

  return { '__next__' : next }

g = f()
g.['__next__']() # evaluates to 1
g.['__next__']() # evaluates to 2
g.['__next__']() # throws "StopIteration"
}

For the function, we build the @code{yielder} function, which takes a
value, which it returns, and continuation argument, which it stores
in the @code{to_call_next} field.  The @code{next} function always
returns the result of calling this stored value.  Each @code{yield}
statement is rewritten to put everything after it into a new function
definition, which is passed to the call to @code{yielder}.

This rewriting is well-intentioned but does not work.  If this
program is run under Python, it results in an error:

@verbatim{
    x += 1
UnboundLocalError: local variable 'x'
                   referenced before assignment
}

This is because Python creates a @emph{new scope} for each function
definition, and assignments within that scope create new variables.
in the body of @code{rest}, the assignment @code{x += 1} refers to a
new @code{x}, not the one defined by @code{x = 1} in @code{start}.  This
runs counter to traditional notions of functions that can close over
mutable variables.  And in general, with multiple assignment
statements and branching control flow, it is completely unclear if a
CPS transformation to Python function definitions can work.

The lesson from this example is that the @emph{interaction} of
non-traditional scope and control flow made a traditional normal-form
translation (rewriting to CPS) not work.  This isn't too surprising:
to understand the state that generators are storing, we need a
precise account of just how variables work!  It happens that both
have their own idiosyncrasies in Python, and they interact in
non-obvious ways.  We'll move on to describing how we can express
Pythonic scope in a more traditional lexical model, and later we will
return to a CPS transformation that does work for Python's
generators.

@section{Scope}

Most identifiers are @code{local}; this includes function parameters and
variables defined with the @code{=} operator.  There are also @code{global} and
@code{nonlocal} variables, with their own special semantics within closures,
and interaction with classes.  Our core contribution to explaining Python's
scope is to give a desugaring of the @code{nonlocal} keyword, along with
implicit @code{local} identifiers, into traditional lexically scoped closures.
Global scope is still handled specially, since it exhibits a form of dynamic
scope that isn't straightforward to capture with traditional let-bindings.

We proceed by describing Python's handling of scope for local variables, the
extension to @code{nonlocal}, and the interaction of both of these features with
classes.

@subsection{Declaring and Updating Local Variables}

In Python, the assignment operator @code{=} performs local variable binding:

@verbatim{
def f():
  x = 'local variable'
  return x

f() # evaluates to 'local variable'
}

The syntax for updating and creating a local variable are identical, so
subsequent @code{=} statements mutate the variable created by the first.

@verbatim{
def f():
  x = 'local variable'
  x = 'reassigned'
  x = 'reassigned again'
  return x

f() # evaluates to 'reassigned again'
}

Bindings can occur within branching statements as well, so it isn't statically
determinable if a variable will be defined at certain program points.  Note
also that variable declarations are scoped to function definitions, not
blocks:

@verbatim{
import random
def f():
  if random.random() > .5: x = 'big'
  else                   : pass
  return x

f() # either evaluates to 'big' or
    # throws an exception
}

\paragraph{Desugaring for Local Scope}

Handling these cases is straightforward to translate into a lexically-scoped
language.  @(lambda-py) has a usual @code{let} form that allows for lexical
binding.  In desugaring, we scan the body of the function and accumulate all
the variables on the left-hand side of assignment statements in the body.
These are let-bound at the top of the function to a special value, {\tt
Undefined}, which evaluates to an exception in any context other than a {\tt
let}-binding context.  We use @code{x := e} as the expression form for variable
assignment, which is not a binding form in the core.
So in @(lambda-py), the example above rewrites to:

@verbatim{
import random
def f():
  let x = Undefined in {
    if random.random() > .5: x := 'big'
    else                   : pass
    return x
  }

f() # either evaluates to 'big' or
    # throws an exception
}

This strategy is simple and works for variables defined in the branches of
@code{if} statements and loop bodies.  It is far from the whole story for
Pythonic scope, however.

@subsection{Closing Over Variables}


Bindings from outer scopes can be @emph{seen} by inner scopes:

@verbatim{
def f():
  x = 'closed-over-variable'
  def g()
    return x
  return g

f()() # evaluates to 'closed-over-variable'
}

However, since @code{=} defines a new local variable, one cannot close over a
variable and mutate it with the constructs we've seen so far; @code{=} simply
defines a new variable with the same name.  This was the underlying problem
with the attempted CPS translation from the last section:

@verbatim{
def g():
  x = 'not affected by h'
  def h()
    x = 'inner x'
    return x
  return (x, h())

g() # evaluates to
    # ('not affected by h', 'inner x')
}

Python 3.0 introduced a new keyword to allow this pattern, @code{nonlocal}.  A
function definition can include a @code{nonlocal} declaration at the top, which
allows assignments within its body to refer to variables in enclosing scopes.
If we add such a declaration to the previous example, we get a different
answer:

@verbatim{
def g():
  x = 'not affected by h'
  def h():
    nonlocal x
    x = 'inner x'
    return x
  return (h(), x)

g() # evaluates to
    # ('inner x', 'inner x')
}

The @code{nonlocal} declaration allows the inner assignment to {\tt x} to
``see'' the outer binding from @code{g}.  This effect can span any nesting
depth of functions:

@verbatim{
def g():
  x = 'not affected by h'
  def h():
    def h2():
      nonlocal x
      x = 'inner x'
      return x
    return h2
  return (h()(), x)

g() # evaluates to
    # ('inner x', 'inner x')
}

\paragraph{Desugaring for @code{nonlocal} Scope}

The rule for desugaring @code{nonlocal} variables refines the earlier
desugaring for simple local variables.  In terms of purely lexical {\tt
let}-bindings, a @code{nonlocal} declaration means that re-binding particular
variables to @code{Undefined} should be skipped.  So the program with a single
@code{h} above can be desugared to:

@verbatim{
def g():
  let x = Undefined in {
    x := 'not affected by h'
    def h():
      # no new binding added for x here!
      x := 'inner x'
      return x
    return (h(), x)
  }

g() # evaluates to
    # ('inner x', 'inner x')
}

@subsection{Miscellaneous Scope Features}

Uses of variables that are not defined at all attempt to look up the variable
in global scope and fail:

@verbatim{
def f():
  # x is not bound anywhere
  return x

f()
# yields "NameError: global name 'x' is not defined"
}

Python does, however, distinguish variables that may be declared locally but
haven't reached their assignment yet:

@verbatim{
def f():
  # x is not bound anywhere
  return x
  x = 'this will never happen'

f()
# yields "UnboundLocalError: local variable 'x'
# referenced before assignment"
}

@subsection{Rest}

Most of Python's scope (with a few exceptions noted below), can be modelled
with a lexically-scoped core semantics.  Some operations do require
@emph{reifying} lexical scope into a value, but with very few exceptions, this
reification cannot be reflected back into ordinary variables and cause
dynamic-scope like behavior.

Existing editors use heuristics to figure out if variables could be bound to
particular instances.@note{http://wingware.com/doc/edit/points-of-use}
This makes variable naming refactorings less precise than in say, an IDE for
Java, requiring developer intervention to specify which instances should be
renamed.  We provide a more precise account of scope that would enable
corrent points-of-use analysis for lexical variables in Python.

@section{Modules}

Python's module system combines Python's notions of objects and scope to both
get a representation of the global bindings in one module, and introduce them
as an object or bindings in another.  Some patterns of module importing are
strictly lexical, and can be modeled via inlining.  Others amount to dynamic
code loading that affects scope in a way that isn't determinable until runtime
time.

@section{Generators}

Via the @code{yield} statement, Python allows the automatic creation of
generator objects from function-like expression forms.  Generators and the {\tt
yield} operation are often modelled using local or delimited continuations, or
can be implemented explicitly with continuation-passing style.  However, due to
complications of @emph{scope}, a naive desugaring strategy for a CPS
transformation isn't effective.  We step through this initial approach on a
simple model of Python's scope, and then discuss how our different model of
desugaring scope helps fix the problems of this naive solution.

@section{Engineering \& Evaluation}

There are two properties we evaluated for @(lambda-py):

@verbatim{
\paragraph{Property 1: $\textit{desugar}$ is a total function:}
\begin{displaymath}
\forall p \in \textrm{\ Python}, \exists e \in \lambda_\pi \textit{\ such that\ }
\textit{desugar}(p) = e
\end{displaymath}

\paragraph{Property 2: $\textit{desugar}$ composed with $\rightarrow^*$ is accurate:}
\begin{displaymath}
\forall p \in \textrm{\ Python}, \textrm{if\ }
\textit{eval}_\textit{py}(p) = v
\textrm{\ then\ } \textit{desugar}(e) \rightarrow^* \textit{desugar}(v)
\end{displaymath}
}

We do not have a proof of either, since doing so would require formalizing
Python, which is our goal here in the first place.  In order to ascertain the
degree to which @(lambda-py) enjoys these properties, we @emph{test} our
semantics against Python's own unit test suite to confirm that our semantics
matches a real implementation (CPython).  We of course do not have perfect
fidelity to real-world Python for a number of reasons; in this section we
outline which tests we pass, which we fail, which are within reach, and which
are out of scope for the semantics we've presented. We begin with an overview
of the engineering work that goes into implementing and testing the semantics,
and then discuss our results.

@subsection{Python Libraries in Python}

We implement as many libraries as possible in Python, with one small addition:
we define a small @emph{superset} of Python with macros that are recognized
specially by our desugaring to transform into particular @(lambda-py) forms.
This allows us to write implementations of libraries that more closely match
Pythonic descriptions of them, while still maintaining the guarantee that
everything is implementable in @(lambda-py) itself.

@subsection{Performance}

@(lambda-py) is a semantics first, and an implementation of the Python language
second.  From a semantics perspective, the performance of @(lambda-py) is
irrelevant:@note{For applications that don't rely on the timing behavior
of Python.} as long as it is an accurate model of Python's behavior, the
tool-builder can implement with respect to @(lambda-py) programs regardless of
their runtime.

However, to actually @emph{test} the semantics, we do require that the tests
complete at some point so we can iterate the design and regression test as we
add new features!  This required making a few engineering decisions to improve
performance to the point where running large programs and test suites is
possible.

In our initial implementation, the execution strategy had a few steps:

@itemlist[
  @item{Parse and desugar roughly 1 KLOC of libraries implemented in Python}
  @item{Parse and desugar the target program}
  @item{Built up a syntax tree of several built-in libraries, coded by building the AST directly in Racket}
  @item{Compose items 1-3 into a single @(lambda-py) expression}
  @item{Evaluate the @(lambda-py) expression}
]

Parsing and desugaring for 1 takes a nontrivial amount of time (on the order of
4 seconds on the first author's laptop).  When running a suite of tests in
order, this parsed syntax tree is the same for each test.  Switching to memoize
this parsing and desugaring for the duration of a test run cut the time for
running 100 tests from around 7 minutes to around 22 seconds.  A corollary is
that evaluating @(lambda-py) programs is relatively quick, but desugaring and
loading external files is not.

