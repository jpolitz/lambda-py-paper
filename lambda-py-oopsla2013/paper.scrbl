#lang scribble/sigplan @10pt @preprint

@(require scriblib/footnote scribble/manual scriblib/figure racket/base)
@(require
  slideshow/pict
  redex
  "../redex/lambdapy-core.rkt"
  "../redex/lambdapy-reduction.rkt"
  "../redex/lambdapy-prim.rkt"
  "typesetting.rkt"
  "figures.rkt")

@(define (lambda-py) (elem "λ" (subscript (larger "π"))))
@(define (lambda-interp) (elem "λ" (subscript (larger "π↓"))))
@title{Python: The Full Monty@(linebreak)@smaller{A Tested Semantics for Python}}

@authorinfo["Joe Gibbs Politz" "Providence, RI, USA" "joe@cs.brown.edu"]
@authorinfo["Alejandro Martinez" "La Plata, BA, Argentina" "amtriathlon@gmail.com"]
@authorinfo["Matthew Milano" "Providence, RI, USA" "matthew@cs.brown.edu"]
@authorinfo["Sumner Warren" "Providence, RI, USA" "jswarren@cs.brown.edu"]
@authorinfo["Daniel Patterson" "Providence, RI, USA" "dbpatter@cs.brown.edu"]
@authorinfo["Junsong Li" "Beijing, China" "ljs.darkfish@gmail.com"]
@authorinfo["Anand Chitipothu" "Bangalore, India" "anandology@gmail.com"]
@authorinfo["Shriram Krishnamurthi" "Providence, RI, USA" "sk@cs.brown.edu"]

@abstract{
We present a small-step operational semantics for the Python
programming language.  We present both a core language for Python,
suitable for tools and proofs, and a translation process for
converting Python source to this core.  We have tested the composition
of translation and evaluation of the core for conformance with the
primary Python implementation, thereby giving confidence in the
fidelity of the semantics. We briefly report on the engineering of
these components. Finally, we examine subtle aspects of the language,
identifying scope as a pervasive concern that even impacts features
that might be considered orthogonal.
}

@section{Motivation and Contributions}

The Python programming language is currently widely used
in industry, science, and education. Because of its popularity
it now has several third-party tools, including analyzers
that check for various potential error patterns [CITE].
@; https://pypi.python.org/pypi/pylint
@; https://pypi.python.org/pypi/pep8
@; {https://pypi.python.org/pypi/pyflakes}
@; {https://pypi.python.org/pypi/PyChecker}
It also features interactive development environments [CITE]
@; http://www.jetbrains.com/pycharm/, http://pydev.org/,
@; http://wingware.com/
that offer a variety of features such as variable-renaming
refactorings and code completion. Unfortunately, all these tools are
unsound: for instance, a simple eight-line program that uses no
``dynamic'' features was able to confuse the variable renaming feature
of all these environments.

The difficulty of reasoning about Python becomes even more pressing as
the language is adopted in increasingly important domains. For
instance, the US Securities and Exchange Commission has proposed using
Python as an executable specification of financial contracts [CITE],
@; note{https://www.sec.gov/rules/proposed/2010/33-9117.pdf}, and Python
and it is now being used to script new network paradigms [CITE].
@; cite a real paper, not a Web site
Thus, it is vital to have a precise semantics available for analyzing
programs and proving properties about them.

This paper presents a semantics for Python. Mindful that authors of
tools and of proofs prefer to contend with small languages, we divide
the semantics into two parts: a core language, @(lambda-py), with a
small number of constructs, and a desugaring function that translates
source programs into the core. The core language is a mostly
traditional stateful lambda-calculus-like language augmented with
features to represent the essence of Python (such as classes and
dictionaries), and should thus be familiar to its potential users.

Because desugaring converts Python surface syntax to the core
language, when it is composed with an interpreter for @(lambda-py)
(which is easy to write), we have another implementation of Python. We
can then ask how this implementation compares with the traditional
CPython implementation, which represents a form of ground truth. By
carefully adjusting the core and desugaring, we have achieved high
fidelity with CPython. Therefore, users can built tools atop
@(lambda-py), confident that they are capturing the language in all
its glory.

In the course of creating this high-fidelity semantics, we have also
identified some peculiar corners of the language, including
non-orthogonal features. In particular, scope proves to be
non-trivial and interacts with perhaps unexpected features. Our
exposition focuses on these aspects.

In sum, this paper makes the following contributions:
@itemlist[

  @item{a @emph{core semantics} for Python, dubbed @(lambda-py), which
  is defined as a reduction semantics using PLT Redex [CITE];}

  @item{an @emph{interpreter}, dubbed @(lambda-interp), implemented in
  800LOC of Racket, that has been tested against the Redex model;}

  @item{a @emph{desugaring} translation from Python programs to @(lambda-py),
  implemented in Racket;}

  @item{a demonstration of @emph{conformance} of the composition of
  desugaring with @(lambda-interp) to a real Python implementation; and,}

  @item{@emph{insights} gained from this process.}

]

Presenting the semantics in full is neither feasible, given space
limits, nor especially enlightening. We instead focus on the parts
that are important or interesting. We first give an overview of
@(lambda-py)'s value and object model. We then introduce desugaring by
showing how several interation and overloading patterns can be
implemented atop the object model. We then discuss generators,
classes, and their interaction with scope. Finally, we describe the
results of testing our semantics against CPython.

@section{Warmup: A Quick Tour of @(lambda-py)}

@figure["f:exprs" (elem (lambda-py) " expressions")]{
  @(with-rewriters
    (lambda () (render-language λπ #:nts '(e t v v+undef opt-var mval Σ ref))))
}

@figure*["f:skull" "Handling undefined identifiers"]{
  @(lp-reduction '(E-LetLocal E-GetVar E-GetVarUndef))
}

We
provide an overview of the object model of @(lambda-py) and Python, some of the
basic operations on objects, and the shape of our small step semantics.  This
introduces notation and concepts that will be used later in the document to
explain the harder parts of Python's semantics.

@subsection{@(lambda-py) Values}

@Figure-ref["f:exprs"] shows all the values and expressions @(lambda-py).  The
metavariables @(lp-term v) and @(lp-term val) range over the values of the
language.  All values in @(lambda-py) are either objects, written as
triples in @(lp-term 〈〉), or references to entries in the store Σ, written
@(lp-term (pointer-val ref)).

Each @(lambda-py) object is written as a triple of one of the forms:
@centered{
  @(lp-term (obj-val v mval ((string ref) ...)))
  @(newline)
  @(lp-term (obj-val x mval ((string ref) ...)))
}
These objects have their @emph{class} in the first position, their primitive
content in the second, and the dictionary of string-indexed fields that they
holds in the third.  The class value is either another @(lambda-py) value or a
lazily-evaluated identifier pointing to an environment of built-in classes.
The primitive content, or @emph{meta-val},
position holds special kinds of builtin data, of which
there is one per builtin type that @(lambda-py) models: numbers, strings, the
distinguished @(lp-term (meta-none)) value, lists, tuples, sets, classes, and
functions.

The distinguished @(lp-term (undefined-val)) form represents values on the heap
that are uninitialized, and whose lookup should raise an exception.
@Figure-ref["f:skull"] shows the behavior of lookup in heaps Σ for values and
for @(lp-term (undefined-val)).  The @(lp-term let) form is the only expression
that handles @(lp-term (undefined-val)), allocating a location for it in the
store.  An assignment must be performed to change the store to a value at that
location before a lookup will succeed.  This notion of undefined locations will
come into play heavily when we discuss scope [REF].

Python programs cannot manipulate object values directly; rather, they always
work with references to objects.  Thus, many of the operations in @(lambda-py)
involve the heap, and few are purely functional.  As an example of what such an
operation looks like, take constructing a list. This takes the values
that should populate the list, store them in the heap, and return a
pointer to the newly-created reference:
@centered[
  @(lp-reduction '("E-List"))
]
E-List is a good example for understanding the shape of evaluation in
@(lambda-py).  The general form of the reduction relation is over expressions
@(lp-term e), global environments @(lp-term ε), and heaps @(lp-term Σ):
@centered[
  @(lp-term (e ε Σ)) @(arrow->pict '-->) @(lp-term (e ε Σ))
]
In the E-List rule, we also use evaluation contexts @(lp-term E) to
enforce an order of operations and eager calling semantics.  This is a
standard application of Felleisen-Hieb-style small-step semantics [CITE].
Saliently, a new list value is populated from the list expression via the
@(lp-term alloc) metafunction, this is allocated in the store, and the
resulting value of the expression is a pointer @(lp-term ref_new) to
that new list.

Similar rules for objects in general, tuples, and sets are shown in
@figure-ref["f:steps-values"].  Lists, tuples, and sets are given their own
expression forms because they need to evaluate all of their sub-expressions and
have corresponding evaluation contexts.

@figure["f:steps-values" (elem (lambda-py) " reduction rules for creating objects")]{
  @(lp-reduction '("E-Object" "E-Tuple" "E-Set" "E-List"))
}

@subsection{Accessing Built-in Values}

@figure*["f:delta" (elem "A sample of " (lambda-py) " primitives")]{
  @(lp-metafunction δ '(0 1 2 3))
}

@figure["f:references" (elem (lambda-py) " reduction rules for references")]{
  @(lp-reduction '("E-Fetch" "E-Set!" "E-Alloc"))
}

Now that we've created a list, we should be able to perform some operations on
it, like look up its elements.  @(lambda-py) defines a number of builtin
primitives that model Python's internal operators for manipulating data, and
these are used to access the contents of a given object's @(lp-term mval).  We
formalize these builtin primitives in a metafunction δ.  A few selected cases
of the δ function are shown in @figure-ref["f:delta"].  This metafunction lets
us, for example, look up values on builtin lists:
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
@figure-ref["f:references"].  Thus, the real @(lambda-py) program
corresponding to the one above would be:
@centered{
  @(lp-term (prim "list-getitem" ((fetch (list (id %list local) ((obj-val %str (meta-str "first-elt") ()))))
                                  (fetch (object (id %int local) (meta-num 0))))))
}
Similarly, we can use @(lp-term set!) and @(lp-term alloc) to update the values
in lists, and to allocate the return values of primitive operations.  We
desugar to patterns like the above from Python's actual surface operators for
accessing the elements of a list in expressions like @code{mylist[2]}.

@subsection{Updating and Accessing Fields}

So far, the dictionary part of @(lambda-py) objects have always been empty.
Python does, however, support arbitrary field assignments on objects.  The
expression
@centered{
  @(lp-term (assign (get-field e_obj str_f) := e_val))
}
has one of two behaviors, defined in @figure-ref["f:simple-objs"].  Both
behaviors work over references to objects, not over objects themselves, in
contrast to @(lp-term δ).  If @(lp-term str_f) is a string that is already a
member of @(lp-term e_obj), that field is imperatively updated with @(lp-term
e_val).  If the string is not present, then a new field is added to the object,
with a newly-allocated store position, and the object's location in the heap is
updated.

The simplest rule for accessing fields simply checks in the object's dictionary
for the provided name and returns the appropriate value, shown in E-GetField in
@figure-ref["f:simple-objs"].  E-GetField also works over reference values,
rather than objects directly.  [FILL update to meta-vals that contain strings
and not literal strings]

@figure*["f:simple-objs" @elem{Simple field access and update in @(lambda-py)}]{
  @(lp-reduction '("E-AssignUpdate" "E-AssignAdd" "E-GetField"))
}

@subsection{First-class Functions}

@figure*["f:functions" @elem{Evaluating function expressions}]{
  @(lp-reduction '("E-Fun"))
}

Functions in Python are objects like any other.  They are defined with the
keyword @code{def}, which produces a callable object with a mutable set of
fields, whose class is the built-in @(lp-term function) class.  For example a
programmer is free to write:
@verbatim{

def f():
  return 22

f.x = -1
f() # evaluates to 22

}
We model functions as just another kind of object value, with a type of
@(lp-term mval) that looks like the usual functional λ: 

@centered{
  @(lp-term (meta-closure (λ (x ...) opt-var e)))   
}

The only deviation from the norm is that we have an explicit optional position
for a varargs identifier: if @(lp-term opt-var) is of the form @(lp-term (y)),
then if the function is called with more arguments than are in its list of
variables @(lp-term (x ...)), they are allocated in a new tuple and bound to
@(lp-term y) in the body.

@subsection{Loops, Exceptions, and Modules}

We defer a full explanation of the terms in @figure-ref["f:exprs"], and the
entire reduction relation, to the appendix [REF].  This includes a mostly-routine
encoding of control operators via special evaluation contexts, and a mechanism
for loading new code via modules.  We continue here by focusing on some of the
cases in the semantics that are unique in Python, and how we model them with
@(lambda-py).

@section{Classes, Methods, and Pythonic Desugarings}

Python has a featureful class system with first-class methods, implicit
reciever binding, multiple inheritance, and more.  In this section we discuss
what parts of the class system we put in @(lambda-py), and which parts
we chose to eliminate by desugaring.

@subsection{Field Lookup in Classes}

In the last section, we touched on field lookup in an object's local
dictionary, and didn't discuss the purpose of the class position at all.
When an object lookup @(lp-term (get-field (obj-val val_c mval d) str))
doesn't find @(lp-term str) in the local dictionary @(lp-term d), it defers
to a lookup algorithm on the class value @(lp-term val_c).  More
specifically, it uses the @(lp-term "__mro__") (short for @emph{method
resolution order}) field of the class to
determine which class dictionaries to search for the field.  This field is 
visible to the Python programmer:
@verbatim{
class C(object):
  pass # a class that does nothing

print(C.__mro__)
# (<class '__main__.C'>, <class 'object'>)
}

Field lookups on objects whose class value is @(lp-term C) will first look in
the dictionary of @(lp-term C), and then in the dictionary of the built-in
class @(lp-term object).  We define this lookup algorithm within @(lambda-py)
as @(lp-term class-lookup), shown in @figure-ref["f:lookup-class"] along with
the reduction rule for field access that uses it.

@figure*["f:lookup-class" @elem{Class lookup}]{
  @para{
    @(lp-reduction '("E-GetField-Class"))
  }
  @para{
    @(lp-metafunction class-lookup #f)
  }
  @para{
    @(lp-metafunction class-lookup-mro #f)
  }
}

This rule allows us to model field lookups that defer to a superclass (or
indeed, a list of them).  But programmers don't explicitly define
@(lp-term "__mro__") fields; rather, they use higher-level language
constructs to build up the inheritance hierarchy the instances eventually use.


@subsection{Desugaring Classes}

Most Python programmers use the special @code{class} form to create classes in
Python.  However, @code{class} is merely syntactic sugar for a use of the
builtin Python function
@code{type}.@note{http://docs.python.org/3/library/functions.html#type} The
documentation states explicitly that the two following forms [sic] produce
@emph{identical} type objects:
@verbatim{
class X:
     a = 1

X = type('X', (object,), dict(a=1))
}
This means that to implement classes, we merely need to understand the built-in
function @code{type}, and how it creates new classes on the fly.  Then it is a
simple matter to desugar class forms to this function call.

The implementation of @code{type} creates a new object value for the class,
allocates it, sets the @(lp-term "__mro__") field to be the computed
inheritance graph,@note{This uses an algorithm that is implementable in
pure Python: http://www.python.org/download/releases/2.3/mro/.} and sets the
fields of the class to be the bindings in the dictionary.  We elide some of the
verbose detail in the iteration over @(lp-term (id dict local)) by using the
@(lp-term for) syntactic abbreviation, which expands into the desired iteration:
@centered{
  @(lp-term
    (assign (id %type global) :=
      (fun (classname bases dict)
        (let (newcls local = (alloc (obj-val %type (meta-class classname) ()))) in
          (seq
          (assign (get-field (id newcls local) "__mro__") :=
            (builtin-prim "type-buildmro" (cls bases)))
          (seq
          (for (key elt) in (app (get-field (id dict local) "__items__") ())
            (assign (get-field (id newcls local) (id key local)) := (id elt local)))
          (return (id newcls local))))))))
}
This function, along with the built-in @code{type}
class, suffices for bootstrapping the object system in @(lambda-py).

@subsection{Pythonic Patterns}

Pythonic objects can have a number of so-called @emph{magic fields} that allow
for overriding the behavior of built-in syntactic forms.  These magic fields
can be set anywhere in an object's inheritance hierarchy, and provide a lot of
the flexibility for which Python is well-known.

For example, the field accesses that Python programmers write are not directly
translated to the rules in @(lambda-py).  Even the execution of @code{o.x}
depends heavily on its inheritance hierarchy.  This
program desugars to:
@centered{
@(lp-term (app (get-field (id o local) "__getattribute__") ((id o local) (obj-val %str (meta-str "x") ()))))
}
For objects that don't override the @(lp-term "__getattribute__") field, the
built-in object class's implementation does more than simply look up the
@(lp-term "x") property using the field access rules we presented earlier.
Python allows for attributes to implement special accessing functionality via
@emph{properties},@note{http://docs.python.org/3/library/functions.html#property}
which can cause special functions to be called on property access.  The
@(lp-term "__getattribute__") function of @(lp-term (id object local)) checks
if the value of the field it accesses is a property, and if it is, calls its
@(lp-term "__get__") method:
@centered{
@(lp-term
  (assign (get-field object "__getattribute__") :=
    (fun (obj field)
      (let (value local = (get-attr obj field)) in
        (if (app (id is-property? global) ((id value local)))
            (return (app (get-field (id value local) "__get__") ()))
            (return (id value local)))))))
}

This pattern is used to implement a myriad of features.  For example, when
accessing function values on classes, the @(lp-term "__get__") method of the
function implicitly binds the self argument:
@verbatim{
class C(object):
  def f(self):
    return self

c = C() # constructs a new C instance
g = c.f # accessing c.f creates a 
        # method object closed over c
g() is c # evaluates to True

# We can also bind a self value manually:
self_is_5 = C.f.__get__(5)
self_is_5() # evaluates to 5
}
Thus, very few object-based primitives are needed to create
static class methods and instance methods.

Python has a number of other special method names that can be overridden to
provide specialized behavior.  @(lambda-py) tracks Python this regard; it desugars
surface expressions into calls to methods with particular names, and provides
built-in implementations of those methods for arithmetic, dictionary access,
and a number of other operations.  Some examples:
@nested{

@code{o[x]} @emph{ desugars to... } @(lp-term (app (get-field (id o local) "__getitem__") ()))

@code{x + y} @emph{ desugars to... } @(lp-term (app (get-field (id o local) "__add__") ((id y local))))

@code{f(x)} @emph{ desugars to... } @(lp-term (app (get-field (id f local) "__call__") ((id x local))))

}

With the basics of @code{type} and object lookup in place, getting all of these
operations right is just a matter of desugaring to the right method calls, and
providing the right built-in versions. numbers to handle the base cases
for primitive values.  This is what we do for much of our desugaring to
@(lambda-py) and, though it is labor-intensive, it is also the
straightforward part of the process.

@section{Python, the Hard Parts}

Not all of Python has a semantics as straightforward as that presented so far.
Python has a unique notion of scope, with new scope operators added in Python 3 to
provide some features of more traditional static scoping.  It also has powerful
control flow constructs, notably generators. We now begin examining these in detail.

@subsection{Generators}

Python has a built-in notion of @emph{generators}, which provide a control-flow
construct, @code{yield}, that can implement lazy or generative sequences and
coroutines.  The programmer interface for creating a generator in Python is
straightforward: any function definition that uses the @code{yield} keyword in
its body is automatically converted into an object with a generator
interface.  To illustrate the easy transition from function to generator,
consider this simple program:
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
When called, this function always returns @code{1}.

Changing @code{return} to @code{yield}
turns this into a generator. As a result, applying @code{f()} no longer
immediately evaluates the body of the function; instead, it creates an 
object whose @code{next} method evaluates the body until the next
@code{yield} statement, stores its state for later resumption, and
returns the yielded value:
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

Contrast this with the following program, which seems to perform a 
simple abstraction over the process of yielding:
@verbatim{
def f():
  def do_yield(n):
    yield n
  x = 0
  while True:
    x += 1
    do_yield(x)
}
Invoking @code{f()} results in an @emph{infinite loop}. That is because
Python strictly converts only the innermost function with a @code{yield}
into a generator, so only @code{do_yield} is a generator. Thus, the
generator stores only the execution context of @code{do_yield}, not of
@code{f}.

The experienced linguist will immediately see what is going
on. Clearly, Python has made a design decision to store only
@emph{local} continuations.  This design can be justified on the
grounds that converting a whole program to continuation-passing style
(CPS) can be onerous, is not modular, can impact performance, and
depends on the presence of tail-calls (which Python does not have). In
contrast, it is easy to envision a translation strategy that performs
only a local conversion to CPS (or, equivalently, stores the local
stack frames) while still presenting a continuation-free interface to
the rest of the program.

From the perspective of our semantics, this offers a boon: we don't
need to use a CPS-style semantics for the whole language!
Furthermore, generators can be handled by a strictly local rewriting
process that can be handled by desugaring. That is, generators can be
handled in the core language by reifying them into into first-class
functions and applications and using a little state to record which
function is the continuation of the @code{yield} point. Thus,
generators seem to fit perfectly with our desguaring strategy.

@subsection{A (Local) CPS Transformation for Python}

When converting programs to CPS, we take operators that can cause
control-flow and reify each into a continuation function and
appropriate application. These operators include simple sequences,
loops combined with @code{break} and @code{continue}, and
@code{try-except} and @code{try-finally} combined with @code{raise}
(generators cannot use @code{return}).

Our CPS transformation turns every expression into a function that accepts an
argument for each of the above control operators, and turns uses of control
operators into applications of the appropriate continuation inside the
function.  By passing in different continuation arguments, the caller of the
resulting function has complete control over the behavior of control operators.
For example, we might rewrite a @code{try-except} block from
@verbatim{

try:
  raise Exception()
except e:
  print(e)

}
to
@verbatim{

def except_handler(e): print(e)
except_handler(Exception())

}

In the case of generators, rewriting @code{yield}
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
g.next() # evaluates to 1
g.next() # evaluates to 2
g.next() # throws "StopIteration"
}
would be rewritten to something like:@note{This being a sketch, we
have taken some liberties for simplicity.}
@verbatim{
def f():

  def yielder(val, rest_of_function):
    next.to_call_next = rest_of_function
    return val

  def next():
    return next.to_call_next()

  def done(): raise StopIteration()
  def start():
    x = 1
    def rest():
      x += 1
      return yielder(x, done)
    return yielder(x, rest)

  next.to_call_next = start

  return { 'next' : next }

g = f()
g.['next']() # evaluates to 1
g.['next']() # evaluates to 2
g.['next']() # throws "StopIteration"
}
We build the @code{yielder} function, which takes a value, which it returns
after storing a continuation argument in the @code{to_call_next} field.  The
@code{next} function always returns the result of calling this stored value.
Each @code{yield} statement is rewritten to put everything after it into a new
function definition, which is passed to the call to @code{yielder}. In
other words, this is the canonical CPS transformation, applied in the
usual fashion.

This rewriting is well-intentioned but does not work.  If this
program is run under Python, it results in an error:
@verbatim{
    x += 1
UnboundLocalError: local variable 'x'
                   referenced before assignment
}
This is because Python creates a @emph{new scope} for each function
definition, and assignments within that scope create new variables.
In the body of @code{rest}, the assignment @code{x += 1} refers to a
new @code{x}, not the one defined by @code{x = 1} in @code{start}.  This
runs counter to traditional notions of functions that can close over
mutable variables.  And in general, with multiple assignment
statements and branching control flow, it is entirely unclear whether a
CPS transformation to Python function definitions can work.

The lesson from this example is that the @emph{interaction} of non-traditional
scope and control flow made a traditional translation
not work.  The straightforward CPS solution, which doesn't require
extending the number of concepts in the language, is inexpressible in Python
due to the mechanics of variable binding.  We'll move on to describing how we
can express Pythonic scope in a more traditional lexical model, and
later [CITE] we
will return to a CPS transformation that does work for Python's generators.

@section{Scope}

Python has a rich notion of scope, with several types of variables and implicit
binding semantics that depend on the block structure of the program.  Most
identifiers are @code{local}; this includes function parameters and variables
defined with the @code{=} operator.  There are also @code{global} and
@code{nonlocal} variables, with their own special semantics within closures,
and interaction with classes.  Our core contribution to explaining Python's
scope is to give a desugaring of the @code{nonlocal} and @code{global}
keywords, along with implicit @code{local}, @code{global} and @code{instance}
identifiers, into traditional lexically scoped closures. 
Global scope is still handled specially, since it exhibits a form of dynamic
scope that isn't straightforward to capture with traditional
let-bindings.@note{We actually exploit this dynamic scope in bootstrapping
Python's object system [REF].}

We proceed by describing Python's handling of scope for local variables, the
extension to @code{nonlocal}, and the interaction of both of these features with
classes.

@subsection{Declaring and Updating Local Variables}

In Python, the operator @code{=} performs local variable binding:
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

Crucially, there is @emph{no syntactic difference} between a statement
that updates a variable and one that initially binds it.  Because
bindings can also be introduced inside branches of conditionals, it
isn't statically determinable if a variable will be defined at certain
program points.  Note also that variable declarations are not scoped
to all blocks---here they are scoped to function definitions:
@verbatim{
def f(y):
 if y > .5: x = 'big'
 else : pass
 return x

f(0) # throws an exception
f(1) # evaluates to "big"
}

@subsubsection{Desugaring for Local Scope}

Handling simple declarations of variables and updates to variables is
straightforward to translate into a lexically-scoped language.  @(lambda-py)
has a usual @code{let} form that allows for lexical binding.  In desugaring, we
scan the body of the function and accumulate all the variables on the left-hand
side of assignment statements in the body.  These are let-bound at the top of
the function to the special @(lp-term (undefined-val)) form, which evaluates to an
exception in any context other than a @code{let}-binding context ([REF section]}.  We use
@code{x := e} as the expression form for variable assignment, which is not a
binding form in the core.  So in @(lambda-py), the example above rewrites to:

@centered{
  @(lp-term
    (let (f global = (undefined-val)) in
      (seq
      (assign f :=
        (fun (y) (no-var)
         (let (x local = (undefined-val)) in
          (seq
          (if (builtin-prim "num>" ((id y local) (object %float (meta-num 0.5))))
              (assign x := (object %str (meta-str "big")))
              none)
          (return (id x local))))
         (no-var)))
      (seq
      (app (id f global) ((object %float (meta-num 0))))
      (app (id f global) ((object %float (meta-num 1))))))))
}

In the first application (to 0), the assignment will never happen, and the
attempt to look up the @(lp-term (undefined-val))-valued @(lp-term x) in the
return statement will fail with an exception.  In the second application, the
assignment in the then-branch will change the value of @(lp-term x) in the
store to a non-@(lp-term (undefined-val)) string value, and the string
@(lp-term "big") will be returned.

The algorithm for desugaring scope so far is thus:
@itemlist[

  @item{For each function body:
  
    @itemlist[
      @item{Collect all variables on the left-hand side of @(lp-term =) in a set @emph{locals}, stopping at other function boundaries,}

      @item{For each variable @(lp-term var) in @emph{locals}, wrap the
      function body in a @(lp-term let)-binding of @(lp-term var) to @(lp-term
      (undefined-val)).}
    ]
  }

]
This strategy works for simple assignments that may or may not occur within a
function, and maintains lexical structure for the possibly-bound variables in a
given scope.  Unfortunately, this covers only the simplest cases of Pythonic scope.


@subsection{Closing Over Variables}

Bindings from outer scopes can be @emph{seen} by inner scopes:
@verbatim{
def f():
  x = 'closed-over'
  def g()
    return x
  return g

f()() # evaluates to 'closed-over'
}
However, since @code{=} defines a new local variable, one cannot close over a
variable and mutate it with the constructs we've seen so far; @code{=} simply
defines a new variable with the same name:
@verbatim{
def g():
  x = 'not affected by h'
  def h():
    x = 'inner x'
    return x
  return (h(), x)

g() # evaluates to
    # ('inner x', 'not affected by h')
}
This is mirrored in our desugaring:
each function adds a new let-binding
inside its own body, shadowing any bindings from outside.  This was the
underlying problem with the attempted CPS translation from the last section,
highlighting the consequences of using the same syntactic form for both
variable binding and update.

Closing over a mutable variable is, however, a common and useful pattern.  Perhaps
recognizing this, Python added a new keyword in Python 3.0 to
allow this pattern, called @code{nonlocal}.  A function
definition can include a @code{nonlocal} declaration at the top, which allows
mutations within the function's body to refer to variables in enclosing scopes
on a per-variable basis.  If we add such a declaration to the previous example,
we get a different answer:
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
The @code{nonlocal} declaration allows the inner assignment to @code{x} to
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

Thus, the presence or absence of a @code{nonlocal} declaration can change an
assignment statement from a binding occurrence of a variable to an assigning
occurence.  We augment our algorithm for desugaring scope to reflect this:
@itemlist[

  @item{For each function body:
  
    @itemlist[
      @item{Collect all variables on the left-hand side of @(lp-term =) in a set @emph{locals}, stopping at other function boundaries,}

      @item{Let @emph{locals'} be @emph{locals} with any variables in
      @code{nonlocal} declarations removed,}

      @item{For each variable @(lp-term var) in @emph{locals'}, wrap the
      function body in a @(lp-term let)-binding of @(lp-term var) to @(lp-term
      (undefined-val)).}
    ]
  }

]
Thus the above program would desugar to the following, which @emph{does not}
let-bind @(lp-term x) inside the body of the function assigned to @(lp-term h).
@centered{
  @(lp-term
    (let (g global = (undefined-val)) in
      (seq
      (assign g :=
        (fun ()
         (let (x local = (undefined-val)) in
          (let (h local = (undefined-val)) in
            (seq
            (assign x := (obj-val %str (meta-str "not affected by h") ()))
            (seq
            (assign h :=
              (fun ()
                (seq
                (assign x := (obj-val %str (meta-str "inner x") ()))
                (return (id x local)))))
            (return (tuple %tuple ((app (app (id h local) ()) ()) (id x local))))))))))
      (app (id g local) ()))))

}
The assignment to @(lp-term x) inside the body of @(lp-term h) behaves as a
typical assignment statement in a closure-based language like Scheme, ML, or
JavaScript: it mutates the let-bound @(lp-term x) defined in @(lp-term g).

@subsection{Global vs Local Unbound Errors}

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

}

@subsection{Classes and Scope}

We've covered some subtleties of scope for local and nonlocal variables and
their interaction with closures.  What we've presented so far would be enough
to recover lexical scope for a CPS transformation for generators if function
bodies contained only other functions.  However, it turns out that we observe a
different closure behavior for variables in a class definition than we do for
variables elsewhere in Python, and we must address classes to wrap up the story
on scope.

@figure["f:classexample" "An example of class and function scope interacting"]{
@verbatim{
def f(x, y):
  print(x); print(y); print("")
  class c:
    x = 4
    print(x); print(y)
    print("")
    def g(self):
      print(x); print(y); print(c)
  return c

f("x-value", "y-value")().g()

# produces this result:

x-value
y-value

4
y-value

x-value
y-value
<class '__main__.c'>

}
}

@figure*["f:class-scope" "Interactions between class bodies and function scope"]{
  @class-scope
}

Consider the example in @figure-ref["f:classexample"].  Here we observe an
interesting phenomenon: in the body of @code{g}, the value of the variable
@code{x} is @emph{not} @code{4}, the value of the most recent apparent
assignment to @code{x}.  In fact, the body of @code{g} seems to "skip" the
scope in which x is bound to 4, instead closing over the outer scope in which
@code{x} is bound to @code{"x-value"}.  At first glance this does not appear to
be compatible with our previous notions of Pythonic closures.  We will see,
however, that the correct desugaring is capable of expressing the semantics of
scope in classes within the framework we have already established for dealing
with Python's scope.  

@subsubsection{Desugaring classes}

Desugaring classes is substantially more complicated than handling simple local
and nonlocal cases.  Consider the example from @figure-ref["f:classexample"],
stripped of print statements: 

@verbatim{

def f(x, y):
  class c:
    x = 4
    def g(self): pass
  return c
f("x-value", "y-value")().g()

}

In this example, we have three local scopes: the body of the function f, the
body of the class definition c, and the body of the function g.  The scopes of
@code{c} and @code{g} close over the same scope as @code{f}, but have distinct,
non-nesting scopes themselves.  @Figure-ref["f:class-scope"] shows the
relationship graphically.  Algorithmically, we add new steps to scope
desugaring:


@itemlist[

  @item{For each function body:
  
    @itemlist[

      @item{For each nested class body:
        @itemlist[
          
          @item{Collect all the function definitions within the class body.
          Let the set of their names be @(lp-term defnames) and the set of the
          expressions be @(lp-term defbodies),}

          @item{Generate a fresh variable @(lp-term deflifted) for each variable in
          @(lp-term defnames).  Add assignment statements to the function body just
          before the class definition assigning each @(lp-term deflifted) to the
          corresponding expression in @(lp-term defbodies),}

          @item{Change each function definition in the body of the class to
          @(lp-term (assign defname := (id deflifted local)))}
          

        ]
      }

      @item{Collect all variables on the left-hand side of @(lp-term =) in a set @emph{locals}, stopping at other function boundaries,}

      @item{Let @emph{locals'} be @emph{locals} with any variables in
      @code{nonlocal} declarations removed,}

      @item{For each variable @(lp-term var) in @emph{locals'}, wrap the
      function body in a @(lp-term let)-binding of @(lp-term var) to @(lp-term
      (undefined-val)).}
    ]
  }

]

Recalling that the instance variables of a class desugar roughly to assignments
to the class object itself, the function would desugar to the following:

@centered{
  @(lp-term
    (let (f local = (undefined-val)) in
      (assign (id f local) :=
        (fun (x y)
          (let (extracted-g local = (undefined-val)) in
          (let (c local = (undefined-val)) in
            (seq
            (assign (id extracted-g local) := (fun () none))
            (seq
            (assign (id c local) := (class "c"))
            (seq
            (assign (get-field (id c local) "x") := (obj-val %int (meta-num 4) ()))
            (seq
            (assign (get-field (id c local) "g") := (id extracted-g local))
            (return (id c local))))))))))))
}

This achieves our desired semantics: the bodies of functions defined in the
class @code{C} will close over the @code{x} and @code{y} from the function
definition, and the statements written in c-scope can still see those bindings.

@subsubsection{Instance Variables}

When we introduced classes [REF] we said that there is no apparent difference
between classes that introduce identifiers in their body and classes that
introduce identifiers by field assignment.  That is,
@verbatim{
class c:
 x = 3
}
and 
@verbatim{
class c: pass
c.x = 3
}
will produce the same class.  We do, however, have to still account for
@emph{uses} of the instance variables inside the class body, which are referred
to with the variable name, not with a field lookup like @code{c.x}.  This
observation is the key insight into @(lambda-py)'s treatment of instance
variables.  We perform a final desugaring step for instance variables, where we
let-bind them in a new scope just for evaluating the class body, and desugar
each instance variable assignment into both a class assignment and an
assignment to the variable itself:
@centered{
  @(lp-term
    (let (f local = (undefined-val)) in
      (assign (id f local) :=
        (fun (x y)
          (let (extracted-g local = (undefined-val)) in
          (let (c local = (undefined-val)) in
            (seq
            (assign (id extracted-g local) := (fun () none))
            (seq
            (assign (id c local) := (class "c"))
            (seq
              (let (g local = (undefined-val)) in
              (let (x local = (undefined-val)) in
                (seq
                (assign (get-field (id c local) "x") := (obj-val %int (meta-num 4) ()))
                (seq
                (assign (id x local) := (obj-val %int (meta-num 4) ()))
                (seq
                (assign (get-field (id c local) "g") := (id extracted-g local))
                (assign (id g local) := (id extracted-g local)))))))
            (return (id c local)))))))))))
}
We have now covered Python's class semantics:
function bodies do not close over the class body's scope, class bodies
create their own local scope, statements in class bodies are executed sequentially,
and definitions/assignments in class bodies result in the creation of class
members.  The @code{nonlocal} and @code{global} keywords do not require special treatment 
beyond what we have outlined here, even when present in class bodies.

@subsection{Generators Redux}

@figure["f:generators" "The desugaring of generators"]{
@verbatim{def f(x ...): body-with-yield}

@emph{desugars to...}

@(lp-term
  (fun (x ...)
    (let (done local = 
      (fun () (raise (app (id StopIteration global) ())))) in
    (let (initializer local = 
      (fun (self)
        (let (end-of-gen-normal local = 
          (fun (last-val)
            (seq
            (assign (get-field (id self local) "__next__") := (id done local))
            (raise (app (id StopIteration global) ()))))) in
        (let (end-of-gen-exn local = 
          (fun (exn-val)
            (seq
            (assign (get-field (id self local) "__next__") := (id done local))
            (raise exn-val)))) in
        (let (unexpected-case local =
          (fun (v)
            (raise (app (id SyntaxError global) ())))) in
        (let (resumer local =
          (fun (yield-send-value)
            (return
              (app (cps-of body-with-yield)
                   ((id end-of-gen-normal local)
                    (id unexpected-case local)
                    (id end-of-gen-exn local)
                    (id unexpected-case local)
                    (id unexpected-case local)))))) in
        (assign (get-field (id self local) "___resume") := (id resumer local)))))))) in
      (app (id %generator global) ((id initializer local)))))))

@emph{where...}

@verbatim{
class %generator(object):
    def __init__(self, init):
        init(self)

    def __next__(self, *args):
        if len(args) > 0:
            return self.___resume(args[0])
        else:
            return self.___resume(None)

    def __iter__(self):
        return self
        
    def __list__(self):
        return [x for x in self]
}
}

With the transformation to a lexical core in hand, we can return to our
discussion of generators, and their implementation with a local CPS
transformation.

To implement generators, we first desugar Python down to a version of
@(lambda-py) with an explicit @code{yield} statement, passing @code{yields}
through unchanged.  As the final stage of desugaring, we identify functions
that contain @code{yield}, and convert them to generators via local CPS.  We
show the desugaring machinery @emph{around} the CPS transformation in
@figure-ref["f:generators"].  To desugar them, in the body of the function we
construct a generator object and store the CPS-ed body as a @code{___resume}
attribute on the object. The @code{__next__} method on the generator, when
called, will call the @code{___resume} closure with any arguments that are
passed in. To handle yielding, we desugar the core @code{yield} expression to
update the @code{___resume} attribute to store the current normal continuation,
and then @code{return} the value that was yielded.

Matching Python's operators for control flow, we have five continuations, one
for the normal completion of a statement or expression going onto the next, one
for a @code{return} statement, one each for @code{break} and @code{continue},
and one for the exception throwing @code{raise}.  This means that each CPSed
expression becomes an anonymous function of five arguments, and can be passed
in the appropriate behavior for each control operator.

We use this configurability to handle two special cases of generators:

@itemlist[

  @item{Exceptions thrown during execution that are uncaught by the generator}

  @item{Running the generator to completion}

]

In the latter case, the generator raises a @code{StopIteration} exception. We
encode this by setting the initial ``normal'' continuation to a function that
will update @code{___resume} to always raise @code{StopIteration}, and then to
raise that exception. Thus, if we evaluate the entire body of the generator, we
will pass the result to this continuation, and the proper behavior will occur.

Similarly, if an uncaught exception occurs in a generator, the generator will
raise that exception, and any subsequent calls to the generator will result in
@code{StopIteration}. We handle this by setting the initial @code{raise}
continuation to be code that updates @code{___resume} to always raise
@code{StopIteration}, and then we raise the exception that was passed to the
continuation. Since each @code{try} block in CPS installs a new exception
continuation, if a value is passed to the top-level exception handler it means
that the exception was not caught, and again the expected behavior will occur.

@section{Perspective}

Existing editors use heuristics to figure out if variables could be bound to
particular instances.@note{http://wingware.com/doc/edit/points-of-use}
This makes variable naming refactorings less precise than in say, an IDE for
Java, requiring developer intervention to specify which instances should be
renamed.  We provide a more precise account of scope that would enable
correct points-of-use analysis for lexical variables in Python.

@itemlist[

  @item{Many overloadings and implicit method calls are nice}

  @item{However, there are corner cases, and they have to do with the thing stuck in programmers' face: scope}

  @item{Unclear if scope behavior is a product of growing up from a dynamic language or intentional}

  @item{All the values of Python, all the scope of something saner, would be a really nice thing to have}
]

@section{Engineering & Evaluation}

Python
3.2.3.@note{http://www.python.org/getit/releases/3.2.3/, released April 2012}

There are two properties we evaluated for @(lambda-py).

Property 1: @emph{desugar} is a total function:

@centered{
  ∀ p ∈ Python, ∃ @(lp-term e) ∈ @(lambda-py) such that @emph{desugar}(p) = @(lp-term e)
}

Property 2: @emph{desugar} composed with → is accurate:

@centered{
  ∀ p,v ∈ Python, if eval(p) = v
  
  then @emph{desugar}(p) →* @emph{desugar}(v)
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

RELATED WORK

- the swedish(?) thesis
- arjun's \JS

@;{Acknowledgments:
- Ben Lerner for title
- NSF and Google for funding
- Brown for hosting
- redex
}
