#lang scribble/sigplan @10pt

@(require
  scriblib/footnote
  scribble/manual
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
@title{Python: The Full Monty@(linebreak)
  @smaller{A Tested Semantics for the}
  @(linebreak)
  @smaller{Python Programming Language}
}

@authorinfo["Joe Gibbs Politz" "Providence, RI, USA" "joe@cs.brown.edu"]
@authorinfo["Alejandro Martinez" "La Plata, BA, Argentina" "amtriathlon@gmail.com"]
@authorinfo["Matthew Milano" "Providence, RI, USA" "matthew@cs.brown.edu"]
@authorinfo["Sumner Warren" "Providence, RI, USA" "jswarren@cs.brown.edu"]
@authorinfo["Daniel Patterson" "Providence, RI, USA" "dbpatter@cs.brown.edu"]
@authorinfo["Junsong Li" "Beijing, China" "ljs.darkfish@gmail.com"]
@authorinfo["Anand Chitipothu" "Bangalore, India" "anandology@gmail.com"]
@authorinfo["Shriram Krishnamurthi" "Providence, RI, USA" "sk@cs.brown.edu"]

@;{NOTE(joe 1 Aug 2013): This relies on adding the right text to the
\permission option in racket/collects/scribble/sigplan/sigplanconf.cls:

Permission to make digital or hard copies of all or part of this work for personal or classroom use is granted without fee provided that copies are not made or distributed for profit or commercial advantage and that copies bear this notice and the full citation on the first page. Copyrights for components of this work owned by others than ACM must be honored. Abstracting with credit is permitted. To copy otherwise, or republish, to post on servers or to redistribute to lists, requires prior specific permission and/or a fee. Request permissions from Permissions@acm.org.} 

@copyrightyear{2013}
@conferenceinfo["OOPSLA '13" "October 29-31 2013, Indianapolis, IN, USA"]
@copyrightdata{978-1-4503-2374-1/13/10}

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

@category["J.3" "Life and Medical Sciences" "Biology and Genetics"]

@section[#:tag "s:motivation"]{Motivation and Contributions}

The Python programming language is currently widely used
in industry, science, and education. Because of its popularity
it now has several third-party tools, including analyzers
that check for various potential error patterns@~cite["pylint" "pyflakes" "pep8" "pychecker"].
It also features interactive development environments@~cite["pycharm" "pydev" "wingware"]
that offer a variety of features such as variable-renaming
refactorings and code completion. Unfortunately, all these tools are
unsound: for instance, the simple eight-line program shown in the appendix uses no
``dynamic'' features and confuses the variable renaming feature
of all these environments.

The difficulty of reasoning about Python becomes even more pressing as
the language is adopted in increasingly important domains. For
instance, the US Securities and Exchange Commission has proposed using
Python as an executable specification of financial contracts@~cite["sec-python"], and
it is now being used to script new network paradigms@~cite["pox"].
Thus, it is vital to have a precise semantics available for analyzing
programs and proving properties about them.

This paper presents a semantics for much of Python (@secref["s:engineering"]).
To make the semantics tractable for tools and proofs, we divide
it into two parts: a core language, @(lambda-py), with a
small number of constructs, and a desugaring function that translates
source programs into the core.@note{@emph{Desugaring} is more complex than mere
removal of syntactic sugar.  We blame Arjun Guha for the confusing term.} The
core language is a mostly
traditional stateful lambda-calculus augmented with
features to represent the essence of Python (such as method lookup order and
primitive lists), and should thus be familiar to its potential users.

Because desugaring converts Python surface syntax to the core
language, when it is composed with an interpreter for @(lambda-py)
(which is easy to write), we have another implementation of Python. We
can then ask how this implementation compares with the traditional
CPython implementation, which represents a form of ground truth. By
carefully adjusting the core and desugaring, we have achieved high
fidelity with CPython. Therefore, users can built tools atop
@(lambda-py), confident that they are conformant with the actual language.

In the course of creating this high-fidelity semantics, we have also
identified some peculiar corners of the language.
In particular, scope proves to be
non-trivial and interacts with perhaps unexpected features. Our
exposition focuses on these aspects.

In sum, this paper makes the following contributions:
@itemlist[

  @item{a @emph{core semantics} for Python, dubbed @(lambda-py), which
  is defined as a reduction semantics using PLT Redex@~cite["redex"];}

  @item{an @emph{interpreter}, dubbed @(lambda-interp), implemented in
  700LOC of Racket, that has been tested against the Redex model;}

  @item{a @emph{desugaring} translation from Python programs to @(lambda-py),
  implemented in Racket;}

  @item{a demonstration of @emph{conformance} of the composition of
  desugaring with @(lambda-interp) to a real Python implementation; and,}

  @item{@emph{insights} about Python gained from this process.}

]

Presenting the semantics in full is neither feasible, given space
limits, nor especially enlightening. We instead focus on the parts
that are important or interesting. We first give an overview of
@(lambda-py)'s value and object model. We then introduce desugaring
through classes. We then discuss generators,
classes, and their interaction with scope. Finally, we describe the
results of testing our semantics against CPython.  All of our code
is available online at @url{https://www.github.com/brownplt/lambda-py}.

@section[#:tag "s:warmup"]{Warmup: A Quick Tour of @(lambda-py)}

@figure["f:exprs" (elem (lambda-py) " expressions")]{
  @(with-rewriters
    (lambda () (render-language λπ #:nts '(e t v val e+undef v+undef opt-var mval Σ ref))))
}

@figure*["f:skull" "Let-binding identifiers, and looking up references"]{
  @(lp-reduction '(E-LetLocal E-GetVar E-GetVarUndef))
}

We
provide an overview of the object model of @(lambda-py) and Python, some of the
basic operations on objects, and the shape of our small step semantics.  This
introduces notation and concepts that will be used later to
explain the harder parts of Python's semantics.

@subsection{@(lambda-py) Values}

@Figure-ref["f:exprs"] shows all the values and expressions of @(lambda-py).  The
metavariables @(lp-term v) and @(lp-term val) range over the values of the
language.  All values in @(lambda-py) are either objects, written as
triples in @(lp-term 〈〉), or references to entries in the store Σ, written
@(lp-term (pointer-val ref)).

Each @(lambda-py) object is written as a triple of one of the forms:
@centered{
  @(lp-term (obj-val v mval ((string ref) ...)))
  @(linebreak)
  @(lp-term (obj-val x mval ((string ref) ...)))
}
These objects have their @emph{class} in the first position, their primitive
content in the second, and the dictionary of string-indexed fields that they
hold in the third.  The class value is either another @(lambda-py) value or the
name of a built-in class.
The primitive content, or @emph{meta-val},
position holds special kinds of builtin data, of which
there is one per builtin type that @(lambda-py) models: numbers, strings, the
distinguished @(lp-term (meta-none)) value, lists, tuples, sets, classes, and
functions.@note{We express dictionaries in terms of lists and tuples, so we do
not need to introduce a special @(lp-term mval) form for them.}

The distinguished @(lp-term (undefined-val)) (``skull'') form represents uninitialized heap
locations whose lookup should raise an exception.  Within
expressions, this form can @emph{only} appear in @(lp-term let)-bindings
whose binding position can contain both expressions and @(lp-term
(undefined-val)).  The evaluation of @(lp-term (undefined-val)) in a @(lp-term
let)-binding 
allocates it on the heap.  Thereafter, it is an error to look up a
store location containing @(lp-term (undefined-val)); that location must have a
value @(lp-term val) assigned into it for lookup to succeed.
@Figure-ref["f:skull"] shows the behavior of lookup in heaps Σ for values and
for @(lp-term (undefined-val)).  This notion of undefined locations will
come into play when we discuss scope in @secref["s:scope"].

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
standard application of Felleisen-Hieb-style small-step semantics@~cite["felleisen:state"].
Saliently, a new list value is populated from the list expression via the
@(lp-term alloc) metafunction, this is allocated in the store, and the
resulting value of the expression is a pointer @(lp-term ref_new) to
that new list.

Similar rules for objects in general, tuples, and sets are shown in
@figure-ref["f:steps-values"].  Lists, tuples, and sets are given their own
expression forms because they need to evaluate their subexpressions and
have corresponding evaluation contexts.

@figure["f:steps-values" (elem (lambda-py) " reduction rules for creating objects")]{
  @(lp-reduction '("E-Object" "E-Tuple" "E-Set"))
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
  @(linebreak)
  @(lp-term ==>)
  @(lp-term (obj-val %str (meta-str "first-elt") ()))
}
Since δ works over object values themselves, and not over references, we need
a way to access the values in the store.  @(lambda-py) has the usual set of
operators for accessing and updating mutable references, shown in
@figure-ref["f:references"].  Thus, the real @(lambda-py) program
corresponding to the one above would be:
@centered{
  @(lp-term (prim "list-getitem"
                  ((fetch (list (id %list local) ((obj-val %str (meta-str "first-elt") ()))))
                   (fetch (object (id %int local) (meta-num 0))))))
}
Similarly, we can use @(lp-term set!) and @(lp-term alloc) to update the values
in lists, and to allocate the return values of primitive operations.  We
desugar to patterns like the above from Python's actual surface operators for
accessing the elements of a list in expressions like @pyinline{mylist[2]}.

@subsection{Updating and Accessing Fields}

So far, the dictionary part of @(lambda-py) objects have always been empty.
Python does, however, support arbitrary field assignments on objects.  The
expression
@centered{
  @(lp-term (set-attr e_obj e_str := e_val))
}
has one of two behaviors, defined in @figure-ref["f:simple-objs"].  Both
behaviors work over references to objects, not over objects themselves, in
contrast to @(lp-term δ).  If @(lp-term e_str) is a string object that is already a
member of @(lp-term e_obj), that field is imperatively updated with @(lp-term
e_val).  If the string is not present, then a new field is added to the object,
with a newly-allocated store position, and the object's location in the heap is
updated.

The simplest rule for accessing fields simply checks in the object's dictionary
for the provided name and returns the appropriate value, shown in E-GetField in
@figure-ref["f:simple-objs"].  E-GetField also works over reference values,
rather than objects directly.

@figure*["f:simple-objs" @elem{Simple field access and update in @(lambda-py)}]{
  @(lp-reduction '("E-SetFieldUpdate" "E-SetFieldAdd" "E-GetField"))
}

@subsection{First-class Functions}

Functions in Python are objects like any other.  They are defined with the
keyword @pyinline{def}, which produces a callable object with a mutable set of
fields, whose class is the built-in @(lp-term function) class.  For example a
programmer is free to write:
@pycode{
def f():
  return f.x

f.x = -1
f() # ==> -1
}
We model functions as just another kind of object value, with a type of
@(lp-term mval) that looks like the usual functional λ: 

@centered{
  @(lp-term (meta-closure (λ (x ...) opt-var e)))   
}

The @(lp-term opt-var) indicates whether the function is variable-arity:
if @(lp-term opt-var) is of the form @(lp-term (y)),
then if the function is called with more arguments than are in its list of
variables @(lp-term (x ...)), they are allocated in a new tuple and bound to
@(lp-term y) in the body.  Since these rules are relatively unexciting and verbose, we defer their explanation to the appendix.

@subsection{Loops, Exceptions, and Modules}

We defer a full explanation of the terms in @figure-ref["f:exprs"], and the
entire reduction relation, to the appendix.  This includes a mostly-routine
encoding of control operators via special evaluation contexts, and a mechanism
for loading new code via modules.  We continue here by focusing on
cases in @(lambda-py) that are unique in Python.

@section[#:tag "s:classes"]{Classes, Methods, and Desugaring}

Python has a large system with first-class methods, implicit
receiver binding, multiple inheritance, and more.  In this section we discuss
what parts of the class system we put in @(lambda-py), and which parts
we choose to eliminate by desugaring.

@subsection{Field Lookup in Classes}

In the last section, we touched on field lookup in an object's local
dictionary, and didn't discuss the purpose of the class position at all.
When an object lookup @(lp-term (get-attr (obj-val val_c mval d) e_str))
doesn't find @(lp-term e_str) in the local dictionary @(lp-term d), it defers
to a lookup algorithm on the class value @(lp-term val_c).  More
specifically, it uses the @(lp-term "__mro__") (short for @emph{method
resolution order}) field of the class to
determine which class dictionaries to search for the field.  This field is 
visible to the Python programmer:
@pycode{
class C(object):
  pass # a class that does nothing

print(C.__mro__)
# (<class 'C'>, <class 'object'>)
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
    @(lp-metafunctions class-lookup class-lookup-mro fetch-pointer #f)
  }
}

This rule allows us to model field lookups that defer to a superclass (or
indeed, a list of them).  But programmers don't explicitly define
@(lp-term "__mro__") fields; rather, they use higher-level language
constructs to build up the inheritance hierarchy the instances eventually use.


@subsection[#:tag "s:desugaring-classes"]{Desugaring Classes}

Most Python programmers use the special @pyinline{class} form to create classes in
Python.  However, @pyinline{class} is merely syntactic sugar for a use of the
builtin Python function
@pyinline{type}.@note{http://docs.python.org/3/library/functions.html#type} The
documentation states explicitly that the two following forms [sic] produce
@emph{identical} type objects:
@pycode{
class X:
     a = 1

X = type('X', (object,), dict(a=1))
}
This means that to implement classes, we merely need to understand the built-in
function @pyinline{type}, and how it creates new classes on the fly.  Then it is a
simple matter to desugar class forms to this function call.

The implementation of @pyinline{type} creates a new object value for the class,
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
          (set-attr (id newcls local) (object %str (meta-str "__mro__")) :=
            (builtin-prim "type-buildmro" (newcls bases)))
          (seq
          (for (key elt) in (app (get-attr (id dict local) (object %str (meta-str "__items__"))) ())
            (set-attr (id newcls local) (id key local) := (id elt local)))
          (return (id newcls local))))))))
}
This function, along with the built-in @pyinline{type}
class, suffices for bootstrapping the object system in @(lambda-py).

@subsection{Python Desugaring Patterns}

Python objects can have a number of so-called @emph{magic fields} that allow
for overriding the behavior of built-in syntactic forms.  These magic fields
can be set anywhere in an object's inheritance hierarchy, and provide a lot of
the flexibility for which Python is well-known.

For example, the field accesses that Python programmers write are not directly
translated to the rules in @(lambda-py).  Even the execution of @pyinline{o.x}
depends heavily on its inheritance hierarchy.  This
program desugars to:
@centered{
@(lp-term (app (get-attr (id o local) (object %str (meta-str "__getattribute__"))) ((id o local) (object %str (meta-str "x")))))
}
For objects that don't override the @(lp-term "__getattribute__") field, the
built-in object class's implementation does more than simply look up the
@(lp-term "x") property using the field access rules we presented earlier.
Python allows for attributes to implement special accessing functionality via
@emph{properties},@note{http://docs.python.org/3/library/functions.html#property}
which can cause special functions to be called on property access.  The
@(lp-term "__getattribute__") function of @(lp-term (id object local)) checks
if the value of the field it accesses has a special @(lp-term "__get__")
method, and if it does, calls it:
@centered{
@(lp-term
  (set-attr (id object global) (object %str (meta-str "__getattribute__")) :=
    (fun (obj field)
      (let (value local = (get-attr obj field)) in
        (if (builtin-prim "has-field?" ((id value local)
                                        (object %str (meta-str "__get__"))))
            (return (app (get-attr (id value local) (object %str (meta-str "__get__"))) ()))
            (return (id value local)))))))
}

This pattern is used to implement a myriad of features.  For example, when
accessing function values on classes, the @(lp-term "__get__") method of the
function binds the self argument:
@pycode{
class C(object):
  def f(self):
    return self

c = C() # constructs a new C instance
g = c.f # accessing c.f creates a 
        # method object closed over c
g() is c # ==> True

# We can also bind self manually:
self_is_5 = C.f.__get__(5)
self_is_5() # ==> 5
}
Thus, very few object-based primitives are needed to create
static class methods and instance methods.

Python has a number of other special method names that can be overridden to
provide specialized behavior.  @(lambda-py) tracks Python this regard; it desugars
surface expressions into calls to methods with particular names, and provides
built-in implementations of those methods for arithmetic, dictionary access,
and a number of other operations.  Some examples:
@nested[#:style 'code-inset]{
@pyinline{o[p]} @emph{ desugars to... } @(lp-term (app (get-attr (id o local) (object %str (meta-str "__getitem__"))) ((id p local))))

@pyinline{n + m} @emph{ desugars to... } @(lp-term (app (get-attr (id n local) (object %str (meta-str "__add__"))) ((id m local))))

@pyinline{fun(a)} @emph{ desugars to... } @(lp-term (app (get-attr (id fun local) (object %str (meta-str "__call__"))) ((id a local))))
}

With the basics of @pyinline{type} and object lookup in place, getting these
operations right is just a matter of desugaring to the right method calls, and
providing the right built-in versions
for primitive values.  This is the form of much of our desugaring, and though
it is labor-intensive, it is also the
straightforward part of the process.

@section[#:tag "s:hardparts"]{Python: the Hard Parts}

Not all of Python has a semantics as straightforward as that presented so far.
Python has a unique notion of scope, with new scope operators added in Python 3 to
provide some features of more traditional static scoping.  It also has powerful
control flow constructs, notably generators. We now begin examining these in detail.

@subsection{Generators}

Python has a built-in notion of @emph{generators}, which provide a control-flow
construct, @pyinline{yield}, that can implement lazy or generative sequences and
coroutines.  The programmer interface for creating a generator in Python is
straightforward: any function definition that uses the @pyinline{yield} keyword in
its body is automatically converted into an object with a generator
interface.  To illustrate the easy transition from function to generator,
consider this simple program:
@pycode{
def f():
  x = 0
  while True:
    x += 1
    return x

f() # ==> 1
f() # ==> 1
# ...
}
When called, this function always returns @pyinline{1}.

Changing @pyinline{return} to @pyinline{yield}
turns this into a generator. As a result, applying @pyinline{f()} no longer
immediately evaluates the body of the function; instead, it creates an 
object whose @pyinline{next} method evaluates the body until the next
@pyinline{yield} statement, stores its state for later resumption, and
returns the yielded value:
@pycode{
def f():
  x = 0
  while True:
    x += 1
    yield x

gen = f()
gen.__next__() # ==> 1
gen.__next__() # ==> 2
gen.__next__() # ==> 3
# ...
}

Contrast this with the following program, which seems to perform a 
simple abstraction over the process of yielding:
@pycode{
def f():
  def do_yield(n):
    yield n
  x = 0
  while True:
    x += 1
    do_yield(x)
}
Invoking @pyinline{f()} results in an @emph{infinite loop}. That is because
Python strictly converts only the innermost function with a @pyinline{yield}
into a generator, so only @pyinline{do_yield} is a generator. Thus, the
generator stores only the execution context of @pyinline{do_yield}, not of
@pyinline{f}.

@subsubsection[#:style 'unnumbered]{Failing to Desugar Generators with (Local) CPS}

The experienced linguist will immediately see what is going
on. Clearly, Python has made a design decision to store only
@emph{local} continuations.  This design can be justified on the
grounds that converting a whole program to continuation-passing style
(CPS) can be onerous, is not modular, can impact performance, and
depends on the presence of tail-calls (which Python does not have). In
contrast, it is natural to envision a translation strategy that performs
only a local conversion to CPS (or, equivalently, stores the local
stack frames) while still presenting a continuation-free interface to
the rest of the program.

From the perspective of our semantics, this is a potential boon: we don't
need to use a CPS-style semantics for the whole language!
Furthermore, perhaps generators can be handled by a strictly local rewriting
process. That is, in the core language generators can be reified
into first-class
functions and applications that use a little state to record which
function is the continuation of the @pyinline{yield} point. Thus,
generators seem to fit perfectly with our desugaring strategy.

To convert programs to CPS, we take operators that can cause
control-flow and reify each into a continuation function and
appropriate application. These operators include simple sequences,
loops combined with @pyinline{break} and @pyinline{continue},
@pyinline{try-except} and @pyinline{try-finally} combined with @pyinline{raise},
and @pyinline{return}.
Our CPS transformation turns every expression into a function that accepts an
argument for each of the above control operators, and turns uses of control
operators into applications of the appropriate continuation inside the
function.  By passing in different continuation arguments, the caller of the
resulting function has complete control over the behavior of control operators.
For example, we might rewrite a @pyinline{try-except} block from
@pycode{
try:
  raise Exception()
except e:
  print(e)
}
to
@pycode{
def except_handler(e): print(e)
except_handler(Exception())
}

In the case of generators, rewriting @pyinline{yield}
with CPS would involve creating a handler that stores a function holding the
code for what to do next, and rewriting @pyinline{yield} expressions to call that
handler:
@pycode{
def f():
  x = 1
  yield x
  x += 1
  yield x

g = f()
g.__next__() # ==> 1
g.__next__() # ==> 2
g.__next__() # throws "StopIteration"
}
would be rewritten to something like:@note{This being a sketch, we
have taken some liberties for simplicity.}
@pycode{
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
g['next']() # ==> 1
g['next']() # ==> 2
g['next']() # throws "StopIteration"
}
We build the @pyinline{yielder} function, which takes a value, which it returns
after storing a continuation argument in the @pyinline{to_call_next} field.  The
@pyinline{next} function always returns the result of calling this stored value.
Each @pyinline{yield} statement is rewritten to put everything after it into a new
function definition, which is passed to the call to @pyinline{yielder}. In
other words, this is the canonical CPS transformation, applied in the
usual fashion.

This rewriting is well-intentioned but does not work.  If this
program is run under Python, it results in an error:
@pycode{
    x += 1
UnboundLocalError: local variable 'x'
}
This is because Python creates a @emph{new scope} for each function
definition, and assignments within that scope create new variables.
In the body of @pyinline{rest}, the assignment @pyinline{x += 1} refers to a
new @pyinline{x}, not the one defined by @pyinline{x = 1} in @pyinline{start}.  This
runs counter to traditional notions of functions that can close over
mutable variables.  And in general, with multiple assignment
statements and branching control flow, it is entirely unclear whether a
CPS transformation to Python function definitions can work.

The lesson from this example is that the @emph{interaction} of non-traditional
scope and control flow made a traditional translation
not work.  The straightforward CPS solution is thus incorrect
in the presence of Python's mechanics of variable binding.  We now move on to describing how we
can express Python's scope in a more traditional lexical model.
Then, in @secref["s:generators-redux"] we will
demonstrate a working transformation for Python's generators.

@subsection[#:tag "s:scope"]{Scope}

Python has a rich notion of scope, with several types of variables and implicit
binding semantics that depend on the block structure of the program.  Most
identifiers are @pyinline{local}; this includes function parameters and variables
defined with the @pyinline{=} operator.  There are also @pyinline{global} and
@pyinline{nonlocal} variables, with their own special semantics within closures,
and interaction with classes.  Our core contribution to explaining Python's
scope is to give a desugaring of the @pyinline{nonlocal} and @pyinline{global}
keywords, along with implicit @pyinline{local}, @pyinline{global} and @pyinline{instance}
identifiers, into traditional lexically scoped closures. 
Global scope is still handled specially, since it exhibits a form of dynamic
scope that isn't straightforward to capture with traditional
let-bindings.@note{We actually exploit this dynamic scope in bootstrapping
Python's object system, but defer an explanation to the appendix.}

We proceed by describing Python's handling of scope for local variables, the
extension to @pyinline{nonlocal}, and the interaction of both of these features with
classes.

@subsubsection{Declaring and Updating Local Variables}

In Python, the operator @pyinline{=} performs local variable binding:
@pycode{
def f():
  x = 'local variable'
  return x

f() # ==> 'local variable'
}
The syntax for updating and creating a local variable are identical, so
subsequent @pyinline{=} statements mutate the variable created by the first.
@pycode{
def f():
  x = 'local variable'
  x = 'reassigned'
  x = 'reassigned again'
  return x

f() # ==> 'reassigned again'
}

Crucially, there is @emph{no syntactic difference} between a statement
that updates a variable and one that initially binds it.  Because
bindings can also be introduced inside branches of conditionals, it
isn't statically determinable if a variable will be defined at certain
program points.  Note also that variable declarations are not scoped
to all blocks---here they are scoped to function definitions:
@pycode{
def f(y):
 if y > .5: x = 'big'
 else : pass
 return x

f(0) # throws an exception
f(1) # ==> "big"
}

Handling simple declarations of variables and updates to variables is
straightforward to translate into a lexically-scoped language.  @(lambda-py)
has a usual @pyinline{let} form that allows for lexical binding.  In desugaring, we
scan the body of the function and accumulate all the variables on the left-hand
side of assignment statements in the body.  These are let-bound at the top of
the function to the special @(lp-term (undefined-val)) form, which evaluates to an
exception in any context other than a @pyinline{let}-binding context (@secref["s:warmup"]).  We use
@pyinline{x := e} as the expression form for variable assignment, which is not a
binding form in the core.  Thus, in @(lambda-py), the example above rewrites to:
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
      (app (id f global) ((object %int (meta-num 0))))
      (app (id f global) ((object %int (meta-num 1))))))))
}
In the first application (to 0) the assignment will never happen, and the
attempt to look up the @(lp-term (undefined-val))-valued @(lp-term x) in the
return statement will fail with an exception.  In the second application, the
assignment in the then-branch will change the value of @(lp-term x) in the
store to a non-@(lp-term (undefined-val)) string value, and the string
@(lp-term "big") will be returned.

The algorithm for desugaring scope is so far:
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
given scope.  Unfortunately, this covers only the simplest cases of Python's scope.


@subsubsection[#:tag "s:nonlocal-scope"]{Closing Over Variables}

Bindings from outer scopes can be @emph{seen} by inner scopes:
@pycode{
def f():
  x = 'closed-over'
  def g():
    return x
  return g

f()() # ==> 'closed-over'
}
However, since @pyinline{=} defines a new local variable, one cannot close over a
variable and mutate it with what we've seen so far; @pyinline{=} simply
defines a new variable with the same name:
@pycode{
def g():
  x = 'not affected'
  def h():
    x = 'inner x'
    return x
  return (h(), x)

g() # ==> ('inner x', 'not affected')
}
This is mirrored in our desugaring:
each function adds a new let-binding
inside its own body, shadowing any bindings from outside.  This was the
underlying problem with the attempted CPS translation from the last section,
highlighting the consequences of using the same syntactic form for both
variable binding and update.

Closing over a mutable variable is, however, a common and useful pattern.  Perhaps
recognizing this, Python added a new keyword in Python 3.0 to
allow this pattern, called @pyinline{nonlocal}.  A function
definition can include a @pyinline{nonlocal} declaration at the top, which allows
mutations within the function's body to refer to variables in enclosing scopes
on a per-variable basis.  If we add such a declaration to the previous example,
we get a different answer:
@pycode{
def g():
  x = 'not affected by h'
  def h():
    nonlocal x
    x = 'inner x'
    return x
  return (h(), x)

g() # ==> ('inner x', 'inner x')
}
The @pyinline{nonlocal} declaration allows the inner assignment to @pyinline{x} to
``see'' the outer binding from @pyinline{g}.  This effect can span any nesting
depth of functions:
@pycode{
def g():
  x = 'not affected by h'
  def h():
    def h2():
      nonlocal x
      x = 'inner x'
      return x
    return h2
  return (h()(), x)

g() # ==> ('inner x', 'inner x')
}

Thus, the presence or absence of a @pyinline{nonlocal} declaration can change an
assignment statement from a binding occurrence of a variable to an assigning
occurrence.  We augment our algorithm for desugaring scope to reflect this:
@itemlist[

  @item{For each function body:
  
    @itemlist[
      @item{Collect all variables on the left-hand side of @(lp-term =) in a set @emph{locals}, stopping at other function boundaries,}

      @item{Let @emph{locals'} be @emph{locals} with any variables in
      @pyinline{nonlocal} declarations removed,}

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

@subsubsection[#:tag "s:class-scope"]{Classes and Scope}

We've covered some subtleties of scope for local and nonlocal variables and
their interaction with closures.  What we've presented so far would be enough
to recover lexical scope for a CPS transformation for generators if function
bodies contained only other functions.  However, it turns out that we observe a
different closure behavior for variables in a class definition than we do for
variables elsewhere in Python, and we must address classes to wrap up the story
on scope.

@figure["f:classexample" "An example of class and function scope interacting"]{
@pycode{
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

@figure["f:class-scope" "Interactions between class bodies and function scope"]{
  @centered{@image["class-scope.png" #:scale 0.7]}
}

Consider the example in @figure-ref["f:classexample"].  Here we observe an
interesting phenomenon: in the body of @pyinline{g}, the value of the variable
@pyinline{x} is @emph{not} @pyinline{4}, the value of the most recent apparent
assignment to @pyinline{x}.  In fact, the body of @pyinline{g} seems to "skip" the
scope in which x is bound to 4, instead closing over the outer scope in which
@pyinline{x} is bound to @pyinline{"x-value"}.  At first glance this does not appear to
be compatible with our previous notions of Python's closures.  We will see,
however, that the correct desugaring is capable of expressing the semantics of
scope in classes within the framework we have already established for dealing
with Python's scope.  

Desugaring classes is substantially more complicated than handling simple local
and nonlocal cases.  Consider the example from @figure-ref["f:classexample"],
stripped of print statements: 

@pycode{
def f(x, y):
  class c:
    x = 4
    def g(self): pass
  return c
f("x-value", "y-value")().g()
}

In this example, we have three local scopes: the body of the function f, the
body of the class definition c, and the body of the function g.  The scopes of
@pyinline{c} and @pyinline{g} close over the same scope as @pyinline{f}, but have distinct,
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
      @pyinline{nonlocal} declarations removed,}

      @item{For each variable @(lp-term var) in @emph{locals'}, wrap the
      function body in a @(lp-term let)-binding of @(lp-term var) to @(lp-term
      (undefined-val)).}
    ]
  }

]

Recalling that the instance variables of a class desugar roughly to assignments
to the class object itself, the function desugars to the following:

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
              (set-attr (id c local) (object %str (meta-str "x")) := (object %int (meta-num 4)))
              (seq
              (set-attr (id c local) (object %str (meta-str "g")) := (id extracted-g local))
              (return (id c local))))))))))))
}

This achieves our desired semantics: the bodies of functions defined in the
class @pyinline{C} will close over the @pyinline{x} and @pyinline{y} from the function
definition, and the statements written in c-scope can still see those bindings.
We note that scope desugaring yields terms in an intermediate language with a
@(lp-term class) keyword.  In a later desugaring step, we remove the class
keyword as we describe in @secref["s:desugaring-classes"].

@subsubsection{Instance Variables}

When we introduced classes we saw that there is no apparent difference
between classes that introduce identifiers in their body and classes that
introduce identifiers by field assignment.  That is, either of the following
forms will produce the same class @pyinline{C}:
@pycode{
class C:
  x = 3
# or ...
class C: pass
C.x = 3
}

We do, however, have to still account for
@emph{uses} of the instance variables inside the class body, which are referred
to with the variable name, not with a field lookup like @pyinline{c.x}.
We perform a final desugaring step for instance variables, where we
let-bind them in a new scope just for evaluating the class body, and desugar
each instance variable assignment into both a class assignment and an
assignment to the variable itself.  The full desugaring of the example
is shown in @figure-ref["f:full-class-desugar"].

@figure["f:full-class-desugar" "Full class scope desugaring"]{
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
                    (set-attr (id c local) (object %str (meta-str "x")) := (object %int (meta-num 4)))
                    (seq
                    (assign (id x local) := (object %int (meta-num 4)))
                    (seq
                    (set-attr (id c local) (object %str (meta-str "g")) := (id extracted-g local))
                    (assign (id g local) := (id extracted-g local)))))))
              (return (id c local)))))))))))
}
}

We have now covered Python classes' scope semantics:
function bodies do not close over the class body's scope, class bodies
create their own local scope, statements in class bodies are executed sequentially,
and definitions/assignments in class bodies result in the creation of class
members.  The @pyinline{nonlocal} keyword does not require further special treatment, even when present in class bodies.

@subsection[#:tag "s:generators-redux"]{Generators Redux}

@figure["f:generators" "The desugaring of generators"]{
@pycode{def f(x ...): body-with-yield}

@(linebreak)
@emph{desugars to...}
@(linebreak)

@(lp-term
  (fun (x ...)
    (let (done local = 
      (fun () (raise (app (id StopIteration global) ())))) in
    (let (initializer local = 
      (fun (self)
        (let (end-of-gen-normal local = 
          (fun (last-val)
            (seq
            (set-attr (id self local) (object %str (meta-str "__next__")) := (id done local))
            (raise (app (id StopIteration global) ()))))) in
        (let (end-of-gen-exn local = 
          (fun (exn-val)
            (seq
            (set-attr (id self local) (object %str (meta-str "__next__")) := (id done local))
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
        (set-attr (id self local) (object %str (meta-str "___resume")) := (id resumer local)))))))) in
      (app (id %generator global) ((id initializer local)))))))

@(linebreak)
@emph{where...}
@(linebreak)

@pycode{
class generator(object):
    def __init__(self, init):
        init(self)

    def __next__(self):
        return self.___resume(None)

    def send(self, arg):
        return self.___resume(arg)

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
@(lambda-py) with an explicit @pyinline{yield} statement, passing @pyinline{yields}
through unchanged.  As the final stage of desugaring, we identify functions
that contain @pyinline{yield}, and convert them to generators via local CPS.  We
show the desugaring machinery @emph{around} the CPS transformation in
@figure-ref["f:generators"].  To desugar them, in the body of the function we
construct a generator object and store the CPS-ed body as a @pyinline{___resume}
attribute on the object. The @pyinline{__next__} method on the generator, when
called, will call the @pyinline{___resume} closure with any arguments that are
passed in. To handle yielding, we desugar the core @pyinline{yield} expression to
update the @pyinline{___resume} attribute to store the current normal continuation,
and then @pyinline{return} the value that was yielded.

Matching Python's operators for control flow, we have five continuations, one
for the normal completion of a statement or expression going onto the next, one
for a @pyinline{return} statement, one each for @pyinline{break} and @pyinline{continue},
and one for the exception throwing @pyinline{raise}.  This means that each CPSed
expression becomes an anonymous function of five arguments, and can be passed
in the appropriate behavior for each control operator.

We use this configurability to handle two special cases:

@itemlist[

  @item{Throwing an exception while running the generator}

  @item{Running the generator to completion}

]

In the latter case, the generator raises a @pyinline{StopIteration} exception. We
encode this by setting the initial ``normal'' continuation to a function that
will update @pyinline{___resume} to always raise @pyinline{StopIteration}, and then to
raise that exception. Thus, if we evaluate the entire body of the generator, we
will pass the result to this continuation, and the proper behavior will occur.

Similarly, if an uncaught exception occurs in a generator, the generator will
raise that exception, and any subsequent calls to the generator will result in
@pyinline{StopIteration}. We handle this by setting the initial @pyinline{raise}
continuation to be code that updates @pyinline{___resume} to always raise
@pyinline{StopIteration}, and then we raise the exception that was passed to the
continuation. Since each @pyinline{try} block in CPS installs a new exception
continuation, if a value is passed to the top-level exception handler it means
that the exception was not caught, and again the expected behavior will occur.

@section[#:tag "s:engineering"]{Engineering & Evaluation}

Our goal is to have desugaring and @(lambda-py) enjoy two properties:
@itemlist[

  @item{Desugaring translates all Python source programs to @(lambda-py) (@emph{totality}).}

  @item{Desugared programs evaluate to
  the same value as the source would in Python (@emph{conformance}).}

]
The second property, in particular, cannot be proven because there is
no formal specification for what Python does. We therefore tackle both
properties through testing. We discuss various aspects of implementing
and testing below.

@subsection{Desugaring Phases}

Though we have largely presented desugaring as an atomic activity, the
paper has hinted that it proceeds in phases. Indeed, there are four:
@itemlist[

  @item{Lift definitions out of classes (@secref["s:class-scope"]).}

  @item{Let-bind variables (@secref["s:nonlocal-scope"]). This is done second to correctly
  handle occurrences of @pyinline{nonlocal} and @pyinline{global} in class methods.
  The result of these first two steps is an intermediate language between
  Python and the core with lexical scope, but still many surface constructs.}

  @item{Desugar classes, turn Python operators into method calls, turn
  @pyinline{for} loops into guarded @(lp-term while) loops, etc.}

  @item{Desugar generators (@secref["s:generators-redux"]).}

]
These four steps yield a term in our core, but it isn't ready to
run yet because we desugar to open terms. For instance, @pyinline{print(5)}
desugars to
@centered{
@(lp-term (app (id print global) ((object (id %int global) (meta-num 5)))))
}
which relies on free variables @(lp-term print) and @(lp-term %int).

@subsection{Python Libraries in Python}

We implement as many libraries as possible in Python@note{We
 could not initially use existing implementations of these in Python
 for bootstrapping reasons: they required more of the language than we
 supported.}
augmented with some macros recognized by the desugaring.
For example, the builtin class for tuples is implemented mostly in Python, but
for getting the length of a tuple defers to the δ function:
@pycode{
class tuple(object):
  def __len__(self):
    return ___delta("tuple-len", self)
  ...
}
All occurrences of @pyinline{___delta(str, e, ...)} are desugared to
@(lp-term (builtin-prim str (e ...))) directly.  We only do this
for @emph{library} files, so normal Python programs can use
@pyinline{___delta} as the valid identifier it is. As another example,
after the class definition of tuples, we have the statement
@pycode{
___assign("%tuple", tuple)
}
which desugars to an assignment statement @(lp-term (assign (id %tuple global) := (id tuple global))). Since
%-prefixed variables aren't valid in Python,
this gives us an private namespace of global variables that are
un-tamperable by Python.  Thanks to these decisions, this project
 produces far more readable desugaring output than a previous effort
 for JavaScript@~cite["politz:s5"].

@subsection{Performance}

@(lambda-py) may be intended as a formal semantics, but composed with
desugaring, it also yields an implementation. While the performance
does not matter for semantic reasons (other than programs that depend
on time or space, which would be ill-suited by this semantics anyway),
it does greatly affect how quickly we can iterate through
testing!

The full process for running a Python program in our semantics is:
@itemlist[#:style 'ordered
  @item{Parse and desugar roughly 1 KLOC of libraries implemented in Python}
  @item{Parse and desugar the target program}
  @item{Build a syntax tree of several built-in libraries, coded by building the AST directly in Racket}
  @item{Compose items 1-3 into a single @(lambda-py) expression}
  @item{Evaluate the @(lambda-py) expression}
]
Parsing and desugaring for (1) takes a nontrivial amount of time (on the order of
40 seconds on the first author's laptop).  Because this work is
needlessly repeated for each test, we began caching the results of the
desugared library files, which
reduced the time to run our tests into the realm of feasibility for
rapid development.  When we first performed this optimization, it made
running 100 tests drop from roughly 7 minutes to 22 seconds.  Subsequently,
we moved more functionality out of the @(lambda-py) and into verbose but
straightforward
desugaring, which caused a serious performance hit; running 100 tests now
takes on the order of 20 minutes, even with the optimization.

@subsection{Testing}

@figure["f:tests" "Distribution of passing tests"]{
@centered{
  @table[(style #f
         (list (style #f '(center))
                (table-columns (list
                                  (style #f '(left))
                                  (style #f '(right))
                                  (style #f '(right))))))
    (list
      (list @para{Feature} @para{# of tests} @para{@hspace[2]LOC@note{reported by @url{http://cloc.sourceforge.net/}}})
      (list @para{} @para{} @para{})
      (list @para{Built-in Datatypes} @para{81} @para{902})
      (list @para{Scope} @para{39} @para{455})
      (list @para{Exceptions} @para{25} @para{247})
      (list @para{(Multiple) Inheritance} @para{16} @para{303})
      (list @para{Properties} @para{9} @para{184})
      (list @para{Iteration} @para{13} @para{214})
      (list @para{Generators} @para{9} @para{129})
      (list @para{Modules} @para{6} @para{58})
      (list @para{} @para{} @para{})
      (list @para{Total} @para{205} @para{2636})
      )
  ]
}
}

Python comes with an extensive test suite. Unfortunately, this suite
depends on numerous advanced features, and as such was useless as we
were building up the semantics. We therefore went through the test
suite files included with CPython, April 2012,@note{http://www.python.org/getit/releases/3.2.3/}
and ported a representative suite of 205 tests (2600 LOC).  In
our selection of tests, we focused on orthogonality and
subtle corner-cases. The distribution of those tests across features is reported in
@figure-ref["f:tests"].  On all these tests @emph{we obtain the
same results as CPython}.

It would be more convincing to eventually handle all of Python's own
@pyinline{unittest} infrastructure to run CPython's test suite unchanged.  The
@pyinline{unittest} framework of CPython unfortunately relies on a number of
reflective features on modules, and on native libraries, that we don't yet
cover.  For now, we manually move the assertions to simpler if-based
tests, which also run under CPython, to check conformance.

@subsection{Correspondence with Redex}

We run our tests against @(lambda-interp), not against the Redex-defined
reduction relation for @(lambda-py).  We can run tests on @(lambda-py), but
performance is excruciatingly slow: it takes over an hour to run complete
individual
tests under the Redex reduction relation. Therefore, we have been able
to perform only limited testing for conformance by hand-writing portions
of the environment and heap (as Redex terms) that the Python code in the test
uses.  Fortunately, executing
against Redex should be parallelizable, so we hope to increase
confidence in the Redex model as well.

@section[#:tag "s:future"]{Future Work and Perspective}

As @secref["s:engineering"] points out, there are some more parts of Python we
must reflect in the semantics before we can run Python's test
cases in their native form. This is because Python is a large language
with extensive libraries, a foreign-function interface, and more.

Libraries aside, there are some interesting features in Python left to
tackle. These include special fields, such as the properties of
function objects that compute the content of closures, complex cases of
destructuring assignments, a few reflective features like the metaclass form,
and others.

More interestingly, we are not done with scope! Consider
@pyinline{locals}, which
returns a dictionary of the current variable bindings in a given scope:
@pycode{
def f(x):
  y = 3
  return locals()

f("val") # ==> {'x': 'val', 'y': 3}
}
This use of @pyinline{locals} can be desugared to a clever combination of
assignments into a dictionary along with variable assignments, which we do.
However, this desugaring of @pyinline{locals} relies on it being a strictly
@emph{local} operation (for lack of a better word).
But worse, @pyinline{locals} is a value!
@pycode{
def f(x, g):
  y = 3
  return g()

f("x-val", locals)
# ==> {'x': 'x-val', 'y': 3,
#      'g': <builtin function locals>}
}
Thus, @emph{any} application could invoke
@pyinline{locals}.  We would therefore need to deploy our complex
desugaring everywhere we cannot statically determine that a function
is not @pyinline{locals}, and change every application to check for it.
Other built-in values like @pyinline{super} and @pyinline{dir}
exhibit similar behavior.

On top of this, @pyinline{import} can splice all identifiers
 (@pyinline{*}) from a module into local scope. For
now, we handle only @pyinline{import}s that bind the module object to a single
identifier. Indeed, even 
Python 3 advises that @pyinline{import *} should only be used
at module scope.  Finally, we do not handle @pyinline{exec}, Python's
``eval'' (though the code-loading we do for modules comes close). Related
efforts on handling similar operators in 
JavaScript@~cite["politz:s5"] are sure to be helpful here.

We note that most traditional analyses would be seriously challenged by
programs that use functions like @pyinline{locals} in a higher-order way, and
would probably benefit from checking that it isn't used in the first place.
We don't see the lack of full support for such functions as a serious
weakness of @(lambda-py), or an impediment to reasoning about most Python
programs.  Rather, it's an interesting future challenge to handle a few of
these remaining esoteric features. It's also useful to simply call out the
weirdness of these operators, which are liable to violate the soundness of
otherwise-sound program tools.

Overall, what we have learned most from this effort is how central
scope is to understanding Python. Many of its features are orthogonal,
but they all run afoul on the shoals of scope. Whether this is
intentional or an accident of the contorted history of Python's scope is unclear (for
example, see the discussion around the proposal to add
@pyinline{nonlocal}@~cite["yee:nonlocal"]),
but also irrelevant. Those attempting to improve Python or
create robust sub-languages of it---whether for teaching or for
specifying asset-backed securities---would do well to put
their emphasis on scope first, because this is the feature most likely
to preclude sound analyses, correctness-preserving refactorings, and
so on.

@section[#:tag "s:related"]{Related Work}

We are aware of only one other formalization for Python: Smeding's
 unpublished and sadly unheralded master's thesis@~cite["smeding:python-semantics"]. Smeding
 builds an executable semantics and tests it against 134 hand-written
 tests. The semantics is for Python 2.5, a language version without
 the complex scope we handle.  Also, instead of defining a core, it
 directly evaluates (a subset of) Python terms. Therefore, it offers a
 weaker account of the language and is also likely to be less useful
 for certain kinds of tools and for foundational work.

There are a few projects that analyze Python code. They are either
silent about the semantics or explicitly eschew defining one. We
therefore do not consider these related.

Our work follows the path laid out by @(lambda-js)@~cite["guha:js-essence"]
and its follow-up@~cite["politz:s5"], both for variants of JavaScript.

@section[#:style 'unnumbered]{Acknowledgments}

We thank the US NSF and Google for their support. We thank Caitlin Santone for
lending her graphical expertise to @figure-ref["f:class-scope"]. The paper
title is entirely due to Benjamin Lerner.

And now for something completely different: This paper was the result of an
international collaboration resulting from an on-line course taught by the
first and last authors. Several other students in the class also contributed to
the project, including Ramakrishnan Muthukrishnan, Bo Wang, Chun-Che Wang,
Hung-I Chuang, Kelvin Jackson, Victor Andrade, and Jesse Millikan.

@;{Acknowledgments:
- Ben Lerner for title
- Arjun for saying we couldn't do it
- NSF and Google for funding
- Brown and CS for providing "free hosting" services for our course
- redex
- Caitlin for @figure-ref["f:class-scope"]
}

@(generate-bib)


@section[#:tag "s:appendix" #:style 'unnumbered]{Appendix: The Rest of @(lambda-py)}

@figure["f:E" (elem "Evaluation contexts")]{
  @(with-rewriters
    (lambda () (render-language λπ #:nts '(E Es))))
}
@figure["f:T" (elem "Contexts for try-except")]{
  @(with-rewriters
    (lambda () (render-language λπ #:nts '(T Ts))))
}
@figure["f:H" (elem "Contexts for loops")]{
  @(with-rewriters
    (lambda () (render-language λπ #:nts '(H Hs))))
}
@figure["f:R" (elem "Contexts for return statements")]{
  @(with-rewriters
    (lambda () (render-language λπ #:nts '(R Rs))))
}
@figure["f:control" (elem "Control flow reductions")]{
  @(lp-reduction '(E-While E-LoopContinue E-LoopBreak E-LoopNext
                   E-TryDone E-TryCatch
                   E-Return E-FramePop
                   E-FinallyReturn E-FinallyBreak E-FinallyRaise E-FinallyContinue
                   E-IfTrue E-IfFalse E-Seq))
}

The figures in this section show the rest of the @(lambda-py) semantics.  We
proceed to briefly present each of them in turn.

@subsection{Contexts and Control Flow}

@Figure-ref["f:E" "f:T" "f:H" "f:R"] show the different @emph{contexts} we use
to capture left-to-right, eager order of operations in @(lambda-py).  @(lp-term E)
is the usual @emph{evaluation context} that enforces left-to-right, eager
evaluation of expressions. @(lp-term T) is a context for the first expression
of a @(lp-term tryexcept) block, used to catch instances of @(lp-term raise).
Similarly, @(lp-term H) defines contexts for loops, detecting @(lp-term continue) and @(lp-term break),
and @(lp-term R) defines contexts for @(lp-term return) statements inside functions.
Each interacts with a few expression forms to handle non-local control flow.

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

@section[#:style 'unnumbered]{Appendix 2: Confusing Rename Refactorings}

This program:
@pycode{
def f(x):
  class C(object):
    x = "C's x"
    def meth(self):
      return x + ', ' + C.x
  return C

f('input x')().meth()
# ==> 'input x, C's x'
}
confuses the variable rename refactoring of all the Python IDEs we tried.  We
present these weaknesses to show that getting a scope analysis right in Python
is quite hard!  We found these tools by following recommendations on
StackOverflow, a trusted resource.  Two of the tools we tested, PyCharm and
WingWare IDE, are products that developers actually purchase to do Python
development (we performed this experiment in their free trials).

For PyCharm, if we rename the @pyinline{x} parameter to @pyinline{y}, the class
variable @pyinline{x} also gets changed to @pyinline{y}, but the access at
@pyinline{C.x} does not.  This changes the program to throw an error.  If we
instead select the @pyinline{x} in @pyinline{C.x} and refactor to @pyinline{y},
The class variable and use of @pyinline{x} change, but the original
definition's parameter does not.  This changes the behavior to an error again,
as @pyinline{y} is an unbound identifier in the body of @pyinline{meth}.

PyDev has the same problem as PyCharm with renaming the function's parameter.
If we instead try rename the @pyinline{x} in the body of @pyinline{C}, it gets
it mostly right, but also renames all the instances of @pyinline{x} in our
strings (something that even a parser, much less a lexical analyzer should be
able to detect):

@pycode{
def f(x):
  class C(object):
    y = "C's y"
    # we highlighed the x before = above
    # and renamed to y
    def meth(self):
      return x + ' ' + C.y
  return C

f('input y')().meth()
# ==> 'input y, C's y'
}

WingWare IDE for Python is less obviously wrong: it pops up a dialog with
different bindings and asks the user to check the ones they want rewritten.
However, if we try to refactor based on the @pyinline{x} inside the method, it
doesn't give us an option to rename the function parameter, only the class
variable name and the access at @pyinline{C.x}.  In other cases it provides a
list that contains a superset of the actual identifiers that should be renamed.
In other words, it not only overapproximates (which in Python may be
inevitable), it also (more dangerously) undershoots.


