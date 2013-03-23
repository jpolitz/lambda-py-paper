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

@section{Introduction}

@section{Motivation and Contributions}

Python is a widely-used scripting
language@note{https://github.com/blog/841-those-are-some-big-numbers} with a
reputation for simplicity and expressivity.  There are a number of tools for
Python, from style and lint-checkers,@note{https://pypi.python.org/pypi/pylint,
https://pypi.python.org/pypi/pep8} to simple static
checkers,@note{https://pypi.python.org/pypi/pyflakes} to code analyzers that
import and run code to analyze
it.@note{https://pypi.python.org/pypi/PyChecker}.  There are also a number of
IDEs for Python, which provide tools like variable name refactoring and code
completion@note{http://www.jetbrains.com/pycharm/, http://pydev.org/,
http://wingware.com/, among others}.  These tools are all useful, but all are
built on an ad hoc understanding of Python, and provide little in the way of
@emph{guarantees}; in [REF] we note that a simple 8 line program, which uses no
so-called ``dynamic'' features, confuses their variable rename refactoring
because of a wrinkle in Pythonic scope

This is not to say that developers shouldn't use these tools; they are
certainly invaluable for organizing projects, providing symbol completion, and
managing build and deployments.  They could be made even more helpful, however,
if their predictions about programs and refactoring tools could be defined
rigorously and with respect to a semantics for Python, rather than in a
best-effort manner over the Python AST data structure they happen to use.

Indeed, as Python becomes even more widely used, and in even more
correctness-sensitive domains, a precise understanding of programs written in
Python becomes even more important.  The Securities and Exchange Commission has
proposed using Python as an executable specification of financial
contracts@note{https://www.sec.gov/rules/proposed/2010/33-9117.pdf}, and Python
is becoming a scripting language of choice for programming new network
paradigms@note{http://www.noxrepo.org/pox/about-pox/}.  Is an informal
understanding of the language sufficient for such domains?  Having a precise
semantics available for analyzing and proving properties of programs is a much
more comfortable situation for these applications to be in.

In this paper, we present a tested semantics for several features of Python
3.2.3.@note{http://www.python.org/getit/releases/3.2.3/, released April 2012}
As concrete contributions and artifacts, we have produced and will discuss in
this paper:

@itemlist[

  @item{A @emph{core semantics} for Python, dubbed @(lambda-py), which is implemented
  in Redex (and was used to typeset the figures in this document);}

  @item{An @emph{interpreter}, dubbed @(lambda-interp), implemented in 800LOC
  of Racket, that is a more efficient implementation of @(lambda-py), tested
  against the Redex model;}

  @item{A @emph{desugaring} translation from Python programs to @(lambda-py),
  implemented in Racket and described here in prose and pseudocode;}

  @item{The results of @emph{testing} the composition of desugaring with
  @(lambda-interp) against a real Python implementation, to demonstrate conformance
  of @(lambda-py) with real-world Python.}

]

This suite of artifacts is a meaningful contribution in itself, regardless of
any new insights into programming languages theory or practice.  It constitutes
a formal description of the language, and a mathematical foundation for
applying well-known programming language techniques to complex, real-world
applications written in Python.

Along with these concrete implementation and mathematical contributions, we
also provide some more high-level insight into several feature interactions
within Python.  Most notably, Python's scope interacts heavily with both
classes and control flow (in the form of generators), making those features
difficult to understand independently.  In [REF], We show how we untangle the
tight coupling of these features, and manage to express them in a traditional
calculus of scope, control, and objects.

@subsection{Outline} Presenting the entirety of Python's semantics and its
translation to @(lambda-py) is out of the scope of this document, so we focus
on a few particular areas.  We first give an overview Python's value and object
model, whose richness allows many of the other patterns we see in the language.
We then show how many Pythonic patterns for iteration and overloading can be
implemented as straightforward expansions to patterns in this object model.
This also serves as an introduction to the concept of @emph{desugaring} the
surface language to the core.  Next, we tackle Python's unique treatment of
scope for variables and closures, and how it interacts with both classes and a
naïve understanding of generators.  After explaining our model of scope, we
show how generators can be implemented with local CPS.  Finally, we describe
the results of testing our desugaring and interpreter against CPython to ensure
its fidelity to real-world Python programs.

@section{Warmup: A Quick Tour of @(lambda-py)}

@figure["f:values" @elem{Values in @(lambda-py)}]{
  @(with-rewriters
    (lambda () (render-language λπ #:nts '(v val mval ref Σ v+undef opt-var))))
}


For a large portion of @(lambda-py)'s object and value model, we do not find
anything particularly surprising. For these features, describing Python in
terms of @(lambda-py) is a labor-intensive, but straightforward, formalization
of information available in documentation or obvious from test cases.  We
provide an overview of the object model of @(lambda-py) and Python, some of the
basic operations on objects, and the shape of our small step semantics.  This
introduces notation and concepts that will be used later in the document to
explain the harder parts of Python's semantics.

@subsection{@(lambda-py) Values}

@Figure-ref["f:values"] shows the representation of values in @(lambda-py),
which we use the metavariables @(lp-term v) and @(lp-term val) to range over.
All the values in @(lambda-py) are either objects, written as triples in
@(lp-term 〈〉), or references to entries in the store Σ, written @(lp-term
(pointer-val ref)).  The special term @(lp-term (undefined-val)) represents
yet-to-be-bound identifiers, we address it when we discuss scope in [REF].

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
The @emph{meta-val} position holds special kinds of builtin data, of which
there is one per builtin type that @(lambda-py) models: numbers, strings, the
distinguished @(lp-term (meta-none)) value, lists, tuples, sets, classes, and
functions.

Python programmers never manipulate object values directly; rather, they always
work with references to objects.  Thus, many of the operations in @(lambda-py)
involve the heap, and few are purely functional.  As an example of what such an
operation looks like, take constructing a list, which allocates a new reference
in the store holding the list value, and returns a pointer to the newly-created
reference is returned:

@centered[
  @(lp-reduction '("E-List"))
]

E-List is a good example for understanding the shape of evaluation in
@(lambda-py).  The general form of the reduction relation is over expressions
@(lp-term e), global environments @(lp-term ε), and heaps @(lp-term Σ):

@centered[
  @(lp-term (e ε Σ)) @(arrow->pict '-->) @(lp-term (e ε Σ))
]

In the E-List rule, we also make use of evaluation contexts @(lp-term E) to
enforce an order of operations and eager calling semantics.  Since this is a
standard technique in a Felleisen-Hieb style small step semantics, we defer its
definition to the appendix [REF] [CITE].  The relevant points for the list
construction is that a new list is constructed and put in the store with the
class and list of values copied from the list expression itself via the
@(lp-term alloc) metafunction, and the value put back in the evaluation context
is a pointer @(lp-term ref_new) to that list.

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
@figure-ref["f:references"].  The real version of the program above would look
more like:

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

f.x = 22
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

The full language of expressions for @(lambda-py) is in @figure-ref["f:exprs"].
We defer a full explanation of all the terms in that figure, and the full
reduction relation, to the appendix [REF].  This includes a mostly-routine
encoding of control operators via special evaluation contexts, and a mechanism
for loading new code via modules.  We continue here by focusing on some of the
cases in the semantics that are unique to Python.

@figure["f:exprs" (elem (lambda-py) " expressions")]{
  @(with-rewriters
    (lambda () (render-language λπ #:nts '(e t))))
}


@section{Classes, Methods, and Pythonic Desugarings}

[FILL This section is waiting on rewrites (Alejandro) to the class/object model
to make it fully line up with reality]

The first complex feature of Python we address is a featureful first-class
class system.  We'll discuss how @(lambda-py) models its lookup algorithm
(including multiple inheritance) and its mechanism for binding the self
parameter in first-class methods.

@subsection{Field Lookup in Classes}

In the last section, we touched on field lookup in an object's local
dictionary, and didn't discuss the purpose of the class position at all.
When an object lookup @(lp-term (get-field (obj-val val_c mval d) str))
doesn't find @(lp-term str) in the local dictionary @(lp-term d), it defers
to a lookup algorithm on the class value @(lp-term val_c).  More
specifically, it uses the @(lp-term "__mro__") field of the class to
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
class @(lp-term object).  [FILL hopefully remove discussion of method binding
here]

We define this lookup algorithm within @(lambda-py) as @(lp-term class-lookup),
shown in @figure-ref["f:lookup-class"] along with the reduction rule for field
access that uses it.

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
  @para{
    @(lp-metafunction maybe-bind-method #f)
  }
}

This rule and the associated metafunctions are interesting for a few reasons.
[FILL this may change as we make __getattribute__ work, so deferring an
explanation for now]


@subsection{Desugaring Classes}

In the last section, we saw that field lookup depends on a special class
pointer, and a designated @(lp-term "__mro__") field that contains the
inheritance chain of the object.  We didn't discuss how classes and their
associated @(lp-term "__mro__") field get created in the first place.  We next
briefly describe the class form in Python and some of its behavior.  Rather
than attempt to do justice to a full description here, we try to capture the
essence of how @(lambda-py) models Python's classes.

Classes are created with a special @code{class} form in Python.  The simplest
nontrivial classes can define methods by using the same @code{def} syntax as
function definitions.  The special method @code{__init__} defines a constructor
for the class, which is used to initialize fields, and variables in the class's
body are also accessible as fields of instances.  @Figure-ref["f:test-class"]
shows a simple class definition that uses these features.

@figure["f:test-class" @elem{A sample Python class definition}]{

@verbatim{
class Test(object):
  success = 'Test passed'
  failure = 'Test failed'
  def __init__(self, f):
    self.f = f
  def runtest(self, expected):
    if self.f() == expected:
      print(self.success)
    else:
      print(self.failure)

t1 = Test(lambda: "correct")
t1.runtest("correct") # "Test passed"
t1.runtest("incorrect") # "Test failed"
}

}

A few things to note:

@itemlist[

  @item{The @code{Test} class declares @code{object} to be its superclass by
  putting @code{object} in the parentheses of the class
  declaration,@note{Multiple comma-separated superclasses would yield multiple
  inheritance.}}

  @item{Calling the @code{Test} class value itself causes @code{__init__} to be
  called,}

  @item{The @code{__init__} method is purely side-affecting, and is passed an
  already-created (but not initialized) instance of the class,}

  @item{The method receiver @code{t1} is passed to the method @code{runtest}
  implicitly,}

  @item{The variables @code{success} and @code{failure} are available as fields
  on @code{self}.}

]

We tackle these features through desugaring the class form down to particular
object structures.  We can turn @code{Test} itself into an object whose class
is the builtin class @code{type}, and then assign its @(lp-term "__mro__")
field to the correct sequence of objects.  The desugaring below captures most
of the relevant details, though the full desugaring is slightly longer and more
complex:

@centered{
  @(lp-term ;; lp-term is just a wrapper around (with-rewriters ... render-term)
  (let (Test local = (object (id %type local) (meta-class 'Test))) in
  (let (t1 local = undefined) in
    (seq
    (assign (get-field Test "__mro__") := (tuple %tuple ((id Test local) (id %object local))))
    (seq
    (assign (get-field Test "__init__") := (fun (self f) (no-var) (assign (get-field self "f") := (id f local))))
    (seq
    (assign (get-field Test "success") := (object %str (meta-str "success")))
    (seq
    (assign (get-field Test "failure") := (object %str (meta-str "failure")))
    (seq
    (assign (get-field Test "runtest") :=
      (fun (self expected) (no-var)
        (if (builtin-prim "==" (app (get-field (id self local) "f") ()) (id expected local))
            (app (get-field (id print global) "__call__") ((get-field (id self local) "success")))
            (app (get-field (id print global) "__call__") ((get-field (id self local) "failure"))))))
    (seq
    (assign t1 := (app (get-field Test "__call__") ((fun () (no-var) (object %str (meta-str "correct")) (no-var)))))
    (seq
    (app (get-field (get-field (id local t1) "runtest") "__call__") ((object %str (meta-str "correct"))))
    (app (get-field (get-field (id local t1) "runtest") "__call__") ((object %str (meta-str "incorrect"))))))))))))))
     

}

So, after this expression evaluates, @(lp-term obj) is an identifier bound to
an object whose class pointer points to the builtin object @(lp-term %type).
This new value has a @(lp-term meta-class) value stored as well, which
designates it as a class object.  The next line sets up the important @(lp-term
"__mro__") field on the class value, which will be used for future lookups on
instances of the class.  If more than one superclass had been given, a helper
would have been called here to resolve the superclass lookup order.  This can
be implemented in a function written in @(lambda-py), so it isn't an intrinsic
part of the semantics.

The next three lines perform an interesting transformation. First, the class
variables @(lp-term success) and @(lp-term failure) have been changed into
@emph{object assignments} on the class value itself, rather than being
let-bound variables.  Similarly, the function definition inside the class body
is turned into an assignment on the class, rather than a let-bound variable.
Clearly, these values do need to be stored on @(lp-term (id Test local)) at
some point, since they are later accessed.  We will return to the desugaring of
classes and scope later, since the desugaring presented here isn't quite the
whole story.

The last interesting line in the desugaring is where the @(lp-term "__call__")
field of @(lp-term (id Test local)) is applied.  This is the desugaring of all
the function applications shown here, but this one is interesting because of
where the @(lp-term "__call__") method is implemented.  We haven't set it on
the @(lp-term Test) value, so it must be somewhere in the @(lp-term "__mro__")
list of its class.  And indeed, it is the @(lp-term %type) class's @(lp-term
"__call__") method that is responsible for creating a new object value with
class @(lp-term (id Test local)), calling @(lp-term "__init__"), and returning
the resulting object.  The @(lp-term %type) class is defined separately from
desugaring as part of the initial environment that desugared code runs in; we
discuss more of these engineering decisions in [REF].  The interesting point is
that even class construction is deferred to a method on a built-in value; we
express all object creation with only @(lp-term (object e_cls mval)) expressions.

Left implicit in this desugaring is the @(lp-term self)-binding of @(lp-term
t1) in the two method calls [FILL this should be __getattribute__].

@subsection{Reflection}

Python has a number of reflective operations on the values in its object
system; we highlight a few examples here.

@verbatim{

class C(object):
  def method(self):
    pass

c = C()
c.__class__ is C # True

bound_method = c.method
bound_method.__self__ == c
# the object closed over as self is reachable
# through the __self__ field


}

These operations predominantly preserve @emph{integrity} while
compromising @emph{confidentiality}.  That is, the allow the user to observe
and copy values that are internal to objects, but not to change them if they
would affect the internals of the behavior of the object.

@subsection{Pythonic Patterns}

Pythonic objects can have a number of so-called @emph{magic fields} that allow
for overriding the behavior of built-in syntactic forms.  These magic fields
can be set anywhere in an object's inheritance hierarchy, and provide a lot of
the flexibility that Python is well-known for.

@section{Python, the Hard Parts}

Not all of Python has a semantics as straightforward as that presented so far.
It has a unique notion of scope, with new scope operators added in Python 3 to
provide some features of more traditional static scoping.  It also has powerful
implicit constructs for control flow, most notably generators.  We proceed by
presenting the behavior of Python's generators, how we'd like to express them
using traditional programming languages wisdom, and what we need to do so.

@subsection{Generators and Local CPS: A Semantics Parable}

Python has a built-in notion of @emph{generators}, which provide a control-flow
construct, @code{yield}, that can implement lazy or generative sequences and
coroutines.  The programmer interface for creating a generator in Python is
straightforward: any function definition that uses the @code{yield} keyword in
its body is automatically converted into an object with so-called generator
interface.  To illustrate the easy transition from function to generator,
consider this (perhaps foolish) program in Python:

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
didn't immediately return @code{1}.  By changing the {\tt return} statement to
a @code{yield} statement, a generator is created instead that can produce an
arbitrary number of such values:

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
calls.  The documentation of @code{yield} says as much (emphasis added) [FILL
figure out blockquote]:

``...the execution proceeds to the first @code{yield} expression, where it is
suspended again, returning the value of [the @code{yield expression}] to the
generator's caller. By suspended we mean that @emph{all local state is retained,
including the current bindings of local variables, the instruction pointer, and
the internal evaluation stack}. When the execution is resumed by calling one of
the generator's methods, the function can proceed exactly as if the yield
expression was just another external
call.@note{http://docs.python.org/release/3.2.3/reference/expressions.html?highlight=generator#yield-expressions}''

The emphasized text above highlights that the behavior of generators is
dependent on the storage of @emph{local} state and variables.  This implies
that the generator shouldn't need to, for example, keep track of the evaluation
stack or variables of @emph{other} functions.  It is careful to point out that
uses of yield can be treated as such an external function call, as well.
Further, since @code{yield} is a keyword, and not a value, a generator cannot
delegate the ability to @code{yield} to another function, maintaining the
locality of the operation.

To the discerning functional programmer, this well-defined design immediately
suggests an implementation strategy: a local continuation-passing style (CPS)
transformation.  The usual drawback of CPS---that it is a full-program
transformation---is alleviated by the careful restriction of @code{yield} to a
local operation.  That is, generators could be implemented by reifying all
local control operators into first-class functions and applications, and using
a bit of state to store a function representing the rest of the computation at
each @code{yield} point.  With this transformation, generators could be
understood completely in terms of a rewriting to existing constructs that is
local to function bodies.

@subsection{A (Local) CPS Transformation for Python}

Being somewhat discerning functional programmers, we began by attempting to
implement a CPS transformation for Python.  To implement a local CPS
transformation, we needed to take the operators that could cause local control
flow and reify each into a continuation function and an appropriate
application.  These operators include simple sequences, loops combined with
@code{break} and @code{continue}, and @code{try-except} and @code{try-finally}
combined with @code{raise} (generators cannot use @code{return}).

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

To:

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
g.next() # evaluates to 1
g.next() # evaluates to 2
g.next() # throws "StopIteration"

}

Would be rewritten to something like:@note{ This is a sketch, not
the true output of an automated process, so we've taken liberties
with the variable names and continuations' construction. We use a
dictionary for @code{"next"} to avoid verbose object
construction.} 

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
function definition, which is passed to the call to @code{yielder}.

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
statements and branching control flow, it is completely unclear if a
CPS transformation to Python function definitions can work.

The lesson from this example is that the @emph{interaction} of non-traditional
scope and control flow made a traditional normal-form translation (rewriting to
CPS) not work.  The straightforward CPS solution, which doesn't require
extending the number of concepts in the language, is inexpressible in Python
due to the mechanics of variable binding.  We'll move on to describing how we
can express Pythonic scope in a more traditional lexical model, and later we
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
Python's object system [REF]}

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

It is a crucial point that there is @emph{no syntactic difference} between a
statement that updates a variable and one that initially binds it.  This fact,
combined with the fact that bindings can occur within branching statements as
well, so it isn't statically determinable if a variable will be defined at
certain program points.  Note also that variable declarations are not scoped to
all blocks---here they are scoped to function definitions:

@verbatim{

def f(y):
  let x = Undefined in {
    if y > .5: x := 'big'
    else     : pass
    return x
  }

f(0) # throws an exception
f(1) # evaluates to "big"

}

@; I moved the desugaring for local scope and nonlocal scope to after the 
@; discussion of python's scope.  I don't have a strong preference for the 
@; ordering, I just wanted the desugaring discussion to be compacted for the
@; purposes of writing.  --matthew
@; I think it flows better to build up the algorithm incrementally -joe

@subsubsection{Desugaring for Local Scope}

@figure*["f:skull" "Handling undefined identifiers"]{
  @(lp-reduction '(E-LetLocal E-GetVar E-GetVarUndef))
}

Handling simple declarations of variables and updates to variables is
straightforward to translate into a lexically-scoped language.  @(lambda-py)
has a usual @code{let} form that allows for lexical binding.  In desugaring, we
scan the body of the function and accumulate all the variables on the left-hand
side of assignment statements in the body.  These are let-bound at the top of
the function to a special value, @(lp-term (undefined-val)), which evaluates to an
exception in any context other than a @code{let}-binding context.  We use
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
@(lp-term "big") will be returned.  The reduction rules that handle these cases
are shown in @figure-ref["f:skull"], along with the rule for let-binding local
identifiers.

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
given scope.  This covers only the simplest cases of Pythonic scope, however.


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
defines a new variable with the same name.  This is mirrored in our desugaring:
the desugaring of the inner function adds a new let-binding for @(lp-term x)
inside its own body, shadowing any bindings from outside.  This was the
underlying problem with the attempted CPS translation from the last section,
highlighting the consequences of using the same syntactic form for both
variable binding and update.

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

Closing over a mutation is, however, a common and useful pattern.  Perhaps
recognizing this, Python's maintainers added a new keyword in Python 3.0 to
allow this pattern, called @code{nonlocal}, appropriately enough.  A function
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
occurence.  We can augment our algorithm for desugaring scope to reflect this:

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

So the above program would desugar to the following, which @emph{does not}
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

@;{
TODO(joe): This is true, but we might not care

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
and nonlocal cases.  Consdier the example from @figure-ref["f:classexample"],
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

@subsubsection{Desugaring classes: instance variables}

We said, when discussing classes in [REF], that there is no apparent difference
between classes which introduce identifiers in their body and classes which
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
            (assign (id c local) := (class 'c))
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

We have thus achieved everything necessary for Python's class semantics; 
function bodies do not close over the class body's scope, class bodies
create their own local scope, statements in class bodies are executed sequentially 
and definitions/assignments in class bodies result in the creation of class
members.  The nonlocal and global keyword do not require special treatment 
beyond what we have outlined here, even when present in class bodies.

@subsection{Generators Redux}

@figure["f:generators" "The desugaring of generators"]{

@verbatim{def f(x ...): body-with-yield

}

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
            (assign (get-field (id self local) "__next__") := (id done local))
            (raise (app (id global StopIteration) ()))))) in
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

@verbatim{

class %generator(object):
    def __init__(self, init):
        init(self)

    def __next__(self, resume_arg):
        if len(args) > 0:
            return self.___resume(resume_arg)
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

@;{Acknowledgments:
- Ben Lerner for title
- NSF and Google for funding
- Brown for hosting
}
