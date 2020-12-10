.EQ
delim ##
.EN
.NH 1
Informally
.IP \(bu 2)
Every type is a supertype (int, bool, etc.) and a predicate.
.IP \(bu 2)
The type can take a value of the supertype, x if and only if pred(x).
.NH 1
Formally
.NH 2
Available types:
.IP \(bu 2)
anytype (the only type of types, cannot be refined)
.IP \(bu 2)
pointer to a refinement type (cannot be refined)
.IP \(bu 2)
char, int, float, bool, structs, arrays, unit, empty, algebraic types (the supertypes).
These can't be used directly, only when refined.
The usable int type in jam has supertype int and refinement #p(x) = true#.
.IP \(bu 2)
Refinements of the supertypes.
These are a pair of a supertype and a refinement (a predicate).
With supertype #t# and refinement #p#, the refinement type is #\(lC x \(mo t | p(x) \(rC#.
.IP \(bu 2)
Value functions: (param1, \[u2026], paramn) -> returntype.
Represents a function that takes values #v sub 1 \(mo param sub 1 , \[u2026] , v sub n \(mo param sub n# and produces a value of type returntype.
Returntype cannot be the anytype, but the paramaters have no constraints on them.
.IP \(bu 2)
Type functions: (anytype, \[u2026], anytype) -> anytype.
A function that takes types and produces a new type based on them in some way.
Using polymorphism, the same identifier can be used for both a type function and a value function.
This makes the type system much easier to use as value functions can operate on types too when given a different first type argument. 
Type functions cannot be partial. It is recommended to return the empty type when given parameters that don't make sense, such as
.DS L
.ft CW
(> anytype int (typeof 0.0))   -> empty (type anytype)
.ft
.DE
which is trying to find integers greater than the float 0.0. This comparison doesn't make sense so empty is returned.
.NH 2
Predicates
.LP
A predicate must be in this normal form
.EQ
\[te] x sub 1 , \[u2026] , x sub n . f(x sub 1 , \[u2026] , x sub n )
.EN
where #f# contains no quantifiers. This means it is true if and only if #f# is satisfiable.
.NH 2
Primitives
.LP
For a value of type #a# with supertype #S# and predicate #f# and something that takes a value of type #b# also with supertype #S# and predicate #g#, the value is accepted if and only if
.EQ
\[fa] x \[mo] S . f(x) \[rA] g(x)
.EN
.NH 2
Example operations on primitive types
.LP
Type functions from the standard library can combine types in many ways to produce new types. Here are some examples.
.LP
Using polymorphism on all functions returning a boolean, > can be both an operator for comparing integers and floats.
.DS L
.ft CW
(> anytype int (typeof 0))     -> {x \[mo] int | x > 0} (type anytype)
(> int 5 3)                    -> true (type bool)
(> float 1.5 2.0)              -> false (type bool)
.ft
.DE
.LP
Refinement types with the same supertype can be unioned or intersected.
.DS L
.ft CW
(union even odd)               -> int (type anytype)
(intersect even multipleof3)   -> {x \[mo] int | x \[==] 0 (mod 6)} (type anytype)
.ft
.DE
.LP
Polymorphism should also be present in functions returning a value of type #a# to allow it to instead return a subtype of #a#. * can be used this way.
.DS L
.ft CW
(* anytype int (typeof 2))   -> {x \[mo] int | x \[==] 0 (mod 2)} (type anytype)
(* int 2 5)                  -> 10 (type int)
(* float 2.5 2.0)            -> 5.0 (type float)
.ft
.DE
.LP
Refinements can also be removed from types using the #super# function, this gives a type with the same supertype but an always true predicate.
.DS L
.ft CW
(super even)  -> int (type anytype)
.ft
.DE
.NH 2
When are expressions type checked?
.DS L
.ft CW
(let [(var1 type1 val1) \[u2026] (varn typen valn)] \[u2026])
.ft
.DE
The compiler will check that #\[fa] 0 < i \[<=] n . val sub i \[mo] "type" sub i#
.DS L
.ft CW
(f arg1 \[u2026] argn)
.ft
.DE
The compiler will check that #f# is a function with #n# arguments, suppose the type of f is
#(type sub 1 , \[u2026] , "type" sub n ) -> returntype#.
It will also check that #\[fa] 0 < i <= n . arg sub i \[mo] "type" sub i#
.DS L
.ft CW
(fn [...] returntype body)
.ft
.DE
The compiler will check that #body \[mo] returntype#
.NH 2
What is the type of an expression?
.LP
There are 12 types of expressions in the jam grammar.
.IP \(bu 2)
INTEGER - an integer literal #i# has type #\(lC i \(rC# or supertype int and refinement #p(x) = x "==" i#
.IP \(bu 2)
FLOAT - a float literal #i# has type #\(lC i \(rC# or supertype float and refinement #p(x) = x "==" i#
.IP \(bu 2)
STRING - a string is just an array of characters. The string #s# has type #\(lC s \(rC#
.IP \(bu 2)
IDENTIFIER - has the type stored in the environment for that identifier
.IP \(bu 2)
[eltype length values...] - an array literal #a# has type #\(lC a \(rC#
.IP \(bu 2)
{structtype values...} - has type structtype
.IP \(bu 2)
(let [...] expr) - has type of expr
.IP \(bu 2)
(fn [(arg1 type1) ... (argn typen)] returntype expr) - has type #("type" sub 1 , \[u2026] , "type" sub n ) -> returntype#
.IP \(bu 2)
(import "module") - takes the type of the module being imported
.IP \(bu 2)
(valueof type) - has type type
.IP \(bu 2)
(ite cond ifbranch elsebranch) - if cond has type condtype (with supertype bool) and the branches have types iftype and elsetype respectively and supertype s, the expression has type #\(lC x \(mo s | (true \(mo condtype \(AN x \(mo iftype) \(OR (false \(mo condtype \(AN x \(mo elsetype) \(rC#
.IP \(bu 2)
(f arg1 ... argn) - if #f# has type #("type" sub 1 , \[u2026] , "type" sub n ) -> returntype# then the call has type #returntype#
.NH 2
Inductive definition of #value \(mo "type"#
.IP \(bu 2)
value \(mo anytype #iff# value is one of the types listed in section 2.1
.IP \(bu 2)
value \(mo pointer(ttype) #iff# the type of value is a pointer pointing to #pointed# and #pointed \(mo ttype#
.IP \(bu 2)
value \(mo type where type is a refinement type with supertype #s# and refinement #p# #iff#
value has supertype #s# and #p(value)#
.IP \(bu 2)
value \(mo #(param sub 1 , \[u2026], param sub n ) -> returntype# where returntype isn't the anytype #iff# 
.EQ
\(fa arg sub 1 \(mo param sub 1 , \[u2026] , arg sub n \(mo param sub n
.EN
(value #arg sub 1# \[u2026] #arg sub n#) \(mo returntype
.IP \(bu 2)
value \(mo #(anytype, \[u2026], anytype) -> anytype# #iff#
value is a type function with type #(anytype, \[u2026], anytype) -> anytype#
.NH 2
How types are evaluated
.LP
Types and type functions are evaluated at compile time using these rules
.IP \(bu 2)
IDENTIFIER - the value of that identifier in the environment
.IP \(bu 2)
[type length] - an array of length length and elements with type type
.IP \(bu 2)
{prop type ...} - a struct with named properties with respective types
.IP \(bu 2)
(let [(#var sub 1# #"type"# #"type" sub 1#) \[u2026] (#var sub n# #"type"# #"type" sub n#)] #body#) - 
evaluates the first definition's type and value and updates the environment, then uses the updated environment to
evaluate the second definition and continues until the last one, then
evaluates #body# with the updated environment.
.IP \(bu 2)
(fn [(#param sub 1# #"type" sub 1#) \[u2026] (#param sub n# #"type" sub n#)] #"returntype"# #body#) -
a type function taking #n# types as arguments and returning a new type, the environment is updated after
evaluating each type argument when the function is called, so the types of later parameters can depend on the
value of earlier ones, this is how polymorphism works in jam. This way the same definition can produce several
type functions and value functions. #returntype# is then evaluated with the environment, and then #body#.
The value of a type function is just its AST as it doesn't get evaluated in any way until it is called.
.IP \(bu 2)
(import "module") - just evaluates the module as a type TODO reference module section 
.IP \(bu 2)
(typeof value) - the type of value
.IP \(bu 2)
(ite condtype typea typeb) - if condtype is the empty type then typeb, if not then typea. Only the type that is used is evaluated.
.IP \(bu 2)
(#typefn# #arg sub 1# \[u2026] #arg sub n#) - evaluates each of the arguments as types, then evaluates the types of parameters expected of typefn using these types to check they match.
Then evaluates the return type and errors if it isn't anytype, finally evaluates the body of typefn with the updated environment to produce a type.
