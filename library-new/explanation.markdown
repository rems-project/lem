# Library Format Discussion

I now started writing new libraries. I started with the list-library as a comparably
simple example. As discussed, I mainly follow the Haskell library. Attached you find
a file called "list.lem" with my attempt. The file "basic_classes.lem" contains class
definitions used by "list.lem".

In the following, I will try to talk you through "list.lem" explaining some of the problems
and design decisions.


## Basic structure

Let's use the length function of lists as an example, on how I would like to write
simple functions in the library. As before, it all starts with a val-declaration:

    val length : forall 'a. list 'a -> num

Then, I would like in many cases to have a Lem-definition of the function. This 
definition is used as a reference implementation for explaining the semantics. Moreover,
it is used for backends, for which no other representation is provided. 
For `length`, giving such a reference implementation is straightforward. 
Notice the use of ``declare termination_argument`` though. Moreover, notice
that these definitions should be clean and straighforward. Since mappings
to native backend represenations are very likely, efficient execution
is a minor concern.

    let rec length l = match l with
                         | [] -> 0
                         | x :: xs -> length xs + 1
                       end
					   
    declare termination_argument length = automatic

Then the mapping to targets is done. Before, a
separate constant was defined in a backend specific hierarchy.
Then, `let inline` statements were used to perform the mapping
to these target-specific constants. In contrast, I propose
using `declare targetrep` statements:

    declare targetrep hol      length = 'LENGTH'
    declare targetrep ocaml    length = 'List.length'
    declare targetrep isabelle length = 'List.length'
    declare targetrep coq      length = 'List.length'

These `declare targetrep` statements are similar to `let inline` ones.
However, they deliberately allow mappings for exactly one target. Moreover,
the right-hand side is an expression that can contain quotations like `'LENGTH'`.
These parts are literally used by the backend, but not type-checked. For simple
functions like `length`, this is in my opinion not a problem. The benefit is that
it is very easy to extend the library. More complicated examples are discussed
below.

Finally, I also think some simple tests are useful. They serve both as documentation
of the intended semantics and can be used to check semi-automatically, whether the
provided target-mappings are really sensible.

    assert length_0: (length [] = 0)
    assert length_1: (length [2] = 1)
    assert length_2: (length [2;3] = 2)
    
    lemma length_spec: ((length [] = 0) && (forall x xs. length (x :: xs) = length xs + 1))


### Infix operations

`length` is a particularly simple example. Infix operations like
`append` are slightly more tricky. The `declare targetrep` syntax
allows to map to infix operators, specifying the associativity as well. 
Moreover, the `declare ascii_rep` syntax is used to map `++` to a
simple identifier for backends that have trouble handling `++` directly.

    val (++) : forall 'a. list 'a -> list 'a -> list 'a 
    let rec (++) xs ys = match xs with
                         | [] -> ys
                         | x :: xs' -> x :: (xs' ++ ys)
                       end
    declare ascii_rep function (++) = append
    declare termination_argument append = automatic
    
    declare targetrep hol      append = infix (right-assoc 32) '++'
    declare targetrep ocaml    append = 'List.append'
    declare targetrep isabelle append = infix (left-assoc 13) '@'
    declare targetrep coq      append = 'List.app'
    declare targetrep html     append = infix (right-assoc 32) "++"
    
    assert append_1: ([0;1;2;3] ++ [4;5] = [0;1;2;3;4;5])
    lemma append_nil_1: (forall l. l ++ [] = l)
    lemma append_nil_2: (forall l. [] ++ l = l)


### Argument order

Some functions like fold-right are provided by all backends, but with slightly
different signatures. The syntax of `declare targetrep` is flexible enough to
allow for example swapping arguments. Compared with the old library-format, less typechecking
is done here. However, I believe this is justifiable for the benefit of simpler
mappings. The old way is still possible by declaring an auxiliary fold function with
different argument order and using `let inline` to map to this function.

    val foldr : forall 'a 'b. ('a -> 'b -> 'b) -> 'b -> list 'a -> 'b 
    let rec foldr f b l = match l with
      | []      -> b
      | x :: xs -> f x (foldr f b xs)
    end
    declare termination_argument foldr = automatic
    
    declare targetrep hol      foldr = 'FOLDR' 
    declare targetrep ocaml    foldr f b l = 'List.fold_right' f l b
    declare targetrep isabelle foldr f b l = 'List.foldr' f l b
    declare targetrep coq      foldr = 'List.fold_right' 
    
    assert fold_right_0: (foldr (+) 0 [] = 0)
    assert fold_right_1: (foldr (+) 1 [4] = 5)
    assert fold_right_4: (foldr (fun e l -> e::l) [] [1;2;3;4] = [1;2;3;4])


### Fancy mappings

`declare targetrep` is powerful enough to allow also fancy mappings. 
Consider the following predicate `all` that checks whether all elements
of a list satisfy a certain property:

    val all : forall 'a. ('a -> bool) -> list 'a -> bool 
    let all P l = foldl (fun r e = P e && r) true l

Mappings for `hol`, `ocaml` and `coq` are straightforward

    declare targetrep hol      all = 'EVERY'
    declare targetrep ocaml    all = 'List.all'
    declare targetrep coq      all = 'List.forallb' 

However, for Isabelle, there is a minor problem. The idiomatic way
in Isabelle would be to convert the list into a set using `set` and
use bounded quantification over this set. However, if not done
carefully, this introduces an undesired dependency between
the set and list libraries. The `targetrep` syntax circumvents
this problem, by not typechecking `set`:

    declare targetrep isabelle all P l = (forall (x IN ('set' l)). P x)


## Representing equality


In `basic_classes.lem`, there is a typeclass `Eq` for equality. It defines 
the infix operation `=`, i.e. the standard equality used by Lem. All types,
we can perform an equality check on, should be instances of the `Eq` type class.
In order to allow easy structural equality checks, there is also the function
`unsafe_structural_equality`. It plays the role of the old `=`. The name is
deliberately long to discourage it's direct usage. However, it is handy to
instantiate the type-class `Eq` for simple types. The prefix `unsafe` indicates
that this equality check might fail (e.g. when comparing functions in OCaml).

    class ( Eq 'a ) 
      val (=) : 'a -> 'a -> bool
    end
    
    type ordering = LT | EQ | GT

    instance (Eq ordering)
      let (=) = unsafe_structural_equality
    end



### Problems with type classes / equality


With a type-class for equality present, all functions should use this equality.
An example is the membership test for lists. The membership
test is essentially an instance of the existential quantification over
lists, where we check, whether an element equal to the given one exists.

    val elem : forall 'a. Eq 'a => 'a -> list 'a -> bool
    let inline elem e l = any ((=) e) l

However, this is not really what we want. We would like to use the backends
native membership functions to avoid unnecessary complicated output.
This is however only correct, if the equality provided provided by the type-class
is for a concrete type equal to the one used by the backend, i.e. the structural one.

I propose solving  this problem, by adding an additional, raw element check
function to the library. A simple rewrite mechanism could then be used to perform the mapping
for us.

    val elem_raw : forall 'a. 'a -> list 'a -> bool
    declare targetrep hol      elem_raw = 'MEM'
    declare targetrep ocaml    elem_raw = 'List.mem'
    declare targetrep isabelle elem_raw e l = e IN ('set' l)
    declare targetrep coq      elem_raw = 'List.forallb' 
    
    rewrite {HOL} elem_raw_intro: (forall e l. (any (unsafe_structural_equality e) l) = (elem_raw e l))

This is a simple, pragmatic solution. The `rewrite` construct is similar to existing `lemma` statements.
It should be therefore easy to add to the parser. It essentially defines an expression of type bool,
which could be handed to an expression macro to perform the actual rewrite. 



