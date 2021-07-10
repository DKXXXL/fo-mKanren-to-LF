# Defunctionalized miniKanren + Universal Quantifier + Implication

###  Forked from miniKanren with a first-order representation
Defunctionalized miniKanren (first order implementation) decouples the search strategy from the representation of the search space.  This makes it possible to use a variety of strategies, perform program transformations (even while a program is running), and implement tools such as a debugger. Learn more from the [2019 miniKanren Workshop paper](http://minikanren.org/workshop/2019/minikanren19-final2.pdf).

### Initialization
* Note there is a dependency on [struct-update](https://docs.racket-lang.org/struct-update/index.html)

* use `raco test tests-fo-LF.rkt` for sanity check. It should take only around 30 sec.

### How to use this?
* get into racket, `(require "mk-fo.rkt")`
* Several goal constructors
  * primitive constraints -- `=/=`, `==`
  * and a bunch of primitive type constraints: `symbolo`, `stringo`, `boolo`, `numbero` and their negate
  * `(cimpl A B)` indicating $A \rightarrow B$
    * `cimpl` stands for constructive implication. Most of the time when dealing with user-customized relation, it is doing pattern matching. This is the reason it is called constructive implication.
  * `(for-all (vs ..) goal)` indicating $\forall vs, goal$
  * `(for-bounds (vs ..) dag goal)` indicating $\forall vs, dag \rightarrow goal$
    * Note that `dag` has to only have conjunction, disjunction and primitive constraints
    * If you want stronger things in $dag$, just use implication `cimpl`
  * all the quantifier only ranges inside first-order values
    * first order values are only symbols, strings, bools, numbers and the pair of them.

### How to debug this?
* get into racket, `(require "tests-fo-LF.rkt")`
* If you don't want debug dump during the running, use `(set-debug-threshold! 1)`, otherwise, all the `debug-dump` ranging inside this repo will print something during the running
  * `(set-debug-threshold! -100)` usually can turn on all the debug information. It is up to you to decide the debugging info threshold
  * details in `debug-info.rkt`