[Verus](https://github.com/verus-lang/verus) is a language that extends Rust
(through macros) with tools to formally verify a program.  It lets the user
write a specification and proofs, which it feeds to an SMT solver (Z3) and the
Rust type checker to verify the program.

The core language is documented in the [Verus guide](https://verus-lang.github.io/verus/guide/).
We will be using [tokenized state machines](https://verus-lang.github.io/verus/state_machines/intro.html),
which are documented in the separately linked book to model and verify concurrent
programs, but there are key things we need to know about the Verus language:

1. **Ghost code** - this is code used to write specifications or proofs that is
  just used for static verification and doesn't execute at runtime.

  Verus has two modes for this:
  1. `spec` - specification mode.  `spec fn`s must be pure, deterministic, and
     must always terminate.  `spec` code can only interface with other `spec` code.
  2. `proof` - proof code - can use `spec` and other `proof` code, but doesn't need
     to be pure (can mutate values) or deterministic like `spec` code.

2. Ghost code is closer to a mathematical specification language, and has certain
   "powers" that executable Rust code doesn't:
   1. It has the integer types `int` and `nat`, which can represent any integer
      or natural number, not bounded by bit size (so there is no overflow/edge
      behavior, for example)
   2. It can make copies of values that executable code can't (i.e., types that
      aren't marked as `Copy`)
   3. It can instantiate a value of any type (including unconstructable types
      like `!`).
   4. The `==` operator is a mathematical equivalence relation (reflexive,
      symmetric, transitive) that can be applied to types that don't implement
      `Eq` or even `PartialEq` in executable code.
      - *implementation note:* for some structures like the `Seq`, `Set`, and `Map`
        specification abstractions, you (currently?) may need to use the
        **extended equality operator** `=~=` for value equality to help the SMT solver.
      - most pointer types use value equality, but `Cell` and `RefCell` use pointer equality

3. Functions can have preconditions and postconditions, which are specified with
   `spec` code.  For example, this following function has preconditions that `x`
   is greater than 4, and `y` is greater than 5, and has a postcondition that
   the returned value (which we named `sum`) is greater than 9:

   ```rs
   fn add_conditions(x: u8, y: u8) -> (sum: u8)
       requires
         x > 4,
         y > 5,
       ensures
         z > 9,
   {
       x + y
   }
   ```

   When calling `add_conditions`, the SMT solver will verify the preconditions
   `x > 4` and `y > 5`, and then `z > 9` will be added as a fact in the local
   scope (i.e., `z` represents the return value of `add_conditions(x, y)`, whether
   it is used inline or bound to a variable).

4. The special function `assert` makes the SMT solver verify a fact.  Code inside the
   `assert` function is in proof mode, which doesn't need to be pure like `spec`.
   When something is `assert`ed, that fact is available for the SMT solver in subsequent
   lines where it is in scope (and still valid wrt. mutation, etc.).

   - The function `assume` just does the second part of making the SMT solver assume
     that the fact is true, which is helpful for debugging while building a proof but
     can easily introduce unsoundness.

5. Loops can have loop invariants specified with the `invariant` keyword (or
   `invariant_except_break`, which means a property is always true except if
   a `break` statement is used to exit early):

   ```rs
   let mut i = 0u32;
   let mut sum = 0;

   while idx < 10
     invariant
       sum == idx * (idx - 1) / 2
   {
     sum += idx;
     i += 1;
   }

   ```

6. The `View` trait defines a function `view(&self) -> Self::V`, where `V` is a
   mathematical abstraction (like `int` is an abstraction of `i8`) of the type.
   The `item@` postfix operator is shorthand for calling `item.view()`.

7. Enum variants can be unwrapped and verified with the `t is Variant` boolean,
   and using `t->field` (which can be a tuple index) or `t->Variant_field`
   (to qualify) to access fields.  There is also the `matches` syntax
   `t matches Variant { field, .. }` which evaluates to a boolean, but binds
   the name `field` which can be used in subsequent `&&` clauses.

That should be enough background on the part of core Verus we're using to verify
concurrent types.  The [`Verus reference book`](https://verus-lang.github.io/verus/guide/overview.html)
is helpful for a more in-depth reference.

The next page will cover the state machine functionality that helps us model
and verify concurrency.
