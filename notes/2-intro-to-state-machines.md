This part of the guide is based mostly on the [Verus Transition Systems](https://verus-lang.github.io/verus/state_machines/intro.html)
book, as well as my notes on the reference docs and source code.

## State machine

To prove properties of concurrent code, Verus lets us make a state machine that
is an abstraction of the behavior of our system.  Like classical state machines,
these consist of state and transitions between states.  However, these state machines
also encode invariants about the machine, and functions that prove that these
invariants hold. The `{tokenized_,}state_machine!` set of macros are how we
declare and create state machines:

```rs
use state_machines_macros::state_machine;

state_machine! {
    ThreevenChecker {
        // state goes here
        fields {
            pub parity: nat,
        }

        // transition(s?) that initialize state
        init! {
            start() {
                init parity = 0;
            }
        }

        transition! {
            add(n: nat) {
                update parity = (pre.parity + n) % 3;
            }
        }

        // declare invariants here, in `spec` code
        #[invariant]
        pub fn less_than_3(&self) -> bool {
            self.parity < 3
        }

        // proofs section - read more below
        #[inductive(start)]
        fn start_inductive(post: Self) {}

        #[inductive(add)]
        fn add_inductive(pre: Self, post: Self, n: nat) {}
    }
}
```

The proofs section makes sure that all invariants are always true in every valid
state, proven inductively.  For initializers, we need to prove that the invariant
holds in the `post` state after the initializer has run.  For each transition,
we need to show that, if `pre` is a valid state where the invariants hold, the
state `post` after taking the given transition with the given args (in the `add`
case, `n`) also holds the invariants.  Thankfully, Verus and the SMT solver can
often verify these properties on their own, which is why the bodies are empty here,
but sometimes you will have to add extra assertions or lemmas to help the solver.

Transitions can have preconditions on their arguments, but this is specified with
a `requires` statement *inside the transition body*.

## Tokens

To help prove {unsafe, concurrent} code, Verus uses token instances to prove that
it is valid to do an operation considered unsafe by Rust's type checker.

In normal Rust, interior mutability requires `unsafe` code to perform.  Verus uses
*tracked token* instances that prove that doing an unsafe operation is valid and
not undefined behavior.

Consider the [`PPtr`](https://verus-lang.github.io/verus/verusdoc/vstd/simple_pptr/struct.PPtr.html)
type.  A `PPtr<T>` corresponds to a `*mut MaybeUninit<T>` (TODO: is it a `NonNull<_<T>>`?).

However, the function `PPtr::new(T)` returns a pair `(Self, Tracked<PointsTo<T>>)`.
(`Tracked<T>` is a `T` that only exists in ghost code and the verifier keeps track
of the value (TODO - more information on this)).  The `PointsTo` ghost object
represents permission to use the pointer according to Rust's ownership rules:
`read` takes a `&PointsTo`, `write` a `&mut PointsTo`, and `free` takes a `PointsTo`.
(there are more checks and methods because this pointer could be uninitialized,
but this is the general idea).

TODO: talk about general pointer (provenance) implementation, if it is necessary
in the examples.

## Opening invariants

Sometimes, we need to express behavior that is invalid by these ownership rules,
but is still defined behavior.


[TODO: organize] One option is to use `tracked` code, where the verifier keeps
track of the value in an e.g. cell and can prove assertions based on that. But
this is bad/not always possible (why?).

### LocalInvariant and AtomicInvariant

Invariants provide a form of interior mutability for ghost code while still
helping to prove that that behavior is valid.  Instead of reasoning about a
*specific* value inside the container, enforce that whatever value is in the
container satisfies some invariant.  Invariants can be "opened" to modify a value,
but must return a new value that satisfies the invariant at the end.

If the object that contains interior mutability doesn't need to be `Sync`, use
[`LocalInvariant`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/struct.LocalInvariant.html).
To modify a value inside a `LocalInvariant`, use
[`open_local_invariant!`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/macro.open_local_invariant.html):

```rs
open_local_invariant!(inv => id => {
    // id is a &mut V value.  It is guaranteed that the invariant `inv.inv(id)`
    // holds here.

    // use, modify, and/or replace `id`.

    // new_value **must** satisfy the invariant.
    new_value
});
```

Thus, inductively (since `LocalInvariant::new(_, v, _)` requires `v` to satisfy
the invariant), the value inside the invariant `inv` at any point outside of a
`open_local_invariant!`, the invariant must hold.

However, if an object with interior mutability needs to be `Sync`, use the dual
[`AtomicInvariant`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/struct.AtomicInvariant.html).
Like `LocalInvariant`s, an `AtomicInvariant` can be opened with
[`open_atomic_invariant!`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/macro.open_atomic_invariant.html),
with the important additional constraint that the block where the invariant was opened
must be atomic (sequentially consistent). Atomics for synchronization are in the
[`vstd::atomic`](https://verus-lang.github.io/verus/verusdoc/vstd/atomic/index.html)
module, but Verus provides the
[`atomic_ghost`](https://verus-lang.github.io/verus/verusdoc/vstd/atomic_ghost/index.html)
module that provides higher-level abstractions for working with atomic invariants.

An `atomic_ghost` type, like [`AtomicU64`](https://principled-systems.github.io/verus/verusdoc/vstd/atomic_ghost/struct.AtomicU64.html)
provides a memory location that can be atomically accessed and modified, but also
stores associated ghost state (type parameter `G`).

The [`atomic_with_ghost!`](https://verus-lang.github.io/verus/verusdoc/vstd/atomic_ghost/macro.atomic_with_ghost.html)
macro performs some operation on one of these atomic types, which also allows
access to the inner ghost state at the same time:

```rs
atomic_with_ghost!(
    x => fetch_add(1);
    // bind name `prev` to the previous value, and `next` to the new value,
    // for use in the ghost block
    update prev -> next;
    ghost g => {
        // inductive `proof` block.
        // given that x's atomic invariant holds,
        // and that (for the fetch_add case), `next == prev + 1`,
        // use, mutate, and/or replace `g`, such that:

        // the final returned ghost value new_value is the same type as `G`,
        // and the atomic invariant holds on new_value.
        new_value
    }
);
```

See the macro's documentation for more information about the syntax and behavior.

## Structs with invariants

An detail that I glossed over earlier is that `Invariant` and `atomic_ghost::Atomic*`
types have many generic parameters.  Specifially, they have the form `T<K, V, Pred>`,
where:
- `Pred` implements [`InvariantPredicate<K, V>`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/trait.InvariantPredicate.html),
  which has a `spec fn inv(K, V) -> bool` that specifies the predicate parameterized
  by `K` and `V`
- `V` is the value type for interior mutability.
- `K` is a constant type, which lets the user configure the predicate in a way that
  can't be expressed at the type level `Pred` (TODO: is this right?)

TODO: `Atomic*` types take a `AtomicPredicate` type, not an `InvariantPredicate`.
Does this matter?


The [`struct_with_invariants!`](https://verus-lang.github.io/verus/verusdoc/vstd/pervasive/macro.struct_with_invariants.html)
macro simplifies declaring a `struct` whose fields contain types with these predicates.
It lets you declare a `field: AtomicUsize<_, V, _>` and declare predicate functions,
and the macro creates the necessary `K` and `Pred` types:

TODO: create an example.  Refer to the macro documentation for the syntax and
semantics of declaring these invariant functions.

## Tokenizing state machines

Now, let's put it all together.  We can define a state machine, and break it up
into tokens (ghost state), and use interior mutability on these tokens to prove
that our program is correct.

The `state_machines_macros::tokenized_state_machine!` macro is similar to the
non-tokenized version, except for the *sharding declarations*:

```rs
tokenized_state_machine! {
    X {
        fields {
            #[sharding(variable)]
            pub counter: int,

            #[sharding(variable)]
            pub inc_a: bool,

            #[sharding(variable)]
            pub inc_b: bool,
        }

        init! {
            initialize() {
                init counter = 0;
                init inc_a = false;
                init inc_b = false;
            }
        }
    }
}
```

TODO: I stole this example from the counting to 2 page in the book.  Change this
to `OnceCell/Lock` maybe once I better understand it.

`#[sharding(variable)]` means there is one instance of the token for the field
it marks for each instance of the state machine.  We'll look at the different types
of sharding later, but first, what does it mean to instantiate the state machine?

The `tokenized_state_machine!` creates the types `X::Instance` and `X::field`
for each sharded struct field in the state machine.  To create an instance of
the state machine, call `X::Instance::initialize`, where `initialize` is one of
the transitions in the `init!` block:

```rs
let tracked (
    Tracked(instance),
    Tracked(counter_token),
    Tracked(inc_a_token),
    Tracked(inc_b_token),
) = X::Instance::initialize();
```

`instance` is `Clone`, but each of the other values are tokens that represent
permission to use that field, according to Rust's ownership rules. (so `&token` to
read its corresponding field, `&mut` to modify, etc.)

That is, any `transition!` or `property!` that needs to access `field` needs an
`&X::field`, and any `transition!` that `updates` `field` needs an `&mut X::field`.A

TODO: find a source for this ^

These tokens are ghost values, so we can store them in invariant-guarded interior
mutability, if we need to synchronize or share tokens outside of Rust's borrowing
rules.

## Sharding

A field `field` of type `T` in the state machine can be marked as
`#[sharding(strategy)]` where strategy is one of:

- `constant` - this means the field cannot be updated after initialization.  No
  token is needed to read this (because it can't be mutated), and it can be accessed
  using `instance.field()`.
- `variable` - as seen above, the macro creates a token of type `X::field` that
  follows Rust's ownership rules to read or write to this field in transitions
  and properties.
- TODO: fill out more with ones used in our verification

There are more specialized sharding strategies.  See the
[reference](https://verus-lang.github.io/verus/state_machines/strategy-reference.html)
for more  information.
