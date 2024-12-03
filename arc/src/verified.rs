use state_machines_macros::tokenized_state_machine;
use vstd::{
    atomic::{PAtomicUsize, PermissionUsize},
    invariant::{open_atomic_invariant, AtomicInvariant},
    prelude::*,
    shared::Shared,
    simple_pptr::{PPtr, PointsTo},
};

verus! {
    #[verifier::external_body]
    pub fn abort<T>() -> (ret: T)
        ensures false
    {
        std::process::abort()
    }

    tokenized_state_machine! {
        AbstractRc<T> {
            fields {
                #[sharding(constant)]
                pub perm: T,
                #[sharding(storage_option)]
                pub storage: Option<T>,
                #[sharding(variable)]
                pub strong: nat,
                #[sharding(count)]
                pub strong_token: nat,
            }

            #[invariant]
            pub open spec fn storage_inv(&self) -> bool {
                self.storage is Some ==> self.storage === Some(self.perm)
            }

            #[invariant]
            pub open spec fn count_inv(&self) -> bool {
                self.strong >= 1 <==> self.storage is Some
            }

            #[invariant]
            pub open spec fn token_inv(&self) -> bool {
                self.strong == self.strong_token
            }

            init! {
                new(item: T) {
                    init perm = item;
                    init strong = 1;
                    init strong_token = 1;
                    init storage = Some(item);
                }
            }

            #[inductive(new)]
            proof fn new_pf(post: Self, item: T) {

            }

            transition! {
                new_clone() {
                    require pre.strong >= 1;
                    add strong_token += (1);
                    update strong = pre.strong + 1;
                }
            }

            #[inductive(new_clone)]
            proof fn new_clone_pf(pre: Self, post: Self) {

            }

            transition! {
                drop_still_alive() {
                    require pre.strong >= 2;
                    remove strong_token -= (1);
                    update strong = (pre.strong - 1) as nat;
                }
            }

            #[inductive(drop_still_alive)]
            proof fn drop_still_alive_pf(pre: Self, post: Self) {

            }

            transition! {
                into_inner() {
                    require pre.strong == 1;
                    remove strong_token -= (1);
                    update strong = 0;
                    withdraw storage -= Some(pre.perm);
                }
            }

            #[inductive(into_inner)]
            proof fn into_inner_pf(pre: Self, post: Self) {
            }

            property! {
                borrow() {
                    have strong_token >= (1);
                    guard storage >= Some(pre.perm);
                }
            }

            property! {
                imply_nonzero() {
                    have strong_token >= (1);
                    assert pre.strong >= 1;
                }
            }
        }
    }

    pub struct ArcInner<T> {
        pub atomic: PAtomicUsize,
        pub value: T,
    }

    type Perm<T> = PointsTo<ArcInner<T>>;

    pub tracked struct MutableState<T> {
        pub strong: AbstractRc::strong<Perm<T>>,
        pub atomic: PermissionUsize,
    }

    struct_with_invariants! {
        struct Arc<T> {
            ptr: PPtr<ArcInner<T>>,
            // TODO: phantom
            instance: Tracked<AbstractRc::Instance<Perm<T>>>,
            token: Tracked<AbstractRc::strong_token<Perm<T>>>,
            inv: Tracked<Shared<AtomicInvariant<_, MutableState<T>, _>>>,
        }

        pub closed spec fn wf(&self) -> bool {
            predicate {
                &&& self.token@.view().instance == self.instance@
                &&& self.token@@.count == 1
                &&& self.instance@.perm().pptr() == self.ptr
                &&& self.instance@.perm().is_init()
            }

            invariant on inv
                with (instance)
                specifically (self.inv@@)
                is (state: MutableState<T>)
            {
                &&& state.atomic.is_for(instance@.perm().value().atomic)
                &&& state.atomic@.value == state.strong@.value
                &&& state.strong@.value <= MAX_REFCOUNT as nat
                &&& state.strong@.instance == instance@
            }
        }
    }

    // arbitrary constant
    spec const ARC_INVARIANT_NAMESPACE: int = 17;

    pub const MAX_REFCOUNT: usize = isize::MAX as usize;

    impl <T> Arc<T> {
        pub closed spec fn view(&self) -> T {
            self.instance@.perm().value().value
        }

        pub fn new(value: T) -> (ret: Self)
          ensures ret.wf()
        {
            let (atomic, Tracked(atomic_perm)) = PAtomicUsize::new(1);

            let (ptr, Tracked(ptr_perm)) = PPtr::new(ArcInner {
                atomic,
                value,
            });

            let tracked (
                Tracked(instance),
                Tracked(strong),
                Tracked(strong_token)
            ) = AbstractRc::Instance::new(ptr_perm, Some(ptr_perm));

            let tracked instance_ = instance.clone();
            let instance_ = Tracked(instance_);

            let tracked inv = AtomicInvariant::new(
                instance_,
                MutableState {
                    atomic: atomic_perm,
                    strong,
                },
                ARC_INVARIANT_NAMESPACE,
            );

            let tracked inv = Shared::new(inv);

            Self {
                ptr,
                instance: Tracked(instance),
                inv: Tracked(inv),
                token: Tracked(strong_token),
            }
        }

        fn inner<'s>(&'s self) -> (ret: &'s ArcInner<T>)
            requires self.wf(),
            ensures self.instance@.perm().value() === *ret
        {
            let tracked instance = self.instance.borrow();
            let tracked token = self.token.borrow();
            let tracked perm = instance.borrow(token);
            self.ptr.borrow(Tracked(perm))
        }

        pub fn borrow<'s>(&'s self) -> (ret: &'s T)
            requires self.wf()
            ensures *ret === self@
        {
            &self.inner().value
        }


        pub fn clone(&self) -> (ret: Self)
            requires self.wf(),
            ensures
                ret.wf(),
                ret@ === self@,
        {
            let inner = self.inner();


            let tracked inv = self.inv.borrow().borrow();

            let ret;
            let tracked token;

            open_atomic_invariant! (
                inv => state => {
                    ret = inner.atomic.fetch_add(Tracked(&mut state.atomic), 1);
                    let tracked () = self.instance.borrow().imply_nonzero(&state.strong, self.token.borrow());
                    let tracked token_ = self.instance.borrow().new_clone(&mut state.strong);
                    proof {
                        token = token_;
                    }
                    // we will abort, but we can't do it atomically, so we have to
                    // do it after the invariant is closed
                    assume(ret <= MAX_REFCOUNT - 1);
                }
            );

            if ret >= MAX_REFCOUNT {
                return abort();
            }

            let tracked instance = self.instance.borrow().clone();
            let tracked inv = self.inv.borrow().clone();

            Self {
                ptr: self.ptr.clone(),
                instance: Tracked(instance),
                inv: Tracked(inv),
                token: Tracked(token),
            }
        }

        pub fn drop(self)
            requires self.wf()
        {
            let Arc {
                ptr,
                instance: Tracked(instance),
                inv: Tracked(inv),
                token: Tracked(token)
            } = self;

            let tracked perm = instance.borrow(&token);
            let inner = ptr.borrow(Tracked(perm));

            let count;
            let tracked owned_perm = None;

            open_atomic_invariant!(
                inv.borrow() => state => {
                    let tracked () = instance.imply_nonzero(&state.strong, &token);
                    count = inner.atomic.fetch_sub(Tracked(&mut state.atomic), 1);
                    if count > 1 {
                        let tracked () = instance.drop_still_alive(&mut state.strong, token);
                    } else {
                        assert(count == 1);
                        proof {
                            let tracked perm = instance.into_inner(&mut state.strong, token);
                            owned_perm = Some(perm);
                        }
                    }
                }
            );

            if count == 1 {
                let tracked owned_perm = match owned_perm {
                    Some(o) => o,
                    None => proof_from_false(),
                };

                let _ = ptr.into_inner(Tracked(owned_perm));
            }
        }
    }

}

fn main() {
    let item = Arc::new("hello! it's me");

    {
        let item2 = Arc::clone(&item);

        println!("{}", item.borrow());
        println!("{}", item2.borrow());
        item2.drop();
    }

    println!("{}", item.borrow());

    item.drop();
}
