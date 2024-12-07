use state_machines_macros::tokenized_state_machine;
use vstd::{
    atomic_ghost::{atomic_with_ghost, AtomicU8},
    cell::{CellId, PCell, PointsTo},
    prelude::*,
};

verus! {
    #[verifier::external_body]
    fn spin_loop() {
        std::hint::spin_loop();
    }

    tokenized_state_machine! {
        OnceMachine<T> {
            fields {
                #[sharding(constant)]
                pub cell: CellId,
                #[sharding(storage_option)]
                pub storage: Option<PointsTo<T>>,
                #[sharding(bool)]
                pub uninitialized: bool,
                #[sharding(bool)]
                pub lock: bool,
                #[sharding(persistent_option)]
                pub initialized: Option<PointsTo<T>>,
            }

            #[invariant]
            pub fn storage_inv(&self) -> bool {
                &&& self.uninitialized ==> (self.storage matches Some(x) && x.is_uninit())
                &&& self.initialized is Some ==> (self.storage matches Some(x) && x == self.initialized->0 && x.is_init())
                &&& self.lock ==> self.storage is None
                &&& self.storage is Some ==> self.cell == self.storage->0.id()
            }

            #[invariant]
            pub fn state_inv(&self) -> bool {
                &&& self.uninitialized <==> !self.lock && self.initialized is None
                &&& self.lock <==> !self.uninitialized && self.initialized is None
                &&& self.initialized is Some <==> !self.uninitialized && !self.lock
            }

            #[invariant]
            pub fn init_inv(&self) -> bool {
                if let Some(x) = self.initialized {
                    x.is_init() && x.id() == self.cell
                } else {
                    true
                }
            }

            init! {
                new_uninit(value: PointsTo<T>) {
                    require value.is_uninit();
                    init cell = value.id();
                    init storage = Some(value);
                    init lock = false;
                    init initialized = None;
                    init uninitialized = true;
                }
            }

            #[inductive(new_uninit)]
            proof fn new_uninit_pf(post: Self, value: PointsTo<T>) {}

            transition! {
                lock() {
                    remove uninitialized -= true;
                    withdraw storage -= Some(let perm);
                    assert(perm.is_uninit());
                    assert(perm.id() == pre.cell);
                    add lock += true;
                }
            }

            #[inductive(lock)]
            proof fn lock_pf(pre: Self, post: Self) {}

            transition! {
                write(value: PointsTo<T>) {
                    require value.is_init();
                    require value.id() == pre.cell;
                    remove lock -= true;
                    deposit storage += Some(value);
                    add initialized (union)= Some(value);
                }
            }

            #[inductive(write)]
            proof fn write_pf(pre: Self, post: Self, value: PointsTo<T>) {}

            property! {
                borrow() {
                    have initialized >= Some(let x);
                    assert(x.is_init());
                    assert(x.id() == pre.cell);
                    guard storage >= Some(x);
                }
            }
        }
    }

    pub enum State<T> {
        Uninit(OnceMachine::uninitialized<T>),
        Locked,
        Init(OnceMachine::initialized<T>),
    }

    struct_with_invariants! {
        pub struct OnceLock<T> {
            cell: PCell<T>,
            state: AtomicU8<_, State<T>, _>,
            instance: Tracked<OnceMachine::Instance<T>>,
        }

        pub closed spec fn wf(&self) -> bool {
            predicate {
                self.cell.id() == self.instance@.cell()
            }

            invariant on state with (instance)
            is (v: u8, g: State<T>) {
                &&& 0 <= v <= 2
                &&& v == 0 <==> g is Uninit
                &&& v == 1 <==> g is Locked
                &&& v == 2 <==> g is Init
                &&& g is Uninit ==> g->Uninit_0@.instance == instance@
                &&& g is Init ==> g->Init_0@.instance == instance@
            }
        }
    }

    impl <T: 'static> OnceLock<T> {
        pub fn new() -> (ret: Self)
            ensures ret.wf()
        {
            let (cell, Tracked(perm)) = PCell::empty();

            let tracked (
                Tracked(instance),
                Tracked(uninit),
                _, // lock
                _, // initialized
            ) = OnceMachine::Instance::new_uninit(perm, Some(perm));

            let tracked uninit = match uninit {
                Some(x) => x,
                None => proof_from_false(),
            };

            let tracked instance_ = instance.clone();

            Self {
                cell,
                state: AtomicU8::new(Ghost(Tracked(instance_)), 0, Tracked(State::Uninit(uninit))),
                instance: Tracked(instance),
            }
        }

        pub fn get_or_init<F: FnOnce() -> T>(&self, f: F) -> &T
            requires
                self.wf(),
                f.requires(()),
        {
            let tracked mut init = None;
            let tracked mut lock = None;
            let ret = atomic_with_ghost!(
                self.state => compare_exchange(0, 1);
                update old -> new;
                ghost g => {
                    if old == 0 {
                        let tracked mut state = State::Locked;
                        vstd::modes::tracked_swap(&mut state, &mut g);
                        let tracked uninit = match state {
                            State::Uninit(x) => x,
                            _ => proof_from_false(),
                        };
                        let tracked l = self.instance.borrow().lock(uninit);
                        lock = Some(l);
                    } else if old == 2 {
                        let tracked i = match &g {
                            State::Init(x) => x.clone(),
                            _ => proof_from_false(),
                        };

                        init = Some(i);
                    }
                }
            );

            match ret {
                Err(2) => (),
                Err(1) => (while atomic_with_ghost!(
                    self.state => load();
                    returning ret;
                    ghost g => {
                        if ret == 2 {
                            let tracked i = match &g {
                                State::Init(x) => x.clone(),
                                _ => proof_from_false(),
                            };
                            init = Some(i);
                        }
                    }
                ) != 2
                invariant self.wf() {
                    spin_loop();
                }),
                Ok(0) => {
                    let tracked (Tracked(mut perm), Tracked(lock)) = match lock {
                        Some(x) => x,
                        None => proof_from_false(),
                    };

                    let value = f();
                    self.cell.put(Tracked(&mut perm), value);

                    let tracked i = self.instance.borrow().write(perm, perm, lock);

                    atomic_with_ghost!(
                        self.state => store(2);
                        ghost g => {
                            let tracked init = i.clone();
                            g = State::Init(init);
                        }
                    );

                    proof {
                        init = Some(i);
                    }
                },
                _ => assert(false),
            };

            let tracked init = match init {
                Some(x) => x,
                None => proof_from_false()
            };

            assert(init@.instance == self.instance@);


            let tracked init: &'static _ = vstd::modes::tracked_static_ref(init);
            let tracked inst: &'static _ = vstd::modes::tracked_static_ref(self.instance.borrow().clone());
            let tracked perm: &'static _ = inst.borrow(init);

            self.cell.borrow(Tracked(perm))
        }
    }
}

fn main() {
    let lock = OnceLock::new();

    println!("{}", lock.get_or_init(|| 3));
    println!("{}", lock.get_or_init(|| 4));
    println!("{}", lock.get_or_init(|| 5));
}
