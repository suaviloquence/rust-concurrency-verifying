use state_machines_macros::tokenized_state_machine;
use vstd::{
    atomic_ghost::{atomic_with_ghost, AtomicU8},
    cell::{PCell, PointsTo},
    prelude::*,
};

verus! {
    pub enum LockState {
        Unlocked,
        Locked,
        // Poisoned,
    }

    #[verifier::external_body]
    fn spin_loop() {
        core::hint::spin_loop();
    }

    tokenized_state_machine! {
        LockMachine<T> {
            fields {
                #[sharding(storage_option)]
                pub storage: Option<T>,
                #[sharding(variable)]
                pub obj: T,
                #[sharding(variable)]
                pub state: LockState,
                #[sharding(bool)]
                pub lock: bool,
            }

            #[invariant]
            pub fn storage_inv(&self) -> bool {
                self.storage is Some ==> self.obj === self.storage->0
            }

            #[invariant]
            pub fn lock_inv(&self) -> bool {
                self.lock ==> self.storage is None
            }

            #[invariant]
            pub fn state_inv(&self) -> bool {
                match self.state {
                    LockState::Unlocked => self.storage is Some && !self.lock,
                    // State::Poisoned => true,
                    LockState::Locked => self.storage is None && self.lock,
                }
            }

            init! {
                new(value: T) {
                    init obj = value;
                    init storage = Some(value);
                    init state = LockState::Unlocked;
                    init lock = false;
                }
            }

            #[inductive(new)]
            proof fn new_pf(post: Self, value: T) {}

            transition! {
                lock_start() {
                    require pre.state == LockState::Unlocked;
                    add lock += true;
                    // update state = LockState::Poisoned;
                    update state = LockState::Locked;
                    withdraw storage -= Some(pre.obj);
                }
            }

            #[inductive(lock_start)]
            proof fn lock_start_pf(pre: Self, post: Self) {}

            transition! {
                lock_finish(value: T) {
                    remove lock -= true;
                    require pre.state == LockState::Locked;

                    update obj = value;
                    update state = LockState::Unlocked;
                    deposit storage += Some(value);
                }
            }

            #[inductive(lock_finish)]
            proof fn lock_finish_pf(pre: Self, post: Self, value: T) {}

            property! {
                lock_implies_locked() {
                    have lock >= true;
                    assert(pre.state is Locked);
                }
            }
        }
    }

    pub struct MutableState<T> {
        pub state: LockMachine::state<PointsTo<T>>,
        pub obj: LockMachine::obj<PointsTo<T>>,
    }

    struct_with_invariants! {
        pub struct Mutex<T> {
            cell: PCell<T>,
            state: AtomicU8<_, MutableState<T>, _>,
            instance: Tracked<LockMachine::Instance<PointsTo<T>>>,
        }

        pub closed spec fn wf(&self) -> bool {
            invariant on state with (instance, cell)
            is (v: u8, g: MutableState<T>) {
                &&& 0 <= v <= 1
                &&& g.state@.instance == instance@
                &&& g.obj@.instance == instance@
                &&& g.obj@.value.id() == cell.id()
                &&& g.state@.value is Unlocked <==> v == 0 && g.obj@.value.is_init()
                &&& g.state@.value is Locked <==> v == 1
            }
        }
    }

    pub struct MutexGuard<'a, T> {
        lock: Tracked<LockMachine::lock<PointsTo<T>>>,
        perm: Tracked<PointsTo<T>>,
        mutex: &'a Mutex<T>,
        item: T,
    }

    impl<'a, T> MutexGuard<'a, T> {
        pub closed spec fn view(&self) -> T {
            self.item
        }

        pub closed spec fn wf(&self) -> bool {
            &&& self.lock@@.instance == self.mutex.instance@
            &&& self.perm@.is_uninit()
            &&& self.mutex.wf()
            &&& self.perm@.id() == self.mutex.cell.id()
        }

        pub fn borrow(&self) -> &T
          requires self.wf()
        {
            &self.item
        }

        // FIXME: this should not be external, but we currently get this error:
        // error: The verifier does not yet support the following Rust feature: &mut types, except in special cases
        #[verifier::external]
        pub fn borrow_mut(&mut self) -> &mut T
          requires self.wf()
        {
            &mut self.item
        }

        pub fn drop(self)
          requires self.wf()
        {
            let Self {
                lock: Tracked(lock),
                perm: Tracked(mut perm),
                mutex,
                item
            } = self;

            mutex.cell.put(Tracked(&mut perm), item);

            let _ = atomic_with_ghost! (
                mutex.state => compare_exchange(1, 0);
                returning ret;
                ghost g => {
                    let tracked () = mutex.instance.borrow().lock_implies_locked(&g.state, &lock);
                    assert(ret == Ok::<u8, u8>(1));
                    mutex.instance.borrow().lock_finish(perm, perm, &mut g.obj, &mut g.state, lock);
                }
            );
        }
    }

    impl<T> Mutex<T> {
        pub fn new(value: T) -> (r: Self)
          ensures r.wf(),
        {
            let (cell, Tracked(perm)) = PCell::new(value);

            let tracked (
                Tracked(instance),
                Tracked(obj),
                Tracked(state),
                // lock is none
                _,
            ) = LockMachine::Instance::new(perm, Some(perm));

            let tracked instance_ = instance.clone();

            let state = AtomicU8::new(Ghost((Tracked(instance_), cell)), 0, Tracked(MutableState { state, obj }));

            Self {
                cell,
                state,
                instance: Tracked(instance),
            }
        }

        pub fn lock(&self) -> MutexGuard<'_, T>
            requires self.wf()
        {
            let tracked mut ghst = None;
            while atomic_with_ghost!(
                self.state => compare_exchange(0, 1);
                returning ret;
                ghost g => {
                    if ret == Ok::<u8, u8>(0) {
                        let tracked r = self.instance.borrow().lock_start(&g.obj, &mut g.state);
                        ghst = Some(r);
                    }
                }
            ).is_err() invariant self.wf() {
                spin_loop();
            }

            let tracked (Tracked(perm), Tracked(lock)) = match ghst {
                Some(x) => x,
                None => proof_from_false(),
            };

            let item = self.cell.take(Tracked(&mut perm));

            MutexGuard {
                perm: Tracked(perm),
                lock: Tracked(lock),
                item,
                mutex: self,
            }
        }
    }
}

fn main() {
    let mutex = Mutex::new(4);

    let mut guard = mutex.lock();
    *guard.borrow_mut() = 3;
    guard.drop();

    std::thread::scope(|f| {
        f.spawn(|| {
            let mut guard = mutex.lock();
            *guard.borrow_mut() += 3;
            guard.drop();
        });

        f.spawn(|| {
            let mut guard = mutex.lock();
            *guard.borrow_mut() += 4;
            guard.drop();
        });
    });

    let guard = mutex.lock();
    println!("{}", *guard.borrow());
    guard.drop();
}
