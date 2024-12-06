struct Mutex<T> {}

enum LockError {}

enum TryLockError {}

type LockResult<T> = Result<T, LockError>;

impl<T> Mutex<T> {
    pub fn lock(&self) -> LockResult<MutexGuard<'_, T>>;

    pub fn try_lock(&self) -> Result<MutexGuard<'_, T>, TryLockError>;

    pub fn is_poisoned(&self) -> bool;

    pub fn clear_poison(&self);

    pub fn get_mut(&mut self) -> LockResult<&mut T>;

    pub fn into_inner(self) -> LockResult<T>;
}
