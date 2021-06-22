use std::{
    alloc::{alloc, dealloc, Layout},
    iter::{FromIterator, Take},
    marker::PhantomPinned,
    mem,
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
};

/// A node of a `LinkedList`.
///
/// Contains the data and the pointers to the next and previous nodes.
///
/// This is an internal unsafe type, `next` and `prev` may be left dangling in some cases.
#[derive(Debug)]
struct Node<T> {
    next: NonNull<Node<T>>,
    prev: NonNull<Node<T>>,
    data: T,
    pin_: PhantomPinned,
}

impl<T> Node<T> {
    /// Creates a new `Node` containing `data` and returns a pointer to it.
    ///
    /// # Safety
    ///
    /// The `prev` and `next` pointers may or may not be dangling.
    unsafe fn new(data: T, prev: NonNull<Node<T>>, next: NonNull<Node<T>>) -> NonNull<Node<T>> {
        // SAFETY: We check for null pointer returned by alloc with NonNull::new().unwrap()
        let node = NonNull::new(alloc(Layout::new::<Node<T>>()) as *mut Node<T>).unwrap();
        ptr::write(
            node.as_ptr(),
            Node {
                data,
                prev,
                next,
                pin_: PhantomPinned,
            },
        );
        node
    }
    /// Creates a new `Node` containing `data` and returns a pointer to it.
    ///
    /// The new `Node` has its `next` and `prev` members pointing to itself.
    fn new_circular(data: T) -> NonNull<Node<T>> {
        unsafe {
            // SAFETY: This is safe because `prev` and `next` are pointing to a valid `Node`.
            let mut node = Node::new(data, NonNull::dangling(), NonNull::dangling());
            node.as_mut().next = node;
            node.as_mut().prev = node;
            node
        }
    }
    /// Creates a chain of `Node`s with the elements from `iter`.
    ///
    /// Returns a tuple with the pointers to the first and last `Node`s, as well as the count of `Node`s in the chain.
    /// Iff `iter` is empty, this function returns `None`.
    ///
    /// # Safety
    ///
    /// The `first.prev` and `last.next` pointers are left dangling.
    unsafe fn create_chain_dangling(
        mut iter: impl Iterator<Item = T>,
    ) -> Option<(NonNull<Node<T>>, NonNull<Node<T>>, usize)> {
        let first = Node::new(iter.next()?, NonNull::dangling(), NonNull::dangling());
        let mut current = first;
        let mut count = 1;
        for item in iter {
            let new_node = Node::new(item, current, NonNull::dangling());
            current.as_mut().next = new_node;
            current = new_node;
            count += 1;
        }
        Some((first, current, count))
    }
    /// Creates a circular chain of `Node`s with the elements from `iter`.
    ///
    /// Returns a pointer to the first `Node`, as well as the count of `Node`s in the chain.
    /// Iff `iter` is empty, this function returns `None`.
    fn create_chain_circular(iter: impl Iterator<Item = T>) -> Option<(NonNull<Node<T>>, usize)> {
        unsafe {
            // SAFETY: This is safe because we fix the dangling pointers from the first and last nodes.
            let (mut first, mut last, count) = Node::create_chain_dangling(iter)?;
            first.as_mut().prev = last;
            last.as_mut().next = first;
            Some((first, count))
        }
    }
    /// Inserts a new node with `data` after the `current` node.
    ///
    /// # Safety
    ///
    /// `current` and `current.next` should not be dangling.
    unsafe fn insert_after(mut current: NonNull<Node<T>>, data: T) -> NonNull<Node<T>> {
        let mut next = current.as_ref().next;
        let node = Node::new(data, current, next);
        current.as_mut().next = node;
        next.as_mut().prev = node;
        node
    }

    /// Inserts a new node with `data` before the `current` node.
    ///
    /// # Safety
    ///
    /// `current` and `current.prev` should not be dangling.
    unsafe fn insert_before(mut current: NonNull<Node<T>>, data: T) -> NonNull<Node<T>> {
        let mut prev = current.as_ref().prev;
        let node = Node::new(data, prev, current);
        current.as_mut().prev = node;
        prev.as_mut().next = node;
        node
    }

    /// Deallocates `current`.
    ///
    /// Returns the `data` from `current`.
    ///
    /// # Safety
    ///
    /// `current` should not be dangling.
    /// References to `current` will no longer be valid.
    unsafe fn delete_raw(current: NonNull<Node<T>>) -> T {
        let data = ptr::read(current.as_ptr()).data;
        dealloc(current.as_ptr() as *mut u8, Layout::new::<Node<T>>());
        data
    }

    /// Deallocates `current`, and fixes the references from `current.prev` and `current.next`.
    ///
    /// Returns the `data` from `current`, as well as the pointer to the next `Node`.
    /// Iff `current.next == current`, returns `None` instead of the pointer to the next `Node`.
    ///
    /// # Safety
    ///
    /// `current`, `current.prev` and `current.next` should not be dangling.
    /// Other references to `current` will no longer be valid.
    unsafe fn delete(current: NonNull<Node<T>>) -> (T, Option<NonNull<Node<T>>>) {
        let mut prev = current.as_ref().prev;
        let mut next = current.as_ref().next;
        (
            Node::delete_raw(current),
            if current != next {
                prev.as_mut().next = next;
                next.as_mut().prev = prev;
                Some(next)
            } else {
                None
            },
        )
    }
}

/// A circular linked list.
///
/// Every node in the list contains references to the previous and next nodes.
#[derive(Debug)]
pub struct LinkedList<T> {
    head: NonNull<Node<T>>,
    length: usize,
}

impl<T> LinkedList<T> {
    /// Creates a new empty `LinkedList`.
    pub fn new() -> Self {
        LinkedList {
            head: NonNull::dangling(),
            length: 0,
        }
    }
    /// Returns the number of elements in the list.
    pub const fn len(&self) -> usize {
        self.length
    }
    /// Returns `true` if the list contains no elements.
    pub const fn is_empty(&self) -> bool {
        self.length == 0
    }
    /// Returns a `LinkedListIndex` to the first node of the list (`head`), or `None` if the list is empty.
    pub fn first<'a>(&'a self) -> Option<LinkedListIndex<'a, T>> {
        unsafe {
            // SAFETY: self.head can only be dangling if the LinkedList is empty
            if !self.is_empty() {
                Some(LinkedListIndex::new(self, self.head))
            } else {
                None
            }
        }
    }
    /// Returns a `LinkedListIndexMut` to the first node of the list (`head`), or `None` if the list is empty.
    pub fn first_mut<'a>(&'a mut self) -> Option<LinkedListIndexMut<'a, T>> {
        unsafe {
            // SAFETY: self.head can only be dangling if the LinkedList is empty
            if !self.is_empty() {
                Some(LinkedListIndexMut::new(self, self.head))
            } else {
                None
            }
        }
    }
    /// Returns a `LinkedListIndex` to the last node of the list (`head.prev`), or `None` if the list is empty.
    pub fn last<'a>(&'a self) -> Option<LinkedListIndex<'a, T>> {
        unsafe {
            // SAFETY: self.head can only be dangling if the LinkedList is empty
            if !self.is_empty() {
                Some(LinkedListIndex::new(self, self.head.as_ref().prev))
            } else {
                None
            }
        }
    }
    /// Returns a `LinkedListIndexMut` to the last node of the list (`head.prev`), or `None` if the list is empty.
    pub fn last_mut<'a>(&'a mut self) -> Option<LinkedListIndexMut<'a, T>> {
        unsafe {
            // SAFETY: self.head can only be dangling if the LinkedList is empty
            if !self.is_empty() {
                Some(LinkedListIndexMut::new(self, self.head.as_ref().prev))
            } else {
                None
            }
        }
    }
    /// Appends a new node with `data` to the end of the list.
    pub fn push(&mut self, data: T) {
        if let Some(mut index) = self.last_mut() {
            index.insert_after(data);
        } else {
            self.head = Node::new_circular(data);
            self.length = 1;
        }
    }
    /// Appends all the elements from `iter` to the end of the list.
    pub fn extend(&mut self, iter: impl Iterator<Item = T>) {
        if let Some(mut index) = self.last_mut() {
            index.extend_after(iter);
        } else if let Some((head, length)) = Node::create_chain_circular(iter) {
            self.head = head;
            self.length = length;
        }
    }
    /// Removes the last element from the list and returns it, or `None` if it is empty.
    pub fn pop(&mut self) -> Option<T> {
        Some(self.last_mut()?.remove().0)
    }
}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        // Free all the `Node`s
        unsafe {
            // SAFETY: This deletes each node exactly once, assuming that the circular
            // linked list is constructed correctly, and that its length is self.length.
            let mut current = self.head;
            for _ in 0..self.len() {
                let next = current.as_ref().next;
                drop(Node::delete_raw(current));
                current = next;
            }
        }
    }
}

impl<T> FromIterator<T> for LinkedList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        if let Some((head, length)) = Node::create_chain_circular(iter) {
            LinkedList { head, length }
        } else {
            LinkedList::new()
        }
    }
}

/// A `DoubleEndedIterator` which consumes the elements from a `LinkedList`.
pub struct LinkedListIterator<T>(LinkedList<T>);

impl<T> Iterator for LinkedListIterator<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.first_mut()?.remove().0)
    }
}

impl<T> DoubleEndedIterator for LinkedListIterator<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        Some(self.0.last_mut()?.remove().0)
    }
}

impl<T> IntoIterator for LinkedList<T> {
    type Item = T;

    type IntoIter = LinkedListIterator<T>;

    fn into_iter(self) -> Self::IntoIter {
        LinkedListIterator(self)
    }
}

/// Reference to a node from a `LinkedList`.
///
/// Can be dereferenced to get the node's underlying data.
///
/// This is also a circular iterator which traverses the list indefinitely.
/// The `iter_list` method can be used to get a finite iterator which traverses the list once.
#[derive(Clone, Debug)]
pub struct LinkedListIndex<'a, T> {
    list: &'a LinkedList<T>,
    node: NonNull<Node<T>>,
}

impl<'a, T> LinkedListIndex<'a, T> {
    /// Creates a new `LinkedListIndex`.
    ///
    /// # Safety
    ///
    /// `node` must be a node from `list`.
    unsafe fn new(list: &'a LinkedList<T>, node: NonNull<Node<T>>) -> Self {
        Self { list, node }
    }
    /// Returns an immutable reference to the node's underlying data.
    pub fn data(&self) -> &'a T {
        unsafe {
            // SAFETY: This is safe because `list` and `node` must be valid,
            // and `node` cannot be deleted while this borrow is active.
            mem::transmute(&self.node.as_ref().data)
        }
    }
    /// Creates a finite iterator which traverses the list starting from the current node.
    pub fn iter_list(self) -> Take<Self> {
        let len = self.list.len();
        self.take(len)
    }
}

impl<'a, T> Deref for LinkedListIndex<'a, T> {
    type Target = T;
    fn deref(&self) -> &'a Self::Target {
        self.data()
    }
}

impl<'a, T> PartialEq for LinkedListIndex<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.node.as_ptr(), other.node.as_ptr())
    }
}

impl<'a, T> Eq for LinkedListIndex<'a, T> {}

impl<'a, T> From<LinkedListIndexMut<'a, T>> for LinkedListIndex<'a, T> {
    fn from(source: LinkedListIndexMut<'a, T>) -> Self {
        unsafe {
            // SAFETY: This is safe because `list` and `node` come
            // from a `LinkedListIndexMut` instance and must be valid.
            Self::new(source.list, source.node)
        }
    }
}

/// Mutable reference to a node from a `LinkedList`.
///
/// Can be dereferenced to get or set the node's underlying data.
///
/// This is also a circular iterator which traverses the list indefinitely.
/// The `iter_list` method can be used to get a finite iterator which traverses the list once.
#[derive(Debug)]
pub struct LinkedListIndexMut<'a, T> {
    list: &'a mut LinkedList<T>,
    node: NonNull<Node<T>>,
}

impl<'a, T> LinkedListIndexMut<'a, T> {
    /// Creates a new `LinkedListIndexMut`.
    ///
    /// # Safety
    ///
    /// `node` must be a node from `list`.
    unsafe fn new(list: &'a mut LinkedList<T>, node: NonNull<Node<T>>) -> Self {
        Self { list, node }
    }
    /// Returns an immutable reference to the node's underlying data.
    pub fn data(&self) -> &'a T {
        unsafe {
            // SAFETY: This is safe because `list` and `node` must be valid,
            // and `node` cannot be deleted while this borrow is active.
            mem::transmute(&self.node.as_ref().data)
        }
    }
    /// Returns a mutable reference to the node's underlying data.
    pub fn data_mut(&mut self) -> &'a mut T {
        unsafe {
            // SAFETY: This is safe because `list` and `node` must be valid,
            // and `node` cannot be deleted while this borrow is active.
            mem::transmute(&mut self.node.as_mut().data)
        }
    }
    /// Sets the current node as the head of the `LinkedList` it references.
    pub fn set_as_head(&mut self) {
        self.list.head = self.node;
    }
    /// Inserts a new node containing `data` after the current node.
    ///
    /// `self` will point to the inserted node.
    pub fn insert_after(&mut self, data: T) {
        unsafe {
            // SAFETY: The existing nodes cannot have dangling pointers, and the list's lenght is correctly updated.
            self.node = Node::insert_after(self.node, data);
            self.list.length += 1;
        }
    }
    /// Inserts a new node containing `data` before the current node.
    ///
    /// `self` will point to the inserted node.
    pub fn insert_before(&mut self, data: T) {
        unsafe {
            // SAFETY: The existing nodes cannot have dangling pointers, and the list's lenght is correctly updated.
            self.node = Node::insert_before(self.node, data);
            self.list.length += 1;
        }
    }
    /// Inserts new nodes containing the elements from `iter` after the current node.
    ///
    /// If `iter` is not empty, `self` will point to the last inserted node.
    pub fn extend_after(&mut self, iter: impl Iterator<Item = T>) {
        unsafe {
            // SAFETY: The existing nodes cannot have dangling pointers, and the list's lenght is correctly updated.
            // The new chain is connected to the list so that there are no dangling pointers.
            if let Some((mut first, mut last, count)) = Node::create_chain_dangling(iter) {
                let mut next = self.node.as_ref().next;
                self.node.as_mut().next = first;
                next.as_mut().prev = last;
                first.as_mut().prev = self.node;
                last.as_mut().next = next;
                self.node = last;
                self.list.length += count;
            }
        }
    }
    /// Removes the current node.
    ///
    /// Returns the data from the removed node and a reference to the next node, or `None` if the last node from the list was removed.
    pub fn remove(mut self) -> (T, Option<Self>) {
        unsafe {
            // SAFETY: `self` is consumed, and a new valid index is returned only if the list is non-empty.
            self.list.length -= 1;
            let (data, next) = Node::delete(self.node);
            (
                data,
                match next {
                    Some(next) => {
                        if self.node == self.list.head {
                            self.list.head = next;
                        }
                        self.node = next;
                        Some(self)
                    }
                    None => None,
                },
            )
        }
    }
    /// Removes the current node.
    ///
    /// Returns the data from the removed node, and makes `self` point to to the next node.
    ///
    /// Panics if the list is empty after removing the current node.
    pub fn remove_advance(&mut self) -> T {
        unsafe {
            // SAFETY: `self` is consumed, and the index is advanced only if the list is non-empty.
            self.list.length -= 1;
            let (data, next) = Node::delete(self.node);
            match next {
                Some(next) => {
                    if self.node == self.list.head {
                        self.list.head = next;
                    }
                    self.node = next;
                }
                None => panic!("List is empty, invalid index"),
            };
            data
        }
    }
    /// Removes the current node.
    ///
    /// Returns the data from the removed node, and makes `self` point to to the next node if possible.
    /// The second element from the returned tuple indicates whether `self` is still valid.
    ///
    /// # Safety
    ///
    /// If the second element of the returned tuple is `false`, indicating that the list is now empty,
    /// `self` will be in an invalid state and must be dropped without calling any of its methods.
    pub unsafe fn remove_dangle(&mut self) -> (T, bool) {
        self.list.length -= 1;
        let (data, next) = Node::delete(self.node);
        (
            data,
            match next {
                Some(next) => {
                    if self.node == self.list.head {
                        self.list.head = next;
                    }
                    self.node = next;
                    true
                }
                None => false,
            },
        )
    }
    /// Creates a finite iterator which traverses the list starting from the current node.
    pub fn iter_list(self) -> Take<Self> {
        let len = self.list.len();
        self.take(len)
    }
}

impl<'a, T> Deref for LinkedListIndexMut<'a, T> {
    type Target = T;
    fn deref(&self) -> &'a Self::Target {
        self.data()
    }
}

impl<'a, T> DerefMut for LinkedListIndexMut<'a, T> {
    fn deref_mut(&mut self) -> &'a mut Self::Target {
        self.data_mut()
    }
}

impl<'a, T> PartialEq for LinkedListIndexMut<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.node.as_ptr(), other.node.as_ptr())
    }
}

impl<'a, T> Eq for LinkedListIndexMut<'a, T> {}

impl<'a, T> Iterator for LinkedListIndex<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            // SAFETY: This is safe because`node.next`
            // must be pointing to another valid node.
            let item = self.data();
            self.node = self.node.as_ref().next;
            Some(item)
        }
    }
}

impl<'a, T> DoubleEndedIterator for LinkedListIndex<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        unsafe {
            // SAFETY: This is safe because`node.prev`
            // must be pointing to another valid node.
            let item = self.data();
            self.node = self.node.as_ref().prev;
            Some(item)
        }
    }
}

impl<'a, T> Iterator for LinkedListIndexMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            // SAFETY: This is safe because`node.next`
            // must be pointing to another valid node.
            let item = self.data_mut();
            self.node = self.node.as_ref().next;
            Some(item)
        }
    }
}

impl<'a, T> DoubleEndedIterator for LinkedListIndexMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        unsafe {
            // SAFETY: This is safe because`node.prev`
            // must be pointing to another valid node.
            let item = self.data_mut();
            self.node = self.node.as_ref().prev;
            Some(item)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::array::IntoIter;
    #[test]
    fn empty() {
        let ll: LinkedList<()> = LinkedList::new();
        assert!(ll.is_empty());
        assert!(ll.first().is_none());
        assert!(ll.last().is_none());
    }
    #[test]
    fn push() {
        let data = [1, 2, 3, 4];
        let mut ll = LinkedList::new();
        for x in data.iter() {
            ll.push(*x);
        }
        assert_eq!(ll.len(), data.len());
        let idx = ll.first().unwrap();
        for (expected, actual) in data.iter().zip(idx) {
            assert_eq!(expected, actual);
        }
    }
    #[test]
    fn index() {
        let data = [1, 2, 3, 4, 5, 6];
        let ll = data.iter().map(|x| *x).collect::<LinkedList<_>>();
        assert_eq!(ll.len(), 6);
        let mut idx = ll.last().unwrap();
        assert_eq!(6, *idx);
        idx.next().unwrap();
        assert_eq!(1, *idx);
        idx.next_back().unwrap();
        assert_eq!(6, *idx);
        idx.next_back().unwrap();
        assert_eq!(5, *idx);
        idx.next_back().unwrap();
        assert_eq!(4, *idx);
    }
    #[test]
    fn index_mut() {
        let data = [1, 2, 3, 4];
        let mut ll = data.iter().map(|x| *x).collect::<LinkedList<_>>();
        let mut idx = ll.first_mut().unwrap();
        idx.next().unwrap();
        idx.insert_after(5);
        idx.insert_after(7);
        idx.insert_before(8);
        *idx = 6;
        assert_eq!(ll.len(), 7);
        let expected: Vec<_> = [1, 2, 5, 6, 7, 3, 4].iter().collect();
        let actual: Vec<_> = ll.first().unwrap().iter_list().collect();
        assert_eq!(expected, actual);
    }
    #[test]
    fn extend_after() {
        let data = [1, 2, 5, 6];
        let mut ll = data.iter().map(|x| *x).collect::<LinkedList<_>>();
        let mut idx = ll.first_mut().unwrap();
        idx.next().unwrap();
        idx.extend_after([3, 4].iter().map(|x| *x));
        let expected: Vec<_> = [1, 2, 3, 4, 5, 6].iter().collect();
        let actual: Vec<_> = ll.first().unwrap().iter_list().collect();
        assert_eq!(expected, actual);
    }
    #[test]
    fn extend_empty() {
        let data = [1, 2, 3, 4];
        let mut ll = LinkedList::new();
        ll.extend(data.iter().map(|x| *x));
        let expected: Vec<_> = [1, 2, 3, 4].iter().collect();
        let actual: Vec<_> = ll.first().unwrap().iter_list().collect();
        assert_eq!(expected, actual);
    }
    #[test]
    fn extend() {
        let data = [1, 2, 3, 4];
        let mut ll = data.iter().map(|x| *x).collect::<LinkedList<_>>();
        ll.extend([5, 6].iter().map(|x| *x));
        let expected: Vec<_> = [1, 2, 3, 4, 5, 6].iter().collect();
        let actual: Vec<_> = ll.first().unwrap().iter_list().collect();
        assert_eq!(expected, actual);
    }
    #[test]
    fn remove() {
        let data = [1, 2, 3, 4];
        let mut ll = data.iter().map(|x| *x).collect::<LinkedList<_>>();
        let mut idx = ll.last_mut().unwrap();
        idx.next_back().unwrap();
        let (value, idx) = idx.remove();
        assert_eq!(3, value);
        assert_eq!(4, *idx.unwrap());
        let (value, idx) = ll.first_mut().unwrap().remove();
        assert_eq!(1, value);
        assert_eq!(2, *idx.unwrap());
        assert_eq!(vec![2, 4], ll.into_iter().collect::<Vec<_>>());
    }
    #[test]
    fn remove_advance() {
        let data = [1, 2, 3, 4];
        let mut ll = data.iter().map(|x| *x).collect::<LinkedList<_>>();
        let mut idx = ll.last_mut().unwrap();
        idx.next_back().unwrap();
        assert_eq!(3, idx.remove_advance());
        assert_eq!(4, *idx);
        let mut idx = ll.first_mut().unwrap();
        assert_eq!(1, idx.remove_advance());
        assert_eq!(2, *idx);
        assert_eq!(vec![2, 4], ll.into_iter().collect::<Vec<_>>());
    }
    #[test]
    fn remove_dangle() {
        unsafe {
            let data = [1, 2, 3, 4];
            let mut ll = data.iter().map(|x| *x).collect::<LinkedList<_>>();
            let mut idx = ll.last_mut().unwrap();
            idx.next_back().unwrap();
            let (value, not_empty) = idx.remove_dangle();
            assert!(not_empty);
            assert_eq!(3, value);
            assert_eq!(4, *idx);
            idx = ll.first_mut().unwrap();
            let (value, not_empty) = idx.remove_dangle();
            assert!(not_empty);
            assert_eq!(1, value);
            assert_eq!(2, *idx);
            let (value, not_empty) = idx.remove_dangle();
            assert!(not_empty);
            assert_eq!(2, value);
            let (value, not_empty) = idx.remove_dangle();
            assert!(!not_empty);
            assert_eq!(4, value);
            assert_eq!(Vec::<i32>::new(), ll.into_iter().collect::<Vec<_>>());
        }
    }
    #[test]
    fn pop() {
        let data = [1, 2, 4];
        let mut ll = data.iter().map(|x| *x).collect::<LinkedList<_>>();
        let mut idx = ll.first_mut().unwrap();
        idx.nth(1);
        idx.insert_before(3);
        assert_eq!(Some(4), ll.pop());
        assert_eq!(Some(3), ll.pop());
        assert_eq!(Some(2), ll.pop());
        assert_eq!(Some(1), ll.pop());
        assert_eq!(None, ll.pop());
        ll.push(6);
        ll.push(7);
        assert_eq!(Some(7), ll.pop());
        ll.push(8);
        assert_eq!(Some(8), ll.pop());
        assert_eq!(Some(6), ll.pop());
    }
    #[test]
    fn into_iter() {
        let data = [1, 2, 3, 4];
        let ll = data.iter().map(|x| *x).collect::<LinkedList<_>>();
        for (expected, actual) in data.iter().map(|x| *x).zip(ll.into_iter()) {
            assert_eq!(expected, actual);
        }
        let ll = data.iter().map(|x| *x).collect::<LinkedList<_>>();
        for (expected, actual) in data.iter().map(|x| *x).rev().zip(ll.into_iter().rev()) {
            assert_eq!(expected, actual);
        }
    }
    #[test]
    fn strings() {
        let data = [
            format!("one"),
            format!("two"),
            format!("three"),
            format!("four"),
        ];
        let mut ll = IntoIter::new(data).collect::<LinkedList<_>>();
        ll.push(format!("five"));
        assert_eq!(ll.len(), 5);
        let mut idx = ll.first_mut().unwrap();
        assert_eq!("one", idx.next().unwrap());
        assert_eq!("four", idx.nth_back(3).unwrap());
        assert_eq!("three", *idx);
        let (e, idx) = idx.remove();
        assert_eq!("three", e);
        let mut idx = idx.unwrap();
        assert_eq!("four", *idx);
        idx.insert_after(format!("zero"));
        assert_eq!("zero", *idx);
        idx.set_as_head();
        assert_eq!(
            vec!["zero", "five", "one", "two", "four"],
            ll.into_iter().collect::<Vec<_>>()
        );
    }
}
