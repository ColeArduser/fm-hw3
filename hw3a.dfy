//================================================
// CS:5810 Formal Methods in Software Engineering
// Fall 2025
//
// Homework 3 -- Part A
//
// Name:  Cole Arduser
//
//================================================

//-------
// Lists
//-------

datatype List<T> = Nil | Cons(head: T, tail: List<T>) 

ghost function listElements<T>(l: List<T>): set<T>
{
  match l
  case Nil => {}
  case Cons(x, t) => { x } + listElements(t)
} 

function at<T>(l: List<T>, i: nat): T
  requires i < len(l)
{
  if i == 0 then l.head else at(l.tail, i - 1)
}

predicate isEmpty<T>(l: List<T>) {
  l == Nil
}

function len<T>(l: List<T>): nat {
  match l
  case Nil => 0
  case Cons(_, t) => 1 + len(t)
}

ghost function listCount<T>(l: List<T>, p: T): nat {
  match l
  case Nil => 0
  case Cons(x, t) =>
    (if x == p then 1 else 0) + listCount(t, p)
}

//--------------
// IntegerLists
//--------------

type IList = List<int>

ghost predicate isOrderedList(l: IList) 
{
  match l
  case Nil => true
  case Cons(x, Nil) => true
  case Cons(x, Cons(y, _)) => x <= y && isOrderedList(l.tail)
}

//===========
// Problem 1
//===========

lemma orderedListLemma(l: IList)
  requires isOrderedList(l)
  ensures forall i, j :: 0 <= i < j < len(l) ==> at(l, i) <= at(l, j)
{
  match l
  case Nil =>
  case Cons(x, Nil) =>
  case Cons(x, Cons(y, _)) =>
    forall i, j | 0 <= i < j < len(l)
      ensures at(l, i) <= at(l, j)
    {
      if i == 0 {
        if j == 1 {
          // Direct from isOrderedList
        } else {
          calc {
            at(l, 0);
          ==  // definition
            x;
          <=  // from isOrderedList(l)
            y;
          ==  // definition
            at(l, 1);
          ==  // definition of at
            at(l.tail, 0);
          <=  // IH on l.tail
            at(l.tail, j - 1);
          ==  // definition of at
            at(l, j);
          }
        }
      } else {
        calc {
          at(l, i);
        ==  // definition of at
          at(l.tail, i - 1);
        <=  // IH on l.tail
          at(l.tail, j - 1);
        ==  // definition of at
          at(l, j);
        }
      }
    }
}


//===========
// Problem 2
//===========

function merge(l1: IList, l2: IList): IList
  requires isOrderedList(l1)
  requires isOrderedList(l2)
  ensures var l := merge(l1, l2);
    isOrderedList(l) &&
    len(l) == len(l1) + len(l2) &&
    listElements(l) == listElements(l1) + listElements(l2) &&
    (forall x :: listCount(l, x) == listCount(l1, x) + listCount(l2, x))
{
  match (l1, l2)
  case (l1, Nil) => l1
  case (Nil, l2) => l2
  case (Cons(x1, t1), Cons(x2, t2)) =>
    if x1 <= x2 then 
      Cons(x1, merge(t1, l2))
    else
      Cons(x2, merge(l1, t2))
}

//--------------
// Binary Trees
//--------------

datatype BTree = Leaf | Node(left: BTree, val: int, right: BTree) 

ghost function treeElements(t: BTree): set<int>
{
  match t
  case Leaf => {}
  case Node(t1, x, t2) => {x} + treeElements(t1) + treeElements(t2)
}

//===========
// Problem 3
//===========

ghost function treeCount(t: BTree, p: int): nat
  ensures treeCount(t, p) > 0 <==> p in treeElements(t)
{
  match t
  case Leaf => 0
  case Node(t1, x, t2) => 
    (if x == p then 1 else 0) + treeCount(t1, p) + treeCount(t2, p)
}


function height(t: BTree): nat
{
  match t
  case Leaf => 0
  case Node(t1, _, t2) => 
    var h1 := height(t1);
    var h2 := height(t2);
    1 + if h1 > h2 then h1 else h2
}

function top(t: BTree): int
  requires t != Leaf
{
  match t
  case Node(_, x, _) => x
} 

//===========
// Problem 4
//===========

ghost predicate isOrderedTree(t: BTree)
{
  match t
  case Leaf => true
  case Node(t1, x, t2) =>
    (t1.Leaf? || x <= top(t1)) &&
    (t2.Leaf? || x <= top(t2)) &&
    isOrderedTree(t1) &&
    isOrderedTree(t2)
}



function ord(x: int, y: int): (int, int)
{
  if x <= y then (x, y) else (y, x)
}

//===========
// Problem 5
//===========

function insert(t: BTree, x: int): BTree
  requires isOrderedTree(t)
  ensures var t' := insert(t, x);
    isOrderedTree(t') &&
    treeElements(t') == treeElements(t) + {x} &&
    treeCount(t', x) == treeCount(t, x) + 1 &&
    (forall y :: y != x ==> treeCount(t', y) == treeCount(t, y))
{
  match t
  case Leaf => Node(Leaf, x, Leaf)
  case Node(t1, y, t2) =>
    var (a, b) := ord(x, y);
    if height(t1) < height(t2) then
      var t1' := insert(t1, b);
      Node(t1', a, t2)
    else
      var t2' := insert(t2, b);
      Node(t1, a, t2')
}

//===========
// Problem 6
//===========

function toTree(l: IList): BTree
  ensures var t := toTree(l);
    isOrderedTree(t) &&
    treeElements(t) == listElements(l) &&
    (forall x :: treeCount(t, x) == listCount(l, x))
{
  match l
  case Nil => Leaf
  case Cons(x, r) => insert(toTree(r), x)
}

//===========
// Problem 7
//===========

function toList(t: BTree): IList
  requires isOrderedTree(t)
  ensures var l := toList(t);
    isOrderedList(l) &&
    listElements(l) == treeElements(t) &&
    (forall x :: listCount(l, x) == treeCount(t, x))
{
  match t
  case Leaf => Nil
  case Node(t1, x, t2) =>
    merge(merge(toList(t1), Cons(x, Nil)), toList(t2))
}


//====================================
// Problem 8 (Optional, extra credit)
//====================================

function abs(n: int): nat {
  if n >= 0 then n else -n
}

ghost predicate isBalanced(t: BTree)
{
  match t
  case Leaf => true
  case Node(t1, x, t2) =>
    abs(height(t1) - height(t2)) <= 1 &&
    isBalanced(t1) &&
    isBalanced(t2)
}

lemma insertBalancedLemma(t: BTree, x: int)
  requires isOrderedTree(t)
  requires isBalanced(t)
  ensures isBalanced(insert(t, x))
{
  // The proof relies on the insert algorithm's strategy
  // of always inserting into the shorter subtree
}