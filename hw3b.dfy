//================================================
// CS:5810 Formal Methods in Software Engineering
// Fall 2025
//
// Homework 3 -- Part B
//
// Name(s):  Cole Arduser
//
//================================================

//===========
// Problem 1
//===========

function pow2(k: nat) : nat
{
  if k == 0 then 1 else 2 * pow2(k - 1)
}

method IntLog(n: nat) returns (l: nat)
  requires n > 0
  ensures pow2(l) <= n < pow2(l + 1)
{
  l := 0;
  var p := 1;  // p tracks pow2(l)
  while p * 2 <= n
    invariant p == pow2(l)
    invariant p <= n
    decreases n - p
  {
    p := p * 2;
    l := l + 1;
  }
}


//===========
// Problem 2
//===========

ghost predicate prime(n: nat)
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

method isPrime(n: nat) returns (res: bool)
  requires n > 1
  ensures res <==> prime(n)
{
	var i := 2;
	while i < n
		invariant 2 <= i <= n
		invariant forall k :: 2 <= k < i ==> n % k != 0
		decreases n - i
	{
		if n % i == 0 {
			return false;
		}
		i := i + 1;
	}
	return true;
}


//===========
// Problem 3
//===========

method isPrefix<T(==)>(a: array<T>, b: array<T>) returns (r: bool)
  requires a.Length <= b.Length
  ensures r <==> forall k :: 0 <= k < a.Length ==> a[k] == b[k]
{
  var i := 0 ;
  r := true ; // if a is empty, it is trivially a prefix of b
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant r <==> forall k :: 0 <= k < i ==> a[k] == b[k]
    decreases a.Length - i
  {
    r := r && (a[i] == b[i]);
    i := i + 1 ;
  }
 }

