// Prove termination of the following loop:

method m1(m: int, n: int) 
  requires 0 < m && 0 < n
{
    var x, y := m, n;

    while x != y
      invariant 0 < x && 0 < y
      decreases (x + y)
    {
      if x < y
      {
          y := y - x;
      } 
      else
      {
          x := x - y;
      }
    }
}

// Prove that the following function terminates:
function f(n: nat, m: nat): nat
  requires m > 0  && n > 0
  decreases (n + m)
{
    if n == m then
      n 
    else if (n < m) then 
      f(n, m - n) 
    else 
      f(n - m, m)
}

// Specify the first requirement of Find: if the algorithm returns an index
// (i.e. non-negative integer), then the key should be present at that index.
method Find(a: array<int>, key: int) returns (index: int)
  requires a.Length > 0
  ensures
    if (index >= 0) then
      (index < a.Length && a[index] == key)
    else
      (index == -1 && forall k :: 0 <= k < a.Length ==> a[k] != key)
{
  index := 0;

  while (index < a.Length)
    invariant 0 <= index <= a.Length
    invariant forall k :: 0 <= k < index ==> a[k] != key
  {
    if (a[index] == key)
    {
      return index;
    }

    index := index + 1;
  }

  index := -1;
}

// Write a method that takes an integer array, which it requires to have at least one element,
// and returns an index to the maximum of the array's elements. Annotate the method with 
// pre- and postconditions that state the intent of the method, and annotate its body with 
// a loop invariant to verify it.
method FindMax(a: array<int>) returns (max: int)
  requires a.Length > 0
  ensures 0 <= max < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[max] >= a[k]
{
  var i := 0;
  max := 0;

  while (i < a.Length)
    invariant 0 <= max < a.Length
    invariant i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[max] >= a[k]
  {
    if (a[i] > a[max])
    {
      max := i;
    }

    i := i + 1;
  }
}

// define the sorted predicate over arrays of integers as a function that takes an array
// as an argument, and returns true if and only if that array is sorted in increasing order:
predicate sorted(a: array<int>)
  reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

// method BinarySearch(a: array<int>, key: int) returns (index: int)
//   requires a.Length > 0 && sorted(a)
//   ensures 0 <= index ==> (index < a.Length) && a[index] == key
//   ensures index == -1 ==> forall k :: 0 < a.Length ==> a[k] != key
// {
//   index := (a.Length / 2) + (a.Length % 2);

//   while (index > 0)
    
//   {
//     if (a[index] == key)
//     {
//       return index;
//     }
//     else if (key > a[index])
//     {
//       index := index + index / 2;  
//     }
//     else
//     {
//       index := index / 2;
//     }
//   }
  
//   index := -1;
// }

