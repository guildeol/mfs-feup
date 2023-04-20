method Max(a :int, b:int) returns (m: int)
  ensures (m == a && a >= b) || (m == b && b >= a)
{
  if(a > b)
  {
    m := a;
  }
  else
  {
    m := b;
  }
}

function fib(n: nat):nat
{
  if (n < 2) then n else fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (f: nat)
  ensures f == fib(n)
{
  f := 0;
  var y := 1;
  var i := 0;

  while (i < n)
  invariant f == fib(i) && y == fib(i + 1) && 0 <= i <= n
  {
    f, y := y, f + y;
    i := i + 1;
  }
}