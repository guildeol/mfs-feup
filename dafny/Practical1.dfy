method between (p: int, r: int)
    returns (q: int)
    requires ((r - p) > 1)
    ensures (p < q < r)
{
    q := (p + r) / 2;
}

method MultipleReturns(x: int, y: int)
    returns (greater: int, lesser: int)
    requires (y > 0)
    ensures (lesser <= x)
    ensures (greater >= x)
{
    greater := x + y;
    lesser := x - y;
}

method Triple(x: int)
    returns (r: int)
    ensures (r == (3 * x))
{
    var y := Double(x);
    r := y + x;
}

method Double(x: int)
    returns (r: int)
    ensures (r == 2 * x)

method Max(a: int, b: int)
    returns (c :int)
    ensures((c == a && a >= b) || (c == b && b >= a))
{
    if (a > b)
    {
        c := a;
    }
    else
    {
        c := b;
    }
}

function abs(x: int): int
{
    if (x < 0) then -x else x
}

method TestAbs()
{
    var v := abs(3);
    assert 0 <= v;
    assert v == 3;
}

function method max_func(a: int, b: int) :int
{
    if (a > b) then a else b
}


method TestMax()
{
    var c := max_func(1, 2);
    assert (c == 2);

    var d := max_func(1, -2);
    assert (d == 1);
}

method new_max(a: int, b: int)
    returns (c: int)
    ensures((c == a && a >= b) || (c == b && b >= a))
{
    return max_func(a, b);
}

function method fib(n: nat): nat
{
    if (n < 2)
        then 1
        else fib(n - 2) + fib(n -1)
}

method test_fib()
{
    var a := fib(3);
    assert a == 3;

    a := fib(4);
    assert a == 5;
}

function method exp_func(m: int, n: nat): int
{
    if (n == 0)
        then 1
        else m * exp_func(m, n - 1)
}

method test_exp()
{
    assert exp_func(2, 0) == 1;
    assert exp_func(2, 1) == 2;
    assert exp_func(2, 2) == 4;
    assert exp_func(2, 3) == 8;
}
