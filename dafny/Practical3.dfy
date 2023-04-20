//////////////////////////////////////////////////////////
// Lab 3: Exercises
//////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////
// Exercise 1. Annotate the following code so that Dafny 
// can verify it.
//method nth_odd (n: nat) returns (j: int)
//ensures j == 1 + 2*n
//{
//    var k := 0;
//    j := 1;
//    while k < n
//    {
//        k := k + 1;
//        j := j + 2;
//    }
//}
//////////////////////////////////////////////////////////
method nth_odd (n: nat) returns (j: int)
  ensures j == 1 + 2 * n
{
   var k := 0;

   j := 1;
   while k < n
    invariant k <= n
    invariant j == (k * 2) + 1
   {
       k := k + 1;
       j := j + 2;
   }
}

//////////////////////////////////////////////////////////
// Exercise 2. Read the code provided and test it by 
// experimenting with it. You can add code to the Main 
// method. Feel free to add comments with your notes.

// You can verify the program is correct by using the command:
//      dafny hello.dfy
// This command is actually short for the command:
//      dafny /compile:1 hello.dfy

// To verify, compile, and execute the program, use the command:
//      dafny /compile:3 hello.dfy

//////////////////////////////////////////////////////////

// Cons (1, Cons (2, Cons (3, Empty))) == [1,2,3]

datatype List<T> = Nil | Cons (head: T, tail: List)

predicate non_empty<T>(l: List<T>) {
    l != Nil
}

function method length<T>(l: List<T>): nat
decreases l
{
    match l 
        case Nil => 0
        case Cons(h,t) => 1 + length(t)
}

function method head<T>(l: List<T>): T
requires non_empty(l)
{
    match l 
        case Cons(h,t) => h
}

function method elem<T(==)>(value: T, l: List<T>): bool
decreases l
{
    match l
        case Nil        => false
        case Cons(h, t) => if value == h then true else elem(value, t)
}

function method append<T>(l1: List<T>, l2: List<T>): List<T>
decreases l1
{
    match l1
        case Nil => l2
        case Cons(h, t) => Cons(h, append(t, l2))
}

method Main()
{
    var l1 := Cons(1, Cons(2, Cons(3, Nil)));
    print "Length of list is ", length(l1), "\n";

    var l2 := Cons(true, Cons(false, Cons(false, Nil)));
    print "Length of list is ", length(l2), "\n";

}

//////////////////////////////////////////////////////////
// Exercise 3. Write a lemma that shows that append is associative:
//
//  append(append(l1, l2), l3) == append(l1, append(l2, l3))
//
// for all l1, l2 and l3
//////////////////////////////////////////////////////////

// TODO

//////////////////////////////////////////////////////////
// Exercise 4. Write a lemma that shows that Nil is the 
// neutral element of append:
//
//  append(l1, Nil) == l1
//  append(Nil, l1) == l1
//
// for all l1
//////////////////////////////////////////////////////////

// TODO

//////////////////////////////////////////////////////////
// Exercise 5. Define a function reverse that reverses
// a list
//////////////////////////////////////////////////////////

// TODO

//////////////////////////////////////////////////////////
// Exercise 6. Show that 
//
// reverse(append(l1, l2)) == append(reverse(l2), reverse(l1))
//
// for all l1 and l2.
//
// Note: Dafny won't be able to do this automatically. 
// You will need to write an inductive proof. It might
// help writing it on paper first.
//////////////////////////////////////////////////////////

// TODO

//////////////////////////////////////////////////////////
// Exercise 7. Use the previous lemma to show that 
// reversing a list twice is the same as not changing it:
//
// reverse(reverse(l)) == l
//
// for all l
//////////////////////////////////////////////////////////

// TODO



//////////////////////////////////////////////////////////
// Exercise 8. Define a function
//
// function del<T>(value: T, l: List<T>): List<T>
//
// such that the properties hold:
//
// 1. forall v,l :: !elem(v, l) ==> del(v, l) == l
// 2. forall v,l :: !elem(v, del(v, l))
// 3. forall v,l1,l2 :: del(v, append(l1,l2)) == 
//                      append(del(v,l1), del(v,l2))
//
// Write the function body and express the three properties
// as lemmas.
//////////////////////////////////////////////////////////

// TODO

//////////////////////////////////////////////////////////
// Exercise 9. Define a similar function to the above
//
// function del1<T>(value: T, l: List<T>): List<T>
//
// such that the properties hold:
//
// 1. forall v,l :: !elem(v, l) ==> del1(v, l) == l
// 2. forall v,l :: elem(v, l) ==> length(l) == 1 + length(del1(v, l))
// 3. forall v,l1,l2 :: elem(v, l) ==>
//                      append(del1(v, l1), l2) == del1(v, append(l1,l2))
//
// Write the function body and express the three properties
// as lemmas.
//////////////////////////////////////////////////////////