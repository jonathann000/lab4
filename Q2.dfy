



function fact(n: nat): nat
  requires 0 <= n; 
  ensures 1 <= fact(n)
{
  if n == 0 then 1 else fact(n-1) * n
}


method ComputeFact(n : nat) returns (res : nat)
  requires n > 0;
  ensures fact(n) == res;
 {
  res := 1;
  var i := 2;

  while i <= n
    decreases n - i;
    invariant res == fact(i-1);
    invariant i <= n+1;
  {
    res := res * i;
    i := i + 1;
  }
 }

 


