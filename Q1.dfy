
/* 
Answer Question 1a here:
"error message: The postcondition might not hold on all return paths." - why? 
If for example x == y the postcondition will not hold.
*/
method M(x : int, y : int) returns (a : int, b : int) 
  
  ensures a > b;
{
  if (x > y)
   {a:= x;
    b := y;}
  else
   {a := y; 
    b := x;}
}

method M1(x : int, y : int) returns (a : int, b : int) 
  ensures a >= b;
{
  if (x > y)
   {a:= x;
    b := y;}
  else
   {a := y; 
    b := x;}
}

method M2(x : int, y : int) returns (a : int, b : int)
  requires x != y
  ensures a > b;
{
  if (x > y)
   {a:= x;
    b := y;}
  else
   {a := y; 
    b := x;}
}

method M3(x : int, y : int) returns (a : int, b : int)
  ensures a > b;
{
  if (x > y)
   {a:= x;
    b := y;}
  else if (x == y)
    {a := x+1;
      b := y;}
  else
   {a := y; 
    b := x;}
}



