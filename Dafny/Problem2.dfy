function abs(x: int): int
{
  if x > 0 then x else -x  
}

method M() returns (x: int)
{
  while(x != 100)
  decreases abs(100 - x),x;
  {
    if(x > 100)
    {
      x := 200 - x;
    }
    else
    {
      x := 199 - x;
    }
  }
}