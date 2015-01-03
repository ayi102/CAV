method GCD(x: int, y: int) returns (r: int)
  requires 0 < x && 0 < y;
  ensures (r>0) && (r<= x) && (r <= y);
  {
    var a: int := x;
    var b: int := y;
    while((a>0) && (b>0))
    decreases a + b;
    invariant x >= a >= 0 && y >= b >= 0;
    invariant a == 0 ==> ( y >= b > 0 && x >= b);
    invariant b == 0 ==> ( x >= a > 0 && y >= a);
    
    {
      if( a > b)
      {
        a := a - b;
      }
      else
      {
        b := b - a;
      }
    }
    if (a > 0)
    {
      r := a;
    }
    else
    {
      r := b;
    }
  }
