function exp(n: int, e: int): int
	requires e >= 0;
	{
		if e>0 then n*exp(n,e-1) else 1
	}

method expon(n: int, e: int) returns(r: int)
	requires e >= 0;
	ensures r == exp(n,e);
	{
		var b: int := e;
		r := 1;
		while (b>0)
		invariant 0 <= b;
		invariant exp(n,e) == exp(n,b) * r;
		{
			r := r * n;
			b := b - 1;
		}
	}