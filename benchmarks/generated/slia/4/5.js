function add(x_0, x_1)
{
	return x_0 + x_1;
}

function mult(x_0, x_1)
{
	return x_0 * x_1;
}

function concat(x_0, x_1)
{
	return x_0 + x_1;
}

function len(x_0)
{
	return x_0.length;
}

function toStr(x_0)
{
	return x_0 + "";
}

function beforeAfter(x_0)
{
	return 'B' + x_0 + 'A';
}

function f135f(x_0, x_1, x_2)
{
	return len(x_0);
}

function f569f(x_0)
{
	return toStr(f135f(x_0, x_0, x_0));
}

function f455f(x_0, x_1, x_2)
{
	return f569f(x_0);
}

function f560f(x_0, x_1, x_2)
{
	return add(x_2, x_2);
}

function f66f(x_0, x_1, x_2)
{
	return f569f(concat(x_2, x_2));
}

//@pbe (constraint (= (f970f "asdf" "mno pqr st" 7) 14))
//@pbe (constraint (= (f970f "404" "asdf" 6) 12))
//@pbe (constraint (= (f970f "xyz" "hello world" 5) 10))