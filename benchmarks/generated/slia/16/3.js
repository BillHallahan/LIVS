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
	return (x_0 + 10) + "";
}

function beforeAfter(x_0)
{
	return 'B' + x_0 + 'A';
}

function f964f(x_0, x_1, x_2)
{
	return len(x_1);
}

function f800f(x_0, x_1)
{
	return len(concat(x_1, x_0));
}

function f785f(x_0, x_1)
{
	return f800f(concat(x_1, x_1), toStr(x_0));
}

//@pbe (constraint (= (f660f "asdf" 2 8) 6))
//@pbe (constraint (= (f660f "" 2 5) 6))
//@pbe (constraint (= (f660f "xyz" 9 8) 27))
//@pbe (constraint (= (f660f "vvvvv" 0 0) 0))
//@pbe (constraint (= (f660f "xyz" -5 3) -15))