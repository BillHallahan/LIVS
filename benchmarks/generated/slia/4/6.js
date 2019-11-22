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

function f970f(x_0, x_1, x_2)
{
	return f560f(mult(x_2, x_2), f135f(x_0, x_1, x_1), x_2);
}

//@pbe (constraint (= (f511f "hello world" "mno pqr st") "11mno pqr st"))
//@pbe (constraint (= (f511f "asdf" "404") "4404"))
//@pbe (constraint (= (f511f "vvvvv" "404") "5404"))
//@pbe (constraint (= (f511f "hello world" "vvvvv") "11vvvvv"))