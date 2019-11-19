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

function f365f(x_0, x_1, x_2)
{
	return beforeAfter(concat(x_0, x_0));
}

function f337f(x_0, x_1)
{
	return beforeAfter(f365f(x_1, x_0, x_0));
}

function f450f(x_0)
{
	return len(toStr(x_0));
}

function f969f(x_0, x_1)
{
	return f450f(x_0);
}

//@pbe (constraint (= (f766f 2 "asdf" "404") "BBBB404404AABB404404AAAA"))
//@pbe (constraint (= (f766f 2 "vvvvv" "mno pqr st") "BBBBmno pqr stmno pqr stAABBmno pqr stmno pqr stAAAA"))
//@pbe (constraint (= (f766f 8 "xyz" "ab cd") "BBBBab cdab cdAABBab cdab cdAAAA"))