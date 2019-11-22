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

//@pbe (constraint (= (f135f "ab cd" "xyz" "hello world") 5))
//@pbe (constraint (= (f135f "asdf" "mno pqr st" "xyz") 4))
//@pbe (constraint (= (f135f "404" "404" "hello world") 3))
//@pbe (constraint (= (f135f "ab cd" "404" "asdf") 5))
//@pbe (constraint (= (f135f "mno pqr st" "xyz" "404") 10))