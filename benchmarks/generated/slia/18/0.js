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

//@pbe (constraint (= (f319f 8 "hello world" "mno pqr st") 72))
//@pbe (constraint (= (f319f 8 "asdf" "ab cd") 72))
//@pbe (constraint (= (f319f 1 "ab cd" "mno pqr st") 2))
//@pbe (constraint (= (f319f 3 "404" "asdf") 12))
//@pbe (constraint (= (f319f 9 "xyz" "mno pqr st") 90))