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

//@pbe (constraint (= (f272f 2 "xyz" "xyz") 6))
//@pbe (constraint (= (f272f 6 "hello world" "asdf") 18))
//@pbe (constraint (= (f272f 9 "asdf" "ab cd") 27))
//@pbe (constraint (= (f272f 0 "404" "asdf") 0))
//@pbe (constraint (= (f272f 2 "ab cd" "ab cd") 6))