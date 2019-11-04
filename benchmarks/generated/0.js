function add(x_0, x_1)
{
	return x_0 + x_1;
}

function subtract(x_0, x_1)
{
	return x_0 - x_1;
}

function mult(x_0, x_1)
{
	return x_0 * x_1;
}

function concat(x_0, x_1)
{
	return x_0 + x_1;
}

//@pbe (constraint (= (f0 8 "asdf" "hello") 1024))
//@pbe (constraint (= (f0 10 "hello, world!" "asdf") 2000))
//@pbe (constraint (= (f0 4 "hello" "hello") 128))
//@pbe (constraint (= (f0 0 "asdf" "") 0))
//@pbe (constraint (= (f0 9 "asdf" "asdf") 1458))