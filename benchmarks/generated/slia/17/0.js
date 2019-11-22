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

//@pbe (constraint (= (f753f "asdf" "asdf" 10) 4))
//@pbe (constraint (= (f753f "vvvvv" "404" 3) 3))
//@pbe (constraint (= (f753f "ab cd" "asdf" 9) 4))
//@pbe (constraint (= (f753f "vvvvv" "asdf" 10) 4))