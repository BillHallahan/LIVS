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

function f404f(x_0, x_1, x_2)
{
	return add(mult(x_2, x_1), len(x_0));
}

//@pbe (constraint (= (f853f "asdf" "asdf" 0) 4))
//@pbe (constraint (= (f853f "mno pqr st" "xyz" 2) 43))
//@pbe (constraint (= (f853f "mno pqr st" "hello world" 5) 111))
//@pbe (constraint (= (f853f "mno pqr st" "asdf" 9) 184))
//@pbe (constraint (= (f853f "hello world" "xyz" 8) 179))