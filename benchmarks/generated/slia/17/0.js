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

//@pbe (constraint (= (f15f 10 "xyz" "404") "B404A"))
//@pbe (constraint (= (f15f 6 "ab cd" "xyz") "BxyzA"))
//@pbe (constraint (= (f15f 6 "ab cd" "hello world") "Bhello worldA"))