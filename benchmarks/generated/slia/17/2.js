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

function f753f(x_0, x_1, x_2)
{
	return len(x_1);
}

function f566f(x_0)
{
	return beforeAfter(concat(x_0, x_0));
}

//@pbe (constraint (= (f624f "vvvvv" "mno pqr st" 9) "BvvvvvA"))
//@pbe (constraint (= (f624f "ab cd" "mno pqr st" 9) "Bab cdA"))
//@pbe (constraint (= (f624f "mno pqr st" "ab cd" 5) "Bmno pqr stA"))