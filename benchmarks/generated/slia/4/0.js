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

//@pbe (constraint (= (f365f "hello world" 1 8) "Bhello worldhello worldA"))
//@pbe (constraint (= (f365f "vvvvv" 0 7) "BvvvvvvvvvvA"))
//@pbe (constraint (= (f365f "mno pqr st" 2 10) "Bmno pqr stmno pqr stA"))