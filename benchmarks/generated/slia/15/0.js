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

//@pbe (constraint (= (f428f "hello world" "404" 8) "Bhello worldAhello world404"))
//@pbe (constraint (= (f428f "404" "mno pqr st" 4) "B404A404mno pqr st"))
//@pbe (constraint (= (f428f "mno pqr st" "hello world" 1) "Bmno pqr stAmno pqr sthello world"))