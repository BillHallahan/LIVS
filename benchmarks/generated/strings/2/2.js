function concat(x_0, x_1)
{
	return x_0 + x_1;
}

function len(x_0)
{
	return x_0.length + "";
}

function beforeAfter(x_0)
{
	return 'B' + x_0 + 'A';
}

function lastLetter(x_0)
{
	if (x_0.length > 0) { return x_0.slice(-1); } else { return ''; }
}

function firstWord(x_0)
{
	return x_0.substring(0, x_0.indexOf(" "));
}

function rep(x_0, x_1, x_2)
{
	return x_0.replace(x_1, x_2);
}

function f64f(x_0, x_1, x_2)
{
	return beforeAfter(x_2);
}

function f785f(x_0, x_1, x_2)
{
	return rep(beforeAfter(x_1), len(x_1), firstWord(x_1));
}

//@pbe (constraint (= (f855f "mno pqr st" "mno pqr st" "404") "Bmno pqr stA"))
//@pbe (constraint (= (f855f "vvvvv" "vvvvv" "mno pqr st") "BvvvvvA"))
//@pbe (constraint (= (f855f "hello world" "mno pqr st" "vvvvv") "Bhello worldA"))