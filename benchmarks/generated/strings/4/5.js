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

function f308f(x_0, x_1, x_2)
{
	return lastLetter(len(x_1));
}

function f228f(x_0, x_1)
{
	return lastLetter(firstWord(x_1));
}

function f240f(x_0)
{
	return lastLetter(len(x_0));
}

function f772f(x_0)
{
	return concat(lastLetter(x_0), concat(x_0, x_0));
}

function f534f(x_0, x_1, x_2)
{
	return beforeAfter(f772f(x_1));
}

//@pbe (constraint (= (f928f "mno pqr st" "" "vvvvv") "BA"))
//@pbe (constraint (= (f928f "vvvvv" "mno pqr st" "xyz") "Bmno pqr stA"))
//@pbe (constraint (= (f928f "404" "mno pqr st" "hello world") "Bmno pqr stA"))
//@pbe (constraint (= (f928f "vvvvv" "" "404") "BA"))