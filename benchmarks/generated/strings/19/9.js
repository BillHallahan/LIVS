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

function f585f(x_0)
{
	return firstWord(rep(x_0, x_0, x_0));
}

function f931f(x_0, x_1, x_2)
{
	return beforeAfter(firstWord(x_1));
}

function f11f(x_0, x_1, x_2)
{
	return beforeAfter(f931f(x_2, x_2, x_0));
}

function f954f(x_0, x_1, x_2)
{
	return concat(len(x_2), x_1);
}

function f154f(x_0, x_1, x_2)
{
	return concat(len(x_0), rep(x_2, x_2, x_2));
}

function f926f(x_0, x_1, x_2)
{
	return len(lastLetter(x_2));
}

function f845f(x_0, x_1, x_2)
{
	return f585f(concat(x_0, x_1));
}

function f405f(x_0, x_1)
{
	return lastLetter(f845f(x_1, x_1, x_0));
}

function f754f(x_0, x_1, x_2)
{
	return rep(f405f(x_2, x_0), f954f(x_0, x_1, x_2), x_2);
}

//@pbe (constraint (= (f253f "asdf" "asdf") "BA"))
//@pbe (constraint (= (f253f "404" "404") "BA"))
//@pbe (constraint (= (f253f "asdf" "xyz") "BA"))
//@pbe (constraint (= (f253f "mno pqr st" "") "BmnoA"))
//@pbe (constraint (= (f253f "vvvvv" "hello world") "BA"))