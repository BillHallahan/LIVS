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

function f710f(x_0)
{
	return len(lastLetter(x_0));
}

function f390f(x_0, x_1)
{
	return rep(x_1, len(x_0), concat(x_1, x_1));
}

function f353f(x_0, x_1)
{
	return beforeAfter(rep(x_0, x_1, x_1));
}

function f193f(x_0, x_1)
{
	return f390f(beforeAfter(x_0), x_0);
}

function f509f(x_0, x_1, x_2)
{
	return f390f(concat(x_0, x_0), beforeAfter(x_1));
}

function f960f(x_0, x_1)
{
	return firstWord(f353f(x_1, x_1));
}

function f389f(x_0)
{
	return f193f(rep(x_0, x_0, x_0), len(x_0));
}

function f232f(x_0, x_1)
{
	return f509f(x_0, f390f(x_1, x_0), x_0);
}

//@pbe (constraint (= (f768f "mno pqr st" "vvvvv" "vvvvv") ""))
//@pbe (constraint (= (f768f "vvvvv" "vvvvv" "") ""))