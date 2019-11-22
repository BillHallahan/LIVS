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

function f365f(x_0, x_1)
{
	return concat(beforeAfter(x_1), len(x_0));
}

function f289f(x_0, x_1)
{
	return beforeAfter(firstWord(x_1));
}

function f670f(x_0, x_1, x_2)
{
	return f289f(concat(x_1, x_1), x_1);
}

function f906f(x_0)
{
	return f365f(concat(x_0, x_0), f365f(x_0, x_0));
}

function f1f(x_0, x_1, x_2)
{
	return beforeAfter(x_1);
}

function f321f(x_0)
{
	return rep(f365f(x_0, x_0), f1f(x_0, x_0, x_0), f1f(x_0, x_0, x_0));
}

function f285f(x_0)
{
	return f321f(firstWord(x_0));
}

function f196f(x_0, x_1, x_2)
{
	return f906f(f1f(x_1, x_0, x_0));
}

function f434f(x_0, x_1)
{
	return beforeAfter(f906f(x_1));
}

//@pbe (constraint (= (f332f "404" "asdf") "BBBasdfA4A8A"))
//@pbe (constraint (= (f332f "mno pqr st" "404") "BBB404A3A6A"))
//@pbe (constraint (= (f332f "hello world" "ab cd") "BBBab cdA5A10A"))