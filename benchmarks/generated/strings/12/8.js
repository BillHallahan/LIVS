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

function f102f(x_0, x_1, x_2)
{
	return len(x_0);
}

function f605f(x_0, x_1, x_2)
{
	return beforeAfter(rep(x_2, x_2, x_2));
}

function f244f(x_0, x_1, x_2)
{
	return f605f(lastLetter(x_0), rep(x_1, x_2, x_0), firstWord(x_2));
}

function f253f(x_0, x_1, x_2)
{
	return concat(x_0, firstWord(x_1));
}

function f127f(x_0)
{
	return rep(f244f(x_0, x_0, x_0), concat(x_0, x_0), f253f(x_0, x_0, x_0));
}

function f634f(x_0)
{
	return concat(lastLetter(x_0), f102f(x_0, x_0, x_0));
}

function f221f(x_0)
{
	return f605f(f127f(x_0), f605f(x_0, x_0, x_0), beforeAfter(x_0));
}

function f3f(x_0)
{
	return f634f(lastLetter(x_0));
}

//@pbe (constraint (= (f801f "asdf" "mno pqr st" "vvvvv") "10f4"))
//@pbe (constraint (= (f801f "asdf" "ab cd" "asdf") "5f4"))
//@pbe (constraint (= (f801f "hello world" "hello world" "vvvvv") "11d11"))
//@pbe (constraint (= (f801f "hello world" "xyz" "hello world") "3d11"))
//@pbe (constraint (= (f801f "ab cd" "xyz" "vvvvv") "3d5"))