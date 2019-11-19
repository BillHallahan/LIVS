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

function f617f(x_0)
{
	return beforeAfter(len(x_0));
}

function f455f(x_0, x_1, x_2)
{
	return rep(f617f(x_0), concat(x_0, x_0), len(x_0));
}

function f527f(x_0, x_1)
{
	return lastLetter(firstWord(x_1));
}

function f378f(x_0)
{
	return rep(f617f(x_0), f617f(x_0), lastLetter(x_0));
}

function f706f(x_0)
{
	return f617f(concat(x_0, x_0));
}

function f246f(x_0, x_1, x_2)
{
	return f378f(concat(x_2, x_2));
}

//@pbe (constraint (= (f805f "asdf" "xyz" "") "0B0A"))
//@pbe (constraint (= (f805f "" "xyz" "asdf") "0B0A"))
//@pbe (constraint (= (f805f "" "404" "404") "0B0A"))