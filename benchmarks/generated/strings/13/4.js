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

function f393f(x_0)
{
	return rep(x_0, x_0, rep(x_0, x_0, x_0));
}

function f653f(x_0)
{
	return f393f(concat(x_0, x_0));
}

function f364f(x_0, x_1, x_2)
{
	return firstWord(x_1);
}

function f65f(x_0, x_1, x_2)
{
	return len(x_1);
}

//@pbe (constraint (= (f613f "xyz") ""))
//@pbe (constraint (= (f613f "hello world") "hello"))
//@pbe (constraint (= (f613f "xyz") ""))
//@pbe (constraint (= (f613f "asdf") ""))
//@pbe (constraint (= (f613f "404") ""))