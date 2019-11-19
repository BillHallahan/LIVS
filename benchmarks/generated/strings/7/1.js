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

function f350f(x_0)
{
	return concat(x_0, concat(x_0, x_0));
}

//@pbe (constraint (= (f967f "" "xyz") "xyzxyzxyz3"))
//@pbe (constraint (= (f967f "" "404") "4044044043"))
//@pbe (constraint (= (f967f "ab cd" "404") "4044044043"))
//@pbe (constraint (= (f967f "vvvvv" "asdf") "asdfasdfasdf4"))
//@pbe (constraint (= (f967f "" "hello world") "hello worldhello worldhello world11"))