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

//@pbe (constraint (= (f581f "" "vvvvv") ""))
//@pbe (constraint (= (f581f "" "hello world") "hello"))
//@pbe (constraint (= (f581f "vvvvv" "asdf") ""))
//@pbe (constraint (= (f581f "404" "xyz") ""))
//@pbe (constraint (= (f581f "404" "asdf") ""))