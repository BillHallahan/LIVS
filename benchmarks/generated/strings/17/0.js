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

//@pbe (constraint (= (f719f "hello world" "ab cd" "404") "d"))
//@pbe (constraint (= (f719f "404" "404" "hello world") "4"))
//@pbe (constraint (= (f719f "404" "asdf" "") "4"))
//@pbe (constraint (= (f719f "asdf" "mno pqr st" "404") "f"))
//@pbe (constraint (= (f719f "404" "vvvvv" "xyz") "4"))