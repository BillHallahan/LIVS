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

function f604f(x_0, x_1)
{
	return firstWord(x_1);
}

//@pbe (constraint (= (f45f "ab cd" "xyz" "") "xyz"))
//@pbe (constraint (= (f45f "404" "404" "xyz") "404"))
//@pbe (constraint (= (f45f "" "vvvvv" "mno pqr st") "vvvvv"))
//@pbe (constraint (= (f45f "404" "ab cd" "mno pqr st") "ab cd"))