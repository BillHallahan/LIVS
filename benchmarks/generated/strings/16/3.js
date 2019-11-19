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

function f214f(x_0)
{
	return beforeAfter(rep(x_0, x_0, x_0));
}

function f634f(x_0, x_1, x_2)
{
	return concat(firstWord(x_0), lastLetter(x_1));
}

function f502f(x_0, x_1, x_2)
{
	return rep(firstWord(x_0), beforeAfter(x_2), firstWord(x_0));
}

//@pbe (constraint (= (f324f "ab cd" "ab cd") "dab"))
//@pbe (constraint (= (f324f "vvvvv" "") ""))
//@pbe (constraint (= (f324f "mno pqr st" "404") "4"))
//@pbe (constraint (= (f324f "404" "vvvvv") "v"))
//@pbe (constraint (= (f324f "xyz" "vvvvv") "v"))