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
	return 'A' + x_0 + 'B';
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

function rev(x_0)
{
	return x_0.split("").reverse().join("");
}

function f0f(x_0, x_1, x_2)
{
	return lastLetter(x_0);
}

function f6f(x_0, x_1)
{
	return beforeAfter(lastLetter(x_1));
}

//@pbe (constraint (= (f57f "hello world") "Ahello"))
//@pbe (constraint (= (f57f "404") ""))
//@pbe (constraint (= (f57f "vvvvv") ""))
//@pbe (constraint (= (f57f "ab cd") "Aab"))