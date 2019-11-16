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

//@pbe (constraint (= (f6f "hello world" "asdf") "AfB"))
//@pbe (constraint (= (f6f "404" "asdf") "AfB"))
//@pbe (constraint (= (f6f "vvvvv" "hello world") "AdB"))
//@pbe (constraint (= (f6f "hello world" "xyz") "AzB"))
//@pbe (constraint (= (f6f "xyz" "hello world") "AdB"))