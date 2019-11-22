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

function f443f(x_0, x_1, x_2)
{
	return firstWord(beforeAfter(x_1));
}

function f626f(x_0)
{
	return len(firstWord(x_0));
}

function f791f(x_0, x_1)
{
	return beforeAfter(firstWord(x_0));
}

function f277f(x_0)
{
	return len(f791f(x_0, x_0));
}

//@pbe (constraint (= (f96f "hello world" "ab cd") "Bab cdA"))
//@pbe (constraint (= (f96f "vvvvv" "asdf") "BasdfA"))
//@pbe (constraint (= (f96f "xyz" "mno pqr st") "Bmno pqr stA"))
//@pbe (constraint (= (f96f "ab cd" "xyz") "BxyzA"))
//@pbe (constraint (= (f96f "mno pqr st" "asdf") "BasdfA"))