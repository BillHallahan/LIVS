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

function f753f(x_0)
{
	return firstWord(beforeAfter(x_0));
}

//@pbe (constraint (= (f227f "asdf" "asdf" "hello world") "BA"))
//@pbe (constraint (= (f227f "hello world" "mno pqr st" "hello world") "BhelloA"))
//@pbe (constraint (= (f227f "mno pqr st" "mno pqr st" "vvvvv") "BmnoA"))
//@pbe (constraint (= (f227f "mno pqr st" "vvvvv" "mno pqr st") "BmnoA"))
//@pbe (constraint (= (f227f "mno pqr st" "ab cd" "mno pqr st") "BmnoA"))