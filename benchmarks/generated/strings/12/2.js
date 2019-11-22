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

function f102f(x_0, x_1, x_2)
{
	return len(x_0);
}

function f605f(x_0, x_1, x_2)
{
	return beforeAfter(rep(x_2, x_2, x_2));
}

//@pbe (constraint (= (f244f "mno pqr st" "404" "xyz") "BA"))
//@pbe (constraint (= (f244f "hello world" "vvvvv" "vvvvv") "BA"))
//@pbe (constraint (= (f244f "vvvvv" "xyz" "xyz") "BA"))
//@pbe (constraint (= (f244f "vvvvv" "xyz" "mno pqr st") "BmnoA"))