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

function f713f(x_0)
{
	return len(len(x_0));
}

//@pbe (constraint (= (f779f "hello world" "xyz") "Bhello worldhello worldA"))
//@pbe (constraint (= (f779f "ab cd" "ab cd") "Bab cdab cdA"))
//@pbe (constraint (= (f779f "xyz" "mno pqr st") "BxyzxyzA"))
//@pbe (constraint (= (f779f "vvvvv" "mno pqr st") "BvvvvvvvvvvA"))