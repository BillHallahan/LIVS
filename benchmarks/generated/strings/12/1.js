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

//@pbe (constraint (= (f605f "mno pqr st" "404" "asdf") "BasdfA"))
//@pbe (constraint (= (f605f "hello world" "hello world" "xyz") "BxyzA"))
//@pbe (constraint (= (f605f "ab cd" "404" "xyz") "BxyzA"))
//@pbe (constraint (= (f605f "asdf" "404" "hello world") "Bhello worldA"))