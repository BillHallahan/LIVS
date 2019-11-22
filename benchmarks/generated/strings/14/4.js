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

function f329f(x_0, x_1, x_2)
{
	return lastLetter(len(x_2));
}

function f889f(x_0, x_1, x_2)
{
	return concat(x_0, x_2);
}

function f66f(x_0, x_1)
{
	return rep(x_0, concat(x_1, x_1), lastLetter(x_0));
}

function f709f(x_0, x_1)
{
	return rep(concat(x_0, x_1), lastLetter(x_1), f889f(x_1, x_1, x_1));
}

//@pbe (constraint (= (f999f "xyz" "mno pqr st" "asdf") "BasdfA"))
//@pbe (constraint (= (f999f "hello world" "mno pqr st" "vvvvv") "BvvvvvA"))
//@pbe (constraint (= (f999f "xyz" "vvvvv" "ab cd") "Bab cdA"))