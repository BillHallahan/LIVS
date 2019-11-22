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

function f999f(x_0, x_1, x_2)
{
	return f66f(beforeAfter(x_2), x_1);
}

function f314f(x_0, x_1)
{
	return f709f(lastLetter(x_0), f66f(x_0, x_1));
}

function f62f(x_0, x_1)
{
	return f329f(x_0, f889f(x_0, x_0, x_0), len(x_1));
}

//@pbe (constraint (= (f418f "xyz") "BxyzABxyzABxyzA"))
//@pbe (constraint (= (f418f "hello world") "Bhello worldABhello worldABhello worldA"))
//@pbe (constraint (= (f418f "xyz") "BxyzABxyzABxyzA"))
//@pbe (constraint (= (f418f "xyz") "BxyzABxyzABxyzA"))
//@pbe (constraint (= (f418f "hello world") "Bhello worldABhello worldABhello worldA"))