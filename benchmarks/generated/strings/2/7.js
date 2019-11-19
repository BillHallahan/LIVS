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

function f490f(x_0, x_1)
{
	return concat(x_1, x_1);
}

function f876f(x_0)
{
	return firstWord(beforeAfter(x_0));
}

function f371f(x_0)
{
	return rep(firstWord(x_0), concat(x_0, x_0), f876f(x_0));
}

function f619f(x_0)
{
	return len(f490f(x_0, x_0));
}

function f132f(x_0, x_1, x_2)
{
	return f490f(beforeAfter(x_1), f619f(x_2));
}

function f87f(x_0, x_1)
{
	return f619f(rep(x_1, x_1, x_0));
}

function f830f(x_0, x_1, x_2)
{
	return f490f(firstWord(x_2), lastLetter(x_0));
}

//@pbe (constraint (= (f946f "xyz" "xyz" "hello world") "BA"))
//@pbe (constraint (= (f946f "hello world" "" "xyz") "BA"))
//@pbe (constraint (= (f946f "" "hello world" "asdf") "BhelloA"))