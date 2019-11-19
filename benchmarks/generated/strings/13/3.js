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

function f393f(x_0)
{
	return rep(x_0, x_0, rep(x_0, x_0, x_0));
}

function f653f(x_0)
{
	return f393f(concat(x_0, x_0));
}

function f364f(x_0, x_1, x_2)
{
	return firstWord(x_1);
}

//@pbe (constraint (= (f65f "hello world" "hello world" "hello world") "11"))
//@pbe (constraint (= (f65f "asdf" "404" "asdf") "3"))
//@pbe (constraint (= (f65f "hello world" "404" "asdf") "3"))
//@pbe (constraint (= (f65f "vvvvv" "mno pqr st" "hello world") "10"))
//@pbe (constraint (= (f65f "ab cd" "ab cd" "mno pqr st") "5"))