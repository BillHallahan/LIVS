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

function f397f(x_0, x_1, x_2)
{
	return concat(x_2, lastLetter(x_1));
}

function f665f(x_0, x_1)
{
	return rep(len(x_0), concat(x_1, x_1), len(x_1));
}

function f123f(x_0, x_1, x_2)
{
	return beforeAfter(x_1);
}

//@pbe (constraint (= (f156f "" "ab cd" "xyz") "abBxyzA"))
//@pbe (constraint (= (f156f "hello world" "asdf" "vvvvv") "BvvvvvA"))
//@pbe (constraint (= (f156f "" "hello world" "xyz") "helloBxyzA"))
//@pbe (constraint (= (f156f "ab cd" "mno pqr st" "asdf") "mnoBasdfA"))
//@pbe (constraint (= (f156f "ab cd" "asdf" "vvvvv") "BvvvvvA"))