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

function f719f(x_0, x_1, x_2)
{
	return lastLetter(lastLetter(x_0));
}

function f602f(x_0, x_1)
{
	return concat(beforeAfter(x_0), f719f(x_0, x_1, x_0));
}

function f462f(x_0, x_1)
{
	return concat(beforeAfter(x_0), x_1);
}

function f947f(x_0)
{
	return len(f602f(x_0, x_0));
}

//@pbe (constraint (= (f268f "vvvvv" "" "ab cd") "BBAvvvvvAv"))
//@pbe (constraint (= (f268f "" "hello world" "") "BBhello worldAAA"))
//@pbe (constraint (= (f268f "mno pqr st" "asdf" "vvvvv") "BBasdfAmno pqr stAt"))
//@pbe (constraint (= (f268f "asdf" "mno pqr st" "mno pqr st") "BBmno pqr stAasdfAf"))
//@pbe (constraint (= (f268f "hello world" "" "") "BBAhello worldAd"))