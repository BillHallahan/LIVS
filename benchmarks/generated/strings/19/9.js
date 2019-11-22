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

function f923f(x_0, x_1, x_2)
{
	return firstWord(x_0);
}

function f826f(x_0)
{
	return beforeAfter(beforeAfter(x_0));
}

function f951f(x_0, x_1, x_2)
{
	return concat(x_0, firstWord(x_2));
}

function f454f(x_0, x_1, x_2)
{
	return firstWord(rep(x_2, x_2, x_0));
}

function f227f(x_0)
{
	return concat(rep(x_0, x_0, x_0), firstWord(x_0));
}

function f493f(x_0, x_1, x_2)
{
	return concat(x_0, concat(x_0, x_1));
}

function f719f(x_0, x_1, x_2)
{
	return firstWord(f227f(x_1));
}

function f252f(x_0, x_1, x_2)
{
	return concat(lastLetter(x_0), len(x_1));
}

function f555f(x_0, x_1, x_2)
{
	return f719f(concat(x_1, x_2), f951f(x_0, x_2, x_1), rep(x_2, x_1, x_0));
}

//@pbe (constraint (= (f20f "hello world") "BBhello worldAABBhello worldAAhello worldhello world"))
//@pbe (constraint (= (f20f "hello world") "BBhello worldAABBhello worldAAhello worldhello world"))
//@pbe (constraint (= (f20f "vvvvv") "BBvvvvvAABBvvvvvAAvvvvvvvvvv"))
//@pbe (constraint (= (f20f "ab cd") "BBab cdAABBab cdAAab cdab cd"))
//@pbe (constraint (= (f20f "mno pqr st") "BBmno pqr stAABBmno pqr stAAmno pqr stmno pqr st"))