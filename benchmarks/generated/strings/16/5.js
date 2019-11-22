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

function f443f(x_0, x_1, x_2)
{
	return firstWord(beforeAfter(x_1));
}

function f626f(x_0)
{
	return len(firstWord(x_0));
}

function f791f(x_0, x_1)
{
	return beforeAfter(firstWord(x_0));
}

function f277f(x_0)
{
	return len(f791f(x_0, x_0));
}

function f96f(x_0, x_1)
{
	return beforeAfter(x_1);
}

//@pbe (constraint (= (f701f "ab cd") "Bab cdAab cdab cd"))
//@pbe (constraint (= (f701f "mno pqr st") "Bmno pqr stAmno pqr stmno pqr st"))
//@pbe (constraint (= (f701f "xyz") "BxyzAxyzxyz"))
//@pbe (constraint (= (f701f "ab cd") "Bab cdAab cdab cd"))