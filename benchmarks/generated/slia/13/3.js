function add(x_0, x_1)
{
	return x_0 + x_1;
}

function mult(x_0, x_1)
{
	return x_0 * x_1;
}

function concat(x_0, x_1)
{
	return x_0 + x_1;
}

function len(x_0)
{
	return x_0.length;
}

function toStr(x_0)
{
	return (x_0 + 10) + "";
}

function beforeAfter(x_0)
{
	return 'B' + x_0 + 'A';
}

function f183f(x_0)
{
	return beforeAfter(beforeAfter(x_0));
}

function f759f(x_0, x_1)
{
	return f183f(x_0);
}

function f565f(x_0, x_1, x_2)
{
	return add(x_2, x_2);
}

//@pbe (constraint (= (f684f "vvvvv" "xyz" -5) "vvvvvxyz"))
//@pbe (constraint (= (f684f "" "xyz" -5) "xyz"))
//@pbe (constraint (= (f684f "xyz" "mno pqr st" 5) "xyzmno pqr st"))
//@pbe (constraint (= (f684f "404" "xyz" -5) "404xyz"))
//@pbe (constraint (= (f684f "mno pqr st" "hello world" 2) "mno pqr sthello world"))