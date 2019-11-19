function ite(b, c1, c2)
{
    if(b)
    {
        return c1
    }
    else
    {
        return c2
    }
}

function leqTen(a)
{
    return ite(a <= 10, true, false)
}

function raiseToTen(a)
{
    return ite(leqTen(a), 10, "ERROR")
}

//@pbe (constraint (= (f 5) 10))
//@pbe (constraint (= (f 12) "ERROR"))
//@pbe (constraint (= (f "hello") "ERROR"))
//@pbe (constraint (= (f "") 10))

// return raiseToTen(x)
