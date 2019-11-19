function isNumeric(num)
{
  return !isNaN(num)
}

function concat(s1, s2)
{
    return s1 + s2
}

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

function rpt(s, n)
{
    return ite(isNumeric(n), s.repeat(n), "ERROR")
}

//@pbe (constraint (= (f "hello" "a" 5) "helloaaaaa"))
//@pbe (constraint (= (f "hi" "b" "2") "hibb"))
//@pbe (constraint (= (f "hi" "b" "hello") "hiERROR"))

// return concat(x, rpt(y, z))
