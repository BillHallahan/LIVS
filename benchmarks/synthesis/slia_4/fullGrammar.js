function concat(s1, s2)
{
    return s1 + s2
}

function rpt(s, n)
{
    return s.repeat(n)
}

//@pbe (constraint (= (f "hello" "a" 5) "helloaaaaa"))
//@pbe (constraint (= (f "hi" "b" "2") "hibb"))

// return concat(x, rpt(y, z))
