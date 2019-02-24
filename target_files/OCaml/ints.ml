let add (x: int) (y: int) = x + y

let double (x: int) = add x x

let quadruple (x: int) = double (double x)

let abs(x: int) = if x >= 0 then x else -x