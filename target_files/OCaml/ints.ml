let add (x: int) (y: int) = x + y

let double (x: int) = add x x

let quadruple (x: int) = double (double x)

let abs2 (x: int) = if x >= 0 then x else -x
let abs3 (x: int) = abs2 x
let abs4 (x: int) = abs3 x