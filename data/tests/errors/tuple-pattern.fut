-- Tuple patterns must match the number of elements in their rhs.
--
-- ==
-- error: match

fun main(): int =
  let (x,y) = (1,2,3)
  in x+y
