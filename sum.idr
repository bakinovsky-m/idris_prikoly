s : List Double -> Double
s l = (ss 0 0 l) / (pow 2 $ length l)
 where
  ss : (accum:Double) -> (counter:Nat) -> List Double -> Double
  ss a c (x::xs) = a + ss (x * (pow 2 c)) (c+1) xs
  ss a _ Nil = a

sss : List Double -> Double
sss l = (foldr (\x,a => a*2 + x) 0.0 l) / (pow 2 $ length l)

p1 :
(x : Double) ->
(y : Double) ->
(fn1 : Double -> Double -> Double) ->
(pfn1 : (a:Double) -> (b:Double) -> fn1 a b = a*2 + x) ->
(fn2 : Double -> Double -> Double) ->
(pfn2 : (a:Double) -> (b:Double) -> fn2 a b = x + a*2) ->
(fn1 a b = fn2 a b)
p1 x y fn1 pfn1 fn2 pfn2 = 
  rewrite pfn1 x y in ?hole
--  ?hole --Refl 
