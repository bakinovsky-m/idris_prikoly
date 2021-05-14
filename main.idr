interface (Functor f) => VerifiedFunctor (f : Type -> Type) where
 mapIdentity : (g : a -> a) -> ((v:a) -> g v = v) -> (x : f a) -> (map g x = x)
 mapComposition : (f1 : a -> a) -> (f2 : a -> a) -> (x : f a) ->
  map (f1 . f2) x = (map f1 . map f2) x

infixr 10 :::
data MML a = MMLNil | (:::) (Maybe a) (MML a)

Functor MML where
 map _ MMLNil = MMLNil
 map f (Nothing ::: xs) = Nothing ::: (map f xs)
 map f ((Just value) ::: xs) = (Just (f value)) ::: (map f xs)

VerifiedFunctor MML where
  mapIdentity _ _ MMLNil = Refl
  mapIdentity _id _idprf (maybe ::: xs) =
   let
   zxc = mapIdentity _id _idprf xs
   in
   case maybe of
     Nothing => rewrite zxc in Refl
     Just value => rewrite zxc in rewrite _idprf value in Refl
  mapComposition _ _ MMLNil = Refl
  mapComposition f1 f2 (maybe ::: xs) =
    let
    p1 = mapComposition f1 f2 xs
    in
    case maybe of
    Nothing => rewrite p1 in Refl
    Just value => rewrite p1 in Refl

qwe :
Num a =>
(g : a -> a) ->
((v:a) -> g v = v) ->
(x : a) ->
(y : a) ->
((g x) + (g y) = g (x + y))
qwe g p x y = ?hole0

qwe1 :
Num a =>
(g : a -> a) ->
((v:a) -> g v = v) ->
(x : a) ->
(y : a) ->
((g x) + (g y) = g (x + y))
qwe1 g p x y =
 rewrite p x in
 ?hole1

qwe2 :
Num a =>
(g : a -> a) ->
((v:a) -> g v = v) ->
(x : a) ->
(y : a) ->
((g x) + (g y) = g (x + y))
qwe2 g p x y =
 rewrite p x in
 rewrite p y in
 ?hole


qwe3 :
Num a =>
(g : a -> a) ->
((v:a) -> g v = v) ->
(x : a) ->
(y : a) ->
((g x) + (g y) = g (x + y))
qwe3 g p x y =
 rewrite p x in
 rewrite p y in
 rewrite p (x+y) in
 Refl
