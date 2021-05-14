interface (Functor f) => VerifiedFunctor (f : Type -> Type) where
 mapIdentity : (g : a -> a) -> ((v:a) -> g v = v) -> (x : f a) -> (map g x = x)
 mapComposition : (f1 : a -> a) -> (f2 : a -> a) -> (x : f a) ->
  map (f1 . f2) x = (map f1 . map f2) x

data MyMaybe a = Noth | Ju a

infixr 10 :::
data MML a = MMLNil | (:::) (MyMaybe a) (MML a)

Functor MyMaybe where
 map _ Noth = Noth
 map f (Ju v) = Ju $ f v

Functor MML where
 map _ MMLNil = MMLNil
 map f (Noth ::: xs) = Noth ::: (map f xs)
 map f ((Ju value) ::: xs) = (Ju (f value)) ::: (map f xs)

VerifiedFunctor MyMaybe where
 mapIdentity _ _ Noth = Refl
 mapIdentity _ p (Ju a) = rewrite p a in Refl
 mapComposition _ _ Noth = Refl
 mapComposition f1 f2 (Ju a) = Refl

VerifiedFunctor MML where
  mapIdentity _ _ MMLNil = Refl
  mapIdentity _id _idprf (maybe ::: xs) =
   let
   zxc = mapIdentity _id _idprf xs
   in
   case maybe of
     Noth => rewrite zxc in Refl
     Ju value => rewrite zxc in rewrite _idprf value in Refl
  mapComposition _ _ MMLNil = Refl
  mapComposition f1 f2 (maybe ::: xs) =
    let
    p1 = mapComposition f1 f2 xs
    in
    case maybe of
    Noth => rewrite p1 in Refl
    Ju value => rewrite p1 in Refl

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
