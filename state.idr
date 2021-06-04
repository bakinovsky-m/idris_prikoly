%default total

record MState s a where
 constructor MkMState
 runState : s -> (a,s)
 
Functor (MState s) where
 map f (MkMState r) = MkMState $ \s0 =>
  let
  (a_orig, s_orig) = r s0
  in
  (f a_orig, s_orig)

interface Functor f => VerifiedFunctor (f : Type -> Type) where
  functorIdentity : (g : a -> a) -> (prf : (v : a) -> g v = v) -> (x : f a) -> map g x = x

VerifiedFunctor (MState s) where
  functorIdentity g prf (MkMState x) =
    let
    step1 = Prelude.Basics.fst . x
    in
    cong {f=MkMState} $
    ?hole
