%default total

record MState s a where
 constructor MkMState
 runState : s -> (a,s)
 
Functor (MState s) where
 --map : (a -> b) -> State s a -> State s b
 map f (MkMState a) = MkMState $ \s0 => (f $ fst $ a s0, s0)

interface Functor f => VerifiedFunctor (f : Type -> Type) where
  functorIdentity : (g : a -> a) -> (prf : (v : a) -> g v = v) -> (x : f a) -> map g x = x

VerifiedFunctor (MState s) where
  functorIdentity g prf (MkMState x) =
    let
    step1 = Prelude.Basics.fst . x
    in
    cong {f=MkMState} $
    ?hole
