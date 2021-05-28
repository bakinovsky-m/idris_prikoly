%default total
%hide Nat


data MNat = Z | S MNat

Uninhabited (Z = S a) where
 uninhabited Refl impossible
Uninhabited (S a = Z) where
 uninhabited Refl impossible

infixl 8 .+.
(.+.) : MNat -> MNat -> MNat
(.+.) Z a = a
(.+.) (S a) b = S (a .+. b)

plusRightZero : (a:MNat) -> (a = a .+. Z)
plusRightZero Z = Refl
plusRightZero (S a) = cong $ plusRightZero a

plusRightSucc : (a,b:MNat) -> (a .+. (S b) = S (a .+. b))
plusRightSucc Z b = Refl
plusRightSucc (S a) b = cong $ plusRightSucc a b

plusLeftZero : (a:MNat) -> (Z .+. a = a)
plusLeftZero _ = Refl

plusLeftSucc : (a,b:MNat) -> ((S a) .+. b = S (a .+. b))
plusLeftSucc _ _ = Refl

plusCommute : (a,b:MNat) -> (a .+. b = b .+. a)
plusCommute Z b = plusRightZero b
plusCommute (S a) b = 
 let
 pp = sym $ plusRightSucc b a
 in
 rewrite plusCommute a b in pp

plusAssoc : (a,b,c:MNat) -> (a .+. b) .+. c = a .+. (b .+. c)
plusAssoc Z b c = Refl
plusAssoc (S a) b c = cong $ plusAssoc a b c

infixl 9 .*.
(.*.) : MNat -> MNat -> MNat
(.*.) Z _ = Z
(.*.) (S a) b = b .+. (a .*. b)

timesLeftOne : (a:MNat) -> a .*. (S Z) = a
timesLeftOne Z = Refl
timesLeftOne (S a) = cong $ timesLeftOne a

timesRightOne : (a:MNat) -> a .*. (S Z) = a
timesRightOne Z = Refl
timesRightOne (S a) = cong $ timesRightOne a

timesRightZero : (a:MNat) -> a .*. Z = Z
timesRightZero Z = Refl
timesRightZero (S a) = timesRightZero a


plusOneCommutes : (a,b:MNat) -> a .+. S b = S a .+. b
plusOneCommutes Z _ = Refl
plusOneCommutes (S a) b = case plusOneCommutes a b of
  prf => rewrite prf in Refl


timesPlusSRight : (a,b:MNat) -> a .+. a .*. b = a .*. S b
timesPlusSRight Z b = Refl
timesPlusSRight (S a) b =
  rewrite sym $ plusAssoc a b (a .*. b) in
  rewrite sym $ timesPlusSRight a b in
  rewrite plusCommute a b in
  rewrite plusAssoc b a (a .*. b) in
  Refl

timesCommute : (a,b:MNat) -> a .*. b = b .*. a
timesCommute Z b = rewrite timesRightZero b in Refl
timesCommute (S a) b = rewrite timesCommute a b in timesPlusSRight b a


lemma02 : (a,b:MNat) -> (a = b) -> S a = S b
lemma02 Z b prf = cong prf
lemma02 (S x) b prf = rewrite prf in Refl

sucInj : (prf : S n = S m) -> n = m
sucInj Refl = Refl

--https://github.com/0xd34df00d/fizzbuzz-i/blob/master/Fizzbuzz.idr#L113
lemma1 : (a,b:MNat) -> (a .+. b = a .+. c) -> b = c
lemma1 Z b prf = prf
lemma1 (S x) b prf = ?asd


-- plusTimesDistr : (a,b,c:MNat) -> a .*. (b .+. c) = (a .*. b) .+. (a .*. c)
-- plusTimesDistr Z b c = Refl
-- plusTimesDistr (S a) b c = ?distr
