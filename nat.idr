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

plusLeftZero : (Z .+. a = a)
plusLeftZero = Refl

plusLeftSucc : ((S a) .+. b = S (a .+. b))
plusLeftSucc = Refl

plusCommute : (a,b:MNat) -> (a .+. b = b .+. a)
plusCommute Z b = plusRightZero b
plusCommute (S a) b = rewrite plusCommute a b in sym $ plusRightSucc b a

plusAssocToLeft : (a,b,c:MNat) -> (a .+. b) .+. c = a .+. (b .+. c)
plusAssocToLeft Z b c = Refl
plusAssocToLeft (S a) b c = cong $ plusAssocToLeft a b c

plusAssocToLeft' : (a:MNat) -> (a .+. b) .+. c = a .+. (b .+. c)
plusAssocToLeft' Z = Refl
plusAssocToLeft' (S a) = cong $ plusAssocToLeft' a

plusAssocToRight : (a,b,c:MNat) -> a .+. (b .+. c) = (a .+. b) .+. c
plusAssocToRight a b c = sym $ plusAssocToLeft a b c

plusAssocToRight' : (a:MNat) -> a .+. (b .+. c) = (a .+. b) .+. c
plusAssocToRight' a = sym $ plusAssocToLeft' a

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
plusOneCommutes (S a) b = rewrite plusOneCommutes a b in Refl

timesPlusSRight : (a,b:MNat) -> a .+. a .*. b = a .*. S b
timesPlusSRight Z b = Refl
timesPlusSRight (S a) b =
  rewrite sym $ plusAssocToLeft a b (a .*. b) in
  rewrite sym $ timesPlusSRight a b in
  rewrite plusCommute a b in
  rewrite plusAssocToLeft b a (a .*. b) in
  Refl

timesCommute : (a,b:MNat) -> a .*. b = b .*. a
timesCommute Z b = rewrite timesRightZero b in Refl
timesCommute (S a) b = rewrite timesCommute a b in timesPlusSRight b a

succInj : (prf : S n = S m) -> n = m
succInj Refl = Refl

lemma1 : (a,b,c:MNat) -> (a .+. b = a .+. c) -> b = c
lemma1 Z _ _ prf = prf
lemma1 (S x) b c prf =
 let
 step1 = plusLeftSucc
 step2 = replace prf step1
 step3 = plusLeftSucc
 step4 = replace (sym step2) step3
 step5 = sym $ succInj step4
 in
 lemma1 x b c step5
lemma1' : (a:MNat) -> (a .+. b = a .+. c) -> b = c
lemma1' Z prf = prf
lemma1' (S x) prf =
 let
 step1 = plusLeftSucc
 step2 = replace prf step1
 step3 = plusLeftSucc
 step4 = replace (sym step2) step3
 step5 = sym $ succInj step4
 in
 lemma1' x step5

%hide (+)
(+) : MNat -> MNat -> MNat
(+) = (.+.)
%hide (*)
(*) : MNat -> MNat -> MNat
(*) = (.*.)


---https://github.com/0xd34df00d/fizzbuzz-i/blob/master/Fizzbuzz.idr#L113
shuffleLemma : (n,m,kn,km:MNat) -> (n + m) + (kn + km) = (n+kn)+(m+km)
shuffleLemma n m kn km = ?shuffle_lemma_hole
 -- ((n+m) + (kn+km)) = {plusAssocToLeft}

plusTimesDistr : (a,b,c:MNat) -> a * (b + c) = a * b + a * c
plusTimesDistr Z b c = Refl
plusTimesDistr (S a) b c =
 let
 step3 = lemma1' {b=c+a*(b+c)} {c=(a*b + (c+a*c))} b
 in
 ?hole
 -- step3 ?hole
 -- rewrite lemma1 b (c+a*(b+c)) (a*b+(c+a*c)) in ?hole
