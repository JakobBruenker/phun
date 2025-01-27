plus : (Nat -> Nat -> Nat)
λx.λy.NatInd(λ_.Nat, y, λ_.λr.Succ(r), x)

cong : ΠA:Type. ΠB:Type. Πf:(A -> B). Πa:A. Πb:A. (Id(a, b) -> Id(f a, f b))
λ_.λ_.λf.λa.λb.λp.J(λx.λy.λq.Id(f x, f y), λv.Refl(f v), p)

trans : ΠA:Type. Πa:A. Πb:A. Πc:A. (Id(a,b) -> Id(b,c) -> Id(a,c))
λ_.λa.λb.λc.λp.J(λx.λy.λq.Π_:Id(y,c).Id(x,c), λv.λq.q, p)

plusZeroLeft : Πn:_. Id(plus Zero n, n)
λ_.Refl(_)

plusZeroRight : Πn:_. Id(plus n Zero, n)
λn.NatInd(λm.Id(plus m Zero, m), Refl(Zero), λ_.λp.cong _ _ (λx.Succ(x)) _ _ p, n)

plusSucc : Πn:_. Πm:_. Id(plus n Succ(m), Succ(plus n m))
λn.λm.NatInd(λx.Id(plus x Succ(m), Succ(plus x m)), Refl(Succ(m)), λx.λp.cong _ _ (λy.Succ(y)) _ _ p, n)

plusComm : Πn:_. Πm:_. Id(plus n m, plus m n)
λn.λm.NatInd(
  λx.Id(plus n x, plus x n),
  plusZeroRight n,
  λx.λp.trans _ _ _ _ (plusSucc n x) (cong _ _ (λx.Succ(x)) _ _ p),
  m)

-- If there is an expression at the end of the file, it will be evaluated and printed
plus Succ(Succ(Succ(Zero))) Succ(Succ(Zero))
