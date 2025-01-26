if : ΠA:Type.(Bool -> A -> A -> A)
λA.λc.λt.λf.If(λ_.A, c, t, f)

if₁ : ΠA:Type₁.(Bool -> A -> A -> A)
λA.λc.λt.λf.If(λ_.A, c, t, f)

-- Product : (Type -> Type -> Type)
-- λA.λB.Πc:Bool.if₁ _ c A B
-- 
-- mkProduct : ΠA:Type.ΠB:Type.(A -> B -> Product A B)
-- λA.λB.λa.λb.λc.If(λv.if₁ _ v A B, c, a, b)
-- 
-- proj₁ : ΠA:Type.ΠB:Type.(Product A B -> A)
-- λA.λB.λp.p True
-- 
-- proj₂ : ΠA:Type.ΠB:Type.(Product A B -> B)
-- λA.λB.λp.p False
-- 
-- Coproduct : (Type -> Type -> Type)
-- λA.λB.Πc:Bool.if₁ _ c A B

-- Church encoded product type
Product : (Type -> Type -> Type₁)
λA.λB.ΠR:Type.(A -> B -> (A -> B -> R) -> R)

mkProduct : ΠA:Type.ΠB:Type.(A -> B -> Product A B)
λ_.λ_.λa.λb.λ_.λx.λy.λf.f a b

proj₁ : ΠA:Type.ΠB:Type.(Product A B -> A)
λA.λ_.λp.p A (λa.λb.a)
