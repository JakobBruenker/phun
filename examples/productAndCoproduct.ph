-- Church encoded product type
Product : (Type -> Type -> Type₁)
λA.λB.ΠR:Type.((A -> B -> R) -> R)

mkProduct : ΠA:Type.ΠB:Type.(A -> B -> Product A B)
λ_.λ_.λa.λb.λ_.λf.f a b

proj₁ : ΠA:Type.ΠB:Type.(Product A B -> A)
λ_.λ_.λp.p _ (λa.λ_.a)

proj₂ : ΠA:Type.ΠB:Type.(Product A B -> B)
λ_.λ_.λp.p _ (λ_.λb.b)

-- Church encoded sum type
Either : (Type -> Type -> Type₁)
λA.λB.ΠR:Type.((A -> R) -> (B -> R) -> R)

inl : ΠA:Type.ΠB:Type.(A -> Either A B)
λ_.λ_.λa.λ_.λf.λ_.f a

inr : ΠA:Type.ΠB:Type.(B -> Either A B)
λ_.λ_.λb.λ_.λ_.λg.g b

either : ΠA:Type.ΠB:Type.ΠC:Type.((A -> C) -> (B -> C) -> Either A B -> C)
λ_.λ_.λ_.λf.λg.λe.e _ f g
