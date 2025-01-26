-- foo :: (forall r. (forall a. a -> r) -> r) -> _
-- foo f = f \x -> x

-- Shouldn't compile, and doesn't
foo : Π_:(Πr:Type.Π_:(Πa:Type.Π_:a.r).r).?
\f.f (\x.x)
