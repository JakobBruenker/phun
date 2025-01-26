id : Π_:Type.Type
\x.x

idLeft : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).A
\A.\a.\b.\p.a

idRight : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).A
\A.\a.\b.\p.b

sym : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).Id(b,a)
\_.\_.\_.\p.J(\x.\y.\q.Id(y,x),\v.Refl(v),p)

symsymPisP : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).Id(sym _ _ _ (sym _ _ _ p), p)
\A.\a.\b.\p.J(\x.\y.\q.Id(sym _ _ _ (sym _ _ _ q), q),\v.Refl(Refl(v)),p)

symsymPisP : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).Id(sym _ _ _ (sym _ _ _ p), p)
\A.\a.\b.\p.J(\x.\y.\q.Id(sym _ _ _ (sym _ _ _ q), q),\v.Refl(_),p) -- this also works

idIsNop : ΠA:Type.Id(id(A),A)
\A.Refl(A)

the : ΠX:Type1.Πx:X.X
λt.λx.x

idIsId : ΠA:Type.Id(id, \a.a)
\A.Refl(_)

idIsId : ΠA:Type.Id(id, \a.a)
-- \A.Refl(\y.y) -- this doesn't work at the moment, but maybe should
\A.Refl(the _ (\y.y)) -- this works

trans : ΠA:Type.Πa:A.Πb:A.Πc:A.Π_:Id(a,b).Π_:Id(b,c).Id(a,c)
\A.\a.\b.\c.\p.J(\x.\y.\q.Π_:Id(y,c).Id(x,c), \v.\q.q, p)

-- If you leave out x or y, it results in a type mismatch, because it automatically fills in b here, which is maybe not ideal
-- (The error should instead be that unification variables are still left)
-- \A.\a.\b.\c.\p.J(\x.\y.\q.Π_:Id(_,c).Id(x,c), \v.\q.q, p)
