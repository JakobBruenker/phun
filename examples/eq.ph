-- id : Π_:Type.Type
-- \x.x

idLeft : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).A
\A.\a.\b.\p.a

idRight : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).A
\A.\a.\b.\p.b

--sym : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).Id(b,a)
-- \Aty.\a.\b.\p.J(\q.Id(idRight _ _ _ q, idLeft _ _ _ q),\p'.Refl(p'),p) -- actually i think we do need x and y as arguments to c. maybe.
-- \Aty.\a.\b.\p.J(\q.Id(b,a),\p2.Refl(p2),p) -- actually i think we do need x and y as arguments to c. maybe.
-- i also think refl actually needs a second arg, which is the type of a. Alternatively i guess it could maybe be a product of A and refl(a) in practice
-- \Aty.\a.\b.\p.J(\q.Id(?, ?),?,p)
--\Aty.\a.\b.\p.J(\q.Id(idRight _ _ _ q, ?),?,p)

-- apparently this works
--foo : ΠA:Type.Πa:A.Πp:Id(a,a).A
--\_.\_.\p.idRight _ _ _ p

\c.\t.\p.J(c, t, p)
