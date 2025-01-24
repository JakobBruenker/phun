-- id : Π_:Type.Type
-- \x.x

-- idLeft : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).A
-- \A.\a.\b.\p.a
-- 
-- idRight : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).A
-- \A.\a.\b.\p.b

sym : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).Id(b,a)
\Aty.\a.\b.\p.J(\q.Id(b,a),\p2.Refl(p2),p) -- I think Refl(a) is wrong, this is supposed to be t, not t Refl(x)
-- \Aty.\a.\b.\p.J(\q.Id(?, ?),?,p)
