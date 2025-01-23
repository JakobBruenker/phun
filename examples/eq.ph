-- id : Π_:Type.Type
-- \x.x

idLeft : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).A
\A.\a.\b.\p.a

idRight : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).A
\A.\a.\b.\p.b

sym : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).Id(b,a)
--\Aty.\a.\b.\p.J(\q.Id(a,b),Refl(a),p) -- Actually i don't think C should be constant here
\Aty.\a.\b.\p.J(\q.Id(idLeft Aty a b q, idRight Aty a b q),Refl(a),p)
