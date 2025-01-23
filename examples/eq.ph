id : Π_:Type.Type
\x.x

sym : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).Id(b,a)
\A.\a.\b.\p.J(\q.Id(a,b),Refl(a),p) -- Actually i don't think C should be constant here
