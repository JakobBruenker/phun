-- id : Π_:Type.Type
-- \x.x

idLeft : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).A
\A.\a.\b.\p.a

idRight : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).A
\A.\a.\b.\p.b

sym : ΠA:Type.Πa:A.Πb:A.Πp:Id(a,b).Id(b,a)
\A.\a.\b.\p.J(\x.\y.\q.Id(y,x),\v.Refl(v),p)
