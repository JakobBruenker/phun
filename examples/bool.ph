not : Π_:Bool.Bool
\c.If(\_.Bool, c, False, True)

trueIsTrue : Πc:Bool.Πa:Type.Πb:Type.Π_:Id(c, True).Id(If(\_.Type, c, a, b), a)
\c.\a.\b.\p.J(\x.\y.\q.Id(If(\_.Type, x, a, b), If(\_.Type, y, a, b)),\v.Refl(_),p)

ifCTrueFalseIsC : Πc:Bool.Id(If(\_.Bool, c, True, False), c)
\c.If(\v.Id(If(\_.Bool, v, True, False), v), c, Refl(_), Refl(_))
