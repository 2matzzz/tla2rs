---- MODULE CmSvg ----
\* The SVG module of the CommunityModules, evaluated when TLC starts: its records and the functions
\* over strings it builds print in TLC's order of strings, which counts the names and strings of the
\* release's modules as TLC parses them
EXTENDS Integers, SVG, TLC
Box == Rect(1, 2, 30, 40, [fill |-> "red", x |-> "9"])
Pic == Image(5, 6, 70, 80, "a.png", ("class" :> "c") @@ ("y" :> "0"))
Doc == SVGDoc(Group(<<Box, Circle(3, 4, 5, <<>>)>>, ("transform" :> "t")), 0, 0, 100, 50, [stroke |-> "blue"])
ASSUME PrintT(Box)
ASSUME PrintT(Pic)
ASSUME PrintT(Doc)
ASSUME PrintT(<<Line(1, 2, 3, 4, <<>>), Text(7, 8, "hi", <<>>), Svg(<<>>, <<>>)>>)
ASSUME PrintT(<<DOMAIN Box, DOMAIN Box.attrs, DOMAIN Pic.attrs, DOMAIN Doc.attrs>>)
ASSUME PrintT(<<CHOOSE k \in DOMAIN Pic.attrs : TRUE, CHOOSE k \in DOMAIN Doc.attrs : TRUE>>)
ASSUME PrintT([k \in DOMAIN Pic.attrs |-> k \in DOMAIN Box.attrs])
ASSUME PrintT(<<NodeOfRingNetwork(1, 2, 3, 4, 5), PointOnLine([x |-> 0, y |-> 0], [x |-> 10, y |-> -7], 2), SVGElemToString(Box)>>)
ASSUME PrintT({"zz", "segment", "frameNumber", "TRUNCATE_EXISTING", "atoi", "Folds"})
====
