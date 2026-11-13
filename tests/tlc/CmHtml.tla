---- MODULE CmHtml ----
\* The HTML module of the CommunityModules, evaluated when TLC starts: in the constant definitions
\* and the ASSUMEs
EXTENDS HTML, TLC
Page ==
  HTMLDocument(
    HTMLHeader("Demo", <<HTMLLink("a.css", "stylesheet")>>, <<HTMLClass(".c", <<HTMLAttribute("color", "red")>>)>>),
    HTMLBody(HTMLFrame("f", <<HTMLText("t", "hi"),
                              HTMLGridContainer("g", <<"x", "y">>, <<HTMLBox("b", <<>>, HTMLSize("1px", "2px"), <<>>)>>)>>)),
    <<HTMLScriptFile("s.js"), HTMLScript(<<HTMLJSKeyListener(<<HTMLJSNavigationKey("n", "next.html")>>)>>)>>)
Shown == Print("size", HTMLSize("3px", "4px"))
ASSUME PrintT(HTMLAttribute("color", "blue"))
ASSUME PrintT(HTMLFill("%a% and %a%", <<<<"%a%", "1">>, <<"%a%", "2">>>>))
ASSUME PrintT(HTMLFill("%a%", <<<<"%a%", "%b%">>, <<"%b%", "x">>>>))
ASSUME PrintT(HTMLGridContainer("g", <<"", "a", "", "b">>, <<>>))
ASSUME PrintT(HTMLCircle("c", <<"k">>, "s", <<"inner">>))
ASSUME PrintT(HTMLSVG("v", "0 0 1 1", "s", "<g/>"))
ASSUME PrintT(<<HTMLJSLine("a", "b", "red", "2"), HTMLJSLineDash("a", "b", "red", "2")>>)
ASSUME PrintT(<<HTMLNewLine, HTMLFlexCenterAttributes, HTMLText("", "no id"), HTMLBody("")>>)
ASSUME PrintT(HTMLStyleSheet(<<>>))
ASSUME PrintT(Page)
====
