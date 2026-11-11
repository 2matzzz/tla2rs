//! TLC's standard modules (from tla2tools.jar, TLC 2.19) as TLC reads them: for each, the
//! modules it extends or instantiates, its identifiers and keywords in order of first appearance, and its strings.
//! Used to order strings as TLC does (see `compile::tlc_string_ranks`).

pub const STD_MODULES: &[(&str, &[&str], &[&str], &[&str])] = &[
    ("Naturals", &[], &["Naturals", "Nat", "a", "b", "CHOOSE", "n", "TRUE"], &[]),
    ("Integers", &["Naturals"], &["Integers", "EXTENDS", "Naturals", "Int", "a"], &[]),
    ("Reals", &["Integers"], &["Reals", "EXTENDS", "Integers", "Real", "a", "b", "CHOOSE", "m", "Infinity", "i", "r"], &["Reals"]),
    ("Sequences", &["Naturals"], &["Sequences", "LOCAL", "INSTANCE", "Naturals", "Seq", "S", "UNION", "n", "Nat", "Len", "s", "CHOOSE", "DOMAIN", "t", "i", "IF", "THEN", "ELSE", "Append", "e", "Head", "Tail", "CASE", "SubSeq", "m", "SelectSeq", "Test", "LET", "F", "IN"], &[]),
    ("FiniteSets", &["Naturals", "Sequences"], &["FiniteSets", "LOCAL", "INSTANCE", "Naturals", "Sequences", "IsFiniteSet", "S", "seq", "Seq", "s", "n", "Len", "Cardinality", "LET", "CS", "T", "SUBSET", "IF", "THEN", "ELSE", "CHOOSE", "x", "IN"], &[]),
    ("TLC", &["Naturals", "Sequences", "FiniteSets"], &["TLC", "LOCAL", "INSTANCE", "Naturals", "Sequences", "FiniteSets", "Print", "out", "val", "PrintT", "TRUE", "Assert", "IF", "THEN", "ELSE", "CHOOSE", "v", "JavaTime", "n", "Nat", "TLCGet", "i", "TLCSet", "d", "e", "x", "f", "g", "DOMAIN", "Permutations", "S", "w", "SortSeq", "s", "Op", "LET", "Perm", "p", "Len", "j", "IN", "RandomElement", "Any", "ToString", "a", "b", "STRING", "TLCEval"], &[]),
    ("Bags", &["TLC", "Naturals"], &["Bags", "EXTENDS", "TLC", "LOCAL", "INSTANCE", "Naturals", "IsABag", "B", "DOMAIN", "n", "Nat", "BagToSet", "SetToBag", "S", "e", "BagIn", "EmptyBag", "B1", "B2", "IF", "THEN", "ELSE", "LET", "IN", "d", "Sum", "f", "DSum", "SUBSET", "elt", "CHOOSE", "TRUE", "BagUnion", "UNION", "SubBag", "RemoveFromDom", "x", "y", "Combine", "BagSet", "i", "Biggest", "Range", "r", "s", "RSB", "BB", "BagOfAll", "F", "BagCardinality", "CopiesIn"], &[]),
    ("RealTime", &["Reals"], &["RealTime", "EXTENDS", "Reals", "VARIABLE", "now", "RTBound", "A", "v", "D", "E", "LET", "TNext", "t", "IF", "_v", "ENABLED", "THEN", "ELSE", "Timer", "MaxTime", "MinTime", "IN", "RTnow", "NowNext", "r", "Real", "UNCHANGED", "_now", "WF_now"], &[]),
    ("Toolbox", &["Naturals", "FiniteSets", "TLC"], &["Toolbox", "LOCAL", "INSTANCE", "Naturals", "FiniteSets", "TLC", "_TETrace", "CHOOSE", "f", "Nat", "STRING", "TRUE", "_TETraceLength", "Cardinality", "DOMAIN", "_TEPosition", "IF", "TLCGet", "THEN", "ELSE"], &["level"]),
    ("Randomization", &["Naturals", "FiniteSets"], &["Randomization", "LOCAL", "INSTANCE", "Naturals", "FiniteSets", "RandomSubset", "k", "S", "CHOOSE", "T", "SUBSET", "Cardinality", "RandomSetOfSubsets", "n", "TestRandomSetOfSubsets", "i"], &[]),
];
