# tla2rs

[English](README.md)

TLA+ の仕様を、**その仕様専用の Rust 製モデル検査器**にコンパイルするツール。

TLC は仕様を毎回インタプリタで評価し、値をオブジェクトとして持つ。tla2rs は TypeOK から変数の有限の型を読み取り、
状態をビット列に詰めた構造体、`Next` を入れ子の `for` / `if` に直した Rust を吐いて `cargo build --release` する。
仕様を変えるたびにビルド（数秒）が要る代わりに、探索そのものは TLC より桁違いに速い。

```
$ tla2rs examples/Peterson.tla -config examples/Peterson-Live.cfg
tla2rs: generated .tla2rs/Peterson-Live/src/main.rs in 4 ms
tla2rs: built in 1.3 s
63 states generated, 34 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 10.
Temporal properties hold (3 properties, 2 fairness conditions, 62 edges).
Model checking completed. No error has been found.
```

## 使い方

```sh
cargo build --release
./target/release/tla2rs Spec.tla                  # Spec.cfg を読む
./target/release/tla2rs Spec.tla -config Other.cfg -deadlock -workers 8
./target/release/tla2rs Spec.tla -memlimit 64 -notrace        # メモリを絞る
./target/release/tla2rs Spec.tla --emit-only      # Rust を書くだけ（.tla2rs/<cfg名>/src/main.rs）
```

- `-deadlock` / `CHECK_DEADLOCK FALSE` は TLC と同じ意味（デッドロックを誤りにしない）
- `-workers N` は探索のスレッド数（既定は CPU 数）
- `-memlimit MB` は BFS のキューをメモリに置く上限（既定 256 MB）。超えた分は一時ファイルに逃がす（`-tmpdir`）
- `-notrace` は反例を辿るための記録をやめる（1 状態 16 バイト → 8 バイト）
- `-setcap N` と `-seqcap N` は、配列で持つ集合（大きい型の上の関数とバッグの定義域も）の容量と、列の最大の長さを、どこから始めるかを決める。指定しなくてもよい。値が容量を超えると、tla2rs は倍の容量でチェッカーを作り直して最初から確かめ直す（「制限」を参照）
- `-fp128` は指紋を 64 bit から 128 bit にする
- `-metal` は「もう見たか」の問い合わせを GPU（Apple Metal）で行う。`-batched` は同じ 3 段の流れを CPU で行う
- `-dumpgraph FILE` は、探索でたどった状態と遷移を TLC の `-dump dot FILE` と同じ形で FILE に書き出す（状態ごとに節点を作り、TLC が表示するとおりの状態をラベルにし、後続状態ごとに辺を引く）。`tla2rs --graph FILE` はどちらのファイルも、節点の番号や並び順に左右されない状態と辺のハッシュにまとめる。`--graph-text FILE` はまとめる前の正規形をそのまま出す
- `-lassocheck DIR` を付けると、液性の反例を見つけた検査器は `DIR/Tla2rsLasso.tla` と `Tla2rsLasso.cfg` を書き出す。振る舞いがそのラッソひとつだけになる仕様で、ラッソが元の仕様の公平な振る舞いであり、しかも性質を破っているときに限って、TLC はこれを性質違反と報告する（詳しくは CLAUDE.md の「Counterexamples」）
- `tla2rs --trace FILE` は TLC か検査器の出力にある反例を、その長さと、各状態と各ステップのアクションをまとめたハッシュにする。`--trace-text FILE` はまとめる前の正規形を出す
- `tla2rs --messages FILE` は同じ出力のうち、進み具合・統計・反例を除いた部分（エラーや警告のメッセージと、仕様が表示した行）をハッシュにし、そのうちのエラーの行を別のハッシュにする。`--messages-text FILE` は正規形を出す
- 出力（状態数・反例の書式・80 桁を超える値の折り返し・エラーと警告のメッセージ）は TLC に寄せてある。反例の各ステップに付くアクションの名前と位置も TLC と同じ。終了コードも TLC と同じく 10 = ASSUME（偽、または評価に失敗）、11 = デッドロック、12 = 不変条件、13 = 性質（時相の性質と `[][A]_v`）。評価に失敗したときは、不変条件の中なら 76、初期状態なら 75、それ以外は算術の失敗（0 での `\div` など）なら 255、そのほかは 75 で終わる
- PlusCal のアルゴリズムを持つモジュールで、翻訳の始まりの行にチェックサムが書いてある（`\* BEGIN TRANSLATION (chksum(pcal) = ... /\ chksum(tla) = ...)`）ときは、翻訳器が書いたあとでアルゴリズムか翻訳が変わったことを TLC と同じく警告する。PlusCal 側のチェックサムを TLC と同じに計算できるのは、手続き・マクロ・PlusCal のオプションを使わないアルゴリズムだけで、それ以外では警告の代わりに注意書きを出す（制約を参照）

## 速さ

計測は MacBook Pro（M 系 10 コア、16 GB）。TLC は `-workers auto`、tla2rs は既定のスレッド数。
tla2rs の時間は探索だけで、仕様ごとに一度かかるビルド（数秒）は別に書く。

大きな実仕様（1 状態 767 bit、`VIEW` と `SYMMETRY` あり）では、TLC が 50 分かけて届いた地点に tla2rs は 12 分で並び、
TLC が終わらなかった全探索（distinct 約 5.9 億、深さ 73）を 54 分で終えた。

## 仕組み

1. **構文解析**（`parser.rs`）：TLA+ のよく使うサブセット。`/\` `\/` の箇条書きは列で区切る
2. **展開**（`expand.rs`）：演算子の定義をすべて展開する。束縛変数は付け替えて捕獲を避け、呼び出しの跡（名前と実引数）を残す
3. **型**（`types.rs`）：`TypeOK` の `x \in S` / `x \subseteq S` から変数ごとの有限の型を作る。
   文字列とモデル値は `u16`、整数は `i64`、レコードとタプルは Rust のタプル、関数は配列、集合は `u128` のビットマスク
4. **コード生成**（`codegen.rs`）：定数の部分式はコンパイル時に評価してリテラルにする。ただし `[D -> R]`・`\X`・`[a : S]`・`SUBSET` で組んだ要素が 1024 個を超える定数の集合は、要素を書き出さずに部品だけを書いておき、チェッカーがその集合を回すところで TLC と同じ順に要素を作る。
   アクションは「残りの連言」を持ち回る継続渡しで、`\/` `\E` `IF` ごとに分岐を吐き、`x' = e` は `let` になる
5. **実行時**（`runtime.rs`）：BFS を段ごとにスレッドで分けて展開する。状態は型の値域に合わせてビットに詰め、
   訪問済みは 64 bit の指紋だけを持つ。状態が 64 bit 以下なら指紋は可逆なので衝突しない

### メモリ

不変条件だけを調べるときは、状態そのものを取っておかない。持つのは

- 訪問済みの指紋と、その状態を最初に見つけた状態の指紋（1 状態 16 バイト、`-notrace` なら 8 バイト）
- 今の段と次の段のキュー（`-memlimit` を超えた分は一時ファイルに逃がし、塊ずつ読み戻す）

だけで、反例は見つかってから指紋を初期状態まで辿り、初期状態から `next` を辿り直して作る。
状態の幅やモデルの大きさに関わらず、メモリは「指紋の表 + 上限ぶんのキュー」に収まる。

時相の性質を調べるときは SCC 探索のために状態グラフ全体が要るので、こちらは全部メモリに置く
6. **液性**（`live.rs`、`ltl.rs`）：性質を状態の述語・`ENABLED`・アクションの述語からなる式にし、その否定をタブロー法で Büchi オートマトンにする。
   探索中に、各状態ではどの述語が成り立ちどの公平なアクションが有効か、各辺ではどのアクションの述語と公平なアクションを満たすかを記録する。
   探索の後で、状態グラフとオートマトンの積の強連結成分のうち、受理条件と公平性を満たすものを探す（WF はそのアクションの遷移か無効な状態があればよい。
   SF は遷移があるか有効な状態が無いこと。満たさなければ有効な状態を除いて成分を絞り直す）。反例は TLC と同じ書式のラッソで出す

## 対応している範囲

| | |
|---|---|
| 式 | 論理・算術（`+ - * \div % ^`）・比較、列（`Seq`・`Len`・`Append`・`Head`・`Tail`・`SubSeq`・`SelectSeq`・`\o`・添字、タプルと 1..n 上の関数は同じ値）、値としての集合の集合・関数の集合、`IF` / `CASE` / `LET`、`\E` / `\A`（`<<x, y>> \in S` も）、`CHOOSE`（状態にある集合からも、TLC と同じ要素を選ぶ）、集合を書かない `\E x : P`・`\A x : P`・`CHOOSE x : P`（受け付けて、TLC が評価するところで評価エラーになる）、`RECURSIVE` の演算子（中に `ENABLED` があってもよい）と再帰する関数の定義、演算子の引数と `LAMBDA`、仕様が定義する中置演算子（`a \oplus b == ...`）、TLC の `Assert` / `Print` / `PrintT` / `:>` / `@@`、状態にある集合の `UNION` / `SUBSET` / `\X`、集合（リテラル・`\cup \cap \`・`\subseteq`・`{x \in S : P}`・`{e : x \in S}`・`Cardinality`・`SUBSET`）、関数（`[x \in S |-> e]`・`[x \in S, y \in T |-> e]`（`<<a, b>> \in S` が混じってもよい）・再帰しない定義 `f[x \in S] == e`・`f[x]`・`[f EXCEPT ![a] = @ + 1]`・`[S -> T]`。Nat・Int・STRING・`Seq(S)`・65536 要素を超える集合の上の関数は、`[n \in Nat |-> 2 * n][k]` のように TLC と同じく適用したところでだけ評価する）、レコード（`[a |-> 1]`・`r.a` または `r["a"]`・`[a : S]`・`!.a`）、ラベル（`l :: e`）、SANY と同じ名前の付け方で定義の一部を指す式（ラベルで `Op!lab`・`Op(a)!lab(b)`、位置で `Op!1!2`・`Op!<<`・`Op!>>`・`Op!:`、量化子の本体に値を入れる `Op!(e)`、CASE の腕の `Op!i!j`）、タプルと文字列の比較（TLC と同じく左にある値で決まる。タプルは文字列の文字と比べ、文字列にタプルを比べさせると評価エラーになる）、2・8・16 進の数（`\b101`・`\o17`・`\hFF`）、長さの決まったタプル（`<<a, b>>`・定数の添字の `t[1]`・`![k][1]`・`A \X B`） |
| アクション | `x' = e`、`x' \in S`、`UNCHANGED`（どんな式でもよい）、アクションの層の `\/` `\E` `IF` `CASE`、`\A`（定数の集合でも状態にある集合でもよく、要素の順に本体を連言として扱う）、`[A]_v`、変数に代入する再帰演算子（引数は定数でも状態から読んだ値でもよい）、代入済みの `x'` を読むガード、`ENABLED`（Init の中でも） |
| 仕様 | `SPECIFICATION`（`Init /\ [][Next]_v /\ 公平性`。TLC と同じく、連言と引数のない定義（INSTANCE の定義も）をたどって分ける。`[]P` のようなそれ以外の時相の連言は TLC と同じく確かめず、時相の性質はそれらを仮定して確かめる）または `INIT` / `NEXT`。`CONSTANT` はモデル値・自然数・文字列・真偽と、それらの集合（TLC と同じく何重に入れ子にしてもよい）。モデル値は整数と同じ型に混ぜてよい（`1..4 \cup {None}`）。その値の算術はモデル値のときだけ評価エラーになる。変数は整数と文字列を持ち替えてもよく、両者を比べると TLC と同じく評価エラーになる。cfg の `Name <- Def` で定数に定義を代入できる（仕様を EXTENDS する MC.tla などの定義でもよい）。定義の名前に `<-` や `=` を書くとその定義を置き換える。`Nat`・`Int`・`Seq` も同じように置き換えられる（TLC で検査するために上限を付ける `Nat <- SmallNat` のような書き方）。`name = [Module] value` は、そのモジュール（INSTANCE したものも含む）の定義 `name` を値で置き換える。変数のないモジュールを SPECIFICATION・INIT・NEXT のどれも書いていない cfg で検査すると、TLC と同じく ASSUME だけを確かめる。`ASSUME` も確かめる。`INSTANCE`（名前なし、`LOCAL`、`N!Op` で使う `N(p) == INSTANCE M WITH x <- e`。演算子の引数をとるもの、LET の中のもの、`S!Len` のような標準モジュールのもの、`WITH` の演算子記号も）。`EXTENDS RealTime` で変数 `now` が使える。RTnow と RTBound は TLC と同じに扱う（SPECIFICATION の中では確かめず、時相の性質があると受け付けない）。`Real` は文字列 `"Reals"` なので、集合として使うと評価エラーになる。`ASSUME` と `THEOREM` は式に名前を付けてよい（`ASSUME A == ...`）。定理・証明・`USE` / `HIDE` は TLC と同じく読み飛ばす |
| 性質 | `INVARIANT`（`ENABLED` を使ってよい）。`PROPERTY` は状態の述語・`ENABLED A`・アクションの述語（`<<A>>_v`、`[A]_v`）を `[]` `<>` `~>` `/\ \/ ~ =>`、`IF`、`WF` / `SF`、定数の集合（レコードの集合も）の上の `\A` / `\E` で組んだ時相の式。TLC と同じく、状態の述語 P の `[]P` は不変条件として、`[][A]_v` は探索中に、状態の述語は初期状態で調べる。TLC が受け付けない式（SANY の階層の規則、`<>[]A` や `[]<>A` の形でないアクション、時相の式どうしの `<=>`、定数でない集合の上の量化）は TLC と同じメッセージと終了コードで止まる |
| 公平性 | `WF_v(A)` と `SF_v(A)`。A は名前の付いた定義でも式そのものでもよく、`\A` で量化してもよい（`\/`・`=>`・`~`・`IF`・`\E` の中にあれば、時相の性質の仮定として扱う）。`<<A>>_v` が有効かは TLC と同じく A そのもので決める |
| 状態空間 | `CONSTRAINT`、`ACTION_CONSTRAINT`、`VIEW`、`SYMMETRY`（`TYPE` / `TYPE_CONSTRAINT` は TLC と同じく受け付けて何もしない） |

### 制約

- **すべての変数に `TypeOK` の `x \in S`（または `x \subseteq S`）が要る**。`S` は有限で、定数だけで書けること。
  表現（ビット幅）をここから決めるため。変数がこの型の外に出たら、その時点で型エラーとして止まる（TLC は TypeOK を不変条件に入れない限り止まらない）。
  `TypeOK` に無い変数と、`S` から型が決まらない変数（`[D -> Int]` など）は Init と Next から型を推論する。整数の範囲が落ち着くもの（`Cardinality` や `x % 3`）は有限のまま、増え続けるものは上限なしにする。
  `TypeOK` の型が Init や Next に合わないとき（別のモジュールを EXTENDS してレコードにフィールドを足したときなど）は、すべての型を推論し直し、`TypeOK` は普通の不変条件として確かめる。
  フィールドの違うレコードとモデル値を一つの変数に混ぜてもよい（`[P -> Reqs \cup {NoVal}]`）。そのときは `TypeOK` を状態ごとに確かめる。モデル値は、長さの違うタプル・集合・関数・真偽値とも一つの変数に混ぜられる（`Seq(S) \cup {NoVal}` や、モデル値とモデル値の集合を値に持つ関数）。定義域の大きさが違う関数（n の違う `[i \in 0..n |-> e]`）を一つの変数に持たせてもよい
- 要素の型が 128 通りまでの集合はビットマスクで持つ。それより大きいもの（集合の集合を含む）は容量の決まった整列した配列で、列も最大の長さの決まった配列で持つ。こうしておくと、状態をコピーしたり詰めたりするときにメモリを確保しなくて済む。集合の容量は 8 から始める（`TypeOK` に `Cardinality(x) <= K` があればそこから、Init が変数に入れる定数の集合のほうが大きければその大きさから）。要素の型の値の数より大きくはしない。列の最大の長さは、`TypeOK` か `CONSTRAINT` に `Len(x) <= N`（や `UNION {[1..n -> S] : n \in 0..N}`）があればその 1 つ上から始める。なければ Init と Next から長さを伸びなくなるまで求め（アクションの中の `Len(q) < N` のような長さの判定は、そこでの `q` の上限になる）、それも求まらなければ仕様の中の長さの判定から、それもなければ 8 から始める。値が容量を超えると、tla2rs は `tla2rs: a set grew beyond N elements; checking again from the start with room for 2N`（列なら a sequence）と表示し、チェッカーを作り直して最初から動かす。その行より前に出た表示（進み具合や ASSUME の Print）は、もう一度出る。作り直すたびにビルドの数秒がかかるが、容量に収まる仕様は今までと同じ速さで動く。どちらも 65535 までで、それを超える値は評価エラーになる
- 標準モジュール：`Naturals`、`Integers`、`FiniteSets`、`Sequences`（`SortSeq` も。文字列は `\o`・`Len`・`Head`・`Tail`・`Append`・`SubSeq` では文字の列。`SelectSeq`・`SortSeq`・タプルの後に文字列を続ける `\o` では TLC と同じく文字のタプルになる）、`Bags`、`STRING`、`TLC` の `Print`・`PrintT`・`Assert`・`ToString`・`TLCEval`・`Any`・`:>`・`@@`・`Permutations`。負の数の `\div` は TLC と同じく仕様が読み込むモジュールで決まる。Integers を読み込めば商を小さいほうへ丸めた値、Naturals だけなら 0 に向けて丸めてから、それが負のときだけ 1 を引く（`(0 - 1) \div 3` は 0 になる）
- [CommunityModules](https://github.com/tlaplus/CommunityModules) のモジュール：仕様の隣に同じ名前のモジュールが無ければ、tla2rs が自前で用意する。`Folds`、`Functions`、`FiniteSetsExt`、`SequencesExt`、`UndirectedGraphs`（`Path`・`SimplePath`・`AreConnectedIn`・`ConnectedComponents`・`IsStronglyConnected` を除く。これらは TLC 2.19 も評価できない。下を参照）、`Graphs`（同じく経路を扱う演算子と `IsTreeWithRoot` を除く）、`Relation`、`BagsExt`、`Bitwise`、`Combinatorics`、`Statistics`、`GraphViz`、`DyadicRationals`、`VectorClocks`、`Quorum`、`HTML` に対応する。`Json` と `IOUtils` は、TLC 2.19 が評価できる部分だけを用意している。`ToJson`・`ToJsonArray`・`ToJsonObject`・`zeroPadN` は定数にだけ使える。これらは再帰で文字列を組み立てるが、検査器は動いている途中でそれができないので、状態の値に使うと拒否する。`JsonSerialize`・`ndJsonSerialize`・`IOSerialize` はモジュールの定義どおり TRUE になり、ファイルには何も書かない。ファイルを読んだり、コマンドを走らせたり、環境変数を読んだりする演算子（`JsonDeserialize`・`IOExec`・`IOEnv`・`atoi` など）は、TLC 2.19 がその定義のどこで止まるかを理由に添えて拒否する。HTML の演算子は、定数の定義や ASSUME の中ならすぐに評価できるし、Init やアクション、不変条件の中で使ってもすぐにコンパイルできる。LET の定義や実引数は、TLC と同じように最初に使うところで一度だけ計算するからだ（詳しくは CLAUDE.md の「Arguments written out at each use」）。用意していないのは、ファイルを読み書きする `CSV`・`CBOR`、TLC 2.19 が定義を評価できない `ShiViz`・`DifferentialEquations`、それに TLC と突き合わせる構成がまだ無い `SVG` である（詳しくは CLAUDE.md の「CommunityModules」）。TLC 2.19 は CommunityModules の jar にある Java の上書きを読み込めないので、モジュールの TLA+ の定義をそのまま評価する。tla2rs の定義も同じ値になるように書いてある（CHOOSE が選ぶ値や、畳み込みで要素を取る順も同じ）。エラーも同じで、`SequencesExt` の `Interleave` にある CASE のどの条件も成り立たないとき、TLC と同じ位置を出す。用意していない演算子は、使ったところで拒否する
- レコードの並びは TLC と同じく、まずフィールドの数で決まる。モデル値は文字列より前に並ぶ。`Print` と `PrintT` は 80 桁を超える値を TLC と同じく折り返して表示する
- レコードは TLC と同じ順序（TLC がフィールド名を初めて作った順）でフィールドを比べ、表示する。文字列の上の関数はレコードとして表示する。状態の値の `ToString` は型のすべての値の文字列をコンパイル時に作るので、型の値の数は 16 bit の文字列 ID に収まる分（文字列とモデル値を合わせて 65536 個）まで。仕様がフィールドを TLC と違う順に書いたレコードの `ToString` は拒否する。TLC はそのレコードを初めて比べるまでは書いた順に表示するので、文字列がそのタイミングで変わるため
- 型の一部を定義域にする関数（とバッグ）は、型が 65536 通りまでなら型全体の上の配列で持つ。それより大きい型や上限のない型（Nat、広い整数の範囲、集合、それらのレコード）の上では（キー, 値）の組を整列して持ち、キーの容量は集合と同じように増える（`TypeOK` に `Cardinality(DOMAIN f) <= K` と書けば、そこから始まる）。タプルのリテラルは 99,999 要素まで（要素ごとに生成する型のフィールドになる）
- 列挙できない集合（Nat・Int・STRING・`Seq(S)`）の上の関数は、引数に適用するとき（更新ごとに添字 1 つの EXCEPT の後でもよい）、`x \in DOMAIN f`、`ToString`・`Print`・`PrintT` で使える。TLC もそこでは定義域を列挙せずに評価する（表示は `[n \in Nat |-> <expression line 5, col 26 to line 5, col 30 of module M>]` のように、本体の位置を出す）。それ以外で値として使う（変数に入れる、比べる、ほかの値の中に入れる）と拒否する。TLC もそうした使い方の大半ではエラーで止まる
- 状態にある集合の上の関数（`[x \in S |-> e]`・`[S -> T]`・`:>`・`@@`・`Permutations`）は型の一部を定義域にする関数として持つ。入れ子のモジュールを INSTANCE できる。仕様が定義する後置演算子（`^+`・`^*`・`^#`）と中置の `--`・`|-`・`??`・`!!`・`\bigcirc` も使える。`Print` / `PrintT` は TLC と同じく標準出力に書く。引数のない定数の層の定義と ASSUME の中のものは、検査器が始まったときに一度だけ書く
- 初期述語・アクション・不変条件の中の `Print` / `PrintT` は、ワーカーが 1 つなら TLC と同じ順で書く。状態ごとに、その状態を調べる前に出た行を先に書き、探索を止めた状態より後の行は書かない。TLC が反例を組み立て直すときに Init やアクションを評価し直して出す行も、同じところに書く（CLAUDE.md の「Messages and printed lines」）。こうした仕様は `-batched` を付けても通常の探索で調べる
- 未対応：2 要素以上の `RandomElement`、`JavaTime`、`TLCGet` / `TLCSet`（いずれも理由を添えて拒否する）、文字列と整数を両方持ちうる集合（文字列の集合と整数の集合を比べるのは扱える。TLC と同じく、大きさが違えば等しくなく、同じなら評価エラーになる）、
  CONSTANT への `Name <- [Module] Def`（TLC も受け付けない）、`Op!@`
- SANY が受け付けない仕様は、次の理由のものなら TLC と同じく終了コード 150 で止まる：優先順位の範囲が重なる演算子を括弧なしで並べたもの
  （`a /\ b \/ c`・`a = b = c` のほか、前置・後置の演算子が絡む `[]x = 1`・`ENABLED x' = 1`・`a * -b`・`DOMAIN f + 1`・`UNCHANGED x'`）、
  その位置より前でどこにも宣言・定義されていない名前を使ったもの（使われない定義の中でも同じ。拡張していない標準モジュールの `Len`・`+`・単項のマイナスなど）、
  宣言・定義・引数・LET の定義・束縛変数に、その位置で見えている名前を付けたもの（拡張したモジュールや INSTANCE したモジュールの定義、拡張した標準モジュールの演算子も含む）、
  まわりの束縛変数を引数に並べていないラベル、演算子の引数以外の場所に書いた LAMBDA、存在しない部分を指す位置での名前（使われない定義の中でも同じ）、
  演算子を、取るのとは違う数の引数で使ったもの、文字列の中の使えないエスケープ。どれも SANY と同じ文面と位置で報告する。構文のエラー（優先順位、エスケープ、LAMBDA）と時相の式の階層のエラーに加えて、名前の検査のエラーも、SANY と同じくモジュールの中のものを見つけた順にすべて出し、ぶつかった相手の宣言の位置（標準モジュールの中のものも）を添え、最後に SANY の警告を出す。
  名前が見えるのは SANY と同じくそれを導入した文のあとからなので、演算子の引数にあとで宣言する VARIABLE と同じ名前を付けてもよい。
  集合を書かない `\E x : P`・`CHOOSE x : P` と `\EE`・`\AA` の中の名前、LET の定義を位置で指す名前、演算子を取らない引数に渡した演算子、SANY のそれ以外の検査は調べないので、そうした仕様を受け付けてしまうことがある（CLAUDE.md の「What SANY refuses」）
- PlusCal のアルゴリズムが翻訳のあとで変わったという TLC の警告を再現するのは、手続き・呼び出し・return・マクロ・PlusCal のオプションを使わず、翻訳器が名前を付け替える（同じラベルが二つあるなど）ことも、ラベルを足すこともないアルゴリズムに限る。それ以外では警告を出さず、標準エラーに注意書きを出す
- EXCEPT が値に無い引数やフィールドを指したときの TLC の警告は、TLC と同じように出す。同じ文面は 1 回しか出さず、最初の警告には `-nowarning` についての TLC の注記が付く。ただし、アクションや不変条件の中にある定数の EXCEPT はコンパイラが一度だけ評価するので、検査器はその警告を出さない
- 再帰はワーカーのスタックを 1 MB 使ったところで評価エラーにする（小さな本体で約 9,000 段、コンパイル時は 50,000 段）。TLC の JVM スタックはずっと早く（小さな本体で 500〜900 段）あふれるので、その間の深さの再帰は TLC がスタックあふれを報告するところでここでは通る
- 状態が 64 bit を超えると訪問済みは指紋で持つので、TLC と同じく衝突の確率がわずかにある（終わりに見積もりを出す）
- 液性検査は状態グラフ全体（辺 1 本 40 byte 程度）をメモリに置き、性質のオートマトンとの積の探索には、たどり着く積の大きさのハッシュ表を使う。不変条件だけなら上の「メモリ」のとおり
- 文字列の順序は TLC と同じく、TLC がその文字列を初めて作った順になる。cfg とモジュールに出てくるもの（名前、書いたとおりの数、文字列リテラル）は TLC が読んだ順で、演算（`\o`・`Append`・`Head`・`Tail`・`SubSeq`・`ToString`）で作られるものは TLC が作った順になる。TLC は起動したときに定数レベルの定義を使われていなくてもすべて評価し、続けて ASSUME を評価するので、まずそこで作られた文字列が並び、そのあとに探索の途中で作られた文字列が並ぶ。チェッカーの文字列の番号はビルドするときに決まってしまうので、ワーカーが 1 つのときは、チェッカーが文字列を作った順を記録しておく。その順が番号と食い違っていたら、tla2rs は `tla2rs: strings were made in another order than they were numbered in; checking again from the start with them in that order` と表示して、その順に番号を付け直したチェッカーを作り直し、最初から動かす（8 回まで。その行より前に出た表示はもう一度出る）。合わせていないのは次の場合。ワーカーが複数だと、TLC での順序は実行のタイミングで変わるので、チェッカーはビルドしたときの順のままにする。tla2rs がコンパイル中に計算する定数の式のうち、値そのもの・量化子が動く集合・所属を調べる集合以外のところ（IF の条件など）で作られる文字列と、文字列を文字のタプルに分けたときの各文字（`SelectSeq`・`SortSeq`・文字列とタプルの比較）は、tla2rs が出会った順のままになる
- TLC が区間として持つ集合（`x = 1..3`）は `{1, 2, 3}` と表示する。TLC は、演算で要素を並べた集合に変わるまでは `1..3` と表示する。TLC がどちらの形で表示するかは値の作られ方で決まる（CLAUDE.md の「State graphs」）ので、TLC との比較では区間をそれが表す集合として読む
- 液性の反例は正しいラッソだが、TLC が出すものと同じとは限らない。TLC 自身の反例も実行ごとに変わる（TLC が毎回乱数で選ぶ指紋の多項式に左右される）ので、TLC の反例とは突き合わせない。その代わり、tla2rs のラッソが正しいかを TLC に確かめさせている（`-lassocheck`）。`VIEW` や `SYMMETRY` があるときは、TLC が振る舞いを組み立て直すのと同じく、ラッソを実際の状態でたどり直す。ビューから外した値が増え続ける仕様では、ラッソは閉路の最初の状態にビューの上でしか戻らないので、確かめる側も同じビューで状態をまとめる。確かめた結果は検査用の仕様・モジュール・jar のハッシュで `target/crosscheck/lasso` に残し、ラッソが変わらない限り TLC は回し直さない
- `VIEW` と `SYMMETRY` を同時に使うときは、TLC と同じやり方で状態を畳む。まず置換した状態のうちいちばん小さいもの（値は TLC と同じ比べ方で、変数は TLC が表示する順に比べる）を選び、その状態のビューを取る。置換した状態をまるごと比べるので、ビューだけを比べていたころより手間がかかる

## 確かめ方

`scripts/crosscheck.sh` は TLC（`-workers 1`）と tla2rs で同じ構成を回し、結果・生成状態数・distinct 状態数・エラーで止まったときに TLC のキューに残っていた状態の数・反例・終了コード・メッセージと表示した行に加えて状態グラフを比べる。状態グラフとは、たどり着いた状態の集合と、状態どうしの遷移の集合のことで、TLC の `-dump dot` と tla2rs の `-dumpgraph` の出力をそれぞれ SHA-256 のハッシュにまとめて比べる。各状態の変数は TLC が表示する順のまま比べる。TLC はルートモジュールの名前を入れた SANY のハッシュ表の順に変数を並べるので、tla2rs も同じ表の順を計算して、その順に表示する。安全性の反例は 1 ステップずつ、状態と、そこへ至ったアクション（TLC の付ける名前と位置）を比べる。ワーカーが 1 つなら TLC の反例は毎回同じになる。液性の反例は TLC が乱数で選ぶ指紋の多項式に左右されるので、代わりに `-lassocheck` が書き出す仕様を TLC にかけ、tla2rs のラッソが仕様の公平な振る舞いで、性質を破っていることを TLC に確かめさせる。メッセージとは、TLC が出すエラーと警告の行と、仕様が `Print` / `PrintT` で表示した行を、出た順に並べたものである。進み具合の行は除き、TLC の内部の事情を表す部分（評価していた入れ子の式の一覧や Java のクラス名）も除く。TLC の文面をすべては出せない構成は、cfg にその理由を書けばエラーの行だけを比べる（いまはそれが要る構成はない）。グラフ全体を比べられない場合（初期状態の計算中に止まると TLC はグラフのファイルを最後まで書かない、tla2rs が表せない後続状態がある）は比べる範囲を狭め、`all.sh` がどの規則を使ったかを表示する。規則の一覧は CLAUDE.md にある。
`scripts/all.sh` は `examples/` と `tests/tlc/` の全構成をこれで回す。`-batched` などの引数を付けると、各構成にそのまま渡す。`tla2tools.jar` は `TLA_TOOLS` で渡す（既定 `~/.tla/tla2tools.jar`）。CommunityModules のモジュールを EXTENDS や INSTANCE で使う仕様では、TLC のために `scripts/crosscheck.sh` が固定しているリリース（202611060952、sha256 `a3b27c40f1fb5085f30c6ead37e918457f8cfc62c1e50a1dc668ef592ad2b5fb`）を `COMMUNITY_MODULES` で渡す（既定 `~/.tla/CommunityModules-deps.jar`）。

```sh
curl -L -o ~/.tla/CommunityModules-deps.jar \
  https://github.com/tlaplus/CommunityModules/releases/download/202611060952/CommunityModules-deps-202611060952.jar
shasum -a 256 ~/.tla/CommunityModules-deps.jar
```

TLC 2.19 はこの jar の Java の上書きを読み込めない。2023 年 12 月から 2026 年 11 月までの、試したリリースはどれも TLC 2.19 に無いクラスを使っていて、どんな仕様でも `NoClassDefFoundError: tlc2/value/impl/KSubsetValue` で止まる。そこで `crosscheck.sh` は jar からモジュールだけを `target/community/` に取り出して TLC に渡す。そういう仕様の結果ファイルのキーには jar のハッシュも入る。`tests/expected/` と比べるだけなら jar は要らない。`all.sh` は 4 構成ずつ並行に回す（`JOBS=N` で変えられる）。TLC の結果は構成ごとに `tests/expected/` にコミットしてある。中身は判定・状態数・反例の長さとハッシュ・終了コード・状態グラフとメッセージのハッシュと、jar・cfg・引数・仕様が読むモジュール・`src/graph.rs`・`src/trace.rs`・`src/messages.rs` のハッシュである。時刻・指紋の種・liveness の反例の形は TLC の実行ごとに変わるので記録せず、ファイルはどの実行でも同じになる。`crosscheck.sh` と `all.sh` はこのファイルと比べるだけで、構成そのものに TLC は回さない（回すのはラッソの確認だけ）。ファイルが無いか古いときは失敗にする。TLC を回すのは `scripts/expected.sh [cfg ...]` だけで、無いものと古いものだけを書き、ほかには触らないので、2 回目は何も変えない。`expected.sh -check` は TLC を回し直して食い違うファイルを報告し、書き込みはしない。`-force` はすべて書き直す。ビルドした検査器は、生成コードと rustc の版のハッシュで `target/crosscheck/build` に残す(`CROSSCHECK_NO_CACHE=1` で毎回ビルドし直す)。

```
$ scripts/all.sh
ok    examples/DieHard.cfg
ok    examples/Peterson-Live.cfg
ok    examples/TwoPhase.cfg
...
ok    tests/tlc/AssumeFalse.cfg  (graph not compared: TLC stopped before ending it)
...
```

### 公開されている仕様集との突き合わせ

上の構成は、誰かが思いついた書き方しか確かめられない。そこで `scripts/corpus.sh` は、tlaplus/Examples リポジトリ（https://github.com/tlaplus/Examples）のモデルとも同じやり方で突き合わせる。使うのは `tests/corpus.txt` に固定したコミットで、仕様集は `target/corpus/<コミット>/` に取ってきて TLC と tla2rs に読ませるだけにする。このリポジトリには仕様集の中身を一切写さず、TLC の結果（`tests/expected/corpus/`、書くのは `scripts/expected.sh -corpus`）だけを置く。`tests/corpus.txt` には仕様集のマニフェストにあるモデルをすべて並べ、選んだもの（TLC 2.19 が `tla2tools.jar` と CommunityModules のモジュールで、ワーカー 1 つで 60 秒以内に終える全探索）と、選ばなかったものそれぞれの理由を書いてある。選んだのにまだ tla2rs が一致しないモデルは、測って確かめた理由を添えて差分として載せる。`all.sh` とは別に回すので、`all.sh` の手間は変わらない。選んだ 106 モデルはすべて TLC と一致する（うち 7 つは生成した状態の数だけが違う。TLC は同じ後続状態を `\/` の枝ごとに数えるため）。その理由は `tests/corpus.txt` と CLAUDE.md に書いてある。

| 例 | 中身 |
|---|---|
| `DieHard` | 水差しのパズル。`NotSolved` の反例が答え |
| `Peterson` | 相互排除。`-Live` は弱公平性のもとで飢餓が無いこと、`-Unfair` は片方にしか公平性が無いと破れること |
| `TwoPhase` | 二相コミット（5 RM）。メッセージはレコードの集合 |
| `Features` | 対応範囲をなめる小さな仕様（`SeenOK` が破れる） |
| `Liveness` | `<>` `[]<>` `<>[]` `~>`、足踏みと周回の反例 |

### TLC との速さ比べ

`scripts/bench.sh` は `examples/` と `tests/tlc/` の全構成（`-corpus` を付けると仕様集から選んだモデル）を TLC と tla2rs で回して、構成ごとにかかった時間と最大メモリを測る。TLC はワーカー 1 つで回す。tla2rs は、Rust のコードを生成するところ、それをビルドキャッシュを使わずにビルドするところ、できた検査器をワーカー 1 つで動かすところに分けて測る（`-auto` を付けると、TLC の `-workers auto` と検査器の既定のワーカー数でも測る）。結果は構成ごとに 1 行ずつ `target/bench/results.tsv` に書き、tla2rs のほうが遅い構成を、検査だけの時間とビルドまで含めた時間のそれぞれについて、遅い比率の大きい順に `target/bench/summary.txt` に並べる。測り終えた構成は次に回したときに飛ばすので、途中で止めても続きから測れる（`-force` で測り直す）。既定では 1 構成ずつ測る。`JOBS=N` を付けると N 構成ずつ並行に回せるが、そのぶん時間の精度は落ちる。

```sh
scripts/bench.sh                  # examples/ と tests/tlc/
scripts/bench.sh -corpus          # 仕様集（-norun を付けると、corpus.sh では重すぎて回さないモデルも測る）
scripts/bench.sh -corpus MCbtree  # cfg のパスに MCbtree を含むモデルだけ
```

## これから

- 列（`Sequences`）と、集合の集合
- 定数を実行時の引数にして、構成を変えるたびのビルドを省く

## ライセンス表記

tla2rs の一部は TLC、TLA+ Examples、CommunityModules から派生している。どれも MIT License で、表示と許諾文は [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) にある。
