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
Temporal properties hold (3 properties, 2 fairness instances, 62 edges).
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
- `-setcap N` は実行時に大きさが決まる集合の容量
- `-fp128` は指紋を 64 bit から 128 bit にする
- `-metal` は「もう見たか」の問い合わせを GPU（Apple Metal）で行う。`-batched` は同じ 3 段の流れを CPU で行う
- 出力（状態数・反例の書式）は TLC に寄せてある。終了コードも TLC と同じく 10 = ASSUME、11 = デッドロック、12 = 不変条件、13 = 時相の性質、255 = 評価の誤り

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
4. **コード生成**（`codegen.rs`）：定数の部分式はコンパイル時に評価してリテラルにする。
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
6. **液性**：辺に「どの公平性のインスタンス（`WF(Create(d1))` など）の遷移か」を付けて記録し、探索の後で
   性質を破り続けられる状態だけの部分グラフの SCC を取り、公平なもの（または公平な足踏み）を探す。反例は TLC と同じラッソで出す

## 対応している範囲

| | |
|---|---|
| 式 | 論理・算術（`+ - * \div %`）・比較、`IF` / `CASE` / `LET`、`\E` / `\A`、集合（リテラル・`\cup \cap \`・`\subseteq`・`{x \in S : P}`・`{e : x \in S}`・`Cardinality`・`SUBSET`）、関数（`[x \in S |-> e]`・`[x \in S, y \in T |-> e]`・再帰しない定義 `f[x \in S] == e`・`f[x]`・`[f EXCEPT ![a] = @ + 1]`・`[S -> T]`）、レコード（`[a |-> 1]`・`r.a`・`[a : S]`・`!.a`）、長さの決まったタプル（`<<a, b>>`・定数の添字の `t[1]`・`![k][1]`・`A \X B`） |
| アクション | `x' = e`、`x' \in S`、`UNCHANGED`、アクションの層の `\/` `\E` `IF` `CASE`、代入済みの `x'` を読むガード |
| 仕様 | `SPECIFICATION`（`Init /\ [][Next]_v /\ 公平性`）または `INIT` / `NEXT`。`CONSTANT` はモデル値・数・文字列・真偽・その集合。モデル値は整数と同じ型に混ぜてよい（`1..4 \cup {None}`）。cfg の `Name <- Def` で定数に定義を代入できる（仕様を EXTENDS する MC.tla などの定義でもよい）。定義の名前に `<-` や `=` を書くとその定義を置き換える。`ASSUME` も確かめる |
| 性質 | `INVARIANT`。`PROPERTY` は `<>P` `[]<>P` `<>[]P` `P ~> Q` `[]P` `[][A]_v`（`\A x \in S :` で量化してもよい） |
| 公平性 | `WF_v(A)`（`\A` で量化してもよい）。`A` は名前の付いた定義で、`Next` から呼ばれていること |
| 状態空間 | `CONSTRAINT`、`VIEW`、`SYMMETRY` |

### 制約

- **すべての変数に `TypeOK` の `x \in S`（または `x \subseteq S`）が要る**。`S` は有限で、定数だけで書けること。
  表現（ビット幅）をここから決めるため。変数がこの型の外に出たら、その時点で型エラーとして止まる（TLC は TypeOK を不変条件に入れない限り止まらない）。
  `TypeOK` に無い変数は Init と Next から型を推論する。整数の範囲が落ち着くもの（`Cardinality` や `x % 3`）は有限のまま、増え続けるものは上限なしにする
- 集合の要素の型は 128 通りまで。集合の集合・関数の集合を値として持つことはできない（`TypeOK` の `SUBSET` / `[S -> T]` は使える）
- 未対応：列（長さが変わるタプルと `Sequences` の演算子）、定数でないタプルの添字、文字列と整数を混ぜた値、
  モデル値かもしれない値の算術、状態に依る `CHOOSE`、再帰、強公平性（SF）、
  `ENABLED`、`<<A>>_v`、再帰する関数の定義、CONSTANT への `Name <- [Module] Def`、演算子の定数
- 状態が 64 bit を超えると訪問済みは指紋で持つので、TLC と同じく衝突の確率がわずかにある（終わりに見積もりを出す）
- 液性：公平性つきのアクションが有効かどうかは、それを呼ぶ `Next` の分岐が後続状態を作るかで決める。
  `Next` の中で `A /\ 追加の条件` のように絞って呼ぶと「有効」を少なく見積もり、偽の反例が出ることがある（誤って「成り立つ」とは言わない）
- 液性検査は状態グラフ全体（辺 1 本 24 byte 程度）をメモリに置く。不変条件だけなら上の「メモリ」のとおり
- `VIEW` と `SYMMETRY` を同時に使うと、distinct 数が TLC より少なくなる。TLC はビューの値が一致する状態を
  別物として残すことがあるため（代表状態の選び方が状態そのものに依る）。tla2rs はビューの軌道で畳む。
  どちらか片方だけなら TLC と完全に一致する

## 確かめ方

`scripts/crosscheck.sh` は TLC（`-workers 1`）と tla2rs で同じ構成を回し、結果・生成状態数・distinct 状態数・反例の長さ・終了コードを比べる。
`scripts/all.sh` は `examples/` と `tests/tlc/` の全構成をこれで回す。`tla2tools.jar` は `TLA_TOOLS` で渡す（既定 `~/.tla/tla2tools.jar`）。

```
$ scripts/all.sh
ok    examples/DieHard.cfg
ok    examples/Peterson-Live.cfg
ok    examples/TwoPhase.cfg
...
```

| 例 | 中身 |
|---|---|
| `DieHard` | 水差しのパズル。`NotSolved` の反例が答え |
| `Peterson` | 相互排除。`-Live` は弱公平性のもとで飢餓が無いこと、`-Unfair` は片方にしか公平性が無いと破れること |
| `TwoPhase` | 二相コミット（5 RM）。メッセージはレコードの集合 |
| `Features` | 対応範囲をなめる小さな仕様（`SeenOK` が破れる） |
| `Liveness` | `<>` `[]<>` `<>[]` `~>`、足踏みと周回の反例 |

## これから

- 列（`Sequences`）と、集合の集合
- 定数を実行時の引数にして、構成を変えるたびのビルドを省く
- 強公平性
