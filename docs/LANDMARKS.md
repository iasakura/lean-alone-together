# 重要な定義・定理のランドマーク

この文書は、「全部は読めないが、重要な定義と定理は押さえたい」という目的のためのノートです。  
各項目について、次をまとめています。

- 直感
- 定義や定理の読み方
- 何が本質か
- 証明の方針

細かい補題や proof engineering の都合で入っている補助定理は、基本的に省いています。

## 0. まず把握しておく全体像

この repo の本体は、次のパイプラインです。

1. `Syntax.lean`
   `T` の構文
2. `Semantics.lean`
   実行意味論
3. `Logic.lean`
   rely-guarantee judgment とその意味論
4. `Transformer.lean`
   VCG / transformer inference
5. `Server.lean`
   handler / request / server correctness

読むときのコツは、「定義の依存方向」に沿って読むことです。  
たとえば `globalRG_sound` を読みたいときは、その前に

- `GlobalRG`
- `GlobalValid`
- `globalInterleavedStep`
- `Semantics.Step`

だけ押さえれば十分です。

論文忠実の並列側を追いたいときは、代わりに

- `globalInterleavedStepTR`
- `GlobalValidTR`
- `HandlerRefinesTR`
- `txnPair_parallelValidTR`

を押さえてください。

## 1. `Syntax.lean`

### `Command`
[Command](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Syntax.lean)

**直感**

論文の言語 `T` の構文です。  
ただし source syntax だけではなく、実行時ノードも一緒に入っています。

**どこを見るか**

- `txn`
- `txnRuntime`
- `foreach`
- `foreachRuntime`
- `par`

**どう読むか**

- `txn txnId isolation body`
  transaction を開始する source form
- `txnRuntime txnId isolation localDb snapshot body`
  実行中 transaction
- `par left right`
  並列実行

**何が本質か**

この repo では source term と runtime term を別 datatype にせず、`Command` にまとめています。  
そのため small-step semantics がかなり直接的に書けます。

**補足**

ここで `txnRuntime` の 4 つ目は「現在の global DB」ではなく、transaction が持っている `snapshot` です。これは後で非常に重要です。

## 2. `Semantics.lean`

### `Row`
[Row](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Semantics.lean)

**直感**

論文の hidden metadata つき row です。

**どう読むか**

- `visible`
  ユーザーに見える record
- `txn`
  その row を最後に書いた transaction
- `del`
  削除マーク

**何が本質か**

論文中では hidden field として扱う `txn`, `del` を、Lean では明示的な runtime data として持たせています。

### `IsolationSpec`
[IsolationSpec](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Semantics.lean)

**直感**

分離仕様を `exec` と `commit` に分けたものです。

**どう読むか**

- `exec localDb previous current`
  実行途中に snapshot / visible DB がどう変わってよいか
- `commit localDb previous current`
  commit 直前に何を満たしていなければいけないか

**何が本質か**

論文の isolation assumptions を、Lean では 2 つの relation として明示しています。  
これが `relyMod` と `respectsRely` の中で使われます。

### `Database.flush`
[Database.flush](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Semantics.lean)

**直感**

local write set を global DB に反映する commit 操作です。

**どう読むか**

- localDb に入っている inserted / deleted / updated row をまとめて global DB に反映する

**何が本質か**

後で guarantee はだいたい

```lean
G visibleDb (Database.flush localDb visibleDb)
```

という形で現れます。

### `Semantics.LocalStep`
[Semantics.LocalStep](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Semantics.lean)

**直感**

transaction 本体だけの small-step semantics です。

**どう読むか**

- 第一引数の `snapshot`
  transaction が現在見ている DB
- `localDb`
  transaction の未コミット delta

**何が本質か**

local semantics は global concurrency をまだ見ていません。  
`select`, `insert`, `delete`, `update`, `foreach` がここで定義されます。

### `Semantics.Step`
[Semantics.Step](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Semantics.lean)

**直感**

top-level machine step です。

**どう読むか**

- `txnStart`
  source の `txn` から runtime node へ移る
- `txnExec`
  runtime node の body を 1 step 進める
- `txnCommit`
  body が `skip` なら `flush` して終わる
- `parLeft` / `parRight`
  並列合成の片側を進める

**何が本質か**

この `Step` は actual machine step だけを表します。  
環境による interference はまだ入っていません。

## 3. `Logic.lean`

ここが Sec. 4 の中心です。

### `stableAssertion`, `stableBiAssertion`, `stableIsolation`
[stableAssertion](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

rely step が入っても assertion や isolation relation が壊れないことです。

**どう読むか**

- `stableAssertion R P`
  `P db` が成り立っていて `R db db'` なら `P db'`
- `stableBiAssertion`
  localDb と visibleDb を両方見る版
- `stableIsolation`
  isolation 条件そのものの安定性

**何が本質か**

RG では「環境が動いても前提が保たれる」ことが必要です。  
この repo でも stability は proof rule の side condition として頻出します。

### `relyMod`
[relyMod](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

global rely を、現在の isolation guard で絞ったものです。

**どう読むか**

```lean
relyMod R I localDb visibleDb visibleDb'
```

は

- `R visibleDb visibleDb'`
- かつ `I localDb visibleDb visibleDb'`

の両方を要求します。

**何が本質か**

local proof は「どんな interference でもいい」わけではなく、その isolation level で許される interference だけを相手にします。

### `localInterleavedStep`
[localInterleavedStep](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

local actual step と local rely step を混ぜた遷移です。

**どう読むか**

2 つの disjunct があります。

- 左: `Semantics.LocalStep`
- 右: command と localDb は不変のまま、visibleDb だけ rely で変わる

**何が本質か**

local semantic validity は actual execution だけでなく interference を含む trace に対して定義されます。

### `refreshVisible`
[refreshVisible](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

global DB が変わったあと、runtime transaction node の内部に持っている `snapshot` を更新する bookkeeping です。

**どう読むか**

- `txnRuntime ... localDb _ body`
  の `_` を新しい visible DB に差し替える
- `par` なら左右再帰

**何が本質か**

これは global DB を変える関数ではありません。  
変わった global DB を、program 側の cached snapshot に反映するための関数です。

### `respectsRely`
[respectsRely](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

ある global DB の変化を、program 全体が rely interference として受けてよいかを判定します。

**どう読むか**

- runtime transaction なら `R` に加えて `isolation.exec` または `isolation.commit`
- `par` なら左右両方が受けられないといけない

**何が本質か**

`refreshVisible` は単に snapshot を更新するだけですが、それが本当に allowed interference かどうかは `respectsRely` が決めています。

### `globalInterleavedStep`
[globalInterleavedStep](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

top-level actual step と global rely step を混ぜた遷移です。

**どう読むか**

```lean
Semantics.Step ... ∨
(program' = refreshVisible program globalDb' ∧ respectsRely R program globalDb globalDb')
```

の形です。

**何が本質か**

`GlobalValid` や `globalRG_sound` はこの interleaved semantics に対して定義されています。  
この repo の concurrency semantics の本体です。

### `globalInterleavedStepTR`
[globalInterleavedStepTR](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

TR Appendix C.2 に忠実な top-level interleaving です。

**どう読むか**

```lean
Semantics.Step ... ∨
(program' = program ∧ R globalDb globalDb')
```

の形です。

**何が本質か**

rely step では outer DB だけが動き、program は変わりません。`globalInterleavedStep` と違って `refreshVisible` を使わないので、cached snapshot は transaction 自身が次に actual step を取るまで更新されません。

### `GlobalValidTR`
[GlobalValidTR](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

`GlobalValid` の TR-faithful 版です。

**どう読むか**

`GlobalMultiStepTR` を使う以外は `GlobalValid` と同じです。

**何が本質か**

既存の VCG や server 層を、論文忠実の global semantics 側へ運ぶときの基準点です。

### `globalValid_false_to_TR_false`
[globalValid_false_to_TR_false](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

rely が `False` なら、旧来の global semantics と TR-faithful semantics は一致します。

**どう読むか**

`GlobalValid I False p G Q` を `GlobalValidTR I False p G Q` に持ち上げます。

**何が本質か**

既存の no-rely VCG 結果を TR 側へ再利用するための基本補題です。

### `globalValidTR_of_silentRely`
[globalValidTR_of_silentRely](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

global DB を変えない rely は stuttering にすぎないので、`False`-rely の TR proof をそのまま持ち上げられます。

**どう読むか**

`R db db' -> db' = db` を仮定して、`GlobalValidTR ... False ...` から `GlobalValidTR ... R ...` を得ます。

**何が本質か**

identity guarantee など silent interference を相手にした transaction proof の入口です。

### `LocalValid`
[LocalValid](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

local judgment の意味論です。

**どう読むか**

`P` が成り立つ状態から `c` を interleaving つきで実行して `skip` まで到達したら、`Q` が成り立つ。

**何が本質か**

`LocalRG` は syntax-directed rule system ですが、`LocalValid` はその「本当の意味」です。

### `GlobalValid`
[GlobalValid](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

top-level judgment の意味論です。

**どう読むか**

定義は 2 つの成分に分かれます。

- postcondition 成分
  final program が `skip` なら invariant/postcondition が成り立つ
- guarantee 成分
  transaction の commit step は保証 relation `G` を満たす

**何が本質か**

この repo では top-level correctness は「終了時の postcondition」だけでなく、「各 commit が何を保証するか」も含みます。

### `LocalRG`
[LocalRG](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

論文 Sec. 4 の local proof system です。

**どう読むか**

各 constructor が 1 つの proof rule に対応します。

- `skip`
- `letE`
- `ite`
- `seq`
- `select`
- `insert`
- `delete`
- `update`
- `foreach`
- `conseq`

**何が本質か**

ここを読むと、「この logic は各構文をどう扱っているか」が分かります。  
特に `insert/delete/update` は operational semantics を直接 reflect した rule になっています。

**証明方針**

`localRG_sound` はこの inductive definition に対する帰納法です。  
各 constructor ごとに対応する `LocalValid` 補題を使って closure しています。

### `GlobalRG`
[GlobalRG](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

top-level proof system です。

**どう読むか**

いまある constructor は主に

- `txn`
- `conseq`

です。

`txn` rule は

- global invariant `I`
- local pre/post `P/Q`
- local proof `LocalRG`
- guarantee `G`

をつないでいます。

**何が本質か**

現時点では一般の `par` rule はここにはありません。  
server-level の並列 reasoning は `Server.lean` に切り出されています。

### `localRG_sound`
[localRG_sound](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

local proof system は semantic に正しい。

**どう読むか**

```lean
LocalRG ... P c Q -> LocalValid ... P c Q
```

という Theorem 4.3 の local 側です。

**証明方針**

構文規則ごとの induction。  
難しいのは `seq` と `foreach` で、そこで使うために前半に multistep 分解や prefix-strip 補題が大量にあります。

### `globalRG_sound`
[globalRG_sound](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Logic.lean)

**直感**

top-level RG proof system も semantic に正しい。

**どう読むか**

```lean
GlobalRG ... I program G Ipost -> GlobalValid ... I program G Ipost
```

です。

**何が本質か**

Theorem 4.3 の global 側です。

**証明方針**

芯は「running transaction の global execution を local execution に前向きシミュレートする」ことです。  
`txnRuntimeFwd_sound` や `txnProgramFwd_sound` がその中核です。

## 4. `Server.lean`

### `HandlerRefinesTR`
[HandlerRefinesTR](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Server.lean)

**直感**

TR-faithful な handler correctness の別名です。

**どう読むか**

`GlobalValidTR` を request / handler 側で読みやすい名前にしたものです。

**何が本質か**

Appendix B/C の parallel theorem を server 層で使うときの前提は、こちらで書きます。

### `txnPair_parallelValidTR`
[txnPair_parallelValidTR](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Server.lean)

**直感**

Appendix B/C の 2 本並列 transaction 向け packaged theorem です。

**どう読むか**

- 左は `R ∨ GRight` の下で `HandlerRefinesTR`
- 右は `R ∨ GLeft` の下で `HandlerRefinesTR`

なら

- `txnLeft || txnRight` は `ParallelValidTR` を満たす

と読みます。

**何が本質か**

標準 RG の `par` 規則を exact projection で示すのではなく、

- first commit
- second phase

に分けて証明している点が重要です。TR の並列 soundness を server 層で再利用するための主定理です。
## 5. `SetLanguage.lean`

### `SetExpr`
[SetExpr](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/SetLanguage.lean)

**直感**

論文 Fig. 7 の集合言語 `S` です。

**どう読むか**

- `.localDb`
- `.globalDb`
- `.comprehension`
- `.bind`
- `.existsSet`
- `.ite`
- `.union`

**何が本質か**

この repo の symbolic VCG は最終的に `SetExpr` を返します。

### `denote`
[denote](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/SetLanguage.lean)

**直感**

`SetExpr` の意味論です。

**どう読むか**

`denote ρ s row` は、「環境 `ρ` のもとで row が set expression `s` に属するか」です。

**何が本質か**

symbolic effect の soundness は、最終的にはこの `denote` と concrete rows の一致として言われます。

### `abstractGlobal`, `weakenToInvariant`
[abstractGlobal](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/SetLanguage.lean)  
[weakenToInvariant](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/SetLanguage.lean)

**直感**

論文の weakening に対応します。

**どう読むか**

- `abstractGlobal x`
  distinguished global DB を symbolic set variable `x` に置き換える
- `weakenToInvariant x I s`
  その `x` を invariant のもとで existentially quantify する

**何が本質か**

exact symbolic post を、そのままではなく invariant で弱めた post に変えるときに使います。

## 6. `Transformer.lean`

### `instantiateExpr`, `instantiateCommand`
[instantiateExpr](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)  
[instantiateCommand](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)

**直感**

環境から変数を埋める前処理です。

**何が本質か**

`select`, `let`, `foreach` の binder をまたぐ syntax-directed inference を書くための基盤です。

### `inferEffect`
[inferEffect](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)

**直感**

transaction body が最終的に localDb に積む rows を直接計算する semantic transformer です。

**どう読むか**

型は

```lean
Semantics.Program -> Database -> Option Database
```

で、visible DB を与えると「書き込まれる rows」が返ります。

**何が本質か**

現在の VCG の土台はまずこれです。  
論文の symbolic `S` より先に、concrete effect を計算しています。

### `TransactionVCG` と `vcg`
[TransactionVCG](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)  
[vcg](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)

**直感**

1 個の transaction に対する verification condition の束です。

**どう読むか**

入っているのは

- `effect`
- `execStable`
- `commitStable`
- `guaranteeOk`
- `preservesInvariant`

です。

**何が本質か**

この repo の「VCG」は、formula を直接返すより、まず effect とその side condition をまとめる設計です。

### `vcg_sound_false`, `vcg_sound`
[vcg_sound_false](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)  
[vcg_sound](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)

**直感**

VCG で出した obligation を満たせば `GlobalValid` が得られる。

**どう読むか**

- `vcg_sound_false`
  no-rely case の扱いやすい版
- `vcg_sound`
  一般版

**何が本質か**

実際に `Examples.lean` で使う入口はまず `vcg_sound_false` です。

**証明方針**

`inferEffect` の soundness を local validity に落とし、さらに transaction-level bridge で `GlobalValid` に持ち上げています。

### `inferSetEffect`
[inferSetEffect](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)

**直感**

`inferEffect` の symbolic 版です。

**どう読むか**

`inferEffect` と同じ構文再帰ですが、結果が rows ではなく `SetExpr` です。

**何が本質か**

論文 Fig. 8 にいちばん近い定義です。

### `inferSetEffect_sound`
[inferSetEffect_sound](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)

**直感**

symbolic effect は concrete effect と一致する。

**どう読むか**

`row ∈ localDb` と `SetLanguage.denote ... s row` の同値を言います。

**何が本質か**

`SetExpr` 側で reasoning しても concrete semantics からズレていないことを保証する定理です。

### `symbolicVcg`, `symbolicVcgForTxn`, `symbolicPostForTxn`
[symbolicVcg](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)  
[symbolicVcgForTxn](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)  
[symbolicPostForTxn](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Transformer.lean)

**直感**

weakened symbolic postcondition の transaction-level interface です。

**何が本質か**

実際に user が symbolic post を見たいときの入口はこのあたりです。

## 6. `FirstOrder.lean`

### `Formula`
[Formula](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/FirstOrder.lean)

**直感**

first-order formula の軽量 deep embedding です。

**何が本質か**

まだ solver に流す完成版ではありませんが、Sec. 5.2 に向かう足場です。

### `MembershipFormula`
[MembershipFormula](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/FirstOrder.lean)

**直感**

「候補 row が symbolic effect に属するか」を表す式言語です。

**どう読むか**

`outVar` のような candidate row 変数を 1 本固定して、その row が insert / delete / update / select / foreach の結果に入る条件を深い式として書きます。

**何が本質か**

この repo の `S -> FOL` は、まず set equality 全体ではなく membership から始まっています。

### `inferMembershipFull`
[inferMembershipFull](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/FirstOrder.lean)

**直感**

transaction body から membership formula を生成する compiler です。

**どう読むか**

visible DB に依存します。`select` や `foreach` がその場で visible DB を参照するためです。

**何が本質か**

`inferSetEffect` のさらに先で、「symbolic set を formula に落とす」役割を持っています。

### `inferMembershipFull_sound`
[inferMembershipFull_sound](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/FirstOrder.lean)

**直感**

生成した membership formula は、実際の concrete effect に対して sound。

**証明方針**

`inferEffect` と `inferMembershipFull` の構文再帰を合わせる証明です。  
本質的には `Transformer` 側の soundness の first-order 版です。

## 7. `Server.lean`

ここは論文本体ではなく、実アプリ verification 用の上位層です。

### `HandlerRefines`
[HandlerRefines](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Server.lean)

**直感**

API handler 用の refinement judgment の別名です。

**どう読むか**

実体は `GlobalValid` です。  
つまり新しい logic を増やしたのではなく、server 文脈で読みやすい名前を付けただけです。

### `ParallelValid`
[ParallelValid](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Server.lean)

**直感**

server-level の正しさです。

**どう読むか**

定義は 2 つの成分を持ちます。

- quiescent state で invariant/post が成り立つ
- 各 commit step が `specs txnId` を満たす

**何が本質か**

server 層では「終了時の postcondition」だけでなく、「どの commit が何を意味するか」を主役にしています。

### `CommitEvent`, `CommitLog`
[CommitEvent](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Server.lean)  
[CommitLog](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Server.lean)

**直感**

server 実行から抽出した commit trace です。

**どう読むか**

各 event は

- `txnId`
- `before`
- `after`

を持ちます。

**何が本質か**

API サーバー correctness を「終了時の state だけ」でなく、「どの request/txn がどの状態変化を起こしたか」という trace として説明できるようにしています。

### `parallelValid_commitLog`
[parallelValid_commitLog](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Server.lean)

**直感**

`ParallelValid` から commit log を取り出す定理です。

**何が本質か**

これが server correctness story の中核です。  
final state theorem は多くの場合、この定理を経由して出ています。

### `parallelValid_foldl_of_graphSpecs`
[parallelValid_foldl_of_graphSpecs](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Server.lean)

**直感**

もし各 commit spec が `state -> state` 関数の graph なら、最終 state は commit 順の `foldl` 合成になる。

**どう読むか**

```lean
specs txnId = StateSpec.graph (fs txnId)
```

という状況で、

```lean
finalDb = foldl ... fs ... commits
```

を出します。

**何が本質か**

「API サーバーの最終 state は、ある順序で spec を合成したものになる」を言う最初の定理です。

### `parallelValid_requestGraphSpecs_sound`
[parallelValid_requestGraphSpecs_sound](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Server.lean)

**直感**

request family 向けの version です。

**どう読むか**

- `requestOf : TxnId -> Req`
- `fs : Req -> Database -> Database`

があるとき、最終 state は request trace に沿った `fs` の合成になる。

**何が本質か**

実アプリで一番使いたい server theorem はこれです。

### `HandlerFamilySpec`, `VerifiedRequestServerSpec`
[HandlerFamilySpec](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Server.lean)  
[VerifiedRequestServerSpec](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Server.lean)

**直感**

API 全体を object としてまとめるための structure です。

**どう読むか**

- `HandlerFamilySpec`
  request ごとの handler + relational spec
- `VerifiedRequestServerSpec`
  それが `ParallelValid` を満たす verified server object

**何が本質か**

library 利用者が core logic を毎回手で組み立てなくても、server object としてまとめて扱えるようにする層です。

## 8. `Examples.lean`

### `zeroBalanceInsert_valid`
[zeroBalanceInsert_valid](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)

**直感**

最小の end-to-end 例です。

**どう読むか**

- transaction body を書く
- guarantee を書く
- invariant preservation を示す
- `vcg_sound_false` で `GlobalValid` を得る

**何が本質か**

transaction 単体 verification の最小パターンがこれです。

### `zeroBalanceHandler_refines_graph`
[zeroBalanceHandler_refines_graph](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)

**直感**

transaction correctness を handler spec に読み替える例です。

### `zeroBalanceServer_parallelValid`
[zeroBalanceServer_parallelValid](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)

**直感**

単一 handler を `par ... skip` に持ち上げて server-layer の `ParallelValid` にする例です。

### `zeroBalanceServer_request_family_sound`
[zeroBalanceServer_request_family_sound](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)

**直感**

request-level final-state theorem を concrete に使う例です。

### `addInterest_*`
[Examples.lean](/home/ia/ghq/github.com/iasakura/db-app-program-logic/DbAppProgramLogic/Examples.lean)

**直感**

read/write を含む transaction を、symbolic `S` と first-order membership まで追う例です。

**何が本質か**

`zeroBalance` が core/VCG/server の最小例なのに対し、`addInterest` は symbolic layer の最小例です。

## 9. 実際の読み順

### 最小限の core logic 理解

1. `Command`
2. `Semantics.Step`
3. `globalInterleavedStep`
4. `GlobalValid`
5. `GlobalRG`
6. `globalRG_sound`

### VCG 理解

1. `inferEffect`
2. `TransactionVCG`
3. `vcg`
4. `vcg_sound_false`
5. `inferSetEffect`
6. `symbolicVcg`

### server / API 理解

1. `HandlerRefines`
2. `ParallelValid`
3. `CommitLog`
4. `parallelValid_commitLog`
5. `parallelValid_requestGraphSpecs_sound`
6. `VerifiedRequestServerSpec`

## 10. いま未解決のランドマーク

理解のために、未実装部分も書いておきます。

- `GlobalRG.par` はまだない
- 一般の `ParallelValid.par` もまだない
- 現在の server correctness は commit-log / commit-order story を主結果にしている
- `FirstOrder.lean` は solver 連携の完成版ではない

なので、この repo の現状を一言でいうと、

**transaction 単体の logic と VCG はかなり揃っていて、server layer は commit-order refinement を主軸にした実用層がある**

です。
