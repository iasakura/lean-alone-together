# このプロジェクトの歩き方

この文書は、「どこから読めばこの repo を理解できるか」をまとめた案内です。  
先に結論を書くと、全部を最初から順番に読む必要はありません。目的ごとに読むべき入口が違います。

## まず全体像

この repo は大きく 4 層あります。

1. `T` の構文と operational semantics
2. rely-guarantee logic とその soundness
3. symbolic transformer / VCG / first-order membership
4. request / handler / server correctness の上位層

対応するファイルは次の通りです。

- `DbAppProgramLogic/Syntax.lean`
- `DbAppProgramLogic/Semantics.lean`
- `DbAppProgramLogic/Logic.lean`
- `DbAppProgramLogic/SetLanguage.lean`
- `DbAppProgramLogic/Transformer.lean`
- `DbAppProgramLogic/FirstOrder.lean`
- `DbAppProgramLogic/Server.lean`
- `DbAppProgramLogic/Examples.lean`

`DbAppProgramLogic/Basic.lean` は全部まとめて import するための入口ですが、理解のためにはあまり向いていません。

## いちばんおすすめの読み順

### A. まず「この repo は何を証明しているのか」を知りたい

この順で読むのがいちばん速いです。

1. `README.md`
2. `DbAppProgramLogic/Examples.lean`
3. `DbAppProgramLogic/Server.lean`
4. `DbAppProgramLogic/Transformer.lean`
5. `DbAppProgramLogic/Logic.lean`
6. `DbAppProgramLogic/Semantics.lean`
7. `DbAppProgramLogic/Syntax.lean`

意図は、末端の定義から積み上げるのではなく、「最終的に何が使えるのか」から逆向きに辿ることです。

### B. 論文の Sec. 4, Sec. 5 を対応づけながら読みたい

この順が自然です。

1. `DbAppProgramLogic/Syntax.lean`
2. `DbAppProgramLogic/Semantics.lean`
3. `DbAppProgramLogic/Logic.lean`
4. `DbAppProgramLogic/SetLanguage.lean`
5. `DbAppProgramLogic/Transformer.lean`
6. `DbAppProgramLogic/FirstOrder.lean`
7. `DbAppProgramLogic/Examples.lean`

`Server.lean` は論文本体そのものではなく、実アプリ verification のための上位層です。論文本体だけ追うなら後回しで大丈夫です。

### C. API サーバー verification に使いたい

この順が実用的です。

1. `DbAppProgramLogic/Examples.lean`
2. `DbAppProgramLogic/Server.lean`
3. `DbAppProgramLogic/Transformer.lean`
4. 必要に応じて `DbAppProgramLogic/Logic.lean`

この読み方では、`HandlerRefines`, `ParallelValid`, `CommitLog`, request-level spec の流れを先に掴み、そのあと必要なら core logic に降ります。

## ファイルごとの役割

### `Syntax.lean`

論文の言語 `T` の構文です。  
ここでまず見るべきものは `Command` です。

重要な点:

- `txn` は source syntax
- `txnRuntime` は実行時ノード
- `foreachRuntime` も実行時ノード
- `par` は構文としては入っている

つまり、この repo は source syntax だけでなく runtime syntax も明示しています。

### `Semantics.lean`

実行時モデルです。最重要なのは次です。

- `Row`
- `Database`
- `IsolationSpec`
- `Semantics.LocalStep`
- `Semantics.Step`

ここで最初に混乱しやすいのは、`RecordLit` と `Row` が別物なことです。

- `RecordLit` は user-visible なレコード
- `Row` は hidden metadata を持つ実行時行

さらに `txnRuntime txnId isolation localDb snapshot body` の 4 つ目は、**現在の global DB ではなく transaction が保持している snapshot** です。

### `Logic.lean`

Sec. 4 の中心です。最初に見るべき定義は次です。

- `LocalValid`
- `GlobalValid`
- `LocalRG`
- `GlobalRG`
- `localRG_sound`
- `globalRG_sound`

読む順は、

1. `stableAssertion`, `stableBiAssertion`, `relyMod`
2. `localInterleavedStep`, `globalInterleavedStep`
3. `LocalValid`, `GlobalValid`
4. `LocalRG`, `GlobalRG`
5. `localRG_sound`, `globalRG_sound`

です。

このファイルでは、actual step と rely step を混ぜた interleaving を先に定義し、その上で judgment の意味論を定義してから soundness を証明しています。

### `SetLanguage.lean`

Fig. 7 に対応する集合言語 `S` です。  
最初に見るべきものは:

- `SetExpr`
- `denote`
- `abstractGlobal`
- `weakenToInvariant`

注意点として、現状の `S` は「完全 deep embedding」ではありません。式や論理部分の一部は shallow に持っています。

### `Transformer.lean`

Sec. 5 の中心です。ここには 2 種類の transformer があります。

- `inferEffect`
  - concrete な semantic effect
- `inferSetEffect`
  - `SetExpr` を返す symbolic effect

最初に見る順は:

1. `instantiateExpr`, `instantiateCommand`
2. `inferEffect`
3. `TransactionVCG`, `vcg`
4. `inferSetEffect`
5. `symbolicVcg`, `symbolicPostForTxn`

この repo の VCG は、「いきなり Hoare logic を計算する」のではなく、まず effect を推論し、それが semantics と一致することを証明する方針で作られています。

### `FirstOrder.lean`

`S` / transaction body を first-order membership formula に落とす層です。  
これは Sec. 5.2 に向かう途中段階です。

見るべきものは:

- `Formula`
- `MembershipFormula`
- `inferMembershipFull`

このファイルは「solver までつながる完成版」ではなく、symbolic postcondition を first-order 風の式に落とす橋です。

### `Server.lean`

論文本体の core ではなく、実アプリ verification 用の上位層です。  
最初に見るべきものは:

- `HandlerRefines`
- `ParallelValid`
- `CommitEvent`, `CommitLog`
- `HandlerFamilySpec`
- `VerifiedRequestServerSpec`

大事な点は、このファイルの主結果が「標準的な RG の一般 `par` 規則」ではなく、

- commit ごとの spec
- commit log
- commit order での spec 合成

だということです。

つまり、現状の server layer は「branchwise parallel rule」より「server-level trace theorem」を主眼にしています。

### `Examples.lean`

最初に読むべき concrete 例です。  
おすすめの順は:

1. `zeroBalanceInsert_valid`
2. `zeroBalanceHandler_refines_graph`
3. `zeroBalanceServer_parallelValid`
4. `zeroBalanceVerifiedServerSpec`
5. `addInterest*`

`zeroBalance` 系は最小例、`addInterest` 系は read/write を含む少し論文寄りの例です。

## 理解のために最初に区別すべき概念

### 1. `RecordLit` と `Row`

- `RecordLit` はユーザーが書くレコード
- `Row` は runtime row

`Row` には hidden metadata が入っています。

### 2. `localDb`, `snapshot`, `globalDb`

この 3 つを混同すると読みづらくなります。

- `localDb`
  - まだ commit していない transaction-local な delta
- `snapshot`
  - transaction runtime node が保持している visible database
- `globalDb`
  - top-level machine state にある現在の global database

### 3. actual step と rely step

`Logic.lean` では interleaved semantics を使っています。

- actual step: 実際の machine step
- rely step: 環境による interference

`refreshVisible` は global DB を変える関数ではなく、**変化した global DB を transaction runtime node 内の snapshot に反映する bookkeeping** です。

### 4. semantic effect と symbolic effect

`Transformer.lean` には 2 種類の effect があります。

- `inferEffect`
  - concrete result を返す
- `inferSetEffect`
  - symbolic `SetExpr` を返す

前者が proof engineering の土台で、後者が論文 Fig. 7/8 に寄せた層です。

## まず追うべき定理

「大きい theorem だけを先に見たい」なら次です。

1. `Logic.localRG_sound`
2. `Logic.globalRG_sound`
3. `Transformer.vcg_sound`
4. `Transformer.vcg_sound_false`
5. `Server.parallelValid_foldl_of_graphSpecs`
6. `Server.parallelValid_requestGraphSpecs_sound`

この順で見ると、core logic から server-level correctness までどう積み上がっているかが分かります。

## 逆に、最初は後回しでよいところ

- `FirstOrder.lean` の細かい encoding 補題
- `SetLanguage.lean` の simp 補題
- `Examples.lean` の後半の exact/hidden txn-id 付き server object

これらは使うと便利ですが、最初のキャッチアップには不要です。

## この repo を「使う」なら何を見るか

transaction 単体を検証したいなら:

1. `Examples.lean` の `zeroBalanceInsert_valid`
2. `Transformer.vcg`
3. `Transformer.vcg_sound_false`

handler family / API サーバーまで行きたいなら:

1. `Server.HandlerRefines`
2. `Server.HandlerFamilySpec`
3. `Server.VerifiedRequestServerSpec`
4. `Server.parallelValid_requestGraphSpecs_sound`

## 現状の限界

理解のために、未実装部分も先に知っておくとよいです。

- `GlobalRG.par` はまだない
- 一般の `ParallelValid.par` もまだない
- server layer は commit-order / request-trace theorem を主結果にしている
- `S -> FOL` の完全 deep encoding と solver 連携は未完成

なので、「論文の RG 並列規則をそのまま mechanize 済み」とはまだ言えません。  
一方で、「transaction 単体の soundness」「VCG」「request/server correctness の commit-order story」はかなり使える状態です。

## 迷ったら

迷ったら次の順で開くと外しません。

1. `DbAppProgramLogic/Examples.lean`
2. `DbAppProgramLogic/Server.lean`
3. `DbAppProgramLogic/Transformer.lean`
4. `DbAppProgramLogic/Logic.lean`

この順は、「何ができるか」から「なぜそれが正しいか」へ降りる読み方です。
