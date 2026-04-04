# このプロジェクトの歩き方

この文書は、「どこから読めば理解できるか」の案内です。  
全部を順番に読む必要はありません。目的ごとにランドマークだけ追う方が速いです。

重要な定義・定理の解説だけを見たい場合は [LANDMARKS.md](LANDMARKS.md) を見てください。

## 全体像

この repo は大きく 4 層です。

1. `T` の構文と実行意味論
2. rely-guarantee logic とその soundness
3. symbolic transformer / VCG / first-order membership
4. 実アプリ向けの handler / server wrapper

対応ファイルは次の通りです。

- `DbAppProgramLogic/Syntax.lean`
- `DbAppProgramLogic/Semantics.lean`
- `DbAppProgramLogic/Logic.lean`
- `DbAppProgramLogic/SetLanguage.lean`
- `DbAppProgramLogic/Transformer.lean`
- `DbAppProgramLogic/FirstOrder.lean`
- `DbAppProgramLogic/Server.lean`
- `DbAppProgramLogic/Examples.lean`

`DbAppProgramLogic/Basic.lean` は全部 import する入口で、理解の入口には向きません。

## いちばんおすすめの読み順

### A. 「この repo は何を証明しているのか」を先に知りたい

1. `DbAppProgramLogic/Examples.lean`
2. `DbAppProgramLogic/Transformer.lean`
3. `DbAppProgramLogic/Logic.lean`
4. `DbAppProgramLogic/Semantics.lean`
5. `DbAppProgramLogic/Syntax.lean`
6. 必要なら `DbAppProgramLogic/Server.lean`

この順だと、まず使い方を見て、その後に意味論へ降りられます。

### B. 論文の Sec. 4, Sec. 5 に沿って読みたい

1. `DbAppProgramLogic/Syntax.lean`
2. `DbAppProgramLogic/Semantics.lean`
3. `DbAppProgramLogic/Logic.lean`
4. `DbAppProgramLogic/SetLanguage.lean`
5. `DbAppProgramLogic/Transformer.lean`
6. `DbAppProgramLogic/FirstOrder.lean`
7. `DbAppProgramLogic/Examples.lean`

`Server.lean` は論文本体の外側にある実アプリ向け wrapper なので後回しでよいです。

### C. 実アプリ verification に使いたい

1. `DbAppProgramLogic/Examples.lean`
2. `DbAppProgramLogic/Server.lean`
3. `DbAppProgramLogic/Transformer.lean`
4. 必要に応じて `DbAppProgramLogic/Logic.lean`

この読み方では、まず `HandlerRefines` と `ParallelValid` を見て、必要になったら core logic に降ります。

## ファイルごとの役割

### `Syntax.lean`

論文の言語 `T` の構文です。最初に見るべきものは `Command` です。

特に重要なのは:

- `txn`
- `txnRuntime`
- `foreach`
- `foreachRuntime`
- `par`

この repo は source syntax だけでなく runtime syntax も `Command` に入れています。

### `Semantics.lean`

実行時モデルです。最初に見るべきものは:

- `Row`
- `IsolationSpec`
- `Database.flush`
- `Semantics.LocalStep`
- `Semantics.Step`

まず区別すべきなのは:

- `RecordLit`
  ユーザが書くレコード
- `Row`
  hidden metadata を持つ runtime row

それから `txnRuntime txnId isolation localDb snapshot body` の 4 つ目は transaction が保持している `snapshot` です。

### `Logic.lean`

Sec. 4 の中心です。最初に見るべきものは:

- `stableAssertion`
- `stableBiAssertion`
- `stableIsolation`
- `relyMod`
- `localInterleavedStep`
- `globalInterleavedStep`
- `LocalValid`
- `GlobalValid`
- `LocalRG`
- `GlobalRG`
- `localRG_sound`
- `globalRG_sound`

この file の読み筋は:

1. rely/stability の定義
2. interleaved semantics
3. judgment の意味論
4. inductive proof rules
5. soundness theorems

です。

### `SetLanguage.lean`

Fig. 7 に対応する集合言語 `S` です。最初に見るべきものは:

- `SetExpr`
- `denote`
- `abstractGlobal`
- `weakenToInvariant`

いまの `S` は完全 deep embedding ではなく、一部に shallow predicate を含みます。

### `Transformer.lean`

Sec. 5 の中心です。最初に見るべきものは:

- `inferEffect`
- `TransactionVCG`, `vcg`
- `inferSetEffect`
- `symbolicVcg`
- `symbolicPostForTxn`

この repo の VCG は、まず effect を推論し、それが semantics と一致することを証明してから `GlobalValid` に上げる方針です。

### `FirstOrder.lean`

`S` / transaction body を first-order membership formula に落とす層です。

最初に見るべきものは:

- `Formula`
- `MembershipFormula`
- `inferMembershipFull`

solver までつながる完成版ではなく、symbolic postcondition を first-order 風に読む橋です。

### `Server.lean`

論文本体の外側にある、実アプリ verification 用の薄い wrapper です。

最初に見るべきものは:

- `StateSpec`
- `HandlerRefines`
- `ProgramDone`
- `TxnCommitStep`
- `ParallelValid`
- `txnParallelValid_of_handlerRefines`

いまの server 層は、まず単一 transaction を server-style spec に持ち上げるところまでを正しく保っています。一般の `par` proof rule はここにはまだ入っていません。

### `Examples.lean`

最初に読むべき concrete 例です。おすすめ順は:

1. `zeroBalanceInsert_valid`
2. `zeroBalanceTxn_parallelValid`
3. `zeroBalance_symbolicVcg_contains_row`
4. `addInterest_symbolicVcg_contains_updatedRow`
5. `addInterest_inferMembershipFull_contains_updatedRow`

`zeroBalance` は最小例、`addInterest` は read/write を含む例です。

## 最初に区別すべき概念

### 1. `localDb`, `snapshot`, `globalDb`

- `localDb`
  未コミットの transaction-local delta
- `snapshot`
  runtime transaction node が保持している DB view
- `globalDb`
  top-level machine state にある現在の global DB

### 2. actual step と rely step

`Logic.lean` の interleaving では:

- actual step
  `Semantics.Step`
- rely step
  program はそのままで outer DB だけが `R` に沿って変わる

です。

### 3. semantic effect と symbolic effect

`Transformer.lean` には 2 種類の effect があります。

- `inferEffect`
  concrete result を返す
- `inferSetEffect`
  symbolic `SetExpr` を返す

前者が proof engineering の土台、後者が Fig. 7/8 に寄せた層です。

## まず追うべき定理

大きい theorem だけ先に見たいなら次です。

1. `Logic.localRG_sound`
2. `Logic.globalRG_sound`
3. `Logic.txnGlobalValid_of_localValid`
4. `Transformer.vcg_sound`
5. `Transformer.vcg_sound_false`
6. `Server.txnParallelValid_of_handlerRefines`

## 迷ったときの最短ルート

「コードは全部読めないが、何が正しいと証明されているかだけ掴みたい」なら、

1. `Examples.zeroBalanceInsert_valid`
2. `Transformer.vcg_sound_false`
3. `Logic.GlobalValid`
4. `Logic.globalRG_sound`
5. `Semantics.Step`

の順に辿るのが一番速いです。
