# POPL'18 弱分離プログラム論理の Lean 形式化

このリポジトリは、`popl18.pdf` の中核にあるプログラム論理を Lean 4 で形式化したものです。対象は主に次の 5 層です。

- コア取引言語 `T`
- small-step operational semantics
- Sec. 4 の rely-guarantee logic
- Sec. 5 の state-transformer / 集合言語 `S` ベースの検証
- 実アプリ向けの request/handler/server correctness 層

現状の実装はすでに有用ですが、論文の全内容をそのまま end-to-end で mechanize したものではありません。Fig. 7 に対応する集合言語 `S` と weakening の層はすでに入り、Sec. 5.2 に向けた first-order membership encoding も `FirstOrder.lean` として部分的にあります。ただし formula 部分はまだ shallow encoding が中心で、Fig. 10 全体の syntax-directed 変換や SMT 向け自動化は未完成です。

## リポジトリ構成

- `DbAppProgramLogic/Syntax.lean`
  - コア言語 `T` の構文
  - リテラル、式、コマンド
- `DbAppProgramLogic/Semantics.lean`
  - 値と式評価
  - 行・データベースの実行時モデル
  - 分離仕様
  - local / top-level の small-step semantics
- `DbAppProgramLogic/Logic.lean`
  - local/global judgment の意味論
  - local/global rely-guarantee rule
  - soundness theorem
- `DbAppProgramLogic/SetLanguage.lean`
  - Fig. 7 に対応する集合言語 `S` の構文
  - `S` の denotation
  - weakening に使う `abstractGlobal`, `weakenToInvariant`
- `DbAppProgramLogic/Transformer.lean`
  - semantic effect inference (`inferEffect`)
  - symbolic set-language inference (`inferSetEffect`)
  - 簡約版 VCG と symbolic VCG
  - inference と semantics / global validity をつなぐ soundness 補題
- `DbAppProgramLogic/FirstOrder.lean`
  - `S` / transaction body から first-order membership formula を得る層
  - `select`, `foreach` を含む full body encoder とその soundness
- `DbAppProgramLogic/Server.lean`
  - handler-level refinement の別名 `HandlerRefines`
  - parallel / server 実行用の `ProgramDone`, `TxnCommitStep`, `ParallelValid`
  - compatibility 条件 `ProgramAcceptsSpecs`
  - request family / server object を表す `HandlerFamily{Spec}`, `VerifiedRequestServer{Spec}`, `VerifiedTxnIndexedRequestServerSpec`
  - `TxnIndexedRequestSpec` と `RequestSpec.hideTxnIds`
  - commit-order の合成定理と `CommitLog`
- `DbAppProgramLogic/Examples.lean`
  - 現状の基盤を使った小さな検証例

## 論文中の何が Lean のどれに対応するか

論文を読みながらコードを追うなら、図や定理と Lean 定義を対応づけるのがいちばん分かりやすいです。

| 論文側 | Lean 側 | 補足 |
| --- | --- | --- |
| Fig. 5 の `T` の構文 | `Syntax.lean` の `Command` | source form だけでなく `foreachRuntime` や `txnRuntime` も含みます |
| Fig. 5 の式・レコード | `Syntax.lean` の `Expr`, `Literal`, `RecordLit`, `SetLit` と `Semantics.lean` の `Value`, `Expr.eval` | 論文では暗黙な評価を Lean では明示しています |
| Fig. 5 の local small-step | `Semantics.lean` の `Semantics.LocalStep` | `let`, `if`, `seq`, `insert`, `delete`, `select`, `update`, `foreach` を含みます |
| Fig. 5 の top-level small-step | `Semantics.lean` の `Semantics.Step` | `txnStart`, `txnExec`, `txnCommit`, `par` を含みます |
| hidden field `txn`, `del` | `Semantics.lean` の `Row` と `Row.fromInsert` | ユーザ視点のレコードは `RecordLit`、実行時の行はメタデータを持ちます |
| local store `delta`, global store `Delta` | `localDb`, `visibleDb`, `globalDb` | config に明示的に持たせています |
| commit 時の flush | `Semantics.lean` の `Database.flush` | 削除は `del = true` な行を local store に追加し、flush で除去します |
| 分離仕様 | `Semantics.lean` の `IsolationSpec` | `exec` と `commit` に分けています |
| `Iid` | `Semantics.lean` の `Database.uniqueIds` | id の大域的一意性を保つ isolation property に対応します |
| `Iww` | `Semantics.lean` の `Database.writeWriteConflictFree` | write-write conflict を防ぐ commit 側条件です |
| `Iss` | `Semantics.lean` の `IsolationSpec.snapshot` | transaction が snapshot 上で動くことを表す generic な仕様です |
| snapshot isolation 的な組み合わせ | `Semantics.lean` の `Database.snapshotIsolation` | snapshot 実行 + write-write conflict 回避です |
| Fig. 6 の local/global RG judgment | `Logic.lean` の `LocalRG`, `GlobalRG` | 論文の proof rule に対応します |
| RG judgment の意味論 | `Logic.lean` の `LocalValid`, `GlobalValid`, `txnGuaranteed` | rule が何を意味するかを与える側です |
| local/global interleaving | `Logic.lean` の `localInterleavedStep`, `globalInterleavedStep` | 実際の machine step と interference step を合成しています |
| Sec. 4 の stability | `Logic.lean` の `stableAssertion`, `stableBiAssertion`, `stableIsolation`, `relyMod` | 論文中の stability family に対応します |
| Theorem 4.3 | `Logic.lean` の `localRG_sound`, `globalRG_sound` | RG rule が semantic validity を含意することを示します |
| Fig. 7 の集合言語 `S` | `SetLanguage.lean` の `SetExpr` | ただし `φ`, `ϕ` は深い構文ではなく shallow な predicate として表現しています |
| Fig. 7 の `T·U⟨R, I⟩` に相当する weakening | `SetLanguage.lean` の `abstractGlobal`, `weakenToInvariant` | 論文の existential abstraction を object language に入れた部分です |
| Fig. 8 の semantic transformer | `Transformer.lean` の `inferEffect` | `Database → Option Database` を返す意味論的な推論器です |
| Fig. 8 の symbolic transformer | `Transformer.lean` の `inferSetEffect` | `SetExpr` を返す論文寄りの推論器です |
| Theorem 5.1 相当 | `Transformer.lean` の `inferenceSound*`, `vcg_effect_sound`, `inferSetEffect_sound` | semantic / symbolic の両方について soundness を出しています |
| weakened symbolic VCG | `Transformer.lean` の `symbolicVcg`, `symbolicVcgForTxn`, `symbolicPostForTxn` | symbolic postcondition を transaction に持ち上げる入口です |
| Sec. 5.2 に向けた FOL membership 層 | `FirstOrder.lean` の `MembershipFormula`, `inferMembershipFull*` | full 自動化ではないが、transaction body から row-membership を first-order 風に落とす層です |
| Sec. 5 の transaction-level bridge | `Logic.lean` の `txnGlobalValid_of_localValid` と `Transformer.lean` の `vcg_sound`, `vcg_sound_false` | 推論した effect を `GlobalValid` に戻します |
| 実アプリ向けの handler spec 層 | `Server.lean` の `HandlerRefines`, `HandlerFamily{Spec}`, `TxnIndexedRequestSpec` | 論文の top-level invariant judgment を壊さず、上位層で `P/Q`、request family、内部 txn-id 依存 spec を持つための追加層です |
| parallel / server の quiescent semantics | `Server.lean` の `ProgramDone`, `TxnCommitStep`, `ParallelValid` | 論文本体にはない追加層で、API サーバーのような並列 handler 群を扱うためのものです |
| parallel compatibility | `Server.lean` の `ProgramAcceptsSpecs` | sibling handler の commit spec を rely として受けられることを表す追加条件です |
| commit-order 合成定理 | `Server.lean` の `parallelValid_commitSequence`, `parallelValid_foldl_of_graphSpecs`, `parallelValid_commitLog`, `reachableGraphSpecs_sound`, `parallelValid_requestGraphSpecs_sound` | closed-system 仮定の下で、停止時 state が commit 順の仕様合成になり、各 commit の `txnId / before / after` log も抽出できます |
| request/server object | `Server.lean` の `VerifiedRequestServerSpec`, `VerifiedRequestServer`, `VerifiedTxnIndexedRequestServerSpec`, `VerifiedRequestServerSpec.ofTxnIndexedSpecs` | relation spec と `state -> state` spec の両方を request trace つき server object として包み、必要なら内部 txn-id 付き exact spec と hidden spec を両方持てる追加層です |
| 検証例 | `Examples.lean` の `zeroBalanceInsert_valid`, `zeroBalanceServer_*`, `zeroBalanceVerifiedServer*`, `zeroBalanceVerifiedTxnIndexedServerSpec*`, `addInterest*` | transaction 単体、server-level request trace、event-level trace、txn-id 付き exact spec とそれを隠した request spec の小例があります |

## Lean 側でどうエンコードしたか

### 1. データベースは数学的集合ではなく `List Row`

論文ではデータベースを集合として扱いますが、Lean 側では現在:

- ユーザ可視のレコードを `RecordLit`
- hidden field 付きの実行時行を `Row`
- データベースを `Database := List Row`

として表現しています。

このエンコーディングを選んだ理由は次の通りです。

- `flush` のような操作を具体的に書きやすい
- `append` や prefix を使った補題が扱いやすい
- finite set の extensional equality を全面に出さずに proof engineering を進められる

その代わり、現在の形式化では:

- 等しさは集合の外延的等しさではなく list equality
- 集合的には同じでも並び順が違うと別物
- 特に `foreach` の soundness に順序依存が出る

という性質があります。

### 2. hidden field は `Row` に明示的に持たせている

論文では `txn` と `del` は user-level record の外にある hidden metadata です。Lean では:

- `Row.visible`
- `Row.txn`
- `Row.del`

の 3 つを持つ構造体として明示化しています。

これにより:

- `INSERT` は `Row.fromInsert` で local store に新しい行を加える
- `DELETE` は `del = true` な行を local store に積む
- `UPDATE` は更新後の visible record を持つ行を積む

という operational な記述になっています。

### 3. local state と global state を明示的に分けている

論文の machine state は Lean では:

- `LocalConfig`
  - `cmd`
  - `localDb`
  - `visibleDb`
- `GlobalConfig`
  - `program`
  - `globalDb`

として分離しています。

これにより:

- transaction-local な意味論
- top-level interleaving
- local validity と global validity

を別々に書けます。これは論文の local judgment / global judgment の分離と対応しています。

### 4. 実計算の step と interference を分けている

Lean では:

- 実際の machine step
  - `Semantics.LocalStep`
  - `Semantics.Step`
- rely による interference step
  - `Logic.localInterleavedStep`
  - `Logic.globalInterleavedStep`

を分けています。

rely relation 自体は:

- `Rely := Database -> Database -> Prop`
- `LocalRely := Database -> Database -> Database -> Prop`

で表現し、global rely と isolation guard を合わせたものが `relyMod` です。

また、global rely step のときには runtime transaction node が持っている visible snapshot も更新する必要があるので、そのために:

- `refreshVisible`
- `respectsRely`

を導入しています。ここは論文より Lean の方が operational に細かく書かれている部分です。

### 5. semantic effect と explicit `S` の 2 層を持っている

ここが論文との最大の差分です。

論文では:

- Fig. 7 で集合言語 `S` を定義する
- Fig. 8 で `T` の各コマンドから `S` の式を推論する
- Sec. 5.2 で `S` を first-order logic に落とす

という流れです。

Lean 側では現在、これを 2 段に分けています。

- `inferEffect : Database -> Option Database`
  - 実際の local write-set を直接計算する semantic な推論器
- `inferSetEffect : Database -> Option SetExpr`
  - 同じ transaction body から `S` の式を返す symbolic な推論器

この 2 つは独立ではなく、`inferSetEffect_sound` で

- symbolic `S` の denotation
- semantic effect の concrete result

が一致することを示しています。

さらに weakening についても、

- `abstractGlobal`
- `weakenToInvariant`
- `symbolicVcg`
- `symbolicVcgForTxn`
- `symbolicPostForTxn`

が入り、`inferSetEffect_weaken_sound` や `symbolicVcg*_sound` で soundness を出しています。

ただし、論文の Fig. 7 / Fig. 10 を完全に mechanize したわけではありません。特に、

- `φ`, `ϕ` は shallow encoding
- `S` から first-order logic への変換は未実装
- SMT 連携も未実装

です。なので現状は「semantic effect 先行で進めつつ、Fig. 7/8 に対応する symbolic 層もかなり入った」という段階です。

### 6. `foreach` は現在 deterministic

論文の `FOREACH` は本質的には集合的で、順序に依存しないものとして読みたい構造です。しかし今の Lean では `foreachRuntime` を deterministic な順序で回しています。

理由は単純で:

- `Database = List Row`
- postcondition が list equality

のままだと、真に nondeterministic な iteration order を入れた瞬間に soundness が難しくなるからです。

したがって現状の `foreach` は:

- 論文の意図に近いが、より operational で順序固定

という位置づけです。

## すでに証明済みのもの

### Operational semantics 側

- 式評価
- `select` / `delete` / `update` の record collection
- local / top-level small-step semantics
- `uniqueIds`, `snapshotIsolation` などの helper isolation specification

### Logic 側

- local/global judgment の semantic validity
- local/global RG rule
- `localRG_sound`
- `globalRG_sound`

つまり、Fig. 6 の rule system が意味論的に sound であるところまでは入っています。

### Inference / VCG 側

- transaction body に対する effect inference:
  - `inferEffect`
- transaction body に対する symbolic set-language inference:
  - `inferSetEffect`
- 各構文ケースの soundness:
  - `inferenceSoundEnv_*`
- symbolic inference の soundness:
  - `inferSetEffect_sound`
  - `inferSetEffect_weaken_sound`
- whole-body inference soundness:
  - `inferenceSound_all`
  - `vcg_effect_sound`
- local validity から global validity への bridge:
  - `txnGlobalValid_of_localValid`
- 簡約版 VCG soundness:
  - `vcg_sound`
- no-rely special case の end-to-end theorem:
  - `vcg_sound_false`
- weakened symbolic VCG:
  - `symbolicVcg`
  - `symbolicVcgForTxn`
  - `symbolicPostForTxn`
  - `symbolicVcg*_sound`
  - `symbolicVcg*_overapprox_*`

### Example

`Examples.zeroBalanceInsert_valid` は:

- 0 残高の bank account を insert する transaction が
- 「全口座残高が非負」という invariant を保つ

ことを示しています。

これはかなり小さい例ですが、いまの infrastructure が実際に end-to-end で使えることの確認にはなっています。

加えて `Examples.addInterest*` では:

- `SELECT`
- `FOREACH`
- `UPDATE`
- snapshot isolation transaction wrapper
- weakened symbolic VCG

を通る read/write 例を入れています。論文 Fig. 9 の `add_interest` そのものではありませんが、同系統の「読んだ値に基づいて更新する」例です。

また `Examples.zeroBalanceServer_*` では:

- 単一 transaction の `HandlerRefines`
- それを `txn || skip` に持ち上げた `ParallelValid`
- commit-order の `foldl` 合成定理
- `txnId / before / after` を持つ `CommitLog`

までを end-to-end で確認しています。これはまだ一般の `p || q` 規則ではありませんが、server-level の層が Lean 上で実際に使えることの最小例です。

さらに `Examples.zeroBalanceVerifiedTxnIndexedServerSpec*` では:

- transaction ごとの exact spec `Req -> TxnId -> StateSpec`
- それを `RequestSpec.hideTxnIds` で外部 request spec に落とす層
- `VerifiedTxnIndexedRequestServerSpec` と `hideTxnIds`
- `VerifiedRequestServerSpec.ofTxnIndexedSpecs` で hidden server object に包む流れ

を確認しています。実アプリで内部 transaction id を spec に使いたいが、外側の API 仕様では隠したい、という用途に向けた最小例です。

## 論文どおりに実際のアプリを検証するために足りないもの

ここが一番重要です。いまのリポジトリは「かなり進んだ基盤」ではありますが、論文のように本格的な weak isolation app verification を行うにはまだ足りないものがあります。

### 1. Fig. 7 の `S` は部分的に入ったが、まだ shallow

現在は `SetLanguage.SetExpr` があり、少なくとも次は入っています。

- set variable
- `localDb`, `globalDb`
- comprehension
- existential set binder
- bind
- conditional
- union

ただし `phi`, `ϕ` は deep embedding ではなく、Lean の predicate をそのまま持つ shallow encoding です。したがって:

- 純粋な構文木としての `S`
- syntax-directed な `S -> FOL` 変換
- formula 変形のメタ理論

はまだ未実装です。

### 2. weakening は入ったが、論文の inference algorithm 全体ではない

論文では、unstable な transformer を existential abstraction によって stable にする weakening operator がかなり重要です。特に Fig. 9 の `add_interest` のような例では、これが効いてはじめて proof が通る構図になっています。

Lean では現在、これに対応する object-language の演算子として:

- `abstractGlobal`
- `weakenToInvariant`

が入っています。さらに `symbolicVcg` は `inferSetEffect` の結果をこの weakening で包んだ symbolic postcondition を返します。

ただし、まだ次はありません。

- unstable transformer から weakest な weakened transformer を組み立てる完全な計算規則
- その FOL 変換まで含めた end-to-end な mechanization

### 3. Fig. 10 の `S` から first-order logic への変換は部分的

`FirstOrder.lean` により、少なくとも次はすでにあります。

- row-membership を表す `MembershipFormula`
- `insert/delete/update/select/foreach` を含む body からの membership encoder
- `inferMembershipFull_sound` などの soundness

まだ入っていないもの:

- `SetExpr` 全体に対する syntax-directed な FOL 変換
- uninterpreted predicate の導入
- prenex 形の整理
- その変換の semantics-preserving proof
- SMT / solver 連携

この部分がないので、今の VCG は:

- proof-oriented な Lean formalization

ではあるものの、

- 論文が目指す自動化された verification pipeline

にはまだ到達していません。

### 4. automatic obligation discharge がまだない

論文では、推論された transformer を使って:

- stability check
- guarantee validity
- invariant preservation
- isolation selection / isolation inference

の多くを formula implication に落とします。

今のコードでは、それらの obligation 自体は表現されていますが:

- solver-backed に discharge はしていない
- weakest isolation inference もしていない

という状態です。

### 5. `vcg_sound` と symbolic VCG はあるが、自動化パイプラインは未完成

現在は:

- semantic VCG の soundness (`vcg_sound`, `vcg_sound_false`)
- symbolic VCG の soundness (`symbolicVcg*_sound`)
- visible DB に対する symbolic postcondition (`symbolicPostForTxn`)

まではあります。

ただし論文の最終的な使い方として欲しいのは:

- `vcg` を回す
- `S` / FOL obligation を solver に流す
- そのまま transaction 全体の正しさが出る

という形です。

今は soundness 定理自体はかなり揃っていますが、obligation discharge はまだ Lean 内で手作業です。

### 6. モデルはまだ single-table core model

論文自体も core language ですが、実際の app verification に寄せるには今の repository にはまだ次が足りません。

- 複数テーブル
- typed schema
- table ごとの invariant
- より豊かな query surface
- 実際のアプリに近い data model
- transaction family 単位の proof library

### 7. 実アプリ寄り examples はまだ少ない

すでに入っているもの:

- insert-only の invariant preservation 例
- `select + foreach + update` の `add_interest` 系 read/write 例

まだ入っていない代表例:

- 論文 Fig. 9 をより忠実に写した family
- endpoint 群をまとめた transaction family の証明
- TPC-C 系の transaction family

これらが重要なのは、まさにそこで:

- weakening が必要になり
- stability が非自明になり
- `S -> FOL` 変換と solver が欲しくなる

からです。

### 8. server-level parallel rule はまだ部分的

`Server.lean` により、今は次が言えます。

- handler 単体の `HandlerRefines`
- quiescent な parallel/server 実行の `ParallelValid`
- closed-system 仮定の下での commit-order 合成

ただし、まだ一般の

- `HandlerRefines h1`
- `HandlerRefines h2`
- よって `ParallelValid (h1 || h2)`

という composition rule そのものは入っていません。現在あるのは:

- 単一 transaction から `ParallelValid` への bridge
- `.par p skip` の base case
- `CombinedSpecs` と `ParallelCompatible` による RG 風の spec/rely interface
- `ProgramAcceptsSpecs` による compatibility の切り出し
- non-commit step に限った左右 projection 補題
- commit-order theorem

です。一般の並列合成を証明するには、兄弟 transaction の commit を相手側の rely として再解釈する projection / simulation 補題を追加する必要があります。現在はそのうち、commit が起きない step については `globalInterleavedStep_project_left_noncommit` / `..._right_noncommit` で切り出せており、残っている本体は sibling commit case です。

## いまの README の立場

このリポジトリは、現時点では次のように読むのが正確です。

- POPL'18 の core operational semantics と RG logic の Lean 形式化
- soundness 付きの semantic VCG
- Fig. 7/8 にかなり寄せた symbolic set-language / weakened symbolic VCG
- 実アプリ向けの handler / server correctness を載せるための server-level 基盤
- 将来的に Fig. 10 と solver 連携を mechanize するための基盤

逆に、まだ次のものとして読むべきではありません。

- Fig. 7 の `S` を deep embedding で完全に mechanize した実装
- Sec. 5.2 まで含めた fully automated verifier
- 論文中の realistic app verification をそのまま回せる完成版

## コードを読む順番

Lean の実装順に読むなら:

1. `Syntax.lean`
2. `Semantics.lean`
3. `Logic.lean`
4. `SetLanguage.lean`
5. `Transformer.lean`
6. `Server.lean`
7. `Examples.lean`

論文順に読むなら:

1. Fig. 5 と `Syntax.lean`, `Semantics.lean`
2. Fig. 6 と `Logic.lean`
3. Theorem 4.3 と `localRG_sound`, `globalRG_sound`
4. Fig. 7 と `SetLanguage.lean`
5. Fig. 8 と `inferEffect`, `inferSetEffect`
6. Theorem 5.1 と `inferenceSound*`, `inferSetEffect_sound`
7. transaction-level bridge としての `txnGlobalValid_of_localValid`, `vcg_sound`, `symbolicVcg`, `symbolicPostForTxn`
8. 実アプリ向けの追加層として `Server.lean`
