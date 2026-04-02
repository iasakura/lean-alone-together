# POPL'18 弱分離プログラム論理の Lean 形式化

このリポジトリは、`popl18.pdf` の中核にあるプログラム論理を Lean 4 で形式化したものです。対象は主に次の 4 層です。

- コア取引言語 `T`
- small-step operational semantics
- Sec. 4 の rely-guarantee logic
- Sec. 5 の state-transformer ベースの検証

現状の実装はすでに有用ですが、論文の全内容をそのまま end-to-end で mechanize したものではありません。特に、現在の VCG は Fig. 7 の集合言語 `S` の構文木を直接作るのではなく、意味論的な effect 関数として実装されています。また、Sec. 5.2 の SMT 向け変換もまだ入っていません。

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
- `DbAppProgramLogic/Transformer.lean`
  - state-transformer inference
  - 簡約版 VCG
  - inference と semantics / global validity をつなぐ soundness 補題
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
| Fig. 8 の state transformer inference | `Transformer.lean` の `inferEffect` | ただし現在は `S` の構文ではなく effect 関数を直接返します |
| Theorem 5.1 | `Transformer.lean` の `inferenceSound*`, `vcg_effect_sound` | 実際の証明本体は `inferenceSoundEnv_*` 群です |
| Sec. 5 の transaction-level bridge | `Logic.lean` の `txnGlobalValid_of_localValid` と `Transformer.lean` の `vcg_sound`, `vcg_sound_false` | 推論した effect を `GlobalValid` に戻します |
| 検証例 | `Examples.lean` の `zeroBalanceInsert_valid` | 現状の VCG を end-to-end で使う最小例です |

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

### 5. 今の VCG は `S` の構文木ではなく意味論的 effect を持つ

ここが論文との最大の差分です。

論文では:

- Fig. 7 で集合言語 `S` を定義する
- Fig. 8 で `T` の各コマンドから `S` の式を推論する
- Sec. 5.2 で `S` を first-order logic に落とす

という流れです。

しかし現在の Lean では:

- `TxnEffect := Database -> Option Database`
- `inferEffect` がこの effect を直接返す
- `TransactionVCG.effect` にその関数を入れる

という構成になっています。

つまり今の実装は:

- 「`S` を構文として作る」

よりも

- 「effect をそのまま意味論的に計算する」

に近いです。

この方針にしたことで soundness proof 自体はかなり進めやすくなりましたが、Fig. 7 と Fig. 10 の mechanization としてはまだ不完全です。

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
- 各構文ケースの soundness:
  - `inferenceSoundEnv_*`
- whole-body inference soundness:
  - `inferenceSound_all`
  - `vcg_effect_sound`
- local validity から global validity への bridge:
  - `txnGlobalValid_of_localValid`
- 簡約版 VCG soundness:
  - `vcg_sound`
- no-rely special case の end-to-end theorem:
  - `vcg_sound_false`

### Example

`Examples.zeroBalanceInsert_valid` は:

- 0 残高の bank account を insert する transaction が
- 「全口座残高が非負」という invariant を保つ

ことを示しています。

これはかなり小さい例ですが、いまの infrastructure が実際に end-to-end で使えることの確認にはなっています。

## 論文どおりに実際のアプリを検証するために足りないもの

ここが一番重要です。いまのリポジトリは「かなり進んだ基盤」ではありますが、論文のように本格的な weak isolation app verification を行うにはまだ足りないものがあります。

### 1. Fig. 7 の集合言語 `S` の syntax AST がまだない

現状では、Lean に次のような datatype がまだありません。

- 変数 `x`, `delta`, `Delta`
- comprehension `{x | phi}`
- `exists(Delta, phi, s)`
- bind `s1 >>= fun x => s2`
- conditional
- union

これがないため、論文の Sec. 5 を「そのまま構文付きで mechanize した」とはまだ言えません。

### 2. weakening operator `T_U<R, I>` が object language に入っていない

論文では、unstable な transformer を existential abstraction によって stable にする weakening operator がかなり重要です。特に Fig. 9 の `add_interest` のような例では、これが効いてはじめて proof が通る構図になっています。

現状の Lean では、それに対応するものは:

- `execStable`
- `commitStable`
- `guaranteeOk`
- `preservesInvariant`

のような proof obligation として表現されています。

つまり今は:

- weakening を「構文として計算する」

のではなく、

- VCG がそのために必要な条件を field として持つ

という形です。

これは soundness を示すには十分ですが、論文の inference algorithm をそのまま mechanize した形ではありません。

### 3. Fig. 10 の `S` から first-order logic への変換がない

まだ入っていないもの:

- `S` の式を FOL predicate に落とす変換
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

### 5. `vcg_sound` はまだ最終形ではない

`vcg_sound` は現在、transaction body に対する適切な `LocalValid` 仮定を受け取る形になっています。

これは内部 bridge theorem としては自然ですが、論文の最終的な使い方として欲しいのは:

- `vcg` を回す
- field obligation を解く
- そのまま transaction 全体の正しさが出る

という形です。

現状は:

- `vcg_sound_false` が no-rely case ではかなりそれに近い
- しかし一般の rely ではまだ helper theorem 止まり

です。

### 6. モデルはまだ single-table core model

論文自体も core language ですが、実際の app verification に寄せるには今の repository にはまだ次が足りません。

- 複数テーブル
- typed schema
- table ごとの invariant
- より豊かな query surface
- 実際のアプリに近い data model
- transaction family 単位の proof library

### 7. 論文の実アプリ寄り examples がまだない

現状まだ Lean で入っていない代表例:

- Fig. 9 の `add_interest`
- その後の application-shaped な例
- TPC-C 系の transaction family

これらが重要なのは、まさにそこで:

- weakening が必要になり
- stability が非自明になり
- semantic effect 直書きではなく `S` の構文が欲しくなる

からです。

## いまの README の立場

このリポジトリは、現時点では次のように読むのが正確です。

- POPL'18 の core operational semantics と RG logic の Lean 形式化
- soundness 付きの簡約版 state-transformer / VCG
- 将来的に Fig. 7, Fig. 8, Fig. 10 をより忠実に mechanize するための基盤

逆に、まだ次のものとして読むべきではありません。

- Fig. 7 の `S` を完全に mechanize した実装
- Sec. 5.2 まで含めた fully automated verifier
- 論文中の realistic app verification をそのまま回せる完成版

## コードを読む順番

Lean の実装順に読むなら:

1. `Syntax.lean`
2. `Semantics.lean`
3. `Logic.lean`
4. `Transformer.lean`
5. `Examples.lean`

論文順に読むなら:

1. Fig. 5 と `Syntax.lean`, `Semantics.lean`
2. Fig. 6 と `Logic.lean`
3. Theorem 4.3 と `localRG_sound`, `globalRG_sound`
4. Fig. 8 と `inferEffect`
5. Theorem 5.1 と `inferenceSound*`
6. transaction-level bridge としての `txnGlobalValid_of_localValid`, `vcg_sound`, `vcg_sound_false`

