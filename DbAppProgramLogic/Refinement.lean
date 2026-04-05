import DbAppProgramLogic.Transformer
import DbAppProgramLogic.Server

namespace DbAppProgramLogic

/-!
Thin bridges from transaction-local VCG proofs to the server-facing refinement layer.

The core transaction logic still lives in `Logic`/`Transformer`. This file only packages common
"single verified transaction" patterns so examples and downstream applications can move directly
from VCG obligations to handler/server specifications.
-/

namespace Refinement

/-- A no-rely VCG proof immediately gives a server-facing handler refinement judgment. -/
theorem handlerRefines_of_vcg_sound_false
    {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (hDefined :
      Transformer.effectDefinedOn I
        ((Transformer.vcg (fun _ _ => False) I G txnId isolation body).effect))
    (hGuarantee :
      (Transformer.vcg (fun _ _ => False) I G txnId isolation body).guaranteeOk)
    (hPreserve :
      (Transformer.vcg (fun _ _ => False) I G txnId isolation body).preservesInvariant) :
    Server.HandlerRefines I (fun _ _ => False) (.txn txnId isolation body) G I := by
  exact Transformer.vcg_sound_false txnId isolation body hDefined hGuarantee hPreserve

/-- The same VCG proof can be re-exported as a server-level validity judgment with one exact
commit specification attached to the concrete transaction id. -/
theorem txnParallelValid_exact_of_vcg_sound_false
    {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (hDefined :
      Transformer.effectDefinedOn I
        ((Transformer.vcg (fun _ _ => False) I G txnId isolation body).effect))
    (hGuarantee :
      (Transformer.vcg (fun _ _ => False) I G txnId isolation body).guaranteeOk)
    (hPreserve :
      (Transformer.vcg (fun _ _ => False) I G txnId isolation body).preservesInvariant) :
    Server.ParallelValid I (fun _ _ => False) (.txn txnId isolation body)
      (Server.ExactTxnSpec txnId G) I := by
  refine Server.txnParallelValid_of_handlerRefines_at
    (txnId := txnId)
    (isolation := isolation)
    (body := body)
    (spec := G)
    (specs := Server.ExactTxnSpec txnId G)
    ?_
    ?_
  · intro db db' hSpec
    exact ⟨rfl, hSpec⟩
  · exact handlerRefines_of_vcg_sound_false txnId isolation body hDefined hGuarantee hPreserve

/-- In the closed-system case, the exact server validity judgment yields a concrete commit log for
any reachable execution prefix of the single transaction. -/
theorem txnCommitLog_exact_of_vcg_sound_false
    {I : Assertion} {G : Guarantee}
    (txnId : TxnId) (isolation : IsolationSpec Database) (body : Semantics.Program)
    (hDefined :
      Transformer.effectDefinedOn I
        ((Transformer.vcg (fun _ _ => False) I G txnId isolation body).effect))
    (hGuarantee :
      (Transformer.vcg (fun _ _ => False) I G txnId isolation body).guaranteeOk)
    (hPreserve :
      (Transformer.vcg (fun _ _ => False) I G txnId isolation body).preservesInvariant)
    {db : Database} (hDb : I db)
    {finalCfg : GlobalConfig}
    (hRun :
      Logic.GlobalMultiStep (fun _ _ => False)
        ⟨(.txn txnId isolation body), db⟩ finalCfg) :
    ∃ events,
      Server.CommitLog (Server.ExactTxnSpec txnId G) db events finalCfg.globalDb := by
  exact Server.parallelValid_commitLog_of_silentRely
    (txnParallelValid_exact_of_vcg_sound_false txnId isolation body
      hDefined hGuarantee hPreserve)
    (fun db db' hFalse => False.elim hFalse)
    hDb
    hRun

end Refinement

end DbAppProgramLogic
