import DbAppProgramLogic.Transformer.LogStorageExample.Effects
import DbAppProgramLogic.Transformer.LogStorageExample.TransactionProofs

namespace DbAppProgramLogic

namespace Transformer

namespace LogStorageExample

/-!
# Final theorem skeleton for the log-storage example

User-facing top-down theorem. The remaining work hides in
`TransactionProofs.lean`'s indexed transaction leaves.
-/

/-- Final user-facing theorem.

For any finite prefix of the intended program shape, every completed execution
from `initialDb` leaves the selected result table for `q` equal to a prefix
`0, ..., k - 1` of the generated log stream. -/
theorem selectAllLog_returnsPrefix_final
    (n m q : Nat) {finalCfg : GlobalConfig}
    (hRun :
      Logic.GlobalMultiStep (fun _ _ => False)
        ⟨logStorageProgram n m q, initialDb⟩ finalCfg)
    (hDone : Logic.ProgramDone finalCfg.program) :
    resultPrefixFor finalCfg.globalDb q := by
  have hSpec : logStorageProgramSpec n m q :=
    logStorageProgramSpec_of_indexedTxnSpecs n m q
      (fun i => insertLogIndexedTxnSpec_final i)
      (fun i => archiveLogIndexedTxnSpec_final i)
      (selectAllLogTxnSpec_final q)
  exact logStorageProgramSpec_resultPrefix hSpec initialLogSystemInv_initialDb hRun hDone

theorem logStorageProgramSpec_final (n m q : Nat) :
    logStorageProgramSpec n m q :=
  logStorageProgramSpec_of_indexedTxnSpecs n m q
    (fun i => insertLogIndexedTxnSpec_final i)
    (fun i => archiveLogIndexedTxnSpec_final i)
    (selectAllLogTxnSpec_final q)

end LogStorageExample

end Transformer

end DbAppProgramLogic
