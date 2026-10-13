import Lean
import RequestProject.EFMW.ActionsAndFluids
import RequestProject.EFMW.CognitiveFields
import RequestProject.EFMW.Coherence
import RequestProject.EFMW.Cosmology
import RequestProject.EFMW.Dynamics
import RequestProject.EFMW.GoldenScaling
import RequestProject.EFMW.Information
import RequestProject.EFMW.PhysicalTest
import RequestProject.EFMW.QuantumSector
import RequestProject.EFMW.ScalarField
import RequestProject.EFMW.Synthesis
import RequestProject.EFMW.Systems
import RequestProject.EFMW
import RequestProject.Main

/-! Audit every safe declaration defined in the listed project modules. -/

open Lean in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`RequestProject.EFMW.ActionsAndFluids, `RequestProject.EFMW.CognitiveFields, `RequestProject.EFMW.Coherence, `RequestProject.EFMW.Cosmology, `RequestProject.EFMW.Dynamics, `RequestProject.EFMW.GoldenScaling, `RequestProject.EFMW.Information, `RequestProject.EFMW.PhysicalTest, `RequestProject.EFMW.QuantumSector, `RequestProject.EFMW.ScalarField, `RequestProject.EFMW.Synthesis, `RequestProject.EFMW.Systems, `RequestProject.EFMW, `RequestProject.Main]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axiomState : CollectAxioms.State := {}
  let mut count := 0
  let mut theoremCount := 0
  for (name, info) in env.constants.toList do
    let isProject := match env.getModuleIdxFor? name with
      | some idx => modules.contains env.header.moduleNames[idx.toNat]!
      | none => (`AuditProbe).isPrefixOf (privateToUserName name)
    if isProject && !info.isUnsafe then
      count := count + 1
      if info matches .thmInfo _ then
        theoremCount := theoremCount + 1
      let (_, nextState) := ((CollectAxioms.collect name).run env).run axiomState
      axiomState := nextState
      for ax in axiomState.axioms do
        unless allowed.contains ax do
          throwError "Unapproved axiom {ax} used by {name}"
  if count == 0 then
    throwError "Audit matched no project declarations"
  logInfo m!"Axiom audit passed: {count} safe declarations, {theoremCount} theorem declarations (including generated lemmas)."
