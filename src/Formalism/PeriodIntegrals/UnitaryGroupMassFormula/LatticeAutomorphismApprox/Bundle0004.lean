module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.Bundle0003
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LocSplitChiOf

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LocalIdempotentExistence
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

def smulLin (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : RV I v) :
    (Fin I.n → RV I v) →ₗ[OV I v] (Fin I.n → RV I v) where
  toFun x := c • x
  map_add' x y := smul_add c x y
  map_smul' o x := by
    simp only [RingHom.id_apply]
    rw [PI.FinKW.LocTo.ov_smul_vec, PI.FinKW.LocTo.ov_smul_vec, smul_comm]

theorem idem_kill (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (g : ℕ) (hg : (g : 𝓞 I.F) ∈ v.asIdeal)
    (c : RV I v) (hcc : c * c = c)
    (hc : ∀ x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      ∃ w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), c • x = (g : RV I v) • w) :
    ∀ x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), c • x = 0 := by
  have hfg : ((Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c)).FG :=
    (latLoc_fg I v).map _
  have hle : (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c) ≤
      Ideal.span {(g : OV I v)} • (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨w, hw, hcw⟩ := hc x hx
    have e : (smulLin I v c) x = (g : OV I v) • (smulLin I v c w) := by
      show c • x = (g : OV I v) • (c • w)
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (RV I v), smul_comm, ← hcw, smul_smul, hcc]
    rw [e]
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) (Submodule.mem_map_of_mem hw)
  have hjac : Ideal.span {(g : OV I v)} ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
    exact natCast_mem_max I.F v g hg
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hle hjac
  intro x hx
  have hm : (smulLin I v c) x ∈ (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c) :=
    Submodule.mem_map_of_mem hx
  rw [hbot, Submodule.mem_bot] at hm
  exact hm

theorem kill_zero (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (hn : 0 < I.n) (c : RV I v)
    (h : ∀ x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), c • x = 0) : c = 0 := by
  have key : ∀ x ∈ Submodule.span I.E (I.L : Set (Fin I.n → I.E)),
      c • Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact h _ (Submodule.subset_span ⟨y, hy, rfl⟩)
    | zero => rw [PI.FinKW.ratV_zero', smul_zero]
    | add y z _ _ hy hz => rw [PI.FinKW.ratV_add', smul_add, hy, hz, add_zero]
    | smul a y _ hy =>
      have e : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (a • y) =
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) a) •
            Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) y := by
        funext i
        simp only [Formalism.L2.SG.Sub.ratV, Pi.smul_apply, smul_eq_mul, map_mul]
      rw [e, smul_comm, hy, smul_zero]
  have h0 := key (Pi.single ⟨0, hn⟩ 1) (by rw [I.L_span]; exact Submodule.mem_top)
  have e1 : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (Pi.single ⟨0, hn⟩ (1 : I.E)) =
      Pi.single ⟨0, hn⟩ 1 := by
    funext i
    by_cases hi : i = ⟨0, hn⟩
    · subst hi
      simp [Formalism.L2.SG.Sub.ratV]
    · simp [Formalism.L2.SG.Sub.ratV, hi]
  rw [e1] at h0
  have h1 := congrFun h0 ⟨0, hn⟩
  simpa using h1

theorem local_idempotent_existence : LocIdem := by
  intro I g r k e f Rf hg hn v hv
  have hb : PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) *
      PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) =
      PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) := by
    rw [← map_mul, eps_idem Rf v]
  have hcc : (1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew)) *
      (1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew)) =
      1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) := by
    linear_combination eps_idem Rf v + hb + 2 * eps_orth Rf v
  have hkill := idem_kill I v g hv _ hcc (fun x hx => full_loc Rf v x hx)
  have hz := kill_zero I v (by omega) _ hkill
  linear_combination -hz

end PI.UnitaryGroupMassFormula.ScXuExists
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.SplitLoc
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem locSplitP_dec (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) (hsum : SumOne I v (PI.FinKW.psiV I v Rf.ew)) :
    ∃ p1 : RV I v →+* KV I v, IsAdaptedFirstProjection I v (PI.FinKW.psiV I v Rf.ew) p1 ∧
      ∀ x : RV I v, x = algebraMap (KV I v) (RV I v) (p1 x) * PI.FinKW.psiV I v Rf.ew +
        algebraMap (KV I v) (RV I v) (p1 (PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v x)) *
          PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) := by
  have : CharZero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :=
    charZero_of_injective_algebraMap (algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)).injective
  have h2K : (2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ≠ 0 := two_ne_zero
  obtain ⟨p1, h1, h2, h3, h4⟩ := exists_adapted_first_projection (K := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) I.cm.sig
    (PI.UnitaryGroupMassFormula.AdIndexEq.spl_sig_sig I) (PI.UnitaryGroupMassFormula.AdIndexEq.spl_sig_fix I) I.cm.deg2 h2K
    (PI.FinKW.psiV I v Rf.ew) hsum (eps_orth Rf v)
  refine ⟨p1, ⟨h1, h2, h3, ?_⟩, h4⟩
  rintro x ⟨z, rfl⟩
  obtain ⟨fp, hm, hf⟩ := NumberField.RingOfIntegers.isIntegral_coe z
  have hf' : Polynomial.eval₂ (algebraMap ℤ I.E) (algebraMap (𝓞 I.E) I.E z) fp = 0 := hf
  show (p1.comp (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v)) (algebraMap (𝓞 I.E) I.E z) ∈ OV I v
  refine (Valuation.valuationSubring.integers (Valued.v (R := v.adicCompletion I.F))).mem_of_integral
    ⟨fp.map (Int.castRingHom _), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hc : (algebraMap (Valued.v (R := v.adicCompletion I.F)).valuationSubring (v.adicCompletion I.F)).comp
      (Int.castRingHom (Valued.v (R := v.adicCompletion I.F)).valuationSubring) =
      (p1.comp (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v)).comp (algebraMap ℤ I.E) := RingHom.ext_int _ _
  rw [hc, ← Polynomial.hom_eval₂, hf', map_zero]

theorem local_splitting_projection : LocSplitP := by
  intro I g r k e f Rf v hsum
  obtain ⟨p1, hp, -⟩ := locSplitP_dec I g r k e f Rf v hsum
  exact ⟨p1, hp⟩

end PI.UnitaryGroupMassFormula.ScXuExists
end
end

