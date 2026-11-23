module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0011
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUHerm
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolUHm

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

theorem sigR_inclR (x : E) : sigR (Fv F v) σ (inclR (F := F) (Fv F v) x) = inclR (F := F) (Fv F v) (σ x) := by
  simp [sigR, inclR]

theorem sigR_sc (c : Fv F v) : sigR (Fv F v) σ (sc (E := E) v c) = sc (E := E) v c := by
  simp [sigR, sc, Algebra.TensorProduct.map_tmul]

theorem sigR_smul (c : Fv F v) (x : Fv F v ⊗[F] E) : sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  rw [← VolTU.sc_mul_eq_smul, ← VolTU.sc_mul_eq_smul, map_mul, sigR_sc]

theorem sigR_mem {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : sigR (Fv F v) σ x ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    rw [sigR_inclR]
    exact VolUTr.TrW.inclR_mem' (E := E) v ⟨σ a, (a.2).map σ.toRingHom.toIntAlgHom⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ h1 h2 => rw [map_add (f := _)]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    have e : c • x = (c : Fv F v) • x := rfl
    rw [e, sigR_smul]
    exact Submodule.smul_mem _ c h

def sigL : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) where
  toFun := sigR (Fv F v) σ
  map_add' := map_add _
  map_smul' := sigR_smul σ v

theorem sigR_cont : Continuous (sigR (Fv F v) σ : Fv F v ⊗[F] E → Fv F v ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  exact IsModuleTopology.continuous_of_linearMap (sigL σ v)

theorem sigR_sigR (hinv : ∀ y, σ (σ y) = y) (x : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, Algebra.TensorProduct.map_tmul, hinv]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

section Phi

variable (r : ℕ)

def phiF (Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E :=
  fun p => if p.1 < p.2 then Y p + sigR (Fv F v) σ (Y (p.2, p.1)) else Y p

def phiB (Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E :=
  fun p => if p.1 < p.2 then Y p - sigR (Fv F v) σ (Y (p.2, p.1)) else Y p

theorem phiF_low (Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) {i j : Fin (r + 1)} (h : ¬ i < j) :
    phiF σ v r Y (i, j) = Y (i, j) := by
  simp [phiF, h]

theorem phiF_up (Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) {i j : Fin (r + 1)} (h : i < j) :
    phiF σ v r Y (i, j) = Y (i, j) + sigR (Fv F v) σ (Y (j, i)) := by
  simp [phiF, h]

def phiE : (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) ≃ₜ+ (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) where
  toFun := phiF σ v r
  invFun := phiB σ v r
  left_inv Y := by
    funext p
    by_cases h : p.1 < p.2
    · have h' : ¬ p.2 < p.1 := fun h2 => lt_asymm h h2
      simp [phiF, phiB, h, h']
    · simp [phiF, phiB, h]
  right_inv Y := by
    funext p
    by_cases h : p.1 < p.2
    · have h' : ¬ p.2 < p.1 := fun h2 => lt_asymm h h2
      simp [phiF, phiB, h, h']
    · simp [phiF, phiB, h]
  map_add' Y Z := by
    funext p
    by_cases h : p.1 < p.2
    · simp only [phiF, h, if_true, Pi.add_apply, map_add (f := _)]
      abel
    · simp [phiF, h]
  continuous_toFun := by
    haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
    refine continuous_pi fun p => ?_
    by_cases h : p.1 < p.2
    · simp only [phiF, h, if_true]
      exact (continuous_apply p).add ((sigR_cont σ v).comp (continuous_apply (p.2, p.1)))
    · simp only [phiF, h, if_false]
      exact continuous_apply p
  continuous_invFun := by
    haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
      IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
    refine continuous_pi fun p => ?_
    by_cases h : p.1 < p.2
    · simp only [phiB, h, if_true]
      exact (continuous_apply p).sub ((sigR_cont σ v).comp (continuous_apply (p.2, p.1)))
    · simp only [phiB, h, if_false]
      exact continuous_apply p

theorem phiF_mem_iff (Y : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :
    (∀ i j, phiF σ v r Y (i, j) ∈ OEv (E := E) v) ↔ ∀ i j, Y (i, j) ∈ OEv (E := E) v := by
  constructor
  · intro h i j
    by_cases hij : i < j
    · have h1 := h i j
      have h2 := h j i
      rw [phiF_up σ v r Y hij] at h1
      rw [phiF_low σ v r Y (fun h3 => lt_asymm hij h3)] at h2
      have e : Y (i, j) = (Y (i, j) + sigR (Fv F v) σ (Y (j, i))) - sigR (Fv F v) σ (Y (j, i)) := by ring
      rw [e]
      exact Submodule.sub_mem _ h1 (sigR_mem σ v h2)
    · have h1 := h i j
      rwa [phiF_low σ v r Y hij] at h1
  · intro h i j
    by_cases hij : i < j
    · rw [phiF_up σ v r Y hij]
      exact Submodule.add_mem _ (h i j) (sigR_mem σ v (h j i))
    · rw [phiF_low σ v r Y hij]
      exact h i j

def hermBox (g r : ℕ) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) :
    Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  {Y | ∀ i j, Y (i, j) ∈ OEv (E := E) v ∧
    (i < j → (Y (i, j) - c i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v) ∧
    (i = j → (Y (i, j) + sigR (Fv F v) σ (Y (i, j)) - c i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v)}

theorem volTW_eq (hinv : ∀ y, σ (σ y) = y) (g r : ℕ) (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E))
    (hc : VolTHermInt σ v r c) : VolTW σ v g r c = phiF σ v r ⁻¹' hermBox σ v g r c := by
  ext Y
  simp only [VolTW, hermBox, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · intro h i j
    refine ⟨(phiF_mem_iff σ v r Y).2 (fun i j => (h i j).1) i j, fun hij => ?_, fun hij => ?_⟩
    · rw [phiF_up σ v r Y hij]
      exact (h i j).2
    · subst hij
      rw [phiF_low σ v r Y (lt_irrefl _)]
      exact (h i i).2
  · intro h
    have hO := (phiF_mem_iff σ v r Y).1 (fun i j => (h i j).1)
    intro i j
    refine ⟨hO i j, ?_⟩
    rcases lt_trichotomy i j with hij | hij | hij
    · have := (h i j).2.1 hij
      rwa [phiF_up σ v r Y hij] at this
    · subst hij
      have := (h i i).2.2 rfl
      rwa [phiF_low σ v r Y (lt_irrefl _)] at this
    · have h1 := sigR_mem σ v ((h j i).2.1 hij)
      rw [phiF_up σ v r Y hij, map_mul, sigR_sc, map_sub, map_add (f := _), sigR_sigR σ v hinv, ← hc.1 j i] at h1
      rw [show Y (i, j) + sigR (Fv F v) σ (Y (j, i)) - c i j =
        sigR (Fv F v) σ (Y (j, i)) + Y (i, j) - c i j by ring]
      exact h1

theorem volTW_meas (hinv : ∀ y, σ (σ y) = y) (μ : Measure (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E))
    [μ.IsAddHaarMeasure] (hK : μ (VolTO (E := E) v (Fin (r + 1) × Fin (r + 1))) = 1) (g : ℕ)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) (hc : VolTHermInt σ v r c) :
    μ (VolTW σ v g r c) = μ (hermBox σ v g r c) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := VolUH.top_facts (E := E) v (Fin (r + 1) × Fin (r + 1))
  have h := VolUH.haar_pre μ (phiE σ v r) (VolTO (E := E) v (Fin (r + 1) × Fin (r + 1))) hK (hermBox σ v g r c)
  have hK' : (phiE σ v r) ⁻¹' VolTO (E := E) v (Fin (r + 1) × Fin (r + 1)) =
      VolTO (E := E) v (Fin (r + 1) × Fin (r + 1)) := by
    ext Y
    simp only [VolTO, Set.mem_preimage, Set.mem_setOf_eq, Prod.forall]
    exact phiF_mem_iff σ v r Y
  rw [hK', hK, one_mul] at h
  rw [volTW_eq σ v hinv g r c hc]
  exact h

variable (ψ : AddChar (AF F) ℂ)

def VolTHermBox (g : ℕ) : Prop :=
  ∀ c, VolTHermInt σ v r c →
    sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) (hermBox σ v g r c) = ((g : ℝ≥0∞) ^ ((r + 1) ^ 2))⁻¹

theorem volTHermCnt_of_box (hψ : IsCharAF F ψ) (hfin : Module.finrank F E = 2) (hann : VolUL.AnnAt (E := E) ψ v)
    (hd : absV v (dV v) = 1) (hinv : ∀ y, σ (σ y) = y) (g : ℕ) (hB : VolTHermBox σ v r ψ g) :
    VolTHermCnt σ ψ v g r := by
  obtain ⟨hH, -, hO⟩ := VolUL.sd_facts ψ v hψ hfin hann hd (Fin (r + 1) × Fin (r + 1))
  intro c hc
  rw [volTW_meas σ v r hinv _ hO g c hc]
  exact hB c hc

end Phi

end Formalism.L2.SG.Pf.NcVal.VolUHm
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUTF
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace VolUF

variable {D : D7} (X : HidaSetting D)

theorem star_eq (a : D.host.E) : star a = D.host.conj a := by
  apply D.host.φ₀.injective
  rw [show star a = IsCMField.complexConj D.host.E a from rfl, IsCMField.complexEmbedding_complexConj]
  exact (D.host.conjE_apply D.host.φ₀ a).symm

theorem sig_eq (b : X.B.I.E) : X.ιE (X.B.I.cm.sig b) = star (X.ιE b) := by
  have h1 : X.B.I.cm.sig b = star b := rfl
  rw [h1, X.ιE_conj, star_eq]

theorem hE_crd (x y : (VS D).V) :
    X.ιE (hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas x) (crdOf X.B.I X.ιE X.bas y)) = (VS D).hT x y := by
  unfold hE Formalism.UG.hform crdOf
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe]
  simp only [sig_eq, X.J_eq, RingEquiv.apply_symm_apply]
  conv_rhs => rw [← X.bas.sum_repr x, ← X.bas.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
    RingHom.id_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_eq (w : D.what₂.Word) (i j : Fin (D.R.rS + 1)) :
    X.ιE (gramE X.B.I.cm.sig X.B.I.J (F0 (frameOf X w)) i j) =
      if i = Fin.last D.R.rS ∧ j = Fin.last D.R.rS then -(((D.mem w).A.T : ℕ) : D.host.E) else 0 := by
  unfold gramE
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [F0, Fin.snoc_last, frameOf]
      rw [hE_crd, X.zu_norm]
      simp
    | cast b =>
      simp only [F0, Fin.snoc_last, Fin.snoc_castSucc, frameOf]
      rw [hE_crd, ← LinearMap.isSymm_def.1 (VS D).herm (X.eX b) (X.zu w), (X.zu_orth w b).1, map_zero]
      simp [Fin.castSucc_ne_last]
  | cast a =>
    induction j using Fin.lastCases with
    | last =>
      simp only [F0, Fin.snoc_last, Fin.snoc_castSucc, frameOf]
      rw [hE_crd, (X.zu_orth w a).1]
      simp [Fin.castSucc_ne_last]
    | cast b =>
      simp only [F0, Fin.snoc_castSucc, frameOf]
      rw [hE_crd, X.ee]
      simp [Fin.castSucc_ne_last]

theorem gram_eq' (w : D.what₂.Word) (i j : Fin (D.R.rS + 1)) :
    gramE X.B.I.cm.sig X.B.I.J (F0 (frameOf X w)) i j =
      if i = Fin.last D.R.rS ∧ j = Fin.last D.R.rS then -(((D.mem w).A.T : ℕ) : X.B.I.E) else 0 := by
  apply X.ιE.injective
  rw [gram_eq]
  split_ifs <;> simp

theorem tf_diff (u u' : D.what₂.Word) (v : PlX X) (g : ℕ) (i j : Fin (D.R.rS + 1)) :
    (TFv X u' v i j - TFv X u v i j) * sc (E := X.B.I.E) v (g : Fv X.B.I.F v)⁻¹ =
      sc (E := X.B.I.E) v (if i = Fin.last D.R.rS ∧ j = Fin.last D.R.rS then
        ((((D.mem u).A.T : ℕ) : Fv X.B.I.F v) - (((D.mem u').A.T : ℕ) : Fv X.B.I.F v)) * (g : Fv X.B.I.F v)⁻¹
        else 0) := by
  unfold TFv
  simp only [Matrix.map_apply, gram_eq']
  split_ifs with h
  · rw [VolTU.sc_mul]
    congr 1
    rw [VolUTr.TrW.sc_eq, map_sub, map_natCast, map_natCast, map_neg, map_neg, map_natCast, map_natCast]
    ring
  · rw [sub_self, zero_mul, VolUTr.TrW.sc_eq, map_zero]

theorem sigR_sc (v : PlX X) (x : Fv X.B.I.F v) :
    sigR (Fv X.B.I.F v) X.B.I.cm.sig (sc (E := X.B.I.E) v x) = sc (E := X.B.I.E) v x := by
  simp [sigR, sc, Algebra.TensorProduct.map_tmul]

end VolUF

theorem volTTFCong_of {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (v : PlX X) (hv : TypAt X v) :
    VolTTFCong X u u' v := by
  obtain ⟨m, hm⟩ := tCongX X u u' ⟨v, hv⟩
  have hg0 : (gAt X v : Fv X.B.I.F v) ≠ 0 := VolTU.natCast_ne_zero v (gAt_prime X v).ne_zero
  have hk : ((((D.mem u).A.T : ℕ) : Fv X.B.I.F v) - (((D.mem u').A.T : ℕ) : Fv X.B.I.F v)) *
      (gAt X v : Fv X.B.I.F v)⁻¹ = (m : Fv X.B.I.F v) := by
    have hm' : ((((D.mem u).A.T : ℕ) : ℤ) : Fv X.B.I.F v) - ((((D.mem u').A.T : ℕ) : ℤ) : Fv X.B.I.F v) =
        ((gAt X v : ℤ) : Fv X.B.I.F v) * (m : Fv X.B.I.F v) := by
      rw [← Int.cast_sub, ← Int.cast_mul]
      exact congrArg _ hm
    push_cast at hm'
    rw [hm', mul_comm, ← mul_assoc, inv_mul_cancel₀ hg0, one_mul]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only
    rw [VolUF.tf_diff, VolUF.tf_diff, VolUF.sigR_sc]
    congr 1
    simp only [and_comm]
  · simp only
    rw [VolUF.tf_diff]
    split_ifs
    · rw [hk, VolUTr.TrW.sc_eq]
      exact VolUTr.TrW.alg_mem v (_root_.intCast_mem _ m)
    · rw [VolUTr.TrW.sc_eq, map_zero]
      exact Submodule.zero_mem _

end Formalism.L2.SG.Pf.NcVal
end
end

