module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVSDBwdHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0007

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertBHolds
section
namespace PI.OmVe.Top

theorem fFInertB_holds : PI.OmVd.FFInertB := PI.OmVe.fFInertB_holds

theorem fFSplitB_holds : PI.OmVd.FFSplitB := PI.OmVe.fFSplitB_holds

end PI.OmVe.Top
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.MemALImage
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolV

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def aL (g : Fv F v) (θ : Fv F v ⊗[F] E) : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) :=
  LinearMap.id + (g - 1) • (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)).smulRight θ

theorem aL_apply (g : Fv F v) (θ z : Fv F v ⊗[F] E) :
    aL v g θ z = z + ((g - 1) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z) • θ := by
  simp [aL, LinearMap.smulRight_apply, smul_smul]

theorem trace_aL (g : Fv F v) (θ z : Fv F v ⊗[F] E) (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (aL v g θ z) = g * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z := by
  rw [aL_apply, map_add (f := _), map_smul, hθ, smul_eq_mul]
  ring

theorem det_aL (hfin : Module.finrank F E = 2) (g : Fv F v) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) : LinearMap.det (aL v g θ) = g := by
  classical
  have hrank : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange, hfin]
  have hli : LinearIndependent (Fv F v) ![θ, Δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) hst
    simp only [map_add (f := _), map_smul, hθ, hΔ, smul_eq_mul, mul_one, mul_zero, add_zero, map_zero] at h1
    subst h1
    rw [zero_smul, zero_add, smul_eq_zero] at hst
    exact ⟨rfl, hst.resolve_right hΔ0⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [hrank]; rfl)
  have hb0 : b 0 = θ := by simp [b]
  have hb1 : b 1 = Δ := by simp [b]
  have hf0 : aL v g θ (b 0) = g • b 0 := by
    rw [hb0, aL_apply, hθ, mul_one, sub_smul, one_smul]
    abel
  have hf1 : aL v g θ (b 1) = b 1 := by
    rw [hb1, aL_apply, hΔ, mul_zero, zero_smul, add_zero]
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, hf0, hf1, map_smul, b.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  simp

private theorem int_of_alg_lemma (z : Fv F v ⊗[F] E) (hz : z ∈ OEv (E := E) v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z ∈ v.adicCompletionIntegers F := by
  change z ∈ Submodule.span (v.adicCompletionIntegers F) _ at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.trace_inclR]
    have hint : IsIntegral ℤ (Algebra.trace F E (a : E)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe a)
    have := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) (v := v) (⟨_, hint⟩ : 𝓞 F)
    convert this using 1
    exact (IsScalarTower.algebraMap_apply (𝓞 F) F (Fv F v) (⟨_, hint⟩ : 𝓞 F)).symm
  | zero => rw [map_zero]; exact zero_mem _
  | add y w _ _ hy hw => rw [map_add (f := _)]; exact add_mem hy hw
  | smul c y _ hy =>
    rw [show c • y = (c : Fv F v) • y from rfl, map_smul, smul_eq_mul]
    exact mul_mem c.2 hy

private theorem int_of_alg_lemma_2 (a : 𝓞 E) (z : Fv F v ⊗[F] E) (hz : z ∈ OEv (E := E) v) :
    inclR (Fv F v) (a : E) * z ∈ OEv (E := E) v := by
  change z ∈ Submodule.span (v.adicCompletionIntegers F) _ at hz
  change _ ∈ Submodule.span (v.adicCompletionIntegers F) _
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, -, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨a * b, Set.mem_univ _, ?_⟩
    show inclR (Fv F v) ((a * b : 𝓞 E) : E) = inclR (Fv F v) (a : E) * inclR (Fv F v) (b : E)
    rw [show ((a * b : 𝓞 E) : E) = (a : E) * (b : E) from rfl, map_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add y w _ _ hy hw => rw [mul_add]; exact add_mem hy hw
  | smul c y _ hy =>
    rw [show c • y = (c : Fv F v) • y from rfl, mul_smul_comm]
    exact Submodule.smul_mem _ c hy

private theorem int_of_alg_lemma_3 (x z : Fv F v ⊗[F] E) (hx : x ∈ OEv (E := E) v) (hz : z ∈ OEv (E := E) v) :
    x * z ∈ OEv (E := E) v := by
  change x ∈ Submodule.span (v.adicCompletionIntegers F) _ at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    exact int_of_alg_lemma_2 v a z hz
  | zero => rw [zero_mul]; exact (Submodule.span _ _).zero_mem
  | add y w _ _ hy hw =>
    rw [add_mul]
    exact (Submodule.span (v.adicCompletionIntegers F) _).add_mem hy hw
  | smul c y _ hy =>
    rw [show c • y = (c : Fv F v) • y from rfl, smul_mul_assoc]
    exact (Submodule.span (v.adicCompletionIntegers F) _).smul_mem c hy

theorem int_of_alg {θ : Fv F v ⊗[F] E} (hθO : θ ∈ OEv (E := E) v)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) {x : Fv F v}
    (hx : algebraMap (Fv F v) (Fv F v ⊗[F] E) x ∈ OEv (E := E) v) : x ∈ v.adicCompletionIntegers F := by
  have h := int_of_alg_lemma v _ (int_of_alg_lemma_3 v _ _ hx hθO)
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, hθ, smul_eq_mul, mul_one] at h
  exact h

theorem mem_aL_image (σ : E →ₐ[F] E)
    (htr : ∀ w : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ w)
    {g : ℕ} (hg0 : g ≠ 0) {θ : Fv F v ⊗[F] E} (hθO : θ ∈ OEv (E := E) v)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (y : Fv F v ⊗[F] E) :
    y ∈ aL v (g : Fv F v) θ '' OEv (E := E) v ↔
      y ∈ OEv (E := E) v ∧ (y + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ y) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v := by
  classical
  have hsc : ∀ c : Fv F v, sc (E := E) v c = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := fun c => by
    rw [Algebra.algebraMap_eq_smul_one, ← Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_eq_smul, mul_one]
  have hcond : (y + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ y) * sc (E := E) v (g : Fv F v)⁻¹ =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y * (g : Fv F v)⁻¹) := by
    rw [← htr, hsc, map_mul]
  have hone : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
    have := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.inclR_mem (E := E) v 1
    simp only [OneMemClass.coe_one, map_one] at this
    exact this
  have hsmul : ∀ c ∈ v.adicCompletionIntegers F, ∀ x ∈ OEv (E := E) v, c • x ∈ OEv (E := E) v :=
    fun c hc x hx => by
      rw [← Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_eq_smul]
      exact Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_mem v hc hx
  have halg : ∀ c ∈ v.adicCompletionIntegers F, algebraMap (Fv F v) (Fv F v ⊗[F] E) c ∈ OEv (E := E) v :=
    fun c hc => by
      rw [Algebra.algebraMap_eq_smul_one]
      exact hsmul c hc 1 hone
  have hgO : (g : Fv F v) - 1 ∈ v.adicCompletionIntegers F :=
    sub_mem (Formalism.L2.SG.Pf.NcVal.VolTU.natCast_memO v g) (one_mem _)
  have hgne : (g : Fv F v) ≠ 0 := Formalism.L2.SG.Pf.NcVal.VolTU.natCast_ne_zero v hg0
  rw [hcond]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have htz := int_of_alg_lemma v z hz
    refine ⟨?_, ?_⟩
    · rw [aL_apply]
      exact add_mem hz (hsmul _ (mul_mem hgO htz) θ hθO)
    · rw [trace_aL v _ θ z hθ, mul_comm, ← mul_assoc, inv_mul_cancel₀ hgne, one_mul]
      exact halg _ htz
  · rintro ⟨hy, ht⟩
    have htO := int_of_alg v hθO hθ ht
    set t := Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y * (g : Fv F v)⁻¹ with ht_def
    refine ⟨y - (((g : Fv F v) - 1) * t) • θ, sub_mem hy (hsmul _ (mul_mem hgO htO) θ hθO), ?_⟩
    have htr' : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y = (g : Fv F v) * t := by
      rw [ht_def, mul_comm, mul_assoc, inv_mul_cancel₀ hgne, mul_one]
    rw [aL_apply]
    have : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (y - (((g : Fv F v) - 1) * t) • θ) = t := by
      rw [map_sub, map_smul, hθ, smul_eq_mul, mul_one, htr']
      ring
    rw [this, sub_add_cancel]

end Formalism.L2.SG.Pf.NcVal.VolV
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfThreeX
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def LeftInvO (a : ℕ) : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v →
  ∀ M : Matrix (Fin n) (Fin a) (Fv F v ⊗[F] E), (∀ k i, M k i ∈ OEv (E := E) v) →
    (∀ c : Fin a → Fv F v ⊗[F] E, (∀ k, Matrix.mulVec M c k ∈ OEv (E := E) v) → ∀ i, c i ∈ OEv (E := E) v) →
    ∃ N : Matrix (Fin a) (Fin n) (Fv F v ⊗[F] E), (∀ i k, N i k ∈ OEv (E := E) v) ∧ N * M = 1

theorem primDual_of (a : ℕ) (hB : Red.OBas1 σ J ψ v Λ) (hLI : LeftInvO σ J ψ v (n := n) a) :
    PrimDual σ J ψ v Λ a := by
  classical
  intro hS hSD hUn hL y hy
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabSW.sigma_invol σ hS.1.2.2.2
  obtain ⟨e, he, hg⟩ := hB hS hL hSD hUn
  have hee : ∀ k l, hR (Fv F v) σ J (e k) (e l) = if k = l then 1 else 0 := by
    intro k l
    have := congrFun (congrFun hg k) l
    simpa [gramR, Matrix.one_apply] using this
  have hcoord : ∀ i, ∃ c : Fin n → Fv F v ⊗[F] E, (∀ k, c k ∈ OEv (E := E) v) ∧ y i = ∑ k, c k • e k :=
    fun i => (he (y i)).1 (hy.1 i)
  choose M hM hyM using hcoord
  obtain ⟨N, hN, hNM⟩ := hLI hS hUn (Matrix.of fun k i => M i k) (fun k i => hM i k) (by
    intro c hc i
    apply hy.2 c _ i
    have e1 : ∑ i, c i • y i = ∑ k, Matrix.mulVec (Matrix.of fun k i => M i k) c k • e k := by
      simp only [hyM, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
    rw [e1]
    exact (he _).2 ⟨_, hc, rfl⟩)
  have hNM' : ∀ j i, ∑ l, N j l * M i l = if j = i then 1 else 0 := by
    intro j i
    have := congrFun (congrFun hNM j) i
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  refine ⟨fun j => ∑ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (N j l) • e l,
    fun j => (he _).2 ⟨_, fun l => UnN.sigR_mem σ v (hN j l), rfl⟩, fun i j => ⟨?_, ?_⟩⟩
  · have h1 : ∀ l, hR (Fv F v) σ J (y i) (e l) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (M i l) := by
      intro l
      rw [hyM i, hR_sum_smul_left]
      simp [hee]
    rw [hR_sum_smul_right]
    simp only [h1]
    have e2 : ∑ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (N j l) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (M i l) =
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (∑ l, N j l * M i l) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_mul]
    rw [e2, hNM' j i]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  · have h2 : ∀ k, hR (Fv F v) σ J (∑ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (N j l) • e l) (e k) = N j k := by
      intro k
      rw [hR_sum_smul_left]
      simp only [hee, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact PI.VolStabSW.sigR_invol (Fv F v) σ hσ (N j k)
    rw [hyM i, hR_sum_smul_right]
    simp only [h2]
    have e3 : ∑ k, M i k * N j k = ∑ k, N j k * M i k := Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [e3, hNM' j i]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]

theorem oBas1_holds : Red.OBas1 σ J ψ v Λ := by
  have hR : Red.ResAlg σ J ψ v := Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)
  exact Red.oBas1_of_unitV σ J ψ v Λ
    (Orb.unitV_of σ J ψ v Λ (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hR) (UnN.unitNorm_of_res σ J ψ v Λ hR))

theorem primDual_of_left (a : ℕ) (hLI : LeftInvO σ J ψ v (n := n) a) : PrimDual σ J ψ v Λ a :=
  primDual_of σ J ψ v Λ a (oBas1_holds σ J ψ v Λ) hLI

end Gen

section Loc

open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVBadT_of_std_lat_gram (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hExt : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hLI : ∀ v : PlX X, LeftInvO X.B.I.cm.sig X.B.I.J ψ v (n := X.B.I.n) (D.R.rS + 1 + D.R.rS))
    (hCl : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ClsP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)) :
    OmVBadT X u' ψ :=
  omVBadT_of_primDual_cls X u' ψ hStd hLat hGram hExt
    (fun v => primCos_of _ _ _ _ _ _ (primDual_of_left _ _ _ _ _ _ (hLI v)))
    (fun v => primDual_of_left _ _ _ _ _ _ (hLI v)) hCl

end Loc

end PI.OmVd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVZPrimHolds
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem zu_orth_X (y : (VS D).V) (hy : y ∈ (X.Fu u').X) : (VS D).hT y (X.zu u') = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [← X.flagZVector u']
    exact (X.Fu u').z_orth a
  | zero => simp
  | add x y _ _ h1 h2 => simp [h1, h2]
  | smul c x _ h => simp [h]

theorem glob_prim (g : X.B.I.E) (hg : g • crdOf X.B.I X.ιE X.bas (X.zu u') ∈ X.B.I.L) : IsIntegral ℤ g := by
  have hL0 : X.ιE g • X.zu u' ∈ (VS D).L0 := by
    have h := (X.L_eq _).1 hg
    have e : (∑ i, X.ιE ((g • crdOf X.B.I X.ιE X.bas (X.zu u')) i) • X.bas i) = X.ιE g • X.zu u' := by
      simp only [Pi.smul_apply, smul_eq_mul, crdOf, map_mul, RingEquiv.apply_symm_apply, mul_smul]
      rw [← Finset.smul_sum, X.bas.sum_repr]
    rwa [e] at h
  have horth : X.ιE g • X.zu u' ∈ Formalism.MainNotions.S.Lat.orth (VS D) (X.Fu u').X := by
    simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker, map_smul, smul_eq_mul]
    intro x hx
    rw [zu_orth_X X u' x hx, mul_zero]
  obtain ⟨o, ho⟩ := (X.Fu_fixed u').2.2.2.2 (X.ιE g) (by
    change X.ιE g • (X.Fu u').z ∈ _
    rw [X.flagZVector u']
    unfold Formalism.MainNotions.S.Lat.Lsub Formalism.MainNotions.S.Lat.Lrep
    exact Submodule.mem_inf.2 ⟨Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hL0, horth⟩), horth⟩)
  have e : g = X.ιE.symm (o : D.host.E) := by rw [ho, RingEquiv.symm_apply_apply]
  rw [e]
  exact (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom

theorem yTup_zi (v : PlX X) :
    yTup X u' v (zi (D := D)) = ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas (X.zu u')) := by
  have hs : scl X v (zi (D := D)) = 1 := by
    simp only [scl, zi, Fin.append_left]; exact alp_last v D.R.rS
  have h1 : yTup X u' v (zi (D := D)) = ratV (F := X.B.I.F) (Fv X.B.I.F v) (tupH (frameOf X u') (zi (D := D))) := by
    funext i
    change sc (E := X.B.I.E) v (scl X v (zi (D := D))) * _ = _
    rw [hs]
    simp only [sc, ← Algebra.TensorProduct.one_def, one_mul]
    rfl
  have h2 : hv X u' (zi (D := D)) = X.zu u' := by simp only [hv, zi, Fin.append_left, Fin.snoc_last]
  rw [h1, tupH_eq, h2]

theorem omVZPrim_holds : OmVZPrim X u' := by
  intro v _ c hc
  set z := crdOf X.B.I X.ιE X.bas (X.zu u') with hz_def
  have hz : z ∈ abelian₂ X := crdOf_mem X (frame_vector_mem_base_lattice X u')
  rw [yTup_zi] at hc
  obtain ⟨c', w, hw, hcw⟩ := approx v 1 one_ne_zero c
  have hw' : c - inclR (F := X.B.I.F) (Fv X.B.I.F v) c' = w := by rw [hcw]; simp
  have h1 : ratV (F := X.B.I.F) (Fv X.B.I.F v) (c' • z) ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
    have e : ratV (F := X.B.I.F) (Fv X.B.I.F v) (c' • z) =
        c • ratV (F := X.B.I.F) (Fv X.B.I.F v) z - w • ratV (F := X.B.I.F) (Fv X.B.I.F v) z := by
      funext i
      simp only [ratV, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul]
      rw [← hw']; ring
    rw [e]
    exact Submodule.sub_mem _ hc (lat_oev_smul X v hw (Submodule.subset_span ⟨z, hz, rfl⟩))
  have hpair : ∀ l ∈ X.B.I.L, inclR (F := X.B.I.F) (Fv X.B.I.F v)
      (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l (c' • z)) ∈ OEv (E := X.B.I.E) v := by
    intro l hl
    have h2 : inclR (F := X.B.I.F) (Fv X.B.I.F v) (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l (c' • z)) =
        hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) l)
          (ratV (F := X.B.I.F) (Fv X.B.I.F v) (c' • z)) :=
      (hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J ![l, c' • z] 0 1).symm
    rw [h2]
    exact omVSD_fwd X v (Submodule.subset_span ⟨l, hl, rfl⟩) h1
  obtain ⟨t, ht, htL⟩ := locGlob X v _ hpair
  have hg : IsIntegral ℤ (algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) * c') :=
    glob_prim X u' _ (by rw [mul_smul]; exact htL)
  obtain ⟨hinv, hne⟩ := unit_of_notMem v t ht
  have hc' : inclR (F := X.B.I.F) (Fv X.B.I.F v) c' ∈ OEv (E := X.B.I.E) v := by
    have e : inclR (F := X.B.I.F) (Fv X.B.I.F v) c' =
        (⟨(algebraMap X.B.I.F (Fv X.B.I.F v) (t : X.B.I.F))⁻¹, hinv⟩ : v.adicCompletionIntegers X.B.I.F) •
          inclR (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) * c') := by
      show inclR (F := X.B.I.F) (Fv X.B.I.F v) c' = (algebraMap X.B.I.F (Fv X.B.I.F v) (t : X.B.I.F))⁻¹ •
        inclR (F := X.B.I.F) (Fv X.B.I.F v) (algebraMap X.B.I.F X.B.I.E (t : X.B.I.F) * c')
      rw [map_mul, ← alg_alg, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (incl_mem v (⟨_, (mem_integralClosure_iff ℤ _).2 hg⟩ : 𝓞 X.B.I.E))
  have e2 : c = w + inclR (F := X.B.I.F) (Fv X.B.I.F v) c' := by rw [← hw']; ring
  rw [e2]
  exact Submodule.add_mem _ hw hc'

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ProdDiagonalShiftOneMinus
section
noncomputable section

namespace PI.OmVg

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix PI.OmLocU Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

theorem le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  exact h

theorem natCast_div_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t : ℕ)
    (ht : ((t : 𝓞 F)) ∈ v.asIdeal) {ϖ : Fv F v} (hϖ : IsUnif v ϖ) :
    ((t : ℕ) : Fv F v) * ϖ⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : ((t : ℕ) : Fv F v) = algebraMap (𝓞 F) (Fv F v) (t : 𝓞 F) := by simp
  have hlt : Valued.v ((t : ℕ) : Fv F v) < 1 := by
    rw [h1]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (t : 𝓞 F)).trans_lt ?_
    erw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 ht
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hv]
  calc Valued.v ((t : ℕ) : Fv F v) * (WithZero.exp (-1 : ℤ))⁻¹
      ≤ WithZero.exp (-1 : ℤ) * (WithZero.exp (-1 : ℤ))⁻¹ := by gcongr; exact le_exp_neg_one hlt
    _ = 1 := mul_inv_cancel₀ WithZero.exp_ne_zero

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

def iz : Fin (D.R.rS + 1 + D.R.rS) := ⟨D.R.rS, by omega⟩

theorem piv_iz : piv D.R.rS (iz (D := D)) = iz := by
  apply Fin.ext
  simp [piv, iz]

theorem eq_iz_of_piv {a : Fin (D.R.rS + 1 + D.R.rS)} (h : piv D.R.rS a = iz) : a = iz := by
  have := congrArg (piv D.R.rS) h
  rwa [piv_invol D.R.rS a, piv_iz] at this

theorem gramE_apply (a b : Fin (D.R.rS + 1 + D.R.rS)) :
    gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) a b = if piv D.R.rS a = b then cD X u' a else 0 := by
  rw [gram_eq, diagonal_mul]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Function.Involutive.coe_toPerm]
  by_cases h : piv D.R.rS a = b <;> simp [h]

theorem cD_iz : cD X u' (iz (D := D)) = -((Tw u' : ℕ) : X.B.I.E) := by
  simp [cD, iz]

def diagonalShiftOneMinus (a : Fin (D.R.rS + 1 + D.R.rS)) : X.B.I.E :=
  if a.val = D.R.rS then 1 - ((Tw u' : ℕ) : X.B.I.E) else 1

theorem prod_diagonalShiftOneMinus : ∏ a, diagonalShiftOneMinus X u' a = 1 - ((Tw u' : ℕ) : X.B.I.E) := by
  rw [Finset.prod_eq_single (iz (D := D))]
  · simp [diagonalShiftOneMinus, iz]
  · intro b _ hb
    have : b.val ≠ D.R.rS := fun e => hb (Fin.ext e)
    simp [diagonalShiftOneMinus, this]
  · simp

end PI.OmVg
end
end

