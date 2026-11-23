module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReducedBasisBoundedTypeOfInstance
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionHermitianFrames
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuantitativeMahlerCriterionUnitaryGroup
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.HtMinPf

lemma uj_entry {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (i j : Fin n) :
    ‖uMat g i j‖ = ‖uMat g⁻¹ j i‖ := by
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : uMat g * uMat g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hmi : uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
    calc uMat g⁻¹ = Formalism.REAL.Jm ε * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) * uMat g⁻¹ := by
            rw [hg, hJ, Matrix.one_mul]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]
  rw [hmi]
  unfold Formalism.REAL.Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  by_cases ha : ε j <;> by_cases hb : ε i <;> simp [ha, hb]

variable (I : AutInst)

lemma vec_sum (y : I.Ginf) {N : ℕ} (z : Fin N → ℤ) (e : Fin N → Fin I.n → I.E) :
    vec I y (∑ i, z i • e i) = ∑ i, ((z i : ℝ)) • vec I y (e i) := by
  funext v
  have h : (fun k => I.φ v (∑ i, z i • e i k)) = ∑ i, ((z i : ℝ)) • fun k => I.φ v (e i k) := by
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Finset.sum_apply, map_sum, Complex.real_smul]
  simp only [CuspGeo.vec, Finset.sum_apply, Pi.smul_apply]
  rw [h, Matrix.mulVec_sum, Matrix.mulVec_sum]
  simp [Matrix.mulVec_smul]

lemma vec_one (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) :
    vec I y u v = uMat (y v)⁻¹ *ᵥ vec I 1 u v := by
  have h1 : uMat ((1 : I.Ginf) v)⁻¹ = 1 := by simp [uMat]
  simp only [CuspGeo.vec]
  rw [h1, Matrix.one_mulVec]

lemma vec_trans (x₁ y : I.Ginf) (γ : GL (Fin I.n) I.E)
    (hx : ∀ v, uMat (x₁ v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
    (u : Fin I.n → I.E) : vec I (x₁ * y) ((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u) = vec I y u := by
  funext v
  have hP : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
  have hinv : uMat (x₁ v)⁻¹ * uMat (x₁ v) = 1 := by
    show (((x₁ v)⁻¹ : Formalism.REAL.UJ (I.ε v)) : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ).val * ((x₁ v : Formalism.REAL.UJ (I.ε v)) : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ).val = 1
    rw [Subgroup.coe_inv, Units.inv_mul]
  have hφ : (fun i => I.φ v (((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u) i)) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *ᵥ fun i => I.φ v (u i) := by
    funext i
    exact RingHom.map_mulVec _ _ _ _
  have hmul : uMat ((x₁ * y) v)⁻¹ = uMat (y v)⁻¹ * uMat (x₁ v)⁻¹ := by
    simp [uMat, Pi.mul_apply, _root_.mul_inv_rev]
  simp only [CuspGeo.vec]
  rw [hmul, hφ, ← Matrix.mulVec_mulVec]
  congr 1
  have : (I.P v)⁻¹ *ᵥ ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *ᵥ fun i => I.φ v (u i)) =
      uMat (x₁ v) *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v (u i)) := by
    rw [hx v, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (I.P v), hP, Matrix.mul_one]
  rw [this, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

lemma span_of_zbasis {N : ℕ} (e₀ : Fin N → Fin I.n → I.E) (he₀ : IsZBasis I e₀)
    (w : InfinitePlace I.F → Fin I.n → ℂ) : ∃ c : Fin N → ℝ, w = ∑ l, c l • vec I 1 (e₀ l) := by
  obtain ⟨N', e', ρ, d, hd, he', -, hdet⟩ := _root_.GlobalTheory.CuspGeo.covolume_const I
  set G := gm I ρ 1 e' with hGdef
  have hG : G.det ≠ 0 := by
    intro h
    have := hdet 1
    rw [← hGdef, h] at this
    simp at this
    linarith
  set a := G⁻¹ *ᵥ ρ w with ha
  have hGa : G *ᵥ a = ρ w := by
    rw [ha, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG), Matrix.one_mulVec]
  have hw : w = ∑ j, a j • vec I 1 (e' j) := by
    apply ρ.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hGa, map_sum]
    funext i
    simp [hGdef, gm, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hz : ∀ j, ∃ z : Fin N → ℤ, e' j = ∑ i, z i • e₀ i := fun j =>
    (he₀.2 (e' j)).mp ((he'.2 (e' j)).mpr ⟨Pi.single j 1, by simp [Pi.single_apply]⟩)
  choose z hz using hz
  refine ⟨fun i => ∑ j, a j * (z j i : ℝ), ?_⟩
  rw [hw]
  simp_rw [hz, vec_sum, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

open Classical in
lemma entry_bound (z : I.Ginf) {N : ℕ} (e₀ : Fin N → Fin I.n → I.E) (c : Fin N → ℝ)
    (v : InfinitePlace I.F) (i : Fin I.n)
    (hc : (Pi.single v (Pi.single i (1 : ℂ)) : InfinitePlace I.F → Fin I.n → ℂ) = ∑ l, c l • vec I 1 (e₀ l))
    (j : Fin I.n) : ‖uMat (z v)⁻¹ j i‖ ≤ ∑ l, |c l| * ‖vec I z (e₀ l)‖ := by
  have h : uMat (z v)⁻¹ j i = (∑ l, c l • vec I z (e₀ l)) v j := by
    calc uMat (z v)⁻¹ j i
        = (uMat (z v)⁻¹ *ᵥ (Pi.single v (Pi.single i (1 : ℂ)) : InfinitePlace I.F → Fin I.n → ℂ) v) j := by
          simp [Matrix.mulVec_single_one]
      _ = (uMat (z v)⁻¹ *ᵥ (∑ l, c l • vec I 1 (e₀ l)) v) j := by rw [hc]
      _ = (∑ l, c l • vec I z (e₀ l)) v j := by
          simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, vec_one I z]
  rw [h, Finset.sum_apply, Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [Pi.smul_apply, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (vec I z (e₀ l) v) j).trans
    (norm_le_pi_norm (vec I z (e₀ l)) v)) (abs_nonneg _)

end GlobalTheory.HtMinPf


open GlobalTheory.HtMinPf in
theorem GlobalTheory.htMin_of_reduced : ∀ I : AutInst, HtMin I := by
  intro I
  classical
  obtain ⟨N, R, C, hred⟩ := _root_.GlobalTheory.CuspGeo.redBasis_holds I
  obtain ⟨S, hSfin, hS0, hS⟩ := _root_.GlobalTheory.BasesFin.bases_finite_classes I N R
  obtain ⟨K, hK, hK'⟩ := _root_.GlobalTheory.IntUnitCpt.intUnit_compact I
  have hbd : ∀ e₀ : Fin N → Fin I.n → I.E, ∃ M : ℝ, e₀ ∈ S → ∀ v i, ∃ c : Fin N → ℝ,
      (Pi.single v (Pi.single i (1 : ℂ)) : InfinitePlace I.F → Fin I.n → ℂ) = ∑ l, c l • vec I 1 (e₀ l) ∧
        ∑ l, |c l| ≤ M := by
    intro e₀
    by_cases h : e₀ ∈ S
    · have := fun v i => span_of_zbasis I e₀ (hS0 e₀ h) (Pi.single v (Pi.single i (1 : ℂ)))
      choose c hc using this
      refine ⟨∑ v, ∑ i, ∑ l, |c v i l|, fun _ v i => ⟨c v i, hc v i, ?_⟩⟩
      calc ∑ l, |c v i l| ≤ ∑ i', ∑ l, |c v i' l| :=
            Finset.single_le_sum (f := fun i' => ∑ l, |c v i' l|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
        _ ≤ ∑ v', ∑ i', ∑ l, |c v' i' l| :=
            Finset.single_le_sum (f := fun v' => ∑ i', ∑ l, |c v' i' l|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
              (Finset.mem_univ v)
    · exact ⟨0, fun h' => absurd h' h⟩
  choose M hM using hbd
  obtain ⟨Mt, hMt⟩ := (hSfin.image M).bddAbove
  refine ⟨N, Mt * max C 0, K, hK, ?_⟩
  intro y t ht0 ht1 hns
  obtain ⟨e, heZ, heB, hesz⟩ := hred y
  obtain ⟨e₀, he₀S, γ, hγU, hγi, hγi', hγe⟩ := hS e heZ heB
  obtain ⟨x, hxG, hxK, hx⟩ := hK' γ hγU hγi hγi'
  refine ⟨x, hxG, hxK, fun v i j => ?_⟩
  have hMle : M e₀ ≤ Mt := hMt (Set.mem_image_of_mem M he₀S)
  obtain ⟨c, hc, hcM⟩ := hM e₀ he₀S v i
  have hvec : ∀ l, vec I (x.1 * y) (e₀ l) = vec I y (e l) := fun l => by
    rw [← hγe l]
    exact vec_trans I x.1 y γ hx (e l)
  have hb := entry_bound I (x.1 * y) e₀ c v i hc j
  simp_rw [hvec] at hb
  have ht : 0 ≤ t ^ N := pow_nonneg ht0.le _
  rw [uj_entry]
  calc ‖uMat ((x.1 * y) v)⁻¹ j i‖ * t ^ N ≤ (∑ l, |c l| * ‖vec I y (e l)‖) * t ^ N :=
        mul_le_mul_of_nonneg_right hb ht
    _ = ∑ l, |c l| * (‖vec I y (e l)‖ * t ^ N) := by
        rw [Finset.sum_mul]
        simp_rw [mul_assoc]
    _ ≤ ∑ l, |c l| * max C 0 := Finset.sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_left ((hesz t ht0 ht1 hns l).trans (le_max_left _ _)) (abs_nonneg _)
    _ = (∑ l, |c l|) * max C 0 := by rw [Finset.sum_mul]
    _ ≤ Mt * max C 0 := mul_le_mul_of_nonneg_right (hcM.trans hMle) (le_max_right _ _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorBijectiveFiniteTranslationCombin
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RamBij

variable {D : D7}

def contAutSub (S : HSp D) : Submodule ℂ (GA D S → ℂ) where
  carrier := {φ | IsContAut S φ}
  add_mem' ha hb := ⟨fun γ hγ g => by simp [ha.1 γ hγ g, hb.1 γ hγ g], ha.2.add hb.2⟩
  zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
  smul_mem' c φ h := ⟨fun γ hγ g => by simp [h.1 γ hγ g], h.2.const_smul c⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem formAt_eq (β : Frame p S n) (P : Pair k n) {φ : Form k n (GA D S → ℂ)} (hφ : φ ∈ EqForm β.rep) :
    formAt β P (φ P) = φ := by
  funext P₁
  have h := Classical.epsilon_spec (p := fun g : GL n k => g • P = P₁) (MulAction.exists_smul_eq (GL n k) P P₁)
  show β.rep _ (φ P) = φ P₁
  rw [← hφ, h]

theorem sum_single_sum (β : Frame p S n) {ι : Type} (s : Finset ι) (g : ι → GL n k) (a : ι → ℂ)
    (φ₀ : GA D S → ℂ) :
    (∑ i ∈ s, Finsupp.single (g i) (a i)).sum (fun h b => b • β.rep h φ₀) = ∑ i ∈ s, a i • β.rep (g i) φ₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finsupp.sum_add_index' (h := fun h b => b • β.rep h φ₀) (fun h => zero_smul ℂ (β.rep h φ₀)) (fun h _ _ => add_smul _ _ (β.rep h φ₀)), Finsupp.sum_single_index (h := fun h b => b • β.rep h φ₀) (zero_smul ℂ _), ih]

section Ops

variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (β : Frame p S n)

theorem isRam_diaFFStar (hO : OperatorIdentities k n (GA D S → ℂ) q χ) {φ : Form k n (GA D S → ℂ)}
    (hφ : IsRam β φ) : IsRam β (dia ε (FFStar q χ φ)) := by
  refine ⟨dia_mem_EqForm ε (FFStar_mem_EqForm q χ hφ.1), hO.dia_mem_ram ε _ (hO.FFStar_mem_ram _ hφ.2.1),
    fun P' => ?_⟩
  rw [dia_apply, FFStar_apply]
  exact (contAutSub S).sum_mem fun P₁ _ => (contAutSub S).smul_mem _ (hφ.2.2 P₁)

theorem isRam_FFdia (hO : OperatorIdentities k n (GA D S → ℂ) q χ) (c : ℂ) {φ : Form k n (GA D S → ℂ)}
    (hφ : IsRam β φ) : IsRam β (c • FF q χ (dia ε⁻¹ φ)) := by
  refine ⟨(EqForm β.rep).smul_mem c (FF_mem_EqForm q χ (dia_mem_EqForm _ hφ.1)),
    (Mram k n _).smul_mem c (hO.FF_mem_ram _ (hO.dia_mem_ram _ _ hφ.2.1)), fun P' => ?_⟩
  rw [Pi.smul_apply, FF_apply]
  refine (contAutSub S).smul_mem c ((contAutSub S).sum_mem fun Q _ => (contAutSub S).smul_mem _ ?_)
  rw [dia_apply]
  exact hφ.2.2 _

theorem diaFFStar_inv (hO : OperatorIdentities k n (GA D S → ℂ) q χ) {φ : Form k n (GA D S → ℂ)}
    (h : φ ∈ Mram k n (GA D S → ℂ)) :
    dia ε (FFStar q χ (((resCard k : ℂ) ^ Fintype.card n)⁻¹ • FF q χ (dia ε⁻¹ φ))) = φ := by
  have hqr : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ GlobalTheory.PairOp.resCard_ne_zero
  rw [map_smul, map_smul, hO.FFStar_FF_ram _ (hO.dia_mem_ram _ _ h), map_smul, smul_smul, inv_mul_cancel₀ hqr,
    one_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem diaFFStar_inj (hO : OperatorIdentities k n (GA D S → ℂ) q χ) {φ φ' : Form k n (GA D S → ℂ)}
    (h : φ ∈ Mram k n (GA D S → ℂ)) (h' : φ' ∈ Mram k n (GA D S → ℂ))
    (he : dia ε (FFStar q χ φ) = dia ε (FFStar q χ φ')) : φ = φ' := by
  have hqr : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ GlobalTheory.PairOp.resCard_ne_zero
  have h2 : FF q χ (dia ε⁻¹ (dia ε (FFStar q χ φ))) = FF q χ (dia ε⁻¹ (dia ε (FFStar q χ φ'))) := by rw [he]
  have hd : ∀ X : Form k n (GA D S → ℂ), dia ε⁻¹ (dia ε X) = X := fun X => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hd, hd, hO.FF_FFStar_ram _ h, hO.FF_FFStar_ram _ h'] at h2
  exact smul_right_injective _ hqr h2

end Ops

theorem ramBijective_at (q : Unif k) (χ₀ : AddChar k Circle) (hχ : HasConductor χ₀ 1) (ε : 𝓀[k]ˣ)
    (β : Frame p S n) (P : Pair k n) :
    Set.BijOn (sOp β P q (resChar χ₀ hχ q) ε) {φ₀ | RamAt β P φ₀} {φ₀ | RamAt β P φ₀} ∧
      (∀ φ, IsRam β φ → IsRam β (dia ε (FFStar q (resChar χ₀ hχ q) φ)) ∧
        sOp β P q (resChar χ₀ hχ q) ε (φ P) = dia ε (FFStar q (resChar χ₀ hχ q) φ) P) ∧
      ∃ c c' : GL n k →₀ ℂ, (∀ φ₀, sOp β P q (resChar χ₀ hχ q) ε φ₀ = c.sum fun g a => a • β.rep g φ₀) ∧
        ∀ φ₀, RamAt β P φ₀ → sOp β P q (resChar χ₀ hχ q) ε (c'.sum fun g a => a • β.rep g φ₀) = φ₀ ∧
          RamAt β P (c'.sum fun g a => a • β.rep g φ₀) := by
  set χ := resChar χ₀ hχ q with hχdef
  have hO : OperatorIdentities k n (GA D S → ℂ) q χ :=
    ((GlobalTheory.PairOp.pairOperatorStatement k q χ₀ hχ n).1 (GA D S → ℂ)).2
  set r : ℂ := ((resCard k : ℂ) ^ Fintype.card n)⁻¹ with hr

  have hval : ∀ φ, IsRam β φ → sOp β P q χ ε (φ P) = dia ε (FFStar q χ φ) P := fun φ hφ => by
    show dia ε (FFStar q χ (formAt β P (φ P))) P = _
    rw [formAt_eq β P hφ.1]

  have hinv : ∀ φ, IsRam β φ → sOp β P q χ ε ((r • FF q χ (dia ε⁻¹ φ)) P) = φ P := fun φ hφ => by
    rw [hval _ (isRam_FFdia q χ ε β hO r hφ), diaFFStar_inv q χ ε hO hφ.2.1]
  let gch : Pair k n → GL n k := fun P₁ => Classical.epsilon fun g : GL n k => g • P = P₁
  refine ⟨⟨?_, ?_, ?_⟩, fun φ hφ => ⟨isRam_diaFFStar q χ ε β hO hφ, hval φ hφ⟩,
    ∑ P₁ ∈ withKer (ε • P).lat, Finsupp.single (gch P₁) (χ (-cross q P₁ (ε • P))),
    ∑ Q ∈ withLat P.ker, Finsupp.single (gch (ε⁻¹ • Q)) (r * χ (cross q P Q)), fun φ₀ => ?_, fun φ₀ hφ₀ => ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨_, isRam_diaFFStar q χ ε β hO hφ, (hval φ hφ).symm⟩
  · rintro _ ⟨φ, hφ, rfl⟩ _ ⟨φ', hφ', rfl⟩ he
    rw [hval φ hφ, hval φ' hφ'] at he
    have hX := isRam_diaFFStar q χ ε β hO hφ
    have hX' := isRam_diaFFStar q χ ε β hO hφ'
    have he' : dia ε (FFStar q χ φ) = dia ε (FFStar q χ φ') := by
      rw [← formAt_eq β P hX.1, ← formAt_eq β P hX'.1, he]
    rw [diaFFStar_inj q χ ε hO hφ.2.1 hφ'.2.1 he']
  · rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨_, ⟨_, isRam_FFdia q χ ε β hO r hφ, rfl⟩, hinv φ hφ⟩
  · rw [sum_single_sum]
    rfl
  · obtain ⟨φ, hφ, rfl⟩ := hφ₀
    have hc : (∑ Q ∈ withLat P.ker, Finsupp.single (gch (ε⁻¹ • Q)) (r * χ (cross q P Q))).sum
        (fun g a => a • β.rep g (φ P)) = (r • FF q χ (dia ε⁻¹ φ)) P := by
      rw [sum_single_sum, Pi.smul_apply, FF_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun Q _ => ?_
      rw [smul_smul, dia_apply]
      conv_rhs => rw [← formAt_eq β P hφ.1]
      rfl
    rw [hc]
    exact ⟨hinv φ hφ, _, isRam_FFdia q χ ε β hO r hφ, rfl⟩

end GlobalTheory.FinPl.RamBij

namespace GlobalTheory.FinPl

theorem ramBijective_holds : ∀ D : D7, GlobalTheory.FinPl.RamBijective D := by
  intro D k _ _ _ _ p n _ _ q χ₀ hχ χ hχeq ε S β P
  subst hχeq
  exact RamBij.ramBijective_at q χ₀ hχ ε β P

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFlagUnipotentIsotropicBlockUnitriangular
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.RatBlock

variable {D : D7}

theorem blockX_mem_UX {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {n : GA D V} (hn : n ∈ flagN d) :
    ∃ u ∈ UX D ρ, blockX d n = u.1 := by
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D V V₀ ρ d).1 n).1 hn
  have h1 : mt V (d.levi u * (d.nB b * d.nC c)) ⬝ d.jX = d.jX ⬝ u.1 := by
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]
  refine ⟨u, hu, ?_⟩
  rw [blockX, h1, ← Matrix.mul_assoc d.pX d.jX, d.pX_jX, Matrix.one_mul]

theorem blockX_col_of_fix {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {g : GA D V} (k : Fin ρ)
    (h : g ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => k)) (i : Fin ρ) :
    blockX d g i k = (1 : Mx D ρ ρ) i k := by
  have hcol : ∀ l, (mt V g ⬝ d.jX) l k = d.jX l k := fun l => by
    have := congrFun (congrFun (mem_fixer.1 h) l) 0
    simpa [Matrix.mul_apply, Matrix.submatrix_apply] using this
  rw [← d.pX_jX, blockX, Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [hcol l]

end GlobalTheory.Unf.RatBlock


open GlobalTheory.Unf.RatBlock in
theorem GlobalTheory.Unf.ratBlock_unitri : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (γ : GA D V), γ ∈ GQ V → γ ∈ flagN d → ∃ u u' : Matrix (Fin ρ) (Fin ρ) D.host.E, (rat u : Mx D ρ ρ) = blockX d γ ∧ u * u' = 1 ∧ u' * u = 1 ∧ (∀ i, u i i = 1) ∧ (∀ i k, k < i → u i k = 0) ∧ ∀ j : Fin ρ, γ ∈ Nfix d j → ∀ i k, k ≤ j → u i k = if i = k then 1 else 0 := by
  intro D V V₀ ρ d γ hq hn
  obtain ⟨M, hM⟩ := (mem_GQ_iff V γ).1 hq
  have hM' : rat M = mt V γ := hM
  have hb : (rat (d.qX * (M * d.e)) : Mx D ρ ρ) = blockX d γ := by
    rw [blockX, ← hM', rat_mul, rat_mul]; rfl
  obtain ⟨v, hv, hvb⟩ := blockX_mem_UX d hn
  have hent : ∀ i k, incA D ((d.qX * (M * d.e)) i k) = v.1 i k := fun i k => by
    have := congrFun (congrFun (hb.trans hvb) i) k
    exact this
  have hdiag : ∀ i, (d.qX * (M * d.e)) i i = 1 := fun i =>
    incA_injective (by rw [map_one, hent]; exact ((mem_UX.1 hv) i i).2)
  have hlow : ∀ i k, k < i → (d.qX * (M * d.e)) i k = 0 := fun i k hki =>
    incA_injective (by rw [map_zero, hent]; exact ((mem_UX.1 hv) i k).1 hki)
  have hdet : (d.qX * (M * d.e)).det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i k (hki : k < i) => hlow i k hki)]
    simp [hdiag]
  have hu : IsUnit (d.qX * (M * d.e)).det := by rw [hdet]; exact isUnit_one
  refine ⟨d.qX * (M * d.e), (d.qX * (M * d.e))⁻¹, hb, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu,
    hdiag, hlow, fun j hj i k hkj => ?_⟩
  have hfix : γ ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => k) := by
    have h2 := (Subgroup.mem_inf.1 hj).2
    exact (Subgroup.mem_iInf.1 h2) ⟨k, hkj⟩
  apply incA_injective
  have e1 := blockX_col_of_fix d k hfix i
  rw [← hb] at e1
  change incA D _ = _ at e1
  rw [e1, Matrix.one_apply]
  split_ifs <;> simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFramesSameGramOneUnitaryOrbit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.WittOrbit
variable {D : D7}

theorem isQA_sig (D : D7) : GlobalTheory.SgAlg.IsQA (D.sp.cm.sig : D.host.E →+* D.host.E) := by
  refine ⟨fun x => star_star x, ?_, inferInstance, ?_, fun x _ hx => isUnit_iff_ne_zero.2 hx⟩
  · by_contra h
    push_neg at h
    have hbot : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ :=
      eq_top_iff.2 fun x _ => Algebra.mem_bot.2 ((D.sp.cm.fixed x).1 (h x))
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 hbot
    rw [D.sp.cm.deg2] at h1
    exact absurd h1 (by norm_num)
  · exact isUnit_iff_ne_zero.2 two_ne_zero

theorem free_of_li {n ρ : ℕ} (x : Matrix (Fin n) (Fin ρ) D.host.E) (h : LinearIndependent D.host.E x.transpose) :
    GlobalTheory.SgAlg.Free x := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' x)
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem isUnit_of_unitary (W : HSp D) {g : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (h : gᴴ * W.gram * g = W.gram) : IsUnit g := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact gram_det_ne W this.symm

theorem orb_eq_orbit : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E),
    LinearIndependent D.host.E x₀.transpose →
      (∀ x ∈ Orb W x₀, ∃ γ ∈ GQ W, mt W γ ⬝ (rat x₀ : Mx D W.rank ρ) = rat x) ∧
        ∀ γ ∈ GQ W, ∀ x ∈ Orb W x₀, ∃ x' ∈ Orb W x₀, mt W γ ⬝ (rat x : Mx D W.rank ρ) = rat x' := by
  intro D W ρ x₀ h₀
  have hJ : GlobalTheory.SgAlg.IsHermU (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram :=
    ⟨gram_conjTranspose W, gram_isUnit_det W⟩
  refine ⟨fun x hx => ?_, fun γ hγ x hx => ?_⟩
  · obtain ⟨g, hg, hgx⟩ := GlobalTheory.SgAlg.witt_free_field _ (isQA_sig D) W.gram hJ x₀ x (free_of_li x₀ h₀)
      (free_of_li x hx.1) (by
        show x₀ᴴ * W.gram * x₀ = xᴴ * W.gram * x
        rw [Matrix.mul_assoc, Matrix.mul_assoc]
        exact hx.2.symm)
    have hg' : gᴴ * W.gram * g = W.gram := hg
    have hu : adj (rat g) * (gA W * rat g) = gA W := by
      rw [← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, ← Matrix.mul_assoc, hg']
    refine ⟨ofMat W (rat g) hu, (mem_GQ_iff W _).2 ⟨g, rfl⟩, ?_⟩
    rw [mt_ofMat, ← rat_mul, hgx]
  · obtain ⟨g, hg⟩ := (mem_GQ_iff W γ).1 hγ
    replace hg : rat g = mt W γ := hg
    have hu : gᴴ * W.gram * g = W.gram := rat_injective (by
      rw [rat_mul, rat_mul, rat_conjTranspose, hg]
      exact mt_rel W γ)
    have hgu := isUnit_of_unitary W hu
    refine ⟨g * x, ⟨?_, ?_⟩, by rw [← hg, ← rat_mul]⟩
    · refine Matrix.mulVec_injective_iff.1 ?_
      intro v w hvw
      simp only [← Matrix.mulVec_mulVec] at hvw
      exact Matrix.mulVec_injective_iff.2 hx.1 (Matrix.mulVec_injective_iff_isUnit.2 hgu hvw)
    · show (g * x)ᴴ * (W.gram * (g * x)) = gramQ W x₀
      rw [← hx.2, gramQ, Matrix.conjTranspose_mul]
      calc xᴴ * gᴴ * (W.gram * (g * x)) = xᴴ * ((gᴴ * W.gram * g) * x) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hu]

end GlobalTheory.WittOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharacterDetLatticeStabilizerEqOneStatement
section
open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule 𝒪[k] (n → k)), L.IsFullLattice k → ∀ g ∈ latStab L, ∀ μ : kˣ →* ℂˣ, IsUnram μ → μ (Matrix.GeneralLinearGroup.det g) = 1 := by
  intro k _ _ _ _ n _ _ L hL g hg μ hμ
  letI := hL
  exact GlobalTheory.LatPair.Det.isUnram_det_latStab k n L inferInstance g hg μ hμ
end

