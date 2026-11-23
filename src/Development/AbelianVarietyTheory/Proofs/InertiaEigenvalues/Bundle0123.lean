module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowSubOneOfNotDvd
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Cyc

theorem geom_sum_one_add_expand {R : Type*} [CommRing R] (y : R) (n : ℕ) :
    ∃ z : R, (1 + y) ^ n - 1 = y * ((n : R) + (n.choose 2 : ℕ) * y + y ^ 2 * z) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨z + (n.choose 2 : ℕ) + y * z, ?_⟩
    have h : (1 + y) ^ n = 1 + y * ((n : R) + (n.choose 2 : ℕ) * y + y ^ 2 * z) := by
      rw [← hz]; ring
    have hc : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    rw [pow_succ, h, hc]
    push_cast
    ring

variable {l : ℕ} [hl : Fact l.Prime]

theorem padicInt_norm_add_eq_of_lt {a b : ℤ_[l]} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [PadicInt.norm_add_eq_max_of_ne h.ne', max_eq_left h.le]

theorem norm_pow_sub_one_of_not_dvd (x : ℤ_[l]) (hx : ‖x - 1‖ < 1) (n : ℕ) (hn : ¬ l ∣ n) :
    ‖x ^ n - 1‖ = ‖x - 1‖ := by
  obtain ⟨z, hz⟩ := geom_sum_one_add_expand (x - 1) n
  rw [add_sub_cancel] at hz
  have hn1 : ‖(n : ℤ_[l])‖ = 1 := by
    apply le_antisymm (PadicInt.norm_le_one _)
    by_contra h
    push_neg at h
    have h' : ‖((n : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
    rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
    exact hn (Int.natCast_dvd_natCast.mp h')
  have e : (n : ℤ_[l]) + (n.choose 2 : ℕ) * (x - 1) + (x - 1) ^ 2 * z
      = n + (x - 1) * ((n.choose 2 : ℕ) + (x - 1) * z) := by ring
  rw [hz, norm_mul, e, padicInt_norm_add_eq_of_lt, hn1, mul_one]
  rw [hn1, norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)) hx

theorem norm_pow_prime_sub_one (x : ℤ_[l]) (hx : ‖x - 1‖ ≤ (l : ℝ)⁻¹)
    (h2 : l = 2 → ‖x - 1‖ < (l : ℝ)⁻¹) :
    ‖x ^ l - 1‖ = ‖x - 1‖ * ‖(l : ℤ_[l])‖ := by
  obtain ⟨z, hz⟩ := geom_sum_one_add_expand (x - 1) l
  rw [add_sub_cancel] at hz
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hi0 : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hi1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hsq : (l : ℝ)⁻¹ * (l : ℝ)⁻¹ < (l : ℝ)⁻¹ := mul_lt_of_lt_one_right hi0 hi1
  have hA : ‖((l.choose 2 : ℕ) : ℤ_[l]) * (x - 1)‖ < (l : ℝ)⁻¹ := by
    rw [norm_mul]
    by_cases h : l = 2
    · exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)) (h2 h)
    · have hlt : 2 < l := lt_of_le_of_ne hl.out.two_le (Ne.symm h)
      obtain ⟨c, hc⟩ := hl.out.dvd_choose_self (k := 2) (by norm_num) hlt
      have : ‖((l.choose 2 : ℕ) : ℤ_[l])‖ ≤ (l : ℝ)⁻¹ := by
        rw [hc, Nat.cast_mul, norm_mul, PadicInt.norm_p]
        exact mul_le_of_le_one_right hi0.le (PadicInt.norm_le_one _)
      exact lt_of_le_of_lt (mul_le_mul this hx (norm_nonneg _) hi0.le) hsq
  have hB : ‖(x - 1) ^ 2 * z‖ < (l : ℝ)⁻¹ := by
    rw [norm_mul, sq, norm_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)) ?_
    exact lt_of_le_of_lt (mul_le_mul hx hx (norm_nonneg _) hi0.le) hsq
  rw [hz, norm_mul, add_assoc, padicInt_norm_add_eq_of_lt]
  rw [PadicInt.norm_p]
  exact lt_of_le_of_lt (PadicInt.nonarchimedean _ _) (max_lt hA hB)

theorem norm_pow_nat_sub_one (n : ℕ) (hn : n ≠ 0) : ∀ (x : ℤ_[l]), ‖x - 1‖ ≤ (l : ℝ)⁻¹ →
    (l = 2 → ‖x - 1‖ < (l : ℝ)⁻¹) → ‖x ^ n - 1‖ = ‖x - 1‖ * ‖(n : ℤ_[l])‖ := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hi1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx h2
    by_cases hd : l ∣ n
    · obtain ⟨m, rfl⟩ := hd
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      have hlt : m < l * m := lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm) hl.out.one_lt
      have key := norm_pow_prime_sub_one x hx h2
      have hle : ‖x ^ l - 1‖ ≤ ‖x - 1‖ := by
        rw [key]; exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
      rw [pow_mul, ih m hlt hm (x ^ l) (hle.trans hx) (fun h => hle.trans_lt (h2 h)), key,
        Nat.cast_mul, norm_mul, mul_assoc]
    · have hn1 : ‖(n : ℤ_[l])‖ = 1 := by
        apply le_antisymm (PadicInt.norm_le_one _)
        by_contra h
        push_neg at h
        have h' : ‖((n : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
        rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
        exact hd (Int.natCast_dvd_natCast.mp h')
      rw [norm_pow_sub_one_of_not_dvd x (hx.trans_lt hi1) n hd, hn1, mul_one]

theorem norm_unit_zpow_sub_one :
    ∀ (l : ℕ) [Fact l.Prime], ∀ (s : ℕ) (u : ℤ_[l]ˣ), 1 ≤ s → (l = 2 → 2 ≤ s) →
      ‖(u : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) → ∀ n : ℤ, n ≠ 0 →
      ‖((u ^ n : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) * ‖(n : ℤ_[l])‖ := by
  intro l hl s u hs h2 hu n hn
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hx : ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ)⁻¹ := by
    rw [hu, ← zpow_neg_one]
    exact zpow_le_zpow_right₀ hl1.le (by omega)
  have hx2 : l = 2 → ‖(u : ℤ_[l]) - 1‖ < (l : ℝ)⁻¹ := fun h => by
    have := h2 h
    rw [hu, ← zpow_neg_one]
    exact zpow_lt_zpow_right₀ hl1 (by omega)
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · have hm : m ≠ 0 := by rintro rfl; simp at hn
    rw [zpow_natCast, Units.val_pow_eq_pow_val, norm_pow_nat_sub_one m hm _ hx hx2, hu,
      Int.cast_natCast]
  · have hm : m ≠ 0 := by rintro rfl; simp at hn
    have e : (((u ^ m)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1
        = -((((u ^ m)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (((u ^ m : ℤ_[l]ˣ) : ℤ_[l]) - 1)) := by
      rw [mul_sub, Units.inv_mul]; ring
    rw [zpow_neg, zpow_natCast, e, norm_neg, norm_mul, PadicInt.norm_units, one_mul,
      Units.val_pow_eq_pow_val, norm_pow_nat_sub_one m hm _ hx hx2, hu, Int.cast_neg, norm_neg,
      Int.cast_natCast]

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitalIntegralDescendedEqUnitary
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.DescOrb

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem mulMat_comm (A : Et F E) {r : ℕ} (τ : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (Ax : Matrix (Fin r) (Fin r) E)
    (hA : ∀ z, j (algebraMap A.K A.L τ * z) = Ax *ᵥ j z) (t : A.L) :
    Ax * A.mulMat j t = A.mulMat j t * Ax := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  obtain ⟨z, rfl⟩ := j.surjective v
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Et.mulMat_mulVec_apply, ← hA]
  congr 1; ring

theorem actU_actU {r : ℕ} (g h : unitaryGroup (Fin r) E) (X : Hn r F E) :
    actU g (actU h X) = actU (g * h) X := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · show g.1 * (h.1 * X.1.1 * star h.1) * star g.1 = (g.1 * h.1) * X.1.1 * star (g.1 * h.1)
    rw [star_mul]; simp only [Matrix.mul_assoc]
  · show g.1 *ᵥ (h.1 *ᵥ X.2.1) = (g.1 * h.1) *ᵥ X.2.1
    rw [Matrix.mulVec_mulVec]

end GlobalTheory.JR.DescOrb

namespace GlobalTheory.JR.DescOrb

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_mulMat [hU : Unram F E] (A : Et F E) {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) :
    Continuous fun t : A.L => A.mulMat j t := by
  haveI := hU.lcF
  haveI := EtMeas.finite_L A
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hj : Continuous (j : A.L → Fin r → E) :=
    IsModuleTopology.continuous_of_linearMap ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)
  refine continuous_matrix fun i k => ?_
  simp only [Et.mulMat, LinearMap.toMatrix'_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    LinearEquiv.coe_coe]
  exact (continuous_apply i).comp (hj.comp (continuous_id.mul continuous_const))

theorem orbL_descFn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (τ : A.K) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (hx : A.IsIsom x j) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ (lam : F) (ν : Measure (unitary A.L)), ν.IsHaarMeasure → ∀ (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → (∀ g, 0 ≤ α g) → ∀ Z : Set (Matrix (Fin r) (Fin r) E), (∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * Ax.1 * star g.1 ∈ Z → ∫ t, α (g * (A.uHom hx t)⁻¹) ∂ν = 1) → ∀ f₀ : Hn r F E → ℂ, Continuous f₀ → (∀ X, f₀ X ≠ 0 → X.1.1 ∈ Z) → ∀ y : A.L, (letI := M.mU; Integrable (fun g => f₀ (actU g (Ax, j y, lam))) M.μU) → A.orbL ν (A.descFn M Ax j lam α f₀) y = orbU M f₀ (Ax, j y, lam) := by
  intro F E _ _ _ _ hU A r M τ x j hx Ax hA lam ν hν α hα hα0 Z hZ f₀ hf₀ hf₀Z y hint
  letI := M.mU
  haveI := M.bU
  haveI := M.haarU
  haveI := hU.ultraE; haveI := hU.lcE; haveI := hU.ultraF; haveI := hU.lcF
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : NormedStarGroup E := ⟨fun y => (hU.norm_star y).le⟩
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) E) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → E))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) E) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → E))
  haveI : LocallyCompactSpace (unitaryGroup (Fin r) E) :=
    (isClosed_unitary (R := Matrix (Fin r) (Fin r) E)).locallyCompactSpace
  haveI : SecondCountableTopology (unitaryGroup (Fin r) E) :=
    (isClosed_unitary (R := Matrix (Fin r) (Fin r) E)).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  haveI : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
  haveI : LocallyCompactSpace (unitary A.L) := (isClosed_unitary (R := A.L)).locallyCompactSpace
  haveI : SecondCountableTopology (unitary A.L) :=
    (isClosed_unitary (R := A.L)).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI : SigmaFinite ν := inferInstance
  haveI : SigmaFinite M.μU := inferInstance
  haveI : M.μU.IsMulRightInvariant := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E r).2 M
  have huc : Continuous (A.uHom hx) := continuous_induced_rng.2 ((continuous_mulMat A j).comp continuous_subtype_val)
  have hinvc : Continuous fun g : unitaryGroup (Fin r) E => g⁻¹ := continuous_inv

  set X : Hn r F E := (Ax, j y, lam) with hXdef
  have hcomm : ∀ t : unitary A.L, ((A.uHom hx t : Matrix (Fin r) (Fin r) E)) * Ax.1 = Ax.1 * A.uHom hx t := fun t =>
    (mulMat_comm A τ j Ax.1 hA t).symm
  have hshift : ∀ t : unitary A.L, ((Ax, j (t.1 * y), lam) : Hn r F E) = actU (A.uHom hx t) X := by
    intro t
    refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
    · show Ax.1 = (A.uHom hx t : Matrix (Fin r) (Fin r) E) * Ax.1 * star (A.uHom hx t : Matrix (Fin r) (Fin r) E)
      rw [hcomm, Matrix.mul_assoc, Unitary.mul_star_self_of_mem (A.uHom hx t).2, Matrix.mul_one]
    · show j (t.1 * y) = (A.uHom hx t : Matrix (Fin r) (Fin r) E) *ᵥ j y
      rw [Et.uHom_apply, Et.mulMat_mulVec_apply]
  have step1 : ∀ t : unitary A.L, A.descFn M Ax j lam α f₀ (t.1 * y) =
      ∫ g, f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ) ∂M.μU := by
    intro t
    have h := integral_mul_right_eq_self (μ := M.μU)
      (fun g => f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ)) (A.uHom hx t)
    simp only [mul_inv_cancel_right] at h
    rw [← h]
    show (∫ g, f₀ (actU g ((Ax, j (t.1 * y), lam) : Hn r F E)) * (α g : ℂ) ∂M.μU) = _
    simp only [hshift t, actU_actU]
  have hact : Continuous fun g : unitaryGroup (Fin r) E => actU g X := by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ continuous_const)
    · exact (((continuous_subtype_val.matrix_mul continuous_const).matrix_mul
        (continuous_subtype_val.star))).subtype_mk _
    · exact continuous_subtype_val.matrix_mulVec continuous_const
  have hcont : Continuous (Function.uncurry fun (t : unitary A.L) (g : unitaryGroup (Fin r) E) =>
      f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ)) :=
    (hf₀.comp (hact.comp continuous_snd)).mul (Complex.continuous_ofReal.comp
      (hα.continuous.comp (continuous_snd.mul (hinvc.comp (huc.comp continuous_fst)))))
  have hαint : ∀ g : unitaryGroup (Fin r) E, f₀ (actU g X) ≠ 0 →
      Integrable (fun t => α (g * (A.uHom hx t)⁻¹)) ν := by
    intro g hg
    by_contra hn
    have h1 := integral_undef hn
    rw [hZ g (hf₀Z _ hg)] at h1
    exact one_ne_zero h1
  have hInt : Integrable (Function.uncurry fun (t : unitary A.L) (g : unitaryGroup (Fin r) E) =>
      f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ)) (ν.prod M.μU) := by
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun g => ?_, ?_⟩
    · by_cases hg : f₀ (actU g X) = 0
      · simp [Function.uncurry, hg]
      · exact ((hαint g hg).ofReal).const_mul (f₀ (actU g X))
    · refine hint.norm.congr (Eventually.of_forall fun g => ?_)
      simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [integral_const_mul]
      by_cases hg : f₀ (actU g X) = 0
      · simp [hg]
      · rw [integral_congr_ae (Eventually.of_forall fun t => abs_of_nonneg (hα0 _)), hZ g (hf₀Z _ hg), mul_one]
  show ∫ t : unitary A.L, A.descFn M Ax j lam α f₀ (t.1 * y) ∂ν = ∫ g, f₀ (actU g X) ∂M.μU
  simp_rw [step1]
  rw [integral_integral_swap hInt]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  rw [integral_const_mul, integral_complex_ofReal]
  by_cases hg : f₀ (actU g X) = 0
  · simp [hg]
  · rw [hZ g (hf₀Z _ hg)]; simp

end GlobalTheory.JR.DescOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PiExteriorTensorFlattenedIndexEquivNested
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages

noncomputable section

open PiTensorProduct Module
open scoped TensorProduct

namespace GlobalTheory.JacStages

section SigmaCurry

variable {α : Type} [DecidableEq α] {β : α → Type} [∀ a, DecidableEq (β a)]
  (M : (Σ a, β a) → Type) [∀ p, AddCommGroup (M p)] [∀ p, Module ℂ (M p)]

theorem tprod_tprod_update_sigma [DecidableEq (Σ a, β a)] (x : ∀ p, M p) (a₀ : α) (b₀ : β a₀)
    (v : M ⟨a₀, b₀⟩) :
    (fun a => tprod ℂ fun b => Function.update x ⟨a₀, b₀⟩ v ⟨a, b⟩) =
      Function.update (fun a => tprod ℂ fun b => x ⟨a, b⟩) a₀
        (tprod ℂ (Function.update (fun b => x ⟨a₀, b⟩) b₀ v)) := by
  funext a
  by_cases h : a = a₀
  · subst h
    rw [Function.update_self]
    congr 1
    funext b
    by_cases hb : b = b₀
    · subst hb
      simp
    · rw [Function.update_of_ne hb, Function.update_of_ne]
      intro h'
      exact hb (eq_of_heq (Sigma.mk.inj h').2)
  · rw [Function.update_of_ne h]
    congr 1
    funext b
    rw [Function.update_of_ne]
    intro h'
    exact h (congrArg Sigma.fst h')

def curryML : (∀ p, M p) →ₘₗ[ℂ] ⨂[ℂ] a, ⨂[ℂ] b, M ⟨a, b⟩ where
  toFun x := tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩
  map_update_add' x p v w := by
    obtain ⟨a₀, b₀⟩ := p
    simp only [tprod_tprod_update_sigma]
    rw [MultilinearMap.map_update_add, MultilinearMap.map_update_add]
  map_update_smul' x p c v := by
    obtain ⟨a₀, b₀⟩ := p
    simp only [tprod_tprod_update_sigma, MultilinearMap.map_update_smul, RingHom.id_apply]

theorem curryML_apply (x : ∀ p, M p) : curryML M x = tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := rfl

variable [Finite α] [∀ a, Finite (β a)]

def sigBasis : Basis (∀ p, Free.ChooseBasisIndex ℂ (M p)) ℂ (⨂[ℂ] p, M p) :=
  Basis.piTensorProduct fun p => Free.chooseBasis ℂ (M p)

def nestBasis : Basis (∀ a b, Free.ChooseBasisIndex ℂ (M ⟨a, b⟩)) ℂ (⨂[ℂ] a, ⨂[ℂ] b, M ⟨a, b⟩) :=
  Basis.piTensorProduct fun a => Basis.piTensorProduct fun b => Free.chooseBasis ℂ (M ⟨a, b⟩)

def sigmaCurry : (⨂[ℂ] p, M p) ≃ₗ[ℂ] ⨂[ℂ] a, ⨂[ℂ] b, M ⟨a, b⟩ :=
  (sigBasis M).equiv (nestBasis M) (Equiv.piCurry fun a b => Free.ChooseBasisIndex ℂ (M ⟨a, b⟩))

theorem sigmaCurry_eq_lift : (sigmaCurry M : (⨂[ℂ] p, M p) →ₗ[ℂ] _) = lift (curryML M) := by
  apply (sigBasis M).ext
  intro q
  rw [LinearEquiv.coe_coe, sigmaCurry, Basis.equiv_apply]
  simp only [sigBasis, nestBasis, Basis.piTensorProduct_apply, lift.tprod, curryML_apply]
  rfl

@[simp] theorem sigmaCurry_tprod (x : ∀ p, M p) :
    sigmaCurry M (tprod ℂ x) = tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := by
  have h := LinearMap.congr_fun (sigmaCurry_eq_lift M) (tprod ℂ x)
  simpa [curryML_apply] using h

end SigmaCurry

section Flat

variable {s : ℕ} {t : Fin s → ℕ}

def flatTensorEquiv (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)] :
    (⨂[ℂ] c : Fin (∑ a, t a), Y (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) ≃ₗ[ℂ]
      ⨂[ℂ] a, ⨂[ℂ] b, Y a b :=
  (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv).symm.trans
    (sigmaCurry fun p : Σ a, Fin (t a) => Y p.1 p.2)

theorem flatTensorEquiv_reindex_tprod (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)]
    [∀ a b, Module ℂ (Y a b)] (x : ∀ p : Σ a, Fin (t a), Y p.1 p.2) :
    flatTensorEquiv Y (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv (tprod ℂ x)) =
      tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := by
  rw [flatTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, sigmaCurry_tprod]

theorem flatTensorEquiv_tprod (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)]
    [∀ a b, Module ℂ (Y a b)] (x : ∀ p : Σ a, Fin (t a), Y p.1 p.2) :
    flatTensorEquiv Y (tprod ℂ fun c => x (finSigmaFinEquiv.symm c)) =
      tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := by
  rw [← flatTensorEquiv_reindex_tprod, reindex_tprod]

theorem piTensor_flatHom_equiv : ∀ (s : ℕ) (t : Fin s → ℕ) (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)]
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ : ∀ a b, Representation ℂ (Γ a b) (Y a b)),
    Nonempty (Representation.Equiv ((piTensor fun c : Fin (∑ a, t a) =>
        ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).comp (flatHom Γ))
      (piTensor fun a => piTensor (ρ a))) := by
  intro s t Γ _ Y _ _ ρ
  refine ⟨Representation.Equiv.mk (flatTensorEquiv Y) fun g => ?_⟩
  have key : ∀ w : ⨂[ℂ] p : Σ a, Fin (t a), Y p.1 p.2,
      flatTensorEquiv Y (((piTensor fun c : Fin (∑ a, t a) =>
        ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).comp (flatHom Γ)) g
          (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv w)) =
        piTensor (fun a => piTensor (ρ a)) g
          (flatTensorEquiv Y (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv w)) := by
    intro w
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      simp only [map_smul]
      congr 1
      rw [flatTensorEquiv_reindex_tprod, piTensor_tprod]
      simp only [piTensor_tprod]
      rw [reindex_tprod, MonoidHom.comp_apply, piTensor_tprod]
      exact flatTensorEquiv_tprod Y fun p => ρ p.1 p.2 (g p.1 p.2) (x p)
    | add w w' hw hw' =>
      simp only [map_add (f := _)]
      rw [hw, hw']
  refine LinearMap.ext fun v => ?_
  obtain ⟨w, rfl⟩ := (reindex ℂ (fun p : Σ a, Fin (t a) => Y p.1 p.2) finSigmaFinEquiv).surjective v
  exact key w

end Flat

end GlobalTheory.JacStages
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilUnipotentTorusPreserveTest
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem isLocallyConstant_of_stdChar {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : IsLocallyConstant ψ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  filter_upwards [Metric.closedBall_mem_nhds a one_pos] with b hb
  have h1 : ψ (b - a) = 1 := hψ.1 _ (by simpa [Metric.mem_closedBall, dist_eq_norm] using hb)
  calc ψ b = ψ (a + (b - a)) := by rw [add_sub_cancel]
    _ = ψ a := by rw [AddChar.map_add_eq_mul, h1, mul_one]

theorem continuous_mulLeft (A : Et F E) (c : A.L) : Continuous fun y : A.L => c * y := by
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  exact IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft F c)

def smulHomeo (A : Et F E) (s : A.Kˣ) : A.L ≃ₜ A.L where
  toFun y := (s : A.K) • y
  invFun y := ((s⁻¹ : A.Kˣ) : A.K) • y
  left_inv y := by simp [smul_smul]
  right_inv y := by simp [smul_smul]
  continuous_toFun := by
    simp only [Algebra.smul_def]; exact continuous_mulLeft A _
  continuous_invFun := by
    simp only [Algebra.smul_def]; exact continuous_mulLeft A _

theorem isTest_nOp [Unram F E] (A : Et F E) {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (x z : A.K) {φ : A.L → ℂ}
    (hφ : IsTest φ) : IsTest (nOp A ψ x z φ) := by
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun y : A.L => Algebra.trace F A.K (z * x * A.NL y) :=
    htr.comp (continuous_const.mul (GlobalTheory.JR.EtMeas.continuous_NL A))
  have hl : IsLocallyConstant fun y : A.L => A.psiK ψ (z * x * A.NL y) :=
    (isLocallyConstant_of_stdChar hψ).comp_continuous hc
  exact ⟨hl.mul hφ.1, hφ.2.mul_left⟩

theorem isTest_mOp (A : Et F E) (ω : A.K → ℂ) (s : A.Kˣ) {φ : A.L → ℂ} (hφ : IsTest φ) :
    IsTest (mOp A ω s φ) := by
  have h1 : IsTest (φ ∘ smulHomeo A s) :=
    ⟨hφ.1.comp_continuous (smulHomeo A s).continuous, hφ.2.comp_homeomorph _⟩
  exact ⟨(IsLocallyConstant.const (ω s * (A.absK s : ℂ))).mul h1.1, h1.2.mul_left⟩

theorem isTest_nOp_mOp : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ),
    Hyp A ψ x μ ω → ∀ φ : A.L → ℂ, IsTest φ → (∀ z, IsTest (nOp A ψ x z φ)) ∧ ∀ s, IsTest (mOp A ω s φ) := by
  intro F E _ _ _ _ _ A ψ x μ ω h φ hφ
  exact ⟨fun z => isTest_nOp A h.2.2.1 x z hφ, fun s => isTest_mOp A ω s hφ⟩

end GlobalTheory.JR.WeilQuad
end
end

