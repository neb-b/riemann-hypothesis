module

public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.Bundle0007
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreSupp
public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0054

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreStar
section
noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem star_inj_quot {M T : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T]
    (D : Module.End ℂ M) (D' : Module.End ℂ T) (π : M →ₗ[ℂ] T) (hπ : ∀ x, D' (π x) = π (D x))
    (Y : Submodule ℂ M) [FiniteDimensional ℂ Y] (hY : ∀ y ∈ Y, D y ∈ Y) (hi : ∀ y ∈ Y, D y = 0 → y = 0)
    {y : M} (hy : y ∈ Y) (h0 : D' (π y) = 0) : π y = 0 := by
  let Z : Submodule ℂ M := Y ⊓ LinearMap.ker π
  haveI : FiniteDimensional ℂ Z := Submodule.finiteDimensional_of_le (S₂ := Y) inf_le_left
  have hZ : ∀ z ∈ Z, D z ∈ Z := by
    intro z hz
    refine ⟨hY z hz.1, ?_⟩
    have h2 : π z = 0 := hz.2
    show π (D z) = 0
    rw [← hπ, h2, map_zero]
  have hinj : Function.Injective (D.restrict hZ) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    have h3 : D z.1 = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hz)
    exact Subtype.ext (hi z.1 z.2.1 h3)
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  have hDy : D y ∈ Z := ⟨hY y hy, by
    show π (D y) = 0
    rw [← hπ, h0]⟩
  obtain ⟨z, hz⟩ := hsurj ⟨D y, hDy⟩
  have hz' : D z.1 = D y := congrArg Subtype.val hz
  have h4 : y - z.1 = 0 := hi _ (Y.sub_mem hy z.2.1) (by rw [map_sub, hz', sub_self])
  have h5 : y = z.1 := sub_eq_zero.1 h4
  rw [h5]
  exact z.2.2

theorem star_casK_mem {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    {ρ : Ix r s → Ix r s → Module.End ℂ M} {Y : Submodule ℂ M} (hY : KSt ρ Y) {y : M} (hy : y ∈ Y) :
    casK ρ y ∈ Y := by
  unfold casK
  rw [LinearMap.sum_apply]
  refine Y.sum_mem fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Y.sum_mem fun b _ => ?_
  split_ifs with h
  · exact hY a b h _ (hY b a (PI.FHS.sameBlock_symm h) _ hy)
  · simp

theorem star_trace {r s : ℕ} (a b : Ix r s) : (Eab a b).trace = if a = b then 1 else 0 := by
  unfold Eab
  split_ifs with h
  · subst h; simp
  · exact Matrix.trace_single_eq_of_ne _ _ _ h

theorem star_tw {p q r s : ℕ} (τ : ℂ) (a b : Ix r s) (g : Pol p q r s) :
    units (twAct p q r s τ) a b g =
      units (fockAct2 p q r s) a b g + (if a = b then τ else 0) • g := by
  unfold units
  rw [twAct_apply, star_trace]
  split_ifs <;> simp

theorem star_cas_mk {p q r s : ℕ} (c τ : ℂ) (g : Pol p q r s) :
    casK (units (thAct p q r s c τ)) (thMkC p q r s c g) =
      thMkC p q r s c (casK (units (twAct p q r s τ)) g) := by
  unfold casK
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · simp only [Module.End.mul_apply, units, thAct_mk]
  · simp

theorem star_sb_refl {r s : ℕ} (a : Ix r s) : sameBlock a a := by
  cases a <;> trivial

theorem star_th {p q r s : ℕ} (c τ : ℂ) (c0 τ0 : ℚ) (hc : c = c0) (hτ : τ = τ0) (La : Ix r s → ℚ)
    (hC : CombOK p q c0 τ0 La) (d0 : ℕ) (hd : (d0 : ℚ) = degW (cPair r s) (fun _ : Ix p q => c0)) :
    StarK (thAct p q r s c τ) ((homog (Ix p q × Ix r s) d0).map (thMkC p q r s c))
      ((casW (fun x => La x + τ0) : ℚ) : ℝ) := by
  intro t ht x hx hcas
  let Y : Submodule ℂ (Pol p q r s) :=
    harm1 p q r s ⊓ polChi p q r s c ⊓ homog (Ix p q × Ix r s) (d0 + 2)
  haveI : FiniteDimensional ℂ (homog (Ix p q × Ix r s) (d0 + 2)) :=
    Module.Finite.iff_fg.2 (homogeneousSubmodule_fg _ ℂ (d0 + 2))
  haveI : FiniteDimensional ℂ Y :=
    Submodule.finiteDimensional_of_le (S₂ := homog (Ix p q × Ix r s) (d0 + 2)) inf_le_right
  have hYK : KSt (units (fockAct2 p q r s)) Y := fun a b hab y hy =>
    ⟨⟨harmonic_stable_second_action a b hab y hy.1.1, polChi_stable_second_action c _ hy.1.2⟩, homogeneous_stable_second_action (d0 + 2) a b hab y hy.2⟩
  have hYT : KSt (units (twAct p q r s τ)) Y := by
    intro a b hab y hy
    rw [star_tw]
    exact Y.add_mem (hYK a b hab y hy) (Y.smul_mem _ hy)
  have hgl : GlK (units (twAct p q r s τ)) := glK_of_lie (lie_tw p q r s τ)

  have hx1 : x ∈ (homog (Ix p q × Ix r s) (d0 + 2)).map (thMkC p q r s c) := by
    refine Submodule.span_le.2 ?_ hx
    rintro _ ⟨a, b, hab, _, ⟨g, hg, rfl⟩, rfl⟩
    have hne : a ≠ b := by
      rintro rfl
      exact hab (star_sb_refl a)
    have hlow : thMkC p q r s c (PI.FockOneDegW.lowOp (p := p) (q := q) a b g) = 0 := by
      by_cases h2 : d0 < 2
      · rw [low_homog_small a b h2 hg, map_zero]
      · obtain ⟨e, rfl⟩ : ∃ e, d0 = e + 2 := ⟨d0 - 2, by omega⟩
        refine th_small c c0 hc e ?_ (low_homog a b hg)
        rw [← hd]; push_cast; linarith
    refine ⟨_, second_action_add_lowering hab hg, ?_⟩
    rw [map_add (f := _), hlow, add_zero, thAct_mk, twAct_apply, star_trace, if_neg hne]
    simp
  obtain ⟨y, hy, rfl⟩ := th_next c c0 hc d0 hd hx1
  let D : Module.End ℂ (Pol p q r s) := casK (units (twAct p q r s τ)) - (t : ℂ) • 1
  have hD : ∀ g, D g = casK (units (twAct p q r s τ)) g - (t : ℂ) • g := fun g => rfl
  refine star_inj_quot D (casK (units (thAct p q r s c τ)) - (t : ℂ) • 1) (thMkC p q r s c) ?_ Y ?_ ?_ hy ?_
  · intro g
    rw [hD, map_sub, map_smul, ← star_cas_mk]
    rfl
  · intro g hg
    rw [hD]
    exact Y.sub_mem (star_casK_mem hYT hg) (Y.smul_mem _ hg)
  · intro g0 hg0 hDg0
    by_contra hne
    let U : Submodule ℂ (Pol p q r s) := Y ⊓ LinearMap.ker D
    haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le (S₂ := Y) inf_le_left
    have hU0 : U ≠ ⊥ := by
      intro h
      have : g0 ∈ U := ⟨hg0, hDg0⟩
      rw [h] at this
      exact hne ((Submodule.mem_bot ℂ).1 this)
    have hUT : KSt (units (twAct p q r s τ)) U := by
      intro a b hab u hu
      refine ⟨hYT a b hab u hu.1, ?_⟩
      have h1 : D u = 0 := hu.2
      have h2 := LinearMap.congr_fun (cas_comm hgl hab) u
      simp only [Module.End.mul_apply] at h2
      show D _ = 0
      rw [hD] at h1 ⊢
      rw [h2, ← map_smul, ← map_sub, h1, map_zero]
    have hUK : KSt (units (fockAct2 p q r s)) U := by
      intro a b hab u hu
      have h1 := U.sub_mem (hUT a b hab u hu) (U.smul_mem (if a = b then τ else 0) hu)
      rw [star_tw, add_sub_cancel_right] at h1
      exact h1
    obtain ⟨ν, g, hgU, hw⟩ := hwExist2 U hU0 hUK
    obtain ⟨⟨a, b, hab, hroot⟩, hdeg⟩ := root_of_hw c c0 hc La hC.2.1 d0 hd hgU.1 hw
    have hlt := hC.2.2 ν a b hab hroot (dom2 hw) (supp2 hw) hdeg
    have hK := hwK_of_hwSub.1 hw.2
    have hKT : HwK (units (twAct p q r s τ)) (fun x => ν x + τ0) g := by
      refine ⟨fun a => ?_, fun a b h => ?_⟩
      · rw [star_tw, hK.1 a, if_pos rfl, hτ, ← add_smul]
        push_cast; rfl
      · rw [star_tw, hK.2 a b h, if_neg (PI.FockOneDegW.Core.posC_ne a b h)]
        simp
    have h1 : D g = 0 := hgU.2
    rw [hD, cas_hw hgl hKT, ← sub_smul, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · have h2 : ((casW (fun x => ν x + τ0) : ℚ) : ℝ) = t := by
        have h3 : (((casW (fun x => ν x + τ0) : ℚ) : ℝ) : ℂ) = (t : ℂ) := by
          rw [← sub_eq_zero.1 h1]; simp
        exact_mod_cast h3
      have h4 : ((casW (fun x => La x + τ0) : ℚ) : ℝ) + ((r : ℝ) + s) <
          ((casW (fun x => ν x + τ0) : ℚ) : ℝ) := by exact_mod_cast hlt
      linarith
    · exact hw.1 h1
  · show casK (units (thAct p q r s c τ)) _ - (t : ℂ) • _ = 0
    exact sub_eq_zero.2 hcas

end PositivityTheory.KReal

end
end

-- bundled from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieC
section
noncomputable section

open Complex Matrix Filter Topology

namespace PositivityTheory.RL.Up

theorem exp_mul_inj {z z' : ℂ} (h : ∀ t : ℝ, cexp (z * t) = cexp (z' * t)) : z = z' := by
  have d : ∀ z : ℂ, HasDerivAt (fun t : ℝ => cexp (z * t)) z 0 := fun z => by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul z).cexp
  have := d z
  simp only [h] at this
  exact this.unique (d z')

section Banach

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

def expU (Z : 𝔸) : 𝔸ˣ :=
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  ⟨NormedSpace.exp Z, NormedSpace.exp (-Z),
    by rw [← NormedSpace.exp_add_of_commute (Commute.refl Z).neg_right, add_neg_cancel, NormedSpace.exp_zero],
    by rw [← NormedSpace.exp_add_of_commute (Commute.refl Z).neg_left, neg_add_cancel, NormedSpace.exp_zero]⟩

theorem expU_add (Z : 𝔸) (s t : ℝ) : expU ((s + t) • Z) = expU (s • Z) * expU (t • Z) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  refine Units.ext ?_
  show NormedSpace.exp _ = NormedSpace.exp _ * NormedSpace.exp _
  rw [add_smul, NormedSpace.exp_add_of_commute (((Commute.refl Z).smul_left s).smul_right t)]

theorem expU_zero : expU (0 : 𝔸) = 1 := Units.ext NormedSpace.exp_zero

theorem continuous_expU (Z : 𝔸) : Continuous fun t : ℝ => expU (t • Z) :=
  Units.isOpenEmbedding_val.isInducing.continuous_iff.2
    (continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) Z t).continuousAt)

end Banach

theorem eq_trace {β : Type} [Fintype β] [DecidableEq β] (ξ : Matrix β β ℂ →ₗ[ℂ] ℂ)
    (h : ∀ A B, ξ (A * B - B * A) = 0) : ∃ c : ℂ, ∀ A, ξ A = c * A.trace := by
  rcases isEmpty_or_nonempty β with hβ | ⟨⟨b⟩⟩
  · exact ⟨0, fun A => by rw [Subsingleton.elim A 0, map_zero, zero_mul]⟩
  refine ⟨ξ (single b b 1), fun A => ?_⟩
  have h1 : ∀ i j, i ≠ j → ξ (single i j 1) = 0 := fun i j hij => by
    have := h (single i i 1) (single i j 1)
    rwa [single_mul_single_same, single_mul_single_of_ne (h := hij.symm), one_mul, sub_zero] at this
  have h2 : ∀ i, ξ (single i i 1) = ξ (single b b 1) := fun i => by
    have := h (single i b 1) (single b i 1)
    rwa [single_mul_single_same, single_mul_single_same, one_mul, map_sub, sub_eq_zero] at this
  conv_lhs => rw [matrix_eq_sum_single A]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  rw [Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∀ j, ξ (single i j (A i j)) = A i j * ξ (single i j 1) := fun j => by
    rw [← smul_eq_mul, ← map_smul, smul_single, smul_eq_mul, mul_one]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [e, h1 i j hj.symm, mul_zero]) (by simp), e, h2, mul_comm]
  rfl

theorem real_form_trace {β : Type} [Fintype β] [DecidableEq β] (τ : Matrix β β ℂ →ₗ[ℝ] Matrix β β ℂ)
    (hI : ∀ A, τ (I • A) = -(I • τ A)) (hτ : ∀ A, τ (τ A) = A) (ζ : Matrix β β ℂ →ₗ[ℝ] ℂ)
    (hb : ∀ X Y, τ X = X → τ Y = Y → τ (X * Y - Y * X) = X * Y - Y * X ∧ ζ (X * Y - Y * X) = 0) :
    ∃ c : ℂ, ∀ Z, τ Z = Z → ζ Z = c * Z.trace := by
  let P : Matrix β β ℂ → Matrix β β ℂ := fun A => (1 / 2 : ℝ) • (A + τ A)
  have hP : ∀ A, τ (P A) = P A := fun A => by simp only [P, map_smul, map_add (f := _), hτ, add_comm]
  let ξ0 : Matrix β β ℂ → ℂ := fun A => ζ (P A) - I * ζ (P (I • A))
  have add : ∀ A B, ξ0 (A + B) = ξ0 A + ξ0 B := fun A B => by
    simp only [ξ0, P, smul_add, map_add (f := _), map_smul]
    ring
  have rs : ∀ (r : ℝ) A, ξ0 (r • A) = r * ξ0 A := fun r A => by
    simp only [ξ0, P, smul_comm I r, smul_add, map_add (f := _), map_smul, real_smul]
    ring
  have is : ∀ A, ξ0 (I • A) = I * ξ0 A := fun A => by
    simp only [ξ0, P, smul_smul, I_mul_I, neg_smul, one_smul, smul_add, map_add (f := _), map_smul, map_neg, real_smul, smul_neg]
    linear_combination ((((1 / 2 : ℝ) : ℂ) * ζ (I • A) + ((1 / 2 : ℝ) : ℂ) * ζ (τ (I • A)))) * I_mul_I
  let ξ : Matrix β β ℂ →ₗ[ℂ] ℂ :=
    { toFun := ξ0
      map_add' := add
      map_smul' := fun c A => by
        have e : c • A = c.re • A + I • (c.im • A) := by
          ext i j
          simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, real_smul]
          linear_combination (-A i j) * re_add_im c
        rw [e, add, is, rs, rs, RingHom.id_apply, smul_eq_mul]
        linear_combination (ξ0 A) * re_add_im c }
  have fix : ∀ Z, τ Z = Z → ξ Z = ζ Z := fun Z hZ => by
    have e1 : P Z = Z := by
      simp only [P, hZ]
      module
    have e2 : P (I • Z) = 0 := by simp only [P, hI, hZ, add_neg_cancel, smul_zero]
    show ζ (P Z) - I * ζ (P (I • Z)) = _
    rw [e1, e2, map_zero, mul_zero, sub_zero]
  have dec : ∀ A, A = P A - I • P (I • A) := fun A => by
    simp only [P, hI]
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul, real_smul]
    push_cast
    linear_combination ((A i j - τ A i j) / 2) * I_mul_I
  have br : ∀ X Y, τ X = X → τ Y = Y → ξ (X * Y - Y * X) = 0 := fun X Y hX hY => by
    rw [fix _ (hb X Y hX hY).1, (hb X Y hX hY).2]
  obtain ⟨c, hc⟩ := eq_trace ξ fun A B => by
    have h1 : ∀ X, τ X = X → ξ (X * B - B * X) = 0 := fun X hX => by
      have e : X * B - B * X = (X * P B - P B * X) - I • (X * P (I • B) - P (I • B) * X) := by
        conv_lhs => rw [dec B]
        simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        abel
      rw [e, map_sub, map_smul, br _ _ hX (hP _), br _ _ hX (hP _), smul_zero, sub_zero]
    have e : A * B - B * A = (P A * B - B * P A) - I • (P (I • A) * B - B * P (I • A)) := by
      conv_lhs => rw [dec A]
      simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      abel
    rw [e, map_sub, map_smul, h1 _ (hP _), h1 _ (hP _), smul_zero, sub_zero]
  exact ⟨c, fun Z hZ => by rw [← fix Z hZ, hc]⟩

end PositivityTheory.RL.Up

end
end

