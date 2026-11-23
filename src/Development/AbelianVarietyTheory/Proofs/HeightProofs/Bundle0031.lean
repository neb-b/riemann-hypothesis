module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryAdelicHeightCosetLeNormInfPow
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.HeightCoset

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

theorem opNorm_le_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  refine (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _).trans ?_
  gcongr
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x) i = ∑ j, A i j * x j := rfl
  rw [this, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  gcongr
  exact PiLp.norm_apply_le x j

variable {D : D7}

theorem infMat_mul' (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * h) = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ h := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (g * h) =
    HA.mat (AF D.host.F) D.sp.cm.sig V.gram g * HA.mat (AF D.host.F) D.sp.cm.sig V.gram h := rfl
  simp only [infMat, this, Units.val_mul]
  rw [Matrix.map_mul, Matrix.map_mul]

theorem infMat_one' (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) :
    infMat D.sp.cm.sig V.gram θ (1 : GA D V) = 1 := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (1 : GA D V) = 1 := rfl
  simp only [infMat, this, Units.val_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem finMat_eq (V : HSp D) (g : GA D V) : finMat D.sp.cm.sig V.gram g = (finHom V g).1 := rfl

theorem finHt_mul (V : HSp D) (x g : GA D V) (hg : g ∈ GinfC V) (v) : finHt V v (x * g) = finHt V v x := by
  have h0 : finHom V g = 1 := hg
  have h1 : finMat D.sp.cm.sig V.gram (x * g) = finMat D.sp.cm.sig V.gram x := by
    rw [finMat_eq, finMat_eq, map_mul, h0, mul_one]
  have h2 : finMat D.sp.cm.sig V.gram (x * g)⁻¹ = finMat D.sp.cm.sig V.gram x⁻¹ := by
    rw [finMat_eq, finMat_eq, map_inv, map_inv, map_mul, h0, mul_one]
  simp only [finHt, finNorm, h1, h2]

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem infNorm_mul_le (τ : D.what₂.Tau) (x g : GA D V) :
    infNorm θ V τ (x * g) ≤ infNorm θ V τ x * infNorm θ V τ g := by
  unfold infNorm
  rw [infMat_mul', map_mul]
  exact nnnorm_mul_le _ _

theorem infHt_mul_le (τ : D.what₂.Tau) (x g : GA D V) :
    infHt θ V τ (x * g) ≤ infHt θ V τ x * infHt θ V τ g := by
  refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)) (max_le ?_ ?_)
  · refine (infNorm_mul_le θ V τ x g).trans (mul_le_mul' ?_ ?_) <;>
      exact le_max_of_le_right (le_max_left _ _)
  · rw [_root_.mul_inv_rev, mul_comm (infHt θ V τ x)]
    refine (infNorm_mul_le θ V τ g⁻¹ x⁻¹).trans (mul_le_mul' ?_ ?_) <;>
      exact le_max_of_le_right (le_max_right _ _)

theorem infNorm_le_normInf (τ : D.what₂.Tau) (g : GA D V) :
    (infNorm θ V τ g : ℝ) ≤ normInf θ V g ∧ (infNorm θ V τ g⁻¹ : ℝ) ≤ normInf θ V g := by
  have h : ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖)
      ≤ normInf θ V g :=
    Finset.single_le_sum (f := fun τ => ∑ i, ∑ j,
      (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ)
  constructor
  · refine (opNorm_le_sum _).trans (le_trans ?_ h)
    gcongr
    exact le_add_of_nonneg_right (norm_nonneg _)
  · refine (opNorm_le_sum _).trans (le_trans ?_ h)
    gcongr
    exact le_add_of_nonneg_left (norm_nonneg _)

theorem infHt_le_normInf (hV : 0 < V.rank) (τ : D.what₂.Tau) (g : GA D V) :
    (infHt θ V τ g : ℝ) ≤ normInf θ V g := by
  obtain ⟨h1, h2⟩ := infNorm_le_normInf θ V τ g
  haveI : Nonempty (Fin V.rank) := ⟨⟨0, hV⟩⟩
  have h3 : infNorm θ V τ 1 = 1 := by
    unfold infNorm
    rw [infMat_one', map_one]
    exact nnnorm_one
  have h4 : (1 : ℝ) ≤ infNorm θ V τ g * infNorm θ V τ g⁻¹ := by
    have := infNorm_mul_le θ V τ g g⁻¹
    rw [mul_inv_cancel, h3] at this
    exact_mod_cast this
  have h5 : 1 ≤ normInf θ V g := by
    by_contra hc
    push_neg at hc
    have a0 := (infNorm θ V τ g).coe_nonneg
    have b0 := (infNorm θ V τ g⁻¹).coe_nonneg
    nlinarith
  unfold infHt
  push_cast
  exact max_le h5 (max_le h1 h2)

theorem infHt_rank_zero (hV : V.rank = 0) (τ : D.what₂.Tau) (g : GA D V) : infHt θ V τ g = 1 := by
  haveI : IsEmpty (Fin V.rank) := by rw [hV]; infer_instance
  have h : ∀ g, infNorm θ V τ g ≤ 1 := fun g => by
    have := opNorm_le_sum (infMat D.sp.cm.sig V.gram (θ τ) g)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact_mod_cast this.trans zero_le_one
  exact max_eq_left (max_le (h g) (h g⁻¹))

theorem height_mul_le (x g : GA D V) (hg : g ∈ GinfC V) :
    height θ V (x * g) ≤ height θ V x * ∏ τ, infHt θ V τ g := by
  unfold height
  simp only [finHt_mul V x g hg]
  rw [mul_right_comm, ← Finset.prod_mul_distrib]
  gcongr with τ
  exact infHt_mul_le θ V τ x g

theorem height_le_normInf_pow (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) :
    ∃ M : ℕ, ∀ x : GA D V, ∃ C : ℝ, ∀ g ∈ GinfC V,
      (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V (x * g) : ℝ) ≤ C * normInf θ V g ^ M := by
  rcases Nat.eq_zero_or_pos V.rank with hV | hV
  · refine ⟨0, fun x => ⟨height θ V x, fun g hg => ?_⟩⟩
    have := height_mul_le θ V x g hg
    simp only [infHt_rank_zero θ V hV, Finset.prod_const_one] at this
    rw [pow_zero]
    exact_mod_cast this
  · refine ⟨Fintype.card D.what₂.Tau, fun x => ⟨height θ V x, fun g hg => ?_⟩⟩
    have : (height θ V (x * g) : ℝ) ≤ height θ V x * ∏ τ, (infHt θ V τ g : ℝ) := by
      exact_mod_cast height_mul_le θ V x g hg
    refine this.trans ?_
    gcongr
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => NNReal.coe_nonneg _) fun τ _ => infHt_le_normInf θ V hV τ g

end GlobalTheory.SmoothForms.HeightCoset

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.UnitaryLieComplexification

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}

noncomputable def cj (J Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := -(J⁻¹ * Zᴴ * J)

theorem cj_add (Z W : Matrix (Fin n) (Fin n) ℂ) : cj J (Z + W) = cj J Z + cj J W := by
  simp only [cj, conjTranspose_add, mul_add, add_mul, neg_add]

theorem cj_sub (Z W : Matrix (Fin n) (Fin n) ℂ) : cj J (Z - W) = cj J Z - cj J W := by
  simp only [cj, conjTranspose_sub, mul_sub, sub_mul]
  abel

theorem cj_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) : cj J (c • Z) = star c • cj J Z := by
  simp only [cj, conjTranspose_smul, mul_smul_comm, smul_mul_assoc, smul_neg]

theorem cj_cj (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) : cj J (cj J Z) = Z := by
  simp only [cj, conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hJ,
    mul_neg, neg_mul, neg_neg, Matrix.mul_assoc, Matrix.nonsing_inv_mul J hu, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul J hu, Matrix.one_mul]

theorem mem_iff_cj (hu : IsUnit J.det) (X : Matrix (Fin n) (Fin n) ℂ) : X ∈ lieU J ↔ cj J X = X := by
  change Xᴴ * J + J * X = 0 ↔ _
  constructor
  · intro h
    rw [cj, Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h, mul_neg, neg_neg, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul J hu, Matrix.one_mul]
  · intro h
    have : J * X = -(Xᴴ * J) := by
      conv_lhs => rw [← h]
      rw [cj, mul_neg, Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv J hu, Matrix.one_mul]
    rw [this, add_neg_cancel]

noncomputable def rePart (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) : lieU J :=
  ⟨(1 / 2 : ℂ) • (Z + cj J Z), by
    rw [mem_iff_cj hu, cj_smul, cj_add, cj_cj hJ hu, add_comm]
    simp⟩

noncomputable def imPart (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) : lieU J :=
  ⟨(1 / (2 * Complex.I) : ℂ) • (Z - cj J Z), by
    rw [mem_iff_cj hu, cj_smul, cj_sub, cj_cj hJ hu, ← neg_sub Z, smul_neg, ← neg_smul]
    congr 1
    simp⟩

theorem re_add_im (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (rePart hJ hu Z).1 + Complex.I • (imPart hJ hu Z).1 = Z := by
  have h : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  simp only [rePart, imPart, smul_smul, h]
  module

theorem cj_mk (hu : IsUnit J.det) (X Y : lieU J) :
    cj J (X.1 + Complex.I • Y.1) = X.1 - Complex.I • Y.1 := by
  rw [cj_add, cj_smul, (mem_iff_cj hu _).1 X.2, (mem_iff_cj hu _).1 Y.2]
  simp [sub_eq_add_neg]

theorem rePart_mk (hJ : Jᴴ = J) (hu : IsUnit J.det) (X Y : lieU J) :
    rePart hJ hu (X.1 + Complex.I • Y.1) = X := by
  apply Subtype.ext
  simp only [rePart, cj_mk hu]
  module

theorem imPart_mk (hJ : Jᴴ = J) (hu : IsUnit J.det) (X Y : lieU J) :
    imPart hJ hu (X.1 + Complex.I • Y.1) = Y := by
  apply Subtype.ext
  simp only [imPart, cj_mk hu]
  have h : (1 / (2 * Complex.I)) * (2 * Complex.I) = 1 := by field_simp
  have h2 : X.1 + Complex.I • Y.1 - (X.1 - Complex.I • Y.1) = (2 * Complex.I) • Y.1 := by module
  rw [h2, smul_smul, h, one_smul]

theorem exists_mk (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    ∃ X Y : lieU J, Z = X.1 + Complex.I • Y.1 := ⟨_, _, (re_add_im hJ hu Z).symm⟩

theorem exists_extension (hJ : Jᴴ = J) (hu : IsUnit J.det) {A : Type} [Ring A] [Algebra ℂ A] (ρ : lieU J → A)
    (hadd : ∀ X Y, ρ (X + Y) = ρ X + ρ Y) (hsm : ∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X)
    (hlie : ∀ X Y Z : lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A,
      (∀ Z, R Z = ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)) ∧ (∀ X : lieU J, R X.1 = ρ X) ∧
      ∀ Z W, R (Z * W - W * Z) = R Z * R W - R W * R Z := by
  have hsub : ∀ X Y, ρ (X - Y) = ρ X - ρ Y := by
    intro X Y
    have := hadd (X - Y) Y
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  have h0 : ρ 0 = 0 := by
    have := hsub 0 0
    rwa [sub_self, sub_self] at this
  let r : Matrix (Fin n) (Fin n) ℂ → A := fun Z => ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)
  have key : ∀ X Y : lieU J, r (X.1 + Complex.I • Y.1) = ρ X + Complex.I • ρ Y := by
    intro X Y
    simp only [r, rePart_mk, imPart_mk]
  have hII : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (m : M), Complex.I • Complex.I • m = -m := by
    intro M _ _ m
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have hbr : ∀ X Y : lieU J, ρ ⁅X, Y⁆ = ρ X * ρ Y - ρ Y * ρ X := fun X Y => hlie X Y _ rfl
  have hbc : ∀ X Y : lieU J, (⁅X, Y⁆ : lieU J).1 = X.1 * Y.1 - Y.1 * X.1 := fun X Y => rfl
  refine ⟨{ toFun := r, map_add' := ?_, map_smul' := ?_ }, fun Z => rfl, ?_, ?_⟩
  · intro Z W
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    obtain ⟨X', Y', rfl⟩ := exists_mk hJ hu W
    have : X.1 + Complex.I • Y.1 + (X'.1 + Complex.I • Y'.1) = (X + X').1 + Complex.I • (Y + Y').1 := by
      change _ = (X.1 + X'.1) + Complex.I • (Y.1 + Y'.1)
      module
    rw [this, key, key, key, hadd, hadd]
    module
  · intro c Z
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    generalize c.re = a at hc
    generalize c.im = b at hc
    subst hc
    have : ((a : ℂ) + (b : ℂ) * Complex.I) • (X.1 + Complex.I • Y.1) =
        (a • X - b • Y).1 + Complex.I • (b • X + a • Y).1 := by
      change _ = ((a : ℂ) • X.1 - (b : ℂ) • Y.1) + Complex.I • ((b : ℂ) • X.1 + (a : ℂ) • Y.1)
      simp only [add_smul, smul_add, mul_smul, hII]
      module
    rw [this, key, key, hsub, hadd, hsm, hsm, hsm, hsm]
    simp only [RingHom.id_apply, add_smul, smul_add, mul_smul, hII]
    module
  · intro X
    have := key X 0
    simpa [h0] using this
  · intro Z W
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    obtain ⟨X', Y', rfl⟩ := exists_mk hJ hu W
    have : (X.1 + Complex.I • Y.1) * (X'.1 + Complex.I • Y'.1) - (X'.1 + Complex.I • Y'.1) * (X.1 + Complex.I • Y.1) =
        (⁅X, X'⁆ - ⁅Y, Y'⁆ : lieU J).1 + Complex.I • (⁅X, Y'⁆ + ⁅Y, X'⁆ : lieU J).1 := by
      change _ = ((X.1 * X'.1 - X'.1 * X.1) - (Y.1 * Y'.1 - Y'.1 * Y.1)) +
        Complex.I • ((X.1 * Y'.1 - Y'.1 * X.1) + (Y.1 * X'.1 - X'.1 * Y.1))
      simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc, smul_add, hII]
      module
    change r _ = r _ * r _ - r _ * r _
    rw [this, key, key, key, hsub, hadd, hbr, hbr, hbr, hbr]
    simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc, smul_add, hII]
    module

theorem glRel_and_span : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → IsUnit J.det → ∃ P Q : Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, (∀ a b, (P a b).1 = (1 / 2 : ℂ) • (Matrix.single a b 1 + -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J)) ∧ (Q a b).1 = (1 / (2 * Complex.I)) • (Matrix.single a b 1 - -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J))) ∧ ∀ (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → Formalism.REAL.GlRel (fun a b => ρ (P a b) + Complex.I • ρ (Q a b)) ∧ ∀ X, ρ X ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => ρ (P p.1 p.2) + Complex.I • ρ (Q p.1 p.2)) := by
  intro n J hJ hu
  refine ⟨fun a b => rePart hJ hu (Matrix.single a b 1), fun a b => imPart hJ hu (Matrix.single a b 1),
    fun a b => ⟨rfl, rfl⟩, ?_⟩
  intro A _ _ ρ hadd hsm hlie
  obtain ⟨R, hR, hX, hc⟩ := exists_extension hJ hu ρ hadd hsm hlie
  simp only [← hR]
  constructor
  · intro a b c d
    simp only
    rw [← hc, map_sub]
    congr 1
    · split_ifs with h
      · subst h; rw [Matrix.single_mul_single_same, one_mul]
      · rw [Matrix.single_mul_single_of_ne (h := h), map_zero]
    · split_ifs with h
      · subst h; rw [Matrix.single_mul_single_same, one_mul]
      · rw [Matrix.single_mul_single_of_ne (h := h), map_zero]
  · intro X
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hX, Matrix.matrix_eq_sum_single X.1, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Submodule.sum_mem _ fun b _ => ?_
    have : Matrix.single a b (X.1 a b) = X.1 a b • Matrix.single a b (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b), rfl⟩)

end GlobalTheory.UnitaryLieComplexification
end

