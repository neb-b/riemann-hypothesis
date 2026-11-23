module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DescendBlockDiagPartRatPolyOfFibreConst
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_component_subst {σ : Type} (s : σ → MvPolynomial σ ℚ) (l : ℂ →ₗ[ℚ] ℚ)
    (b : MvPolynomial σ ℂ) :
    ∃ b' : MvPolynomial σ ℚ, ∀ m, AddMonoidAlgebra.coeff (MvPolynomial.aeval s b') m =
      l (AddMonoidAlgebra.coeff (MvPolynomial.aeval (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (s i)) b)
        m) := by
  induction b using MvPolynomial.induction_on' with
  | monomial u a =>
    refine ⟨MvPolynomial.monomial u (l a), fun m => ?_⟩
    rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
    have h : (u.prod fun i k => (MvPolynomial.map (algebraMap ℚ ℂ) (s i)) ^ k) =
        MvPolynomial.map (algebraMap ℚ ℂ) (u.prod fun i k => s i ^ k) := by
      simp [Finsupp.prod, map_prod, map_pow]
    rw [h, MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm a, ← Algebra.smul_def, map_smul,
      smul_eq_mul, mul_comm]
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    refine ⟨p' + q', fun m => ?_⟩
    rw [map_add (f := _), map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, map_add (f := _), hp', hq']

theorem exists_poly_blk {ι : Type} [Fintype ι] [DecidableEq ι] (e : Matrix ι ι ℚ) :
    ∃ s : ι × ι → MvPolynomial (ι × ι) ℚ, ∀ (x : Matrix ι ι ℂ) (ij : ι × ι),
      ev (s ij) x = blk e x ij.1 ij.2 := by
  refine ⟨fun ij => blk e (Matrix.of fun i j => (MvPolynomial.X (i, j) : MvPolynomial (ι × ι) ℚ)) ij.1 ij.2,
    fun x ij => ?_⟩
  set φ : MvPolynomial (ι × ι) ℚ →ₐ[ℚ] ℂ := MvPolynomial.aeval (fun ij : ι × ι => x ij.1 ij.2) with hφ
  have h1 : φ.mapMatrix (e.map (algebraMap ℚ (MvPolynomial (ι × ι) ℚ))) = e.map (algebraMap ℚ ℂ) := by
    ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, AlgHom.commutes]
  have h2 : φ.mapMatrix (Matrix.of fun i j => (MvPolynomial.X (i, j) : MvPolynomial (ι × ι) ℚ)) = x := by
    ext i j
    simp [hφ]
  have h3 : φ.mapMatrix (blk e (Matrix.of fun i j => (MvPolynomial.X (i, j) : MvPolynomial (ι × ι) ℚ)))
      = blk e x := by
    unfold blk
    simp only [map_add (f := _), map_mul, map_sub, map_one, h1, h2]
  rw [← h3]
  rfl

theorem descend_blk_rat : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∀ f : MvPolynomial (ι × ι) ℚ, (∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → ev f x = ev f x') → ∃ b : MvPolynomial (ι × ι) ℚ, ∀ x ∈ Γ, ev f x = ev b (blk e x) := by
  intro ι _ _ Γ e hΓ he hpar f hf
  have hmap : ∀ (p : MvPolynomial (ι × ι) ℚ) (x : Matrix ι ι ℂ),
      evC (MvPolynomial.map (algebraMap ℚ ℂ) p) x = ev p x := by
    intro p x
    unfold evC ev
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.ClassFin.exists_evC_blk_of_fibre_const ι Γ e hΓ he hpar (MvPolynomial.map (algebraMap ℚ ℂ) f)
    (fun x hx x' hx' h => by rw [hmap, hmap]; exact hf x hx x' hx' h)
  obtain ⟨s, hs⟩ := exists_poly_blk e
  obtain ⟨l, hl⟩ : ∃ l : ℂ →ₗ[ℚ] ℚ, l 1 = 1 := by
    obtain ⟨l, hl⟩ := (Algebra.linearMap ℚ ℂ).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (algebraMap ℚ ℂ).injective)
    refine ⟨l, ?_⟩
    have := LinearMap.congr_fun hl 1
    simpa using this
  obtain ⟨b', hb'⟩ := exists_component_subst s l b
  have hsubC : ∀ x : Matrix ι ι ℂ,
      evC (MvPolynomial.aeval (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (s i)) b) x = evC b (blk e x) := by
    intro x
    have h : (fun ij : ι × ι => blk e x ij.1 ij.2) =
        fun ij => MvPolynomial.aeval (fun ij : ι × ι => x ij.1 ij.2) (MvPolynomial.map (algebraMap ℚ ℂ) (s ij)) := by
      funext ij
      rw [← hs, ← hmap]
      rfl
    unfold evC
    rw [h, ← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval, RingHom.coe_coe, RingHom.coe_coe,
      ← MvPolynomial.comp_aeval]
    rfl
  have hsub : ∀ x : Matrix ι ι ℂ, ev (MvPolynomial.aeval s b') x = ev b' (blk e x) := by
    intro x
    have h : (fun ij : ι × ι => blk e x ij.1 ij.2) =
        fun ij => MvPolynomial.aeval (fun ij : ι × ι => x ij.1 ij.2) (s ij) := by
      funext ij
      rw [← hs]
      rfl
    unfold ev
    rw [h, ← MvPolynomial.comp_aeval]
    rfl
  have hvan := _root_.GlobalTheory.ClassFin.component_mem_vanI ι Γ hΓ.aut_mem
    (MvPolynomial.map (algebraMap ℚ ℂ) f -
      MvPolynomial.aeval (fun i => MvPolynomial.map (algebraMap ℚ ℂ) (s i)) b)
    (fun g hg => by
      have h1 := hb g hg
      rw [← hsubC] at h1
      unfold evC at h1 ⊢
      rw [map_sub, h1, sub_self])
    l (f - MvPolynomial.aeval s b')
    (fun m => by
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sub, map_sub, hb', MvPolynomial.coeff_map,
        Algebra.algebraMap_eq_smul_one, map_smul, hl, smul_eq_mul, mul_one])
  refine ⟨b', fun x hx => ?_⟩
  have h1 := hvan x hx
  rw [← hsub]
  unfold ev at h1 ⊢
  rw [map_sub] at h1
  exact sub_eq_zero.mp h1

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLeftTranslationReynoldsOperator
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.ReynoldsLtr

variable {ι : Type} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq =>
    simp only [evC, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [evC, map_mul] at hp ⊢
    rw [hp]
    simp [ltr, Matrix.mul_apply]


omit [DecidableEq ι] in
theorem isInv_iff (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ) :
    IsInv Γ f ↔ ∀ g ∈ Γ, ltr g f = f := by
  constructor
  · intro h g hg
    apply MvPolynomial.funext
    intro x
    have h1 := evC_ltr g (Matrix.of fun i j => x (i, j)) f
    rw [h g hg] at h1
    simpa [evC] using h1
  · intro h g hg y
    rw [← evC_ltr, h g hg]

theorem exists_isReynolds : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ Rey, IsReynolds Γ Rey := by
  intro ι _ _ Γ hΓ hss
  obtain ⟨Rey, h1, h2, -, -, h5, h6⟩ := GlobalTheory.T.exists_reynolds_of_completelyReducible' (MvPolynomial (ι × ι) ℂ)
    ((fun g => (ltr g).toLinearMap) '' Γ) (by
      intro U hU
      obtain ⟨U', hU', hc⟩ := _root_.GlobalTheory.ClassFin.ltr_completely_reducible ι Γ hΓ hss U
        (fun g hg f hf => hU _ ⟨g, hg, rfl⟩ f hf)
      refine ⟨U', ?_, hc⟩
      rintro _ ⟨g, hg, rfl⟩ f hf
      exact hU' g hg f hf)
  refine ⟨Rey, ?_, ?_, ?_, ?_⟩
  · intro f
    rw [isInv_iff]
    intro g hg
    exact h1 f _ ⟨g, hg, rfl⟩
  · intro f hf
    rw [isInv_iff] at hf
    apply h2
    rintro _ ⟨g, hg, rfl⟩
    exact hf g hg
  · intro a f ha
    rw [isInv_iff] at ha
    refine h5 (LinearMap.mulLeft ℂ a) ?_ f
    rintro _ ⟨g, hg, rfl⟩ v
    simp only [LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, map_mul, ha g hg]
  · intro U hU
    apply h6
    rintro _ ⟨g, hg, rfl⟩ f hf
    exact hU g hg f hf

end GlobalTheory.ClassFin.ReynoldsLtr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceNotPowAdicCompletion
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_not_mem_not_pow_completion :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → u ≠ 0 → (∀ r : F, r ^ p ≠ u) → ∃ v, v ∉ S₀ ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) u := by
  classical
  intro p F _ _ _ ζ u S₀ hp hζ hu hns
  by_contra hcon
  push Not at hcon
  have hle : ∀ S, finNorm p F u S₀ ≤ finNorm p F u S := by
    intro S x hx
    rw [finNorm] at hx ⊢
    simp only [Subgroup.mem_iInf] at hx ⊢
    intro v _
    by_cases hv : v ∈ S₀
    · exact hx v hv
    · haveI : CharZero (v.adicCompletion F) :=
        charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
      obtain ⟨r, hr⟩ := hcon v hv
      rw [_root_.GlobalTheory.CNorm.kNorm_eq_top_of_pow p F _ _ u r hp.pos hu hr]
      exact Subgroup.mem_top x
  have hidx := (_root_.GlobalTheory.CNorm.pow_tNon_le_index_finNorm p F ζ u S₀ hp hζ).1
  haveI : (finNorm p F u S₀).FiniteIndex := ⟨hidx⟩
  haveI : Fintype (Fˣ ⧸ finNorm p F u S₀) := Fintype.ofFinite _
  obtain ⟨S₁, -, hS₁⟩ := exists_superset_mem_sUnits F
    (insert (Units.mk0 u hu)
      (Finset.univ.image (fun q : Fˣ ⧸ finNorm p F u S₀ => q.out))) S₀
  obtain ⟨S, hS, hadm⟩ := (_root_.GlobalTheory.CNorm.exists_admissiblePlaces_superset_and_mono p F hp.pos).1 S₁
  have hX := hS₁ S hS
  refine _root_.GlobalTheory.CNorm.sUnits_sup_finNorm_ne_top p F ζ (Units.mk0 u hu) S hp hζ hadm
    (hX _ (Finset.mem_insert_self _ _)) hns ?_
  rw [eq_top_iff]
  intro x _
  have hy : (QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out ∈ sUnits F S :=
    hX _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hz : ((QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out)⁻¹ * x ∈ finNorm p F u S₀ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  have hx : x = (QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out *
      (((QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out)⁻¹ * x) := by
    rw [mul_inv_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup hy (hle S hz)

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsQuaternaryOfCoordinates
section
open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad

section Algebra

variable {k : Type*} [Field k]

theorem exists_norm_of_quaternary [CharZero k] {α β γ s : k} (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (hs : s ^ 2 = α * β * γ) {x y z t : k} (h0 : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0)
    (h : x ^ 2 - α * y ^ 2 - β * z ^ 2 + γ * t ^ 2 = 0) : ∃ X Y : k, β = X ^ 2 - α * Y ^ 2 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (mul_ne_zero hα hβ) hγ (by simpa using hs.symm)
  obtain ⟨u, hu⟩ : ∃ u, u = t * s / (α * β) := ⟨_, rfl⟩
  have hu2 : α * β * u ^ 2 = γ * t ^ 2 := by
    rw [hu, div_pow, mul_pow, hs]; field_simp
  have h1 : x ^ 2 - α * y ^ 2 = β * (z ^ 2 - α * u ^ 2) := by linear_combination h + hu2
  by_cases hD : z ^ 2 - α * u ^ 2 = 0
  · refine GlobalTheory.Published.HasseNormSt.of_isSquare hα ?_ β
    by_cases hu0 : u = 0
    · have hz : z = 0 := by simpa [hu0] using hD
      have ht : t = 0 := by
        have : γ * t ^ 2 = 0 := by rw [← hu2, hu0]; ring
        simpa [hγ] using this
      have hxy : x ^ 2 = α * y ^ 2 := by linear_combination h1 + β * hD
      have hy : y ≠ 0 := by
        rintro rfl
        have hx : x = 0 := by simpa using hxy
        simp [hx, hz, ht] at h0
      exact ⟨x / y, by field_simp; linear_combination -hxy⟩
    · exact ⟨z / u, by field_simp; linear_combination -hD⟩
  · refine ⟨(x * z + α * y * u) / (z ^ 2 - α * u ^ 2), (x * u + y * z) / (z ^ 2 - α * u ^ 2), ?_⟩
    field_simp
    linear_combination (-(z ^ 2 - α * u ^ 2)) * h1

theorem exists_quaternary_of_coordinates {α β γ : k} (hα : α ≠ 0) (hβ : β ≠ 0)
    {X₀ X₁ Y₀ Y₁ : k}
    (h1 : β = X₀ ^ 2 + α * β * γ * X₁ ^ 2 - α * (Y₀ ^ 2 + α * β * γ * Y₁ ^ 2))
    (h2 : X₀ * X₁ = α * (Y₀ * Y₁)) :
    ∃ x y z t : k, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
      x ^ 2 - α * y ^ 2 - β * z ^ 2 + γ * t ^ 2 = 0 := by
  by_cases hw : X₁ ^ 2 - α * Y₁ ^ 2 = 0
  · exact ⟨X₀, Y₀, 1, 0, by simp, by linear_combination -h1 - α * β * γ * hw⟩
  · refine ⟨-Y₁ * (α * β), -X₁ * β, -(X₀ * Y₁ - Y₀ * X₁) * α, (X₁ ^ 2 - α * Y₁ ^ 2) * (α * β),
      Or.inr (Or.inr (Or.inr (mul_ne_zero hw (mul_ne_zero hα hβ)))), ?_⟩
    linear_combination (-(α * β * (X₁ ^ 2 - α * Y₁ ^ 2))) * h1 - α * β * (X₀ * X₁ - α * (Y₀ * Y₁)) * h2

theorem isotropic_four_iff {a : Fin 4 → k} (ha : a 0 ≠ 0) :
    (∃ x : Fin 4 → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ↔
      ∃ x y z t : k, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ t ≠ 0) ∧
        x ^ 2 - (-(a 0 * a 1)) * y ^ 2 - (-(a 0 * a 2)) * z ^ 2 + (a 0 * a 3) * t ^ 2 = 0 := by
  constructor
  · rintro ⟨x, hx, h⟩
    rw [Fin.sum_univ_four] at h
    refine ⟨a 0 * x 0, x 1, x 2, x 3, ?_, by linear_combination a 0 * h⟩
    by_contra hc
    push Not at hc
    obtain ⟨h0, h1, h2, h3⟩ := hc
    apply hx
    funext i
    fin_cases i
    · simpa [ha] using h0
    · exact h1
    · exact h2
    · exact h3
  · rintro ⟨x, y, z, t, hx, h⟩
    refine ⟨![x / a 0, y, z, t], ?_, ?_⟩
    · intro hc
      have h0 := congrFun hc 0
      have h1 := congrFun hc 1
      have h2 := congrFun hc 2
      have h3 := congrFun hc 3
      simp [ha] at h0 h1 h2 h3
      simp [h0, h1, h2, h3] at hx
    · rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp
      linear_combination h

theorem isotropic_succ_iff {n : ℕ} {a : Fin (n + 1) → k} :
    (∃ x : Fin (n + 1) → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ↔
      ∃ (t : k) (z : Fin n → k), (t ≠ 0 ∨ z ≠ 0) ∧ a 0 * t ^ 2 + ∑ i, a i.succ * z i ^ 2 = 0 := by
  constructor
  · rintro ⟨x, hx, h⟩
    rw [Fin.sum_univ_succ] at h
    refine ⟨x 0, fun i => x i.succ, ?_, h⟩
    by_contra hc
    push Not at hc
    apply hx
    funext i
    refine Fin.cases hc.1 (fun j => congrFun hc.2 j) i
  · rintro ⟨t, z, hx, h⟩
    refine ⟨Fin.cons t z, ?_, by simpa [Fin.sum_univ_succ] using h⟩
    intro hc
    rcases hx with hx | hx
    · exact hx (by simpa using congrFun hc 0)
    · exact hx (funext fun i => by simpa using congrFun hc i.succ)

theorem exists_value_isotropic [CharZero k] {n : ℕ} {a a' : k} (ha : a ≠ 0) (ha' : a' ≠ 0)
    {b : Fin (n + 1) → k} (hb : b 0 ≠ 0) {x y : k} {z : Fin (n + 1) → k}
    (h0 : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) (h : a * x ^ 2 + (a' * y ^ 2 + ∑ i, b i * z i ^ 2) = 0) :
    ∃ x y : k, a * x ^ 2 + a' * y ^ 2 ≠ 0 ∧ ∀ μ : k, IsSquare (μ / (a * x ^ 2 + a' * y ^ 2)) →
      ∃ (t : k) (z : Fin (n + 1) → k), (t ≠ 0 ∨ z ≠ 0) ∧ μ * t ^ 2 + ∑ i, b i * z i ^ 2 = 0 := by
  have key : ∀ ν : k, ν ≠ 0 → ∀ z : Fin (n + 1) → k, ν + ∑ i, b i * z i ^ 2 = 0 →
      ∀ μ : k, IsSquare (μ / ν) →
      ∃ (t : k) (z : Fin (n + 1) → k), (t ≠ 0 ∨ z ≠ 0) ∧ μ * t ^ 2 + ∑ i, b i * z i ^ 2 = 0 := by
    rintro ν hν z hz μ ⟨s, hs⟩
    refine ⟨1, fun i => s * z i, Or.inl one_ne_zero, ?_⟩
    have : ∑ i, b i * (s * z i) ^ 2 = s ^ 2 * ∑ i, b i * z i ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [div_eq_iff hν] at hs
    rw [this, hs]
    linear_combination s ^ 2 * hz
  by_cases hμ : a * x ^ 2 + a' * y ^ 2 = 0
  · by_cases hz : z = 0
    · have hy : y ≠ 0 := by
        rintro rfl
        have hx : x = 0 := by simpa [ha] using hμ
        simp [hx, hz] at h0
      obtain ⟨X, Y, hXY⟩ := GlobalTheory.Published.HasseNormSt.of_isSquare (δ := -a' / a) (by simp [ha, ha'])
        ⟨x / y, by field_simp; linear_combination -hμ⟩ (-b 0 / a)
      have e : a * X ^ 2 + a' * Y ^ 2 = -b 0 := by
        field_simp at hXY
        linear_combination -hXY
      refine ⟨X, Y, by rw [e]; exact neg_ne_zero.2 hb, key _ (by rw [e]; exact neg_ne_zero.2 hb)
        (Pi.single 0 1) ?_⟩
      rw [e, Fin.sum_univ_succ]
      simp
    · refine ⟨1, 0, by simpa using ha, fun μ _ => ⟨0, z, Or.inr hz, ?_⟩⟩
      linear_combination h - hμ
  · exact ⟨x, y, hμ, key _ hμ z (by linear_combination h)⟩

theorem isotropic_of_injective {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ → ι)
    (he : Function.Injective e) {a : ι → k}
    (h : ∃ x : κ → k, x ≠ 0 ∧ ∑ j, a (e j) * x j ^ 2 = 0) :
    ∃ x : ι → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  classical
  obtain ⟨x, hx, h⟩ := h
  refine ⟨Function.extend e x 0, fun hc => hx (funext fun j => ?_), ?_⟩
  · simpa [he.extend_apply] using congrFun hc (e j)
  · rw [← h]
    symm
    refine Finset.sum_of_injOn e he.injOn (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_
    · intro i _ hi
      rw [Function.extend_apply' _ _ _ (by simpa using hi)]
      simp
    · intro j _
      rw [he.extend_apply]

theorem isotropic_real {ι : Type*} [Fintype ι] {a : ι → ℝ} {i j : ι} (hi : a i < 0) (hj : 0 < a j) :
    ∃ x : ι → ℝ, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  have hij : i ≠ j := by rintro rfl; linarith
  refine isotropic_of_injective ![i, j] ?_ ⟨![√(a j), √(-a i)], ?_, ?_⟩
  · intro p q h
    fin_cases p <;> fin_cases q <;> simp_all [eq_comm]
  · intro hc
    have := congrFun hc 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at this
    exact (Real.sqrt_pos.2 hj).ne' this
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Real.sq_sqrt hj.le, Real.sq_sqrt (by linarith)]
    ring

end Algebra

end GlobalTheory.LocalQuad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowOfSUnitLocalPowerAtPlaces
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pow_of_mem_sUnits_union_of_mem_finPow :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F]
      [DecidableEq (HeightOneSpectrum (𝓞 F))] (ζ : F) (S T : Finset (HeightOneSpectrum (𝓞 F))),
      p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ →
      ∀ y ∈ sUnits F (S ∪ T), y ∈ finPow p F S → ∃ r : F, r ^ p = (y : F) := by
  intro p F _ _ _ _ ζ S T hp hζ hS hT y hy hyS
  by_contra hne
  have hne' : ∀ r : F, r ^ p ≠ (y : F) := fun r hr => hne ⟨r, hr⟩
  have hadm : AdmP p F (S ∪ T) :=
    (_root_.GlobalTheory.CNorm.exists_admissiblePlaces_superset_and_mono p F hp.pos).2 S (S ∪ T) Finset.subset_union_left hS
  refine _root_.GlobalTheory.CNorm.sUnits_sup_finNorm_ne_top p F ζ y (S ∪ T) hp hζ hadm hy hne' ?_
  rw [eq_top_iff, ← hT]
  refine sup_le_sup_left ?_ _
  unfold finNorm
  refine le_iInf₂ fun v hv => ?_
  rcases Finset.mem_union.1 hv with hv | hv
  · have h1 : y ∈ powSub p (algebraMap F (v.adicCompletion F)) :=
      (iInf₂_le (f := fun w (_ : w ∈ S) => powSub p (algebraMap F (w.adicCompletion F))) v hv) hyS
    obtain ⟨r, hr⟩ := h1
    have : CharZero (v.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
    rw [_root_.GlobalTheory.CNorm.kNorm_eq_top_of_pow p F (v.adicCompletion F) _ (y : F) r hp.pos y.ne_zero hr]
    exact le_top
  · exact le_trans
      (iInf₂_le (f := fun w (_ : w ∈ T) => powSub p (algebraMap F (w.adicCompletion F))) v hv)
      ((_root_.GlobalTheory.CNorm.powSub_le_kNorm_and_kNorm_map p hp.pos).1 F (v.adicCompletion F) _ (y : F))

end GlobalTheory.CNorm
end

