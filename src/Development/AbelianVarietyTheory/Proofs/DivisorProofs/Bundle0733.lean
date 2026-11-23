module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslateHarishChandraFiniteFormProperties
section
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.HCF

theorem fold_replicate_cap {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (c : Module.End ℂ (Sm E a)) (χ : Module.End ℂ (Sm E a) → ℂ) (φ : Sm E a) (n : ℕ) :
    (List.replicate n c).foldr (fun z f => z f - χ z • f) φ = ((c - algebraMap ℂ _ (χ c)) ^ n) φ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply]

theorem rt_translate_kill : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (S : Finset (Module.End ℂ (Sm E a) → ℂ)), X ⊆ ↑S → ∀ (N : ℕ), ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), (∀ γ g, (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ).1 (ratGL E a γ * g) = (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ).1 g) ∧ IsOpen {k | finRep E a k (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ) = rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ} ∧ ∀ (τ : E →+* ℂ) (u : ℂ), Polynomial.aeval (cap τ u) (∏ χ ∈ S, (Polynomial.X - Polynomial.C (χ (cap τ u))) ^ N) (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ) = 0 := by
  intro E _ _ _ a L W X S hXS N φ hφ t κ
  obtain ⟨hA, -, -, χ₀, hχ₀, hnil⟩ := hφ
  set h := finGL E a t * infGL E a (Unitary.toUnits κ) with hh
  refine ⟨fun γ g => ?_, ?_, fun τ u => ?_⟩
  · rw [rt_apply, rt_apply, mul_assoc, hA.left]
  · refine isOpen_stab_of_mem_nhds (finRep E a) _ ?_
    have hc : Continuous fun k : GL (Fin a) (Af E) => t⁻¹ * k * t := by fun_prop
    have ho := hA.level.preimage hc
    refine Filter.mem_of_superset (ho.mem_nhds (by simp)) fun k hk => ?_
    have hk' : rt E a (finGL E a (t⁻¹ * k * t)) φ = φ := hk
    change rt E a (finGL E a k) (rt E a h φ) = rt E a h φ
    have e : finGL E a k * h = h * finGL E a (t⁻¹ * k * t) := by
      rw [hh, mul_assoc (finGL E a t), infGL_comm, ← mul_assoc (finGL E a t), ← map_mul,
        show t * (t⁻¹ * k * t) = k * t by group, map_mul]
      simp only [mul_assoc]
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hk']
  · classical
    have hcap : cap τ u ∈ Zalg E a := Algebra.subset_adjoin ⟨τ, u, rfl⟩
    have hc : Commute (cap (a := a) τ u) (rt E a h) := by
      have h1 : Commute (cap τ u) (rt E a (finGL E a t)) := commute_cap_finRep (a := a) τ u t
      have h2 := GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u (Unitary.toUnits κ)
      rw [hh, map_mul]
      exact h1.mul_right h2
    have hP : ∀ p : Polynomial ℂ, Commute (Polynomial.aeval (cap (a := a) τ u) p) (rt E a h) := by
      intro p
      have hle : Algebra.adjoin ℂ {cap (a := a) τ u} ≤ Subalgebra.centralizer ℂ {rt E a h} := by
        refine Algebra.adjoin_le ?_
        rintro _ rfl
        rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact hc.eq.symm
      exact ((Subalgebra.mem_centralizer_iff ℂ).1 (hle (Polynomial.aeval_mem_adjoin_singleton ℂ _)) _ rfl).symm
    rw [← Module.End.mul_apply, (hP _).eq, Module.End.mul_apply]
    have h0 : Polynomial.aeval (cap (a := a) τ u) ((Polynomial.X - Polynomial.C (χ₀ (cap τ u))) ^ N) φ = 0 := by
      have := hnil (List.replicate N (cap τ u)) (List.length_replicate ..) fun z hz => by
        rw [List.eq_of_mem_replicate hz]; exact hcap
      rw [fold_replicate_cap] at this
      simpa [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] using this
    rw [← Finset.prod_erase_mul S _ (hXS hχ₀), Polynomial.aeval_mul, Module.End.mul_apply, h0]
    simp only [map_zero]

end GlobalTheory.HCF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitOfIsotropic
section
noncomputable section

namespace GlobalTheory.MatrixHomBijective

variable {F : Type} [Field F] [CharZero F]

theorem rep_of_sq {a b s t : F} (ha : a ≠ 0) (ht : t ≠ 0) (h : s ^ 2 = a * t ^ 2) :
    ∃ p q : F, b = p ^ 2 - a * q ^ 2 := by
  have hs : s ≠ 0 := by
    rintro rfl
    have : a * t ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 ht)
    exact this (by rw [← h]; ring)
  have ha' : a = s ^ 2 / t ^ 2 := by
    rw [h]; field_simp
  refine ⟨(b + 1) / 2, (b - 1) * t / (2 * s), ?_⟩
  rw [ha']
  field_simp
  ring

theorem rep_of_isotropic {a b : F} (ha : a ≠ 0) (x : QuaternionAlgebra F a 0 b) (hx : x ≠ 0)
    (hn : GlobalTheory.QSA.nrm x = 0) : ∃ p q : F, b = p ^ 2 - a * q ^ 2 := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  simp only [GlobalTheory.QSA.nrm] at hn
  by_cases hd : x2 ^ 2 - a * x3 ^ 2 = 0
  · by_cases h3 : x3 = 0
    · subst h3
      have h2 : x2 = 0 := by
        have : x2 ^ 2 = 0 := by linear_combination hd
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      subst h2
      have h1 : x1 ≠ 0 := by
        rintro rfl
        have : x0 ^ 2 = 0 := by linear_combination hn
        have h0 : x0 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 this
        subst h0
        exact hx rfl
      exact rep_of_sq (s := x0) ha h1 (by linear_combination hn)
    · exact rep_of_sq (s := x2) ha h3 (by linear_combination hd)
  · refine ⟨(x0 * x2 - a * x1 * x3) / (x2 ^ 2 - a * x3 ^ 2),
      (x1 * x2 - x0 * x3) / (x2 ^ 2 - a * x3 ^ 2), ?_⟩
    obtain ⟨d, hdd⟩ : ∃ d, d = x2 ^ 2 - a * x3 ^ 2 := ⟨_, rfl⟩
    rw [← hdd] at hd ⊢
    have key : b * d ^ 2 = (x0 * x2 - a * x1 * x3) ^ 2 - a * (x1 * x2 - x0 * x3) ^ 2 := by
      rw [hdd]
      linear_combination (-(x2 ^ 2 - a * x3 ^ 2)) * hn
    field_simp
    linear_combination key

def mat {a b : F} (p q : F) (x : QuaternionAlgebra F a 0 b) : Matrix (Fin 2) (Fin 2) F :=
  !![x.re + p * x.imJ + a * q * x.imK, a * x.imI - a * q * x.imJ - a * p * x.imK;
    x.imI + q * x.imJ + p * x.imK, x.re - p * x.imJ - a * q * x.imK]

def hom {a b : F} (p q : F) (h : b = p ^ 2 - a * q ^ 2) :
    QuaternionAlgebra F a 0 b →ₐ[F] Matrix (Fin 2) (Fin 2) F where
  toFun := mat p q
  map_one' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [mat]
  map_mul' x y := by
    subst h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  map_zero' := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [mat]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat] <;> ring
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mat, QuaternionAlgebra.algebraMap_eq, Matrix.algebraMap_matrix_apply]

theorem mat_bijective {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (p q : F) (h : b = p ^ 2 - a * q ^ 2) :
    Function.Bijective (mat (a := a) (b := b) p q) := by
  constructor
  · intro x y hxy
    have e00 := congrFun (congrFun hxy 0) 0
    have e01 := congrFun (congrFun hxy 0) 1
    have e10 := congrFun (congrFun hxy 1) 0
    have e11 := congrFun (congrFun hxy 1) 1
    simp only [mat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at e00 e01 e10 e11
    have two : (2 : F) ≠ 0 := two_ne_zero
    ext
    · apply mul_left_cancel₀ two
      linear_combination e00 + e11
    · apply mul_left_cancel₀ (mul_ne_zero two ha)
      linear_combination e01 + a * e10
    · apply mul_left_cancel₀ (mul_ne_zero two hb)
      linear_combination p * (e00 - e11) - q * (a * e10 - e01) + 2 * (x.imJ - y.imJ) * h
    · apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two ha) hb)
      linear_combination p * (a * e10 - e01) - a * q * (e00 - e11) + 2 * a * (x.imK - y.imK) * h
  · intro M
    refine ⟨⟨(M 0 0 + M 1 1) / 2, (M 0 1 / a + M 1 0) / 2,
      (p * (M 0 0 - M 1 1) - q * (a * M 1 0 - M 0 1)) / (2 * b),
      (p * (a * M 1 0 - M 0 1) - a * q * (M 0 0 - M 1 1)) / (2 * a * b)⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat] <;> field_simp <;> rw [h] <;> ring

theorem det_mat {a b : F} (p q : F) (h : b = p ^ 2 - a * q ^ 2) (x : QuaternionAlgebra F a 0 b) :
    (mat p q x).det = GlobalTheory.QSA.nrm x := by
  subst h
  simp only [mat, Matrix.det_fin_two_of, GlobalTheory.QSA.nrm]
  ring

theorem split_of_isotropic (F : Type) [Field F] [NumberField F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : ∃ x : QuaternionAlgebra F a 0 b, x ≠ 0 ∧ GlobalTheory.QSA.nrm x = 0) :
    ∃ φ : QuaternionAlgebra F a 0 b ≃ₐ[F] Matrix (Fin 2) (Fin 2) F,
      ∀ x, Matrix.det (φ x) = GlobalTheory.QSA.nrm x := by
  obtain ⟨x, hx, hn⟩ := hx
  obtain ⟨p, q, h⟩ := rep_of_isotropic ha x hx hn
  exact ⟨AlgEquiv.ofBijective (hom p q h) (mat_bijective ha hb p q h), fun y => det_mat p q h y⟩

end GlobalTheory.MatrixHomBijective
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqrtNegPrimeKernelCyclic
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem ker_sqrtNegNat_cyclic : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → (∀ k : ℤ, (k : ℂ) * t ∈ L.lattice ↔ (p : ℤ) ∣ k) ∧ (∀ z, sqrtNegNat p * z ∈ L.lattice → ∃ k : ℕ, k < p ∧ z - (k : ℂ) * t ∈ L.lattice) ∧ IsKerReps L (sqrtNegNat p) ((Finset.Ico 1 p).image fun k : ℕ => (k : ℂ) * t) := by
  intro p F L t hp _ _ D
  have hsq : sqrtNegNat p ^ 2 = -(p : ℂ) := sqrtNegNat_sq p
  have hz : ∀ (n : ℤ) (x : ℂ), x ∈ L.lattice → (n : ℂ) * x ∈ L.lattice := fun n x hx => by
    simpa [zsmul_eq_mul] using L.lattice.smul_mem n hx
  have hpt : (p : ℂ) * t ∈ L.lattice := by
    have h := L.lattice.neg_mem (D.mul _ D.ker)
    have e : -(sqrtNegNat p * (sqrtNegNat p * t)) = (p : ℂ) * t := by
      linear_combination (-t) * hsq
    rwa [e] at h
  have h1 : ∀ k : ℤ, (k : ℂ) * t ∈ L.lattice ↔ (p : ℤ) ∣ k := by
    intro k
    constructor
    · intro hk
      by_contra hnd
      have hc : IsCoprime (p : ℤ) k := (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hnd
      obtain ⟨a, b, hab⟩ := hc
      apply D.notMem
      have h := L.lattice.add_mem (hz a _ hpt) (hz b _ hk)
      have hab' : (a : ℂ) * (p : ℂ) + (b : ℂ) * (k : ℂ) = 1 := by exact_mod_cast congrArg (Int.cast (R := ℂ)) hab
      have e : (a : ℂ) * ((p : ℂ) * t) + (b : ℂ) * ((k : ℂ) * t) = t := by
        linear_combination t * hab'
      rwa [e] at h
    · rintro ⟨c, rfl⟩
      have h := hz c _ hpt
      have e : (c : ℂ) * ((p : ℂ) * t) = (((p : ℤ) * c : ℤ) : ℂ) * t := by push_cast; ring
      rwa [e] at h
  have hker : ∀ k : ℕ, sqrtNegNat p * ((k : ℂ) * t) ∈ L.lattice := fun k => by
    have h := hz k _ D.ker
    have e : ((k : ℤ) : ℂ) * (sqrtNegNat p * t) = sqrtNegNat p * ((k : ℂ) * t) := by push_cast; ring
    rwa [e] at h
  have hnot : ∀ k ∈ Finset.Ico 1 p, (k : ℂ) * t ∉ L.lattice := fun k hk h => by
    rw [Finset.mem_Ico] at hk
    have h' : (p : ℤ) ∣ (k : ℤ) := (h1 k).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd hk.1 (Int.natCast_dvd_natCast.mp h')
    omega
  have hinj : ∀ k ∈ Finset.Ico 1 p, ∀ l ∈ Finset.Ico 1 p, (k : ℂ) * t - (l : ℂ) * t ∈ L.lattice → k = l := by
    intro k hk l hl h
    rw [Finset.mem_Ico] at hk hl
    have e : (k : ℂ) * t - (l : ℂ) * t = (((k : ℤ) - (l : ℤ) : ℤ) : ℂ) * t := by push_cast; ring
    rw [e, h1] at h
    have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hn : Complex.normSq (sqrtNegNat p) = p := by
    have h := congrArg Complex.normSq hsq
    rw [map_pow, Complex.normSq_neg, Complex.normSq_natCast, ← sq] at h
    exact (pow_left_inj₀ (Complex.normSq_nonneg _) hp0.le two_ne_zero).mp h
  have hα : sqrtNegNat p ≠ 0 := fun h => by
    rw [h, map_zero] at hn
    exact hp0.ne hn
  obtain ⟨S, hS⟩ := kerRepsExist L _ hα D.mul
  have hcard : S.card + 1 = p := by
    have h := kerRepsCard L _ S hα D.mul hS
    rw [hn] at h
    exact_mod_cast h
  choose f hfS hf using fun k (hk : k ∈ Finset.Ico 1 p) => hS.2.2 _ (hker k) (hnot k hk)
  have hsurj := Finset.surj_on_of_inj_on_of_card_le f hfS
    (fun k l hk hl h => hinj k hk l hl (by
      have h' := L.lattice.sub_mem (hf k hk) (hf l hl)
      rw [h] at h'
      simpa using h'))
    (by rw [Nat.card_Ico]; omega)
  have h3 : ∀ z, sqrtNegNat p * z ∈ L.lattice → z ∉ L.lattice →
      ∃ k ∈ Finset.Ico 1 p, z - (k : ℂ) * t ∈ L.lattice := by
    intro z hz1 hz2
    obtain ⟨P, hP, hzP⟩ := hS.2.2 z hz1 hz2
    obtain ⟨k, hk, rfl⟩ := hsurj P hP
    refine ⟨k, hk, ?_⟩
    simpa using L.lattice.sub_mem hzP (hf k hk)
  refine ⟨h1, fun z hz1 => ?_, ?_, ?_, ?_⟩
  · by_cases hz2 : z ∈ L.lattice
    · exact ⟨0, hp.pos, by simpa using hz2⟩
    · obtain ⟨k, hk, h⟩ := h3 z hz1 hz2
      exact ⟨k, (Finset.mem_Ico.mp hk).2, h⟩
  · intro P hP
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨hker k, hnot k hk⟩
  · intro P hP Q hQ h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hQ
    rw [hinj k hk l hl h]
  · intro z hz1 hz2
    obtain ⟨k, hk, h⟩ := h3 z hz1 hz2
    exact ⟨_, Finset.mem_image_of_mem _ hk, h⟩

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumAddInvLeOfConsecutiveRatioBounds
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

namespace GlobalTheory.RatioIneq

theorem chain_bound (a : ℕ) (t ρ : ℝ) (ht : 0 < t) (hρ : 1 ≤ ρ) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i)
    (hlo : ∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i)
    (hhi : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) :
    ∀ n : ℕ, ∀ i k : Fin a, (i : ℕ) + n = k →
      r i ≤ (max 1 t⁻¹ * ρ) ^ n * r k ∧ r k ≤ (max 1 t⁻¹ * ρ) ^ n * r i := by
  have hM1 : (1:ℝ) ≤ max 1 t⁻¹ := le_max_left _ _
  have hBρ : ρ ≤ max 1 t⁻¹ * ρ := le_mul_of_one_le_left (by linarith) hM1
  have hBt : t⁻¹ ≤ max 1 t⁻¹ * ρ :=
    (le_max_right 1 t⁻¹).trans (le_mul_of_one_le_right (by linarith) hρ)
  intro n
  induction n with
  | zero =>
    intro i k h
    have : i = k := Fin.ext (by simpa using h)
    subst this; simp
  | succ n ih =>
    intro i k h
    have hk' : (i : ℕ) + n < a := by have := k.isLt; omega
    obtain ⟨h1, h2⟩ := ih i ⟨i + n, hk'⟩ rfl
    have hkk : (k : ℕ) = ((⟨i + n, hk'⟩ : Fin a) : ℕ) + 1 := by simp; omega
    have n1 : r ⟨i + n, hk'⟩ ≤ (max 1 t⁻¹ * ρ) * r k :=
      (hhi _ k hkk).trans (mul_le_mul_of_nonneg_right hBρ (hr k).le)
    have n2 : r k ≤ (max 1 t⁻¹ * ρ) * r ⟨i + n, hk'⟩ := by
      have hl := hlo _ k hkk
      have : r k ≤ t⁻¹ * r ⟨i + n, hk'⟩ := by
        calc r k = t⁻¹ * (t * r k) := by rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
          _ ≤ t⁻¹ * r ⟨i + n, hk'⟩ := mul_le_mul_of_nonneg_left hl (inv_nonneg.2 ht.le)
      exact this.trans (mul_le_mul_of_nonneg_right hBt (hr _).le)
    have hB0 : 0 ≤ (max 1 t⁻¹ * ρ) := by linarith
    have hBn : 0 ≤ (max 1 t⁻¹ * ρ) ^ n := pow_nonneg hB0 n
    constructor
    · calc r i ≤ (max 1 t⁻¹ * ρ) ^ n * r ⟨i + n, hk'⟩ := h1
        _ ≤ (max 1 t⁻¹ * ρ) ^ n * ((max 1 t⁻¹ * ρ) * r k) := mul_le_mul_of_nonneg_left n1 hBn
        _ = (max 1 t⁻¹ * ρ) ^ (n+1) * r k := by ring
    · calc r k ≤ (max 1 t⁻¹ * ρ) * r ⟨i + n, hk'⟩ := n2
        _ ≤ (max 1 t⁻¹ * ρ) * ((max 1 t⁻¹ * ρ) ^ n * r i) := mul_le_mul_of_nonneg_left h2 hB0
        _ = (max 1 t⁻¹ * ρ) ^ (n+1) * r i := by ring

theorem pair_bound (a : ℕ) (t ρ : ℝ) (ht : 0 < t) (hρ : 1 ≤ ρ) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i)
    (hlo : ∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i)
    (hhi : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) (i k : Fin a) :
    r i ≤ (max 1 t⁻¹ * ρ) ^ a * r k := by
  have hB1 : 1 ≤ max 1 t⁻¹ * ρ := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hρ
  have hi := i.isLt
  have hk := k.isLt
  rcases le_total (i : ℕ) k with h | h
  · obtain ⟨h1, -⟩ := chain_bound a t ρ ht hρ r hr hlo hhi (k - i) i k (by omega)
    exact h1.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (by omega)) (hr k).le)
  · obtain ⟨-, h2⟩ := chain_bound a t ρ ht hρ r hr hlo hhi (i - k) k i (by omega)
    exact h2.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (by omega)) (hr k).le)

theorem le_max_one_of_pow_le {x c : ℝ} {a : ℕ} (ha : a ≠ 0) (h : x ^ a ≤ c) : x ≤ max 1 c := by
  rcases le_total x 1 with h1 | h1
  · exact h1.trans (le_max_left _ _)
  · exact (le_self_pow₀ h1 ha).trans (h.trans (le_max_right _ _))

end GlobalTheory.RatioIneq

namespace GlobalTheory.RatioIneq

theorem sum_add_inv_le_of_ratio_bounds :
    ∀ (a : ℕ) (t c₁ c₂ : ℝ), 0 < t → 0 < c₁ → ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ r : Fin a → ℝ,
      (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
      c₁ ≤ ∏ i, r i → ∏ i, r i ≤ c₂ → ∀ ρ : ℝ, 1 ≤ ρ →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ ρ * r j) →
      ∑ i, (r i + (r i)⁻¹) ≤ C * ρ ^ K := by
  intro a t c₁ c₂ ht hc₁
  refine ⟨a * (max 1 c₂ + max 1 c₁⁻¹) * (max 1 t⁻¹) ^ a, a, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ max 1 c₂ := (zero_le_one.trans (le_max_left _ _))
    have h2 : (0:ℝ) ≤ max 1 c₁⁻¹ := (zero_le_one.trans (le_max_left _ _))
    have h3 : (0:ℝ) ≤ max 1 t⁻¹ := (zero_le_one.trans (le_max_left _ _))
    positivity
  intro r hr hlo hP1 hP2 ρ hρ hhi
  have hB1 : 1 ≤ max 1 t⁻¹ * ρ := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hρ
  have hBa : 0 < (max 1 t⁻¹ * ρ) ^ a := pow_pos (by linarith) a
  have pb := pair_bound a t ρ ht hρ r hr hlo hhi
  have hup : ∀ i, r i ≤ max 1 c₂ * (max 1 t⁻¹ * ρ) ^ a := by
    intro i
    have ha : a ≠ 0 := by have := i.isLt; omega
    have hx : ∀ k, r i / (max 1 t⁻¹ * ρ) ^ a ≤ r k := fun k => by
      rw [div_le_iff₀ hBa, mul_comm]; exact pb i k
    have hprod : (r i / (max 1 t⁻¹ * ρ) ^ a) ^ a ≤ ∏ k, r k := by
      have := Finset.prod_le_prod₀ (s := Finset.univ)
        (f := fun _ : Fin a => r i / (max 1 t⁻¹ * ρ) ^ a) (g := r)
        (fun _ _ => (div_pos (hr i) hBa).le) (fun k _ => hx k)
      rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    have := le_max_one_of_pow_le ha (hprod.trans hP2)
    rwa [div_le_iff₀ hBa] at this
  have hdown : ∀ i, (r i)⁻¹ ≤ max 1 c₁⁻¹ * (max 1 t⁻¹ * ρ) ^ a := by
    intro i
    have ha : a ≠ 0 := by have := i.isLt; omega
    have hy : 0 < (max 1 t⁻¹ * ρ) ^ a * r i := mul_pos hBa (hr i)
    have hprod : ∏ k, r k ≤ ((max 1 t⁻¹ * ρ) ^ a * r i) ^ a := by
      have := Finset.prod_le_prod₀ (s := Finset.univ) (f := r)
        (g := fun _ : Fin a => (max 1 t⁻¹ * ρ) ^ a * r i)
        (fun k _ => (hr k).le) (fun k _ => pb k i)
      simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using this
    have hc : ((max 1 t⁻¹ * ρ) ^ a * r i)⁻¹ ^ a ≤ c₁⁻¹ := by
      rw [inv_pow]; exact inv_anti₀ hc₁ (hP1.trans hprod)
    have := le_max_one_of_pow_le ha hc
    have heq : (r i)⁻¹ = (max 1 t⁻¹ * ρ) ^ a * ((max 1 t⁻¹ * ρ) ^ a * r i)⁻¹ := by
      rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hBa.ne', one_mul]
    rw [heq, mul_comm (max 1 c₁⁻¹)]
    exact mul_le_mul_of_nonneg_left this hBa.le
  calc ∑ i, (r i + (r i)⁻¹)
      ≤ ∑ _i : Fin a, (max 1 c₂ + max 1 c₁⁻¹) * (max 1 t⁻¹ * ρ) ^ a :=
        Finset.sum_le_sum fun i _ => by rw [add_mul]; exact add_le_add (hup i) (hdown i)
    _ = a * (max 1 c₂ + max 1 c₁⁻¹) * (max 1 t⁻¹) ^ a * ρ ^ a := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_pow]; ring

end GlobalTheory.RatioIneq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPadicValNatMulLogLeLog
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem sum_padicValNat_mul_log_le_log (n : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p ≤ Real.log n := by
  classical
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  have h1 : ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p
      = ∑ p ∈ S, (n.factorization p : ℝ) * Real.log p :=
    Finset.sum_congr rfl fun p hp => by rw [Nat.factorization_def n (hS p hp), Nat.padicValNat_def]
  rw [h1]
  have h2 : ∑ p ∈ S ∪ n.factorization.support, (n.factorization p : ℝ) * Real.log p
      = ∑ p ∈ n.factorization.support, (n.factorization p : ℝ) * Real.log p := by
    symm
    refine Finset.sum_subset Finset.subset_union_right fun p _ hp => ?_
    rw [Finsupp.notMem_support_iff.1 hp]; simp
  rw [← h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

theorem sum_vDiff_mul_log_le :
    ∀ (D : D7) (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p, 0 ≤ vDiff D p) ∧ ∑ p ∈ S, vDiff D p * Real.log p ≤ Real.log D.host.rdE := by
  intro D S hS
  refine ⟨fun p => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  have hn : (0 : ℝ) < (Module.finrank ℚ D.host.E : ℝ) := by exact_mod_cast Module.finrank_pos
  have hd : (0 : ℝ) < |(discr D.host.E : ℝ)| := by
    rw [abs_pos]; exact_mod_cast discr_ne_zero D.host.E
  have hc : ((WeightThresholdDefs.dE D : ℕ) : ℝ) = |(discr D.host.E : ℝ)| := by
    rw [WeightThresholdDefs.dE, Nat.cast_natAbs, Int.cast_abs]
  have hr : Real.log D.host.rdE = Real.log (WeightThresholdDefs.dE D : ℕ) / (Module.finrank ℚ D.host.E : ℝ) := by
    rw [hc]
    unfold Host.rdE
    rw [Real.log_rpow hd]; ring
  rw [hr]
  refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right (sum_padicValNat_mul_log_le_log (WeightThresholdDefs.dE D) S hS) hn.le)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [vDiff]; ring

end GlobalTheory.MeanTop
end

