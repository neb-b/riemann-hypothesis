module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TransvectionIdentitiesUnitary
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Calc

variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)

theorem hf_add_left (x x' y : Fin n → R) : hf σ G (x + x') y = hf σ G x y + hf σ G x' y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y y' : Fin n → R) : hf σ G x (y + y') = hf σ G x y + hf σ G x y' := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_left (c : R) (x y : Fin n → R) : hf σ G (c • x) y = c * hf σ G x y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_smul_right (c : R) (x y : Fin n → R) : hf σ G x (c • y) = σ c * hf σ G x y := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hf_conj (hσ : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a) (x y : Fin n → R) :
    σ (hf σ G x y) = hf σ G y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, hσ, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem tv_mulVec (x : Fin n → R) (t : R) (v : Fin n → R) :
    tv σ G x t *ᵥ v = v + (t * hf σ G v x) • x := by
  rw [tv, Matrix.add_mulVec, Matrix.one_mulVec]
  ext a
  simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  simp only [hf]
  simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem ext_mulVec {A B : Matrix (Fin n) (Fin n) R} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

theorem tv_mul (x : Fin n → R) (t t' : R) :
    tv σ G x t * tv σ G x t' = tv σ G x (t + t' + t * t' * hf σ G x x) := by
  refine ext_mulVec fun v => ?_
  rw [← Matrix.mulVec_mulVec, tv_mulVec, tv_mulVec, tv_mulVec, hf_add_left, hf_smul_left,
    add_assoc, ← add_smul]
  congr 2
  ring

theorem tv_det (x : Fin n → R) (t : R) : (tv σ G x t).det = 1 + t * hf σ G x x := by
  have h : tv σ G x t = 1 + Matrix.replicateCol Unit (t • x) *
      Matrix.replicateRow Unit (fun b => ∑ e, G b e * σ (x e)) := by
    rw [tv]
    congr 1
    ext a b
    simp [Matrix.mul_apply]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simp only [dotProduct, hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem isU_tv (hσ : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a) (x : Fin n → R) (t : R)
    (h : t + σ t + t * σ t * hf σ G x x = 0) : IsU σ G (tv σ G x t) := by
  intro v w
  rw [tv_mulVec, tv_mulVec]
  simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, map_mul, hf_conj σ G hσ hG]
  linear_combination (hf σ G v x * hf σ G x w) * h

theorem conj_tv (γ : Matrix (Fin n) (Fin n) R) (x : Fin n → R) (t : R) (h : IsU σ G γ) :
    γ * tv σ G x t = tv σ G (γ *ᵥ x) t * γ := by
  refine ext_mulVec fun v => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tv_mulVec, tv_mulVec, h, Matrix.mulVec_add,
    Matrix.mulVec_smul]

theorem tv_smul (a : R) (x : Fin n → R) (t : R) :
    tv σ G (a • x) t = tv σ G x (t * a * σ a) := by
  refine ext_mulVec fun v => ?_
  rw [tv_mulVec, tv_mulVec, hf_smul_right, smul_smul]
  congr 2
  ring

theorem isU_mul (γ γ' : Matrix (Fin n) (Fin n) R) (h : IsU σ G γ) (h' : IsU σ G γ') :
    IsU σ G (γ * γ') := by
  intro v w
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, h']

theorem calculus : ∀ (R : Type) [CommRing R] (n : ℕ) (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R), (∀ a, σ (σ a) = a) → (∀ a b, σ (G a b) = G b a) → (∀ x y, σ (hf σ G x y) = hf σ G y x) ∧ (∀ x t v, tv σ G x t *ᵥ v = v + (t * hf σ G v x) • x) ∧ (∀ x t t', tv σ G x t * tv σ G x t' = tv σ G x (t + t' + t * t' * hf σ G x x)) ∧ (∀ x t, (tv σ G x t).det = 1 + t * hf σ G x x) ∧ (∀ x t, t + σ t + t * σ t * hf σ G x x = 0 → IsU σ G (tv σ G x t)) ∧ (∀ γ x t, IsU σ G γ → γ * tv σ G x t = tv σ G (γ *ᵥ x) t * γ) ∧ (∀ (a : R) x t, tv σ G (a • x) t = tv σ G x (t * a * σ a)) ∧ (∀ γ γ', IsU σ G γ → IsU σ G γ' → IsU σ G (γ * γ')) :=
  fun _ _ _ σ G hσ hG => ⟨hf_conj σ G hσ hG, tv_mulVec σ G, tv_mul σ G, tv_det σ G, isU_tv σ G hσ hG,
    conj_tv σ G, tv_smul σ G, isU_mul σ G⟩

end GlobalTheory.UTrans.Calc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulIndexSqsInvolution
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private theorem mem_sqs_iff_exists_sq {G : Type} [CommGroup G] (U : Subgroup G) (x : G) :
    x ∈ sqs U ↔ ∃ y ∈ U, y ^ 2 = x := by
  simp [sqs, Subgroup.mem_map]

theorem two_mul_index_sqs_involution :
    ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) →
      (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε →
      (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) →
      2 * (sqs (⊤ : Subgroup A)).index =
        (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) *
          (sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker := by
  intro A _ σ ε hσ h90 hε1 hε2 hσε h2
  set B : Subgroup A := σ.eqLocus (MonoidHom.id A) with hB
  set N : Subgroup A := (MonoidHom.id A * σ).ker with hN
  set S : Subgroup A := sqs (⊤ : Subgroup A) with hS
  have memB : ∀ a, a ∈ B ↔ σ a = a := fun a => Iff.rfl
  have memN : ∀ a, a ∈ N ↔ a * σ a = 1 := fun a => Iff.rfl
  have memS : ∀ a, a ∈ S ↔ ∃ y, y ^ 2 = a := fun a => by
    rw [hS, mem_sqs_iff_exists_sq]; simp
  let f : A →* A := MonoidHom.id A / σ
  have hf : ∀ a, f a = a / σ a := fun a => rfl
  have hker : ∀ a, f a = 1 ↔ a ∈ B := fun a => by
    rw [hf, memB, div_eq_one, eq_comm]
  have hrange : f.range = N := by
    ext x
    rw [memN, MonoidHom.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      rw [hf, map_div, hσ]; simp
    · intro hx
      obtain ⟨b, hb⟩ := h90 x hx
      exact ⟨b, hb.symm⟩
  have hcomap : B ⊔ S = (sqs N).comap f := by
    apply le_antisymm
    · apply sup_le
      · intro a ha
        rw [Subgroup.mem_comap, (hker a).2 ha]
        exact one_mem _
      · intro a ha
        obtain ⟨y, rfl⟩ := (memS a).1 ha
        rw [Subgroup.mem_comap, mem_sqs_iff_exists_sq]
        exact ⟨f y, hrange ▸ ⟨y, rfl⟩, (map_pow f y 2).symm⟩
    · intro a ha
      rw [Subgroup.mem_comap, mem_sqs_iff_exists_sq] at ha
      obtain ⟨c, hc, hca⟩ := ha
      rw [← hrange] at hc
      obtain ⟨b, rfl⟩ := hc
      have h1 : a / b ^ 2 ∈ B := by
        rw [← hker, map_div, map_pow, hca, div_self']
      have : a = a / b ^ 2 * b ^ 2 := by simp
      rw [this]
      exact Subgroup.mul_mem_sup h1 ((memS _).2 ⟨b, rfl⟩)
  have e1 : (B ⊔ S).index = (sqs N).relIndex N := by
    rw [hcomap, Subgroup.index_comap, hrange]
  have e2 : S.relIndex (B ⊔ S) * (B ⊔ S).index = S.index :=
    Subgroup.relIndex_mul_index le_sup_right
  have e3 : S.relIndex (B ⊔ S) = S.relIndex B := Subgroup.relIndex_sup_right B S
  have hle : sqs B ≤ S ⊓ B := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := (mem_sqs_iff_exists_sq _ _).1 ha
    exact ⟨(memS _).2 ⟨y, rfl⟩, pow_mem hy 2⟩
  have e4 : (sqs B).relIndex (S ⊓ B) * (S ⊓ B).relIndex B = (sqs B).relIndex B :=
    Subgroup.relIndex_mul_relIndex _ _ _ hle inf_le_right
  have e5 : (S ⊓ B).relIndex B = S.relIndex B := Subgroup.inf_relIndex_right S B
  have hεB : ε ∈ B := hσε
  have key : ∀ y, y ^ 2 ∈ sqs B ↔ f y = 1 := by
    intro y
    rw [mem_sqs_iff_exists_sq, hker]
    constructor
    · rintro ⟨b, hb, hby⟩
      have : (y / b) ^ 2 = 1 := by rw [div_pow, hby, div_self']
      have hyb : y / b ∈ B := by
        rcases h2 _ this with h | h
        · rw [h]; exact one_mem _
        · rw [h]; exact hεB
      simpa using mul_mem hyb hb
    · intro hy
      exact ⟨y, hy, rfl⟩
  obtain ⟨a0, ha0⟩ := h90 ε (by rw [hσε, ← sq, hε2])
  rw [← hf] at ha0
  have e6 : (sqs B).relIndex (S ⊓ B) = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    have h0 : a0 ^ 2 ∈ S ⊓ B :=
      ⟨(memS _).2 ⟨a0, rfl⟩, (hker _).1 (by rw [map_pow, ← ha0, hε2])⟩
    refine ⟨⟨a0 ^ 2, h0⟩, ?_⟩
    rintro ⟨x, hxS, hxB⟩
    obtain ⟨y, rfl⟩ := (memS x).1 hxS
    have hy : f y ^ 2 = 1 := by rw [← map_pow]; exact (hker _).2 hxB
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rw [← mul_pow, key, key, map_mul, ← ha0]
    rcases h2 _ hy with h | h
    · rw [h, one_mul]
      exact Or.inr ⟨rfl, hε1⟩
    · rw [h, ← sq]
      exact Or.inl ⟨hε2, hε1⟩
  rw [← e2, e1, e3, ← e4, e5, e6, mul_assoc]

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnipotentUpperSizeReduction
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem unipotent_size_reduction_column {N : ℕ} (n : Matrix (Fin N) (Fin N) ℝ)
    (h1 : ∀ i, n i i = 1) (h0 : ∀ i j, j < i → n i j = 0) (j : Fin N) (k : ℕ) :
    ∃ z : Fin N → ℤ, z j = 1 ∧ (∀ l, j < l → z l = 0) ∧
      ∀ i, i < j → (j : ℕ) ≤ i + k → |∑ l, n i l * (z l : ℝ)| ≤ 1 / 2 := by
  induction k with
  | zero =>
    refine ⟨Pi.single j 1, by simp, fun l hl => by simp [Pi.single_apply, hl.ne'], ?_⟩
    intro i hi hk
    exact absurd hk (by have : (i : ℕ) < j := hi; omega)
  | succ k ih =>
    obtain ⟨z, hz1, hz0, hz⟩ := ih
    by_cases hk : k + 1 ≤ (j : ℕ)
    · let i0 : Fin N := ⟨j - (k + 1), by have := j.2; omega⟩
      have hi0v : (i0 : ℕ) = j - (k + 1) := rfl
      have hi0 : i0 < j := by
        show (i0 : ℕ) < j
        omega
      set c : ℤ := -round (∑ l, n i0 l * (z l : ℝ)) with hc
      have key : ∀ i, ∑ l, n i l * (((z + Pi.single i0 c : Fin N → ℤ) l : ℤ) : ℝ)
          = ∑ l, n i l * (z l : ℝ) + n i i0 * c := by
        intro i
        simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single i0]
        · simp
        · intro b _ hb
          simp [Pi.single_apply, hb]
        · simp
      refine ⟨z + Pi.single i0 c, ?_, ?_, ?_⟩
      · simp [Pi.single_apply, hi0.ne', hz1]
      · intro l hl
        simp [Pi.single_apply, (hi0.trans hl).ne', hz0 l hl]
      · intro i hi hik
        rw [key]
        by_cases h : i = i0
        · subst h
          rw [h1, one_mul, hc, Int.cast_neg, ← sub_eq_add_neg]
          exact abs_sub_round _
        · have hne : (i : ℕ) ≠ i0 := fun e => h (Fin.ext e)
          have hlt : i0 < i := by
            show (i0 : ℕ) < i
            omega
          rw [h0 i i0 hlt, zero_mul, add_zero]
          exact hz i hi (by omega)
    · exact ⟨z, hz1, hz0, fun i hi _ => hz i hi (by omega)⟩

theorem unipotent_size_reduction :
    ∀ (N : ℕ) (n : Matrix (Fin N) (Fin N) ℝ), (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) →
      ∃ ν : Matrix (Fin N) (Fin N) ℤ, (∀ i, ν i i = 1) ∧ (∀ i j, j < i → ν i j = 0) ∧
        ∀ i j, i < j → |(n * ν.map (Int.cast : ℤ → ℝ)) i j| ≤ 1 / 2 := by
  intro N n h1 h0
  choose z hz1 hz0 hz using fun j => unipotent_size_reduction_column n h1 h0 j N
  refine ⟨Matrix.of fun i j => z j i, fun i => hz1 i, fun i j h => hz0 j i h, ?_⟩
  intro i j hij
  rw [Matrix.mul_apply]
  exact hz j i hij (by have := j.2; omega)

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryCharPiComplexUnitsEqProdZpow
section
open scoped Topology BigOperators

namespace GlobalTheory

open scoped Topology BigOperators in
private lemma continuous_circle_toUnits' : Continuous Circle.toUnits := by
  rw [Units.continuous_iff]
  refine ⟨continuous_subtype_val, ?_⟩
  have : Continuous (fun w : Circle => ((w⁻¹ : Circle) : ℂ)) :=
    continuous_subtype_val.comp continuous_inv
  convert this using 2 with w
  simp

open scoped Topology BigOperators in
private lemma div_norm_sq_eq_div_conj_of_ne_zero (x : ℂ) (hx : x ≠ 0) :
    (x / ‖x‖) ^ 2 = x / starRingEnd ℂ x := by
  have h : x * starRingEnd ℂ x = ((‖x‖ : ℂ)) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hc : starRingEnd ℂ x ≠ 0 := by simpa using hx
  rw [div_pow, ← h]
  field_simp


open scoped Topology BigOperators in
theorem _root_.GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow :
    ∀ (ι : Type) [Fintype ι] (f : (ι → ℂˣ) →* Circle), Continuous f → (∀ z : ι → ℂˣ, (∀ i, ((z i : ℂ)).im = 0) → f z = 1) → ∃ k : ι → ℤ, ∀ z, ((f z : Circle) : ℂ) = ∏ i, ((z i : ℂ) / starRingEnd ℂ (z i : ℂ)) ^ k i := by
  intro ι _ f hf hreal
  classical
  let g : ι → Circle →* Circle := fun i =>
    f.comp ((MonoidHom.mulSingle (fun _ => ℂˣ) i).comp Circle.toUnits)
  have hg : ∀ i, Continuous (g i) := fun i =>
    hf.comp ((continuous_mulSingle i).comp continuous_circle_toUnits')
  choose n hn using fun i => _root_.GlobalTheory.circle_hom_eq_zpow (g i) (hg i)
  have heven : ∀ i, Even (n i) := by
    intro i
    have h1 : g i (Circle.exp Real.pi) = 1 := by
      apply hreal
      intro j
      by_cases hj : j = i
      · subst hj
        simp [Circle.coe_exp, Complex.exp_pi_mul_I]
      · simp [Pi.mulSingle_eq_of_ne hj]
    rw [hn] at h1
    have h2 := congrArg (fun w : Circle => (w : ℂ)) h1
    simp [Circle.coe_exp, Complex.exp_pi_mul_I] at h2
    rcases Int.even_or_odd (n i) with h | h
    · exact h
    · rw [h.neg_one_zpow] at h2
      norm_num at h2
  choose k hk using heven
  refine ⟨k, fun z => ?_⟩
  have hne : ∀ i, ((‖(z i : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun i => by simp
  set u : ι → Circle := fun i => Circle.exp (Complex.arg (z i)) with hu_def
  have hu : ∀ i, ((u i : Circle) : ℂ) = (z i : ℂ) / ‖(z i : ℂ)‖ := by
    intro i
    rw [eq_div_iff (hne i), mul_comm]
    simpa [u, Circle.coe_exp] using Complex.norm_mul_exp_arg_mul_I (z i : ℂ)
  have hz : z = (fun i => Units.mk0 ((‖(z i : ℂ)‖ : ℝ) : ℂ) (hne i)) *
      fun i => Circle.toUnits (u i) := by
    funext i
    ext
    simp only [Pi.mul_apply, Units.val_mul, Units.val_mk0]
    simp [hu, mul_div_cancel₀ _ (hne i)]
  have hr : f (fun i => Units.mk0 ((‖(z i : ℂ)‖ : ℝ) : ℂ) (hne i)) = 1 :=
    hreal _ fun i => by simp
  have hv : f (fun i => Circle.toUnits (u i)) = ∏ i, g i (u i) := by
    conv_lhs => rw [← Finset.univ_prod_mulSingle (fun i => Circle.toUnits (u i))]
    rw [map_prod]
    rfl
  have hfz : f z = ∏ i, g i (u i) := by
    conv_lhs => rw [hz]
    rw [map_mul, hr, one_mul, hv]
  rw [hfz]
  refine (map_prod Circle.coeHom (fun i => g i (u i)) Finset.univ).trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  show ((g i (u i) : Circle) : ℂ) = _
  rw [hn, Circle.coe_zpow, hu, hk i, ← two_mul, zpow_mul, zpow_ofNat,
    div_norm_sq_eq_div_conj_of_ne_zero _ (z i).ne_zero]

end GlobalTheory
end

