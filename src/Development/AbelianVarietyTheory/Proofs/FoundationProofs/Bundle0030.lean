module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankEichlerShimuraCoboundariesOfGammaLe
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.CobDim

lemma eval_polySlash (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) (x : ℂ) :
    (slP w g p).eval x = ∑ i ∈ Finset.range (w + 1), p.coeff i *
      (((g 0 0 : ℤ) : ℂ) * x + ((g 0 1 : ℤ) : ℂ)) ^ i * (((g 1 0 : ℤ) : ℂ) * x + ((g 1 1 : ℤ) : ℂ)) ^ (w - i) := by
  simp [slP, LinearMap.sum_apply, eval_finsetSum, mul_assoc]

lemma natDeg_lt {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) : p.natDegree < w + 1 := by
  by_cases h : p = 0
  · simp [h]
  · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)

def upU (M : ℕ) : SL(2, ℤ) := ⟨!![1, (M : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩

lemma upU_mem (M : ℕ) : upU M ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp [upU]

def loU (M : ℕ) : SL(2, ℤ) := ⟨!![1, 0; (M : ℤ), 1], by simp [Matrix.det_fin_two]⟩

lemma loU_mem (M : ℕ) : loU M ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp [loU]

lemma eval_shift {w M : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1))
    (h : slP w (mat (upU M)) p = p) (x : ℂ) : p.eval (x + M) = p.eval x := by
  have h1 := eval_polySlash w (mat (upU M)) p x
  rw [h] at h1
  rw [h1, eval_eq_sum_range' (natDeg_lt hp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [upU, mat, add_comm]

lemma eq_const_of_shift {w M : ℕ} (hM : 0 < M) {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1))
    (h : slP w (mat (upU M)) p = p) : p = C (p.eval 0) := by
  have hroot : ∀ n : ℕ, (p - C (p.eval 0)).IsRoot ((n : ℂ) * M) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := eval_shift hp h ((n : ℂ) * M)
      simp only [IsRoot, eval_sub, eval_C] at ih ⊢
      push_cast
      rw [add_mul, one_mul, this, ih]
  have hinf : {x | (p - C (p.eval 0)).IsRoot x}.Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ) * M) ?_ hroot
    intro a b hab
    have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    exact_mod_cast mul_right_cancel₀ hM' hab
  exact sub_eq_zero.1 (eq_zero_of_infinite_isRoot _ hinf)

lemma const_eq_zero {w M : ℕ} (hM : 0 < M) (hw : 1 ≤ w) (c : ℂ) (h : slP w (mat (loU M)) (C c) = C c) : c = 0 := by
  have h1 := eval_polySlash w (mat (loU M)) (C c) 1
  rw [h, eval_C, Finset.sum_eq_single 0] at h1
  · simp [loU, mat] at h1
    have hne : ((M : ℂ) + 1) ^ w ≠ 1 := by
      have : (M + 1) ^ w ≠ 1 := by
        have : 1 < (M + 1) ^ w := Nat.one_lt_pow (by omega) (by omega)
        omega
      exact_mod_cast this
    by_contra hc
    exact hne (by
      have := h1.symm
      field_simp at this
      linear_combination this)
  · intro i _ hi
    simp [coeff_C, hi]
  · simp

end GlobalTheory.HeckeFamilyMatrices.CobDim

open GlobalTheory.HeckeFamilyMatrices.CobDim in
theorem GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCoboundaries_of_Gamma_le : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (w : ℕ), 0 < M → 1 ≤ w →
    CongruenceSubgroup.Gamma M ≤ Γ → Module.finrank ℂ (B1 Γ w) = w + 1 := by
  intro M Γ w hM hw hΓ
  unfold B1
  rw [LinearMap.finrank_range_of_inj, (degreeLTEquiv ℂ (w + 1)).finrank_eq, Module.finrank_fin_fun]
  intro p q hpq
  rw [← sub_eq_zero, ← map_sub] at hpq
  rw [← sub_eq_zero]
  set r := p - q with hr
  have hfix : ∀ γ : Γ, slP w (mat γ) (r : ℂ[X]) = r := by
    intro γ
    have := congrFun hpq γ
    simpa [sub_eq_zero] using this
  have hc := eq_const_of_shift hM r.2 (hfix ⟨upU M, hΓ (upU_mem M)⟩)
  have h0 : (r : ℂ[X]).eval 0 = 0 := by
    apply const_eq_zero hM hw
    rw [← hc]
    exact hfix ⟨loU M, hΓ (loU_mem M)⟩
  ext1
  rw [hc, h0]
  simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerBasisIndependent
section
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem laurent_terms_eq_zero_of_order_injOn {K ι : Type*} [Field K] (s : Finset ι)
    (f : ι → LaurentSeries K)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → f j ≠ 0 → (f i).order = (f j).order → i = j)
    (hsum : ∑ i ∈ s, f i = 0) : ∀ i ∈ s, f i = 0 := by
  classical
  by_contra hne
  push Not at hne
  have hnon : (s.filter fun i => f i ≠ 0).Nonempty := by
    obtain ⟨i, hi, hfi⟩ := hne
    exact ⟨i, Finset.mem_filter.2 ⟨hi, hfi⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image _ (fun i => (f i).order) hnon
  obtain ⟨his, hfi⟩ := Finset.mem_filter.1 hi
  have h1 : (∑ j ∈ s, f j).coeff (f i).order = (f i).coeff (f i).order := by
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_single_of_mem i his ?_
    intro j hj hji
    by_cases hfj : f j = 0
    · simp [hfj]
    · apply HahnSeries.coeff_eq_zero_of_lt_order
      exact lt_of_le_of_ne (hmin j (Finset.mem_filter.2 ⟨hj, hfj⟩))
        (fun h => hji (hinj i his j hj hfi hfj h).symm)
  rw [hsum] at h1
  exact hfi (HahnSeries.coeff_order_eq_zero.1 (by simpa using h1.symm))

theorem laurent_pow_indep_over_prime_pow_powers :
    ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (c : ℕ → LaurentSeries (ZMod p)), ∑ i ∈ Finset.range (p ^ n), c i ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ i = 0 → ∀ i < p ^ n, c i = 0 := by
  intro p _ n c hsum i hi
  have hX : ∀ j : ℕ, (HahnSeries.single (1 : ℤ) (1 : ZMod p) : LaurentSeries (ZMod p)) ^ j ≠ 0 :=
    fun j => pow_ne_zero _ (HahnSeries.single_ne_zero one_ne_zero)
  have hord : ∀ j : ℕ, c j ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ j ≠ 0 →
      (c j ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ j).order
        = ((p ^ n : ℕ) : ℤ) * (c j).order + j := by
    intro j hj
    rw [HahnSeries.order_mul (left_ne_zero_of_mul hj) (hX j), HahnSeries.order_pow,
      HahnSeries.order_pow, HahnSeries.order_single one_ne_zero]
    simp
  have key := laurent_terms_eq_zero_of_order_injOn (Finset.range (p ^ n))
    (fun j => c j ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ j) ?_ hsum i
    (Finset.mem_range.2 hi)
  · exact pow_eq_zero_iff (by omega) |>.1 ((mul_eq_zero.1 key).resolve_right (hX i))
  · intro a ha b hb hfa hfb h
    have h' := (hord a hfa).symm.trans (h.trans (hord b hfb))
    have ha' := Finset.mem_range.1 ha
    have hb' := Finset.mem_range.1 hb
    have hm := congrArg (fun z : ℤ => z % ((p ^ n : ℕ) : ℤ)) h'
    simp only [Int.mul_add_emod_self_left] at hm
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha'),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hb')] at hm
    exact_mod_cast hm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerReductionCongruence
section
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem aeval_qq_pow_sub_lt_one : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (v : Valuation Ωl ℝ≥0), (∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) → v (p : Ωl) < 1 → ∀ (T : Tower p Ωl) (n : ℕ) (f : (O0 p)[X]), f.natDegree < p ^ n → v (aeval (T.qq n) f ^ (p ^ n) - algebraMap (O0 p) Ωl (∑ i ∈ Finset.range (p ^ n), f.coeff i ^ (p ^ n) * qO p ^ i)) < 1 := by
  intro p hp Ωl _ _ _ v hv hvp T n f hf
  classical
  have hpr : p.Prime := hp.out
  have hq : IsIntegral (O0 p) (T.qq n) :=
    IsIntegral.of_pow (pow_pos hpr.pos n) (by rw [GlobalTheory.K5.Basic.qq_pow]; exact isIntegral_algebraMap)
  let t : ℕ → integralClosure (O0 p) Ωl := fun i =>
    ⟨algebraMap (O0 p) Ωl (f.coeff i) * T.qq n ^ i, isIntegral_algebraMap.mul (hq.pow i)⟩
  have key : ∀ s : Finset ℕ, ∃ r : integralClosure (O0 p) Ωl,
      (∑ i ∈ s, t i) ^ p ^ n = ∑ i ∈ s, t i ^ p ^ n + p * r := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp [zero_pow (pow_ne_zero _ hpr.ne_zero)]⟩
    | insert a s ha ih =>
      obtain ⟨r, hr⟩ := ih
      obtain ⟨r', hr'⟩ := exists_add_pow_prime_pow_eq hpr (t a) (∑ i ∈ s, t i) n
      exact ⟨r + t a * (∑ i ∈ s, t i) * r', by rw [Finset.sum_insert ha, Finset.sum_insert ha, hr', hr]; ring⟩
  obtain ⟨r, hr⟩ := key (Finset.range (p ^ n))
  have term : ∀ i, ((t i ^ p ^ n : integralClosure (O0 p) Ωl) : Ωl) =
      algebraMap (O0 p) Ωl (f.coeff i ^ p ^ n * qO p ^ i) := by
    intro i
    rw [SubmonoidClass.coe_pow, map_mul, map_pow, map_pow]
    show (algebraMap (O0 p) Ωl (f.coeff i) * T.qq n ^ i) ^ p ^ n = _
    rw [mul_pow, ← pow_mul, mul_comm i, pow_mul, GlobalTheory.K5.Basic.qq_pow]
  have e1 : aeval (T.qq n) f = ((∑ i ∈ Finset.range (p ^ n), t i : integralClosure (O0 p) Ωl) : Ωl) := by
    rw [aeval_eq_sum_range' hf]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def]
  have e2 : algebraMap (O0 p) Ωl (∑ i ∈ Finset.range (p ^ n), f.coeff i ^ p ^ n * qO p ^ i) =
      ((∑ i ∈ Finset.range (p ^ n), t i ^ p ^ n : integralClosure (O0 p) Ωl) : Ωl) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun i _ => (term i).symm
  have e3 : aeval (T.qq n) f ^ p ^ n - algebraMap (O0 p) Ωl
      (∑ i ∈ Finset.range (p ^ n), f.coeff i ^ p ^ n * qO p ^ i) = (p : Ωl) * (r : Ωl) := by
    rw [e1, e2, ← SubmonoidClass.coe_pow, hr]
    push_cast
    ring
  rw [e3, map_mul]
  have hr1 : v (r : Ωl) ≤ 1 := (hv _).2 r.2
  calc v (p : Ωl) * v (r : Ωl) ≤ v (p : Ωl) * 1 := by gcongr
    _ = v (p : Ωl) := mul_one _
    _ < 1 := hvp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumMulGaussSumInvPrim
section
noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

theorem gaussSum_mul_gaussSum_inv_prim {K : Type} [Field K] {n : ℕ} [NeZero n]
    {χ : DirichletCharacter K n} {e : AddChar (ZMod n) K} (hχ : χ.IsPrimitive)
    (he : e.IsPrimitive) : gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = (n : K) := by
  classical
  have h1 : ∀ a b : ZMod n, e (b * a) * e⁻¹ b = e (b * (a - 1)) := by
    intro a b
    rw [AddChar.inv_apply, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc gaussSum χ e * gaussSum χ⁻¹ e⁻¹
      = ∑ b, gaussSum χ (e.mulShift b) * e⁻¹ b := by
        rw [show gaussSum χ⁻¹ e⁻¹ = ∑ b, χ⁻¹ b * e⁻¹ b from rfl, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [gaussSum_mulShift_of_isPrimitive e hχ]
        ring
    _ = ∑ b, ∑ a, χ a * e (b * (a - 1)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [gaussSum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [AddChar.mulShift_apply, mul_assoc, h1]
    _ = ∑ a, χ a * ∑ b, e (b * (a - 1)) := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
    _ = ∑ a, χ a * (if a - 1 = 0 then (Fintype.card (ZMod n) : K) else 0) := by
        simp_rw [AddChar.sum_mulShift _ he, Nat.cast_ite, Nat.cast_zero]
    _ = n := by
        simp [sub_eq_zero, ZMod.card]

end GlobalTheory.KummerEisensteinGalois
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricFixedMemClosureFiniteAlgZp
section
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.GeoFix

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem exists_finset_of_mem_closure (R A : Set Ω) {x : Ω} (hx : x ∈ Subfield.closure (R ∪ A)) :
    ∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ x ∈ Subfield.closure (R ∪ (S : Set Ω)) := by
  classical
  have mono : ∀ {S S' : Finset Ω}, S ⊆ S' →
      Subfield.closure (R ∪ (S : Set Ω)) ≤ Subfield.closure (R ∪ (S' : Set Ω)) := fun h =>
    Subfield.closure_mono (Set.union_subset_union_right _ (Finset.coe_subset.2 h))
  have two : ∀ {y z : Ω}, (∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ y ∈ Subfield.closure (R ∪ (S : Set Ω))) →
      (∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ z ∈ Subfield.closure (R ∪ (S : Set Ω))) →
      ∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ y ∈ Subfield.closure (R ∪ (S : Set Ω)) ∧
        z ∈ Subfield.closure (R ∪ (S : Set Ω)) := by
    rintro y z ⟨S, hS, hy⟩ ⟨S', hS', hz⟩
    refine ⟨S ∪ S', ?_, mono Finset.subset_union_left hy, mono Finset.subset_union_right hz⟩
    rw [Finset.coe_union]; exact Set.union_subset hS hS'
  let F : Subfield Ω :=
    { carrier := {y | ∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ y ∈ Subfield.closure (R ∪ (S : Set Ω))}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨S, hS, h1, h2⟩ := two ha hb
        exact ⟨S, hS, mul_mem h1 h2⟩
      one_mem' := ⟨∅, by simp, one_mem _⟩
      add_mem' := fun {a b} ha hb => by
        obtain ⟨S, hS, h1, h2⟩ := two ha hb
        exact ⟨S, hS, add_mem h1 h2⟩
      zero_mem' := ⟨∅, by simp, zero_mem _⟩
      neg_mem' := fun {a} ⟨S, hS, h1⟩ => ⟨S, hS, neg_mem h1⟩
      inv_mem' := fun a ⟨S, hS, h1⟩ => ⟨S, hS, inv_mem h1⟩ }
  have hle : Subfield.closure (R ∪ A) ≤ F := by
    rw [Subfield.closure_le]
    rintro y (hy | hy)
    · exact ⟨∅, by simp, Subfield.subset_closure (Or.inl hy)⟩
    · refine ⟨{y}, by simpa using hy, Subfield.subset_closure (Or.inr (by simp))⟩
  exact hle hx


variable (p Ω) in
def geoField : Subfield Ω :=
  Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x : Ω | IsAlgZp (p := p) x})

theorem mem_geoField_of_fixed (h : IsClo p Ω) (x : Ω) (hx : ∀ g ∈ Ggeo (p := p) Ω, g x = x) :
    x ∈ geoField p Ω := by
  haveI := h.clo
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  have hR : ∀ a : O0 p, algebraMap (O0 p) Ω a ∈ geoField p Ω := fun a =>
    Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  let f : O0 p →+* geoField p Ω := (algebraMap (O0 p) Ω).codRestrict (geoField p Ω) hR
  have hf : (algebraMap (geoField p Ω) Ω).comp f = algebraMap (O0 p) Ω := by ext; rfl
  have hfi : Function.Injective f := fun a b hab => h.inj (congrArg Subtype.val hab)
  have hAlg : Algebra.IsAlgebraic (geoField p Ω) Ω := ⟨fun a => by
    obtain ⟨P, hP0, hP⟩ := h.alg.isAlgebraic a
    refine ⟨P.map f, (Polynomial.map_ne_zero_iff hfi).2 hP0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hf, ← Polynomial.aeval_def, hP]⟩
  letI : Algebra.IsAlgebraic (geoField p Ω) Ω := hAlg
  haveI : IsAlgClosure (geoField p Ω) Ω := ⟨h.clo, hAlg⟩
  haveI : CharZero (geoField p Ω) := ⟨fun m n e =>
    CharZero.cast_injective (congrArg Subtype.val e)⟩
  haveI : IsGalois (geoField p Ω) Ω := inferInstance
  have hbot : x ∈ (⊥ : IntermediateField (geoField p Ω) Ω) := by
    refine (InfiniteGalois.mem_bot_iff_fixed x).2 fun σ => ?_
    let τ : Ω ≃ₐ[O0 p] Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv)
      (fun a => σ.commutes ⟨_, hR a⟩)
    have hτ : τ ∈ Ggeo (p := p) Ω := fun y hy => σ.commutes ⟨y, Subfield.subset_closure (Or.inr hy)⟩
    exact hx τ hτ
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hbot
  exact y.2

theorem fixed_mem_closure : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ x : Ω, (∀ g ∈ Ggeo (p := p) Ω, g x = x) → ∃ S : Finset Ω, (∀ s ∈ S, IsAlgZp (p := p) s) ∧
      x ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)) := by
  intro p _ Ω _ _ h x hx
  obtain ⟨S, hS, hxS⟩ := exists_finset_of_mem_closure _ _ (mem_geoField_of_fixed h x hx)
  exact ⟨S, fun s hs => hS hs, hxS⟩

end GlobalTheory.K5.GeoFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenFormulaPeriodicRectangleUpperHalfPlane
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory

open scoped Interval

theorem green_periodic_rectangle : ∀ (G D : ℂ → ℂ) (T a b : ℝ), 0 < T → 0 < a → a ≤ b →
    (∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L s ∧ L Complex.I - Complex.I * L 1 = D s) →
    ContinuousOn D {s : ℂ | 0 < s.im} → (∀ s : ℂ, 0 < s.im → G (s + T) = G s) →
    (∫ x in (0 : ℝ)..T, G ((x : ℂ) + (b : ℂ) * Complex.I)) -
      (∫ x in (0 : ℝ)..T, G ((x : ℂ) + (a : ℂ) * Complex.I)) =
      ∫ y in a..b, ∫ x in (0 : ℝ)..T, D ((x : ℂ) + (y : ℂ) * Complex.I) := by
  intro G D T a b hT ha hab hG hD hper
  let φL : ℝ × ℝ →L[ℝ] ℂ := (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (1 : ℂ) +
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Complex.I
  have hφ : ∀ p : ℝ × ℝ, φL p = (p.2 : ℂ) + (p.1 : ℂ) * Complex.I := by
    intro p; simp [φL, Complex.real_smul]
  have him : ∀ p : ℝ × ℝ, (φL p).im = p.1 := by
    intro p; simp [hφ]
  have hder : ∀ s : ℂ, 0 < s.im → HasFDerivAt G (fderiv ℝ G s) s ∧
      fderiv ℝ G s Complex.I - Complex.I * fderiv ℝ G s 1 = D s := by
    intro s hs
    obtain ⟨L, hL, hLD⟩ := hG s hs
    rw [hL.fderiv]; exact ⟨hL, hLD⟩
  have hRpos : ∀ p ∈ [[a, b]] ×ˢ [[(0:ℝ), T]], 0 < (φL p).im := by
    intro p hp
    rw [him]
    have h1 := hp.1
    rw [Set.uIcc_of_le hab] at h1
    exact lt_of_lt_of_le ha h1.1
  have hGc : ContinuousOn G {s : ℂ | 0 < s.im} := fun s hs =>
    ((hder s hs).1.continuousAt).continuousWithinAt
  have hfc : ContinuousOn (fun p => G (φL p)) ([[a, b]] ×ˢ [[(0:ℝ), T]]) :=
    hGc.comp φL.continuous.continuousOn (fun p hp => hRpos p hp)
  have hsub : ∀ x ∈ Set.Ioo (min a b) (max a b) ×ˢ Set.Ioo (min (0:ℝ) T) (max 0 T),
      x ∈ [[a, b]] ×ˢ [[(0:ℝ), T]] := fun x hx =>
    ⟨Set.Ioo_subset_Icc_self hx.1, Set.Ioo_subset_Icc_self hx.2⟩
  have hdf : ∀ x ∈ Set.Ioo (min a b) (max a b) ×ˢ Set.Ioo (min (0:ℝ) T) (max 0 T),
      HasFDerivAt (fun p => G (φL p)) ((fderiv ℝ G (φL x)).comp φL) x := fun x hx =>
    (hder _ (hRpos x (hsub x hx))).1.comp x φL.hasFDerivAt
  have hpt : ∀ p : ℝ × ℝ, 0 < p.1 →
      (fderiv ℝ G (φL p)).comp φL (1, 0) + ((-Complex.I) • (fderiv ℝ G (φL p)).comp φL) (0, 1)
        = D (φL p) := by
    intro p hp
    have h := (hder (φL p) (by rw [him]; exact hp)).2
    rw [← h]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, hφ, smul_eq_mul]
    simp
    ring
  have hi : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (fderiv ℝ G (φL p)).comp φL (1, 0) +
        ((-Complex.I) • (fderiv ℝ G (φL p)).comp φL) (0, 1)) ([[a, b]] ×ˢ [[(0:ℝ), T]]) := by
    have hc : ContinuousOn (fun p => D (φL p)) ([[a, b]] ×ˢ [[(0:ℝ), T]]) :=
      hD.comp φL.continuous.continuousOn (fun p hp => hRpos p hp)
    refine (hc.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).congr_fun ?_
      (measurableSet_uIcc.prod measurableSet_uIcc)
    intro p hp
    have := hRpos p hp
    rw [him] at this
    exact (hpt p this).symm
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    (fun p => G (φL p)) (fun p => (-Complex.I) • G (φL p))
    (fun p => (fderiv ℝ G (φL p)).comp φL) (fun p => (-Complex.I) • (fderiv ℝ G (φL p)).comp φL)
    a 0 b T hfc (by exact hfc.const_smul (-Complex.I)) hdf (fun x hx => by exact (hdf x hx).const_smul (-Complex.I)) hi
  have hL : (∫ y in a..b, ∫ x in (0:ℝ)..T,
      (fderiv ℝ G (φL (y, x))).comp φL (1, 0) +
        ((-Complex.I) • (fderiv ℝ G (φL (y, x))).comp φL) (0, 1)) =
      ∫ y in a..b, ∫ x in (0 : ℝ)..T, D ((x : ℂ) + (y : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    have hy' : 0 < y := by
      rw [Set.uIcc_of_le hab] at hy; exact lt_of_lt_of_le ha hy.1
    try simp only
    rw [hpt (y, x) hy', hφ]
  have hg : (∫ y in a..b, (-Complex.I) • G (φL (y, T))) =
      ∫ y in a..b, (-Complex.I) • G (φL (y, 0)) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    have hy' : 0 < y := by
      rw [Set.uIcc_of_le hab] at hy; exact lt_of_lt_of_le ha hy.1
    try simp only
    have : φL (y, T) = φL (y, 0) + (T : ℂ) := by rw [hφ, hφ]; push_cast; ring
    rw [this, hper _ (by rw [him]; exact hy')]
  rw [hL, hg, sub_self, zero_add] at key
  rw [key]
  simp only [hφ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeVOperatorExplicit
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem vOp_hasSum (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) (hq : 0 < q)
    (hf : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) (τ : ℍ) :
    HasSum (fun m => (if q ∣ m then a (m / q) else 0) • Function.Periodic.qParam 1 τ ^ m)
      (GlobalTheory.Hk.vOp q f τ) := by
  have him : 0 < ((q : ℂ) * (τ : ℂ)).im := by
    have : ((q : ℂ) * (τ : ℂ)).im = (q : ℝ) * τ.im := by simp
    rw [this]; exact mul_pos (by exact_mod_cast hq) τ.im_pos
  set τ' : ℍ := ofComplex ((q : ℂ) * τ) with hτ'
  have hc : (τ' : ℂ) = (q : ℂ) * τ := by
    rw [hτ', ofComplex_apply_of_im_pos him]
  have hqp : Function.Periodic.qParam 1 (τ' : ℂ) = Function.Periodic.qParam 1 (τ : ℂ) ^ q := by
    simp only [Function.Periodic.qParam, hc, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have h1 := hf τ'
  unfold vOp
  rw [← hτ']
  refine (Function.Injective.hasSum_iff (g := fun m : ℕ => q * m)
    (fun x y h => Nat.eq_of_mul_eq_mul_left hq h) ?_).mp ?_
  · intro x hx
    have : ¬ q ∣ x := by
      rintro ⟨c, rfl⟩; exact hx ⟨c, rfl⟩
    simp [this]
  · convert h1 using 1
    funext m
    simp only [Function.comp, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hq, hqp, ← pow_mul]

end GlobalTheory.Hk
end

