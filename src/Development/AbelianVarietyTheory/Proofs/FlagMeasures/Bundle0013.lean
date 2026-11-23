module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
section
namespace GlobalTheory.GramCount

variable {A : Type} [CommRing A]

def ip (c : A →+* A) {n : ℕ} (x y : Fin n → A) : A := ∑ i, x i * c (y i)

def Prim (c : A →+* A) {m n : ℕ} (x : Fin m → Fin n → A) : Prop :=
  ∃ y : Fin m → Fin n → A, ∀ a b, ip c (x a) (y b) = if a = b then 1 else 0

def sols (c : A →+* A) {m : ℕ} (n : ℕ) (G : Matrix (Fin m) (Fin m) A) :
    Set (Fin m → Fin n → A) :=
  {x | Prim c x ∧ ∀ a b, ip c (x b) (x a) = G a b}

variable (c : A →+* A) {n : ℕ}

theorem ip_add_left (x x' y : Fin n → A) : ip c (x + x') y = ip c x y + ip c x' y := by
  simp only [ip, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem ip_add_right (x y y' : Fin n → A) : ip c x (y + y') = ip c x y + ip c x y' := by
  simp only [ip, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem ip_sub_left (x x' y : Fin n → A) : ip c (x - x') y = ip c x y - ip c x' y := by
  simp only [ip, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem ip_zero_left (y : Fin n → A) : ip c 0 y = 0 := by
  simp [ip]

theorem ip_zero_right (x : Fin n → A) : ip c x 0 = 0 := by
  simp [ip]

theorem ip_smul_left (a : A) (x y : Fin n → A) : ip c (a • x) y = a * ip c x y := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem ip_smul_right (a : A) (x y : Fin n → A) : ip c x (a • y) = c a * ip c x y := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem ip_sum_left {ι : Type} (s : Finset ι) (x : ι → Fin n → A) (y : Fin n → A) :
    ip c (∑ a ∈ s, x a) y = ∑ a ∈ s, ip c (x a) y := by
  unfold ip
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem ip_sum_right {ι : Type} (s : Finset ι) (x : Fin n → A) (y : ι → Fin n → A) :
    ip c x (∑ a ∈ s, y a) = ∑ a ∈ s, ip c x (y a) := by
  unfold ip
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem cj_ip (hc : ∀ u, c (c u) = u) (x y : Fin n → A) : c (ip c x y) = ip c y x := by
  unfold ip
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hc, mul_comm]

theorem map_ip {B : Type} [CommRing B] (c' : B →+* B) (φ : A →+* B)
    (hφ : ∀ u, φ (c u) = c' (φ u)) (x y : Fin n → A) :
    φ (ip c x y) = ip c' (fun i => φ (x i)) (fun i => φ (y i)) := by
  unfold ip
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hφ]

theorem prim_of_isUnit_det (hc : ∀ u, c (c u) = u) {m : ℕ} (x y : Fin m → Fin n → A)
    (h : IsUnit (Matrix.of fun a b => ip c (x a) (y b)).det) : Prim c x := by

  unfold Prim
  refine ⟨fun b => ∑ k, c ((Matrix.of fun a b => ip c (x a) (y b))⁻¹ k b) • y k,
    fun a b => ?_⟩
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv _ h) a) b
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  simp only [Matrix.of_apply] at h1
  rw [ip_sum_right]
  simp only [ip_smul_right, hc]
  rw [← h1]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem prim_of_sub_mem (hc : ∀ u, c (c u) = u) (I : Ideal A) (hI : ∀ u ∈ I, IsUnit (1 + u))
    {m : ℕ} (x y : Fin m → Fin n → A)
    (h : ∀ a b, ip c (x a) (y b) - (if a = b then 1 else 0) ∈ I) : Prim c x := by

  apply prim_of_isUnit_det c hc x y
  have hone : (Ideal.Quotient.mk I).mapMatrix (Matrix.of fun a b => ip c (x a) (y b)) = 1 := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply]
    have hab := h a b
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at hab
    rw [hab]
    split_ifs <;> simp
  have key : (Matrix.of fun a b => ip c (x a) (y b)).det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det, hone,
      Matrix.det_one, sub_self]
  simpa using hI _ key

theorem Prim.map {B : Type} [CommRing B] (c' : B →+* B) (φ : A →+* B)
    (hφ : ∀ u, φ (c u) = c' (φ u)) {m : ℕ} {x : Fin m → Fin n → A} (h : Prim c x) :
    Prim c' (fun a i => φ (x a i)) := by
  unfold Prim at h ⊢
  obtain ⟨y, hy⟩ := h
  refine ⟨fun b i => φ (y b i), fun a b => ?_⟩
  show ip c' (fun i => φ (x a i)) (fun i => φ (y b i)) = _
  rw [← map_ip c c' φ hφ (x a) (y b), hy a b]
  split_ifs <;> simp

theorem prim_of_map (hc : ∀ u, c (c u) = u) {B : Type} [CommRing B] (c' : B →+* B) (φ : A →+* B)
    (hφ : ∀ u, φ (c u) = c' (φ u)) (hs : Function.Surjective φ)
    (hk : ∀ u, φ u = 0 → IsUnit (1 + u)) {m : ℕ} {x : Fin m → Fin n → A}
    (h : Prim c' (fun a i => φ (x a i))) : Prim c x := by

  unfold Prim at h
  obtain ⟨y', hy'⟩ := h
  choose y hy using fun b i => hs (y' b i)
  apply prim_of_sub_mem c hc (RingHom.ker φ) (fun u hu => hk u (RingHom.mem_ker.mp hu)) x y
  intro a b
  have h2 : ip c' (fun i => φ (x a i)) (y' b) = if a = b then 1 else 0 := hy' a b
  have e : (fun i => φ (y b i)) = y' b := funext (hy b)
  rw [RingHom.mem_ker, map_sub, map_ip c c' φ hφ, e, h2]
  split_ifs <;> simp

theorem Prim.eq_zero {m : ℕ} {x : Fin m → Fin n → A} (h : Prim c x) (s : Fin m → A)
    (hs : ∑ a, s a • x a = 0) : s = 0 := by

  unfold Prim at h
  obtain ⟨y, hy⟩ := h
  funext b
  have hb := congrArg (fun z => ip c z (y b)) hs
  simp only [ip_sum_left, ip_smul_left, hy, ip_zero_left] at hb
  simpa using hb

theorem exists_trace_one (hc : ∀ u, c (c u) = u) {ω : A} (hω : IsUnit (ω - c ω)) :
    ∃ θ e : A, θ + c θ = 1 ∧ IsUnit e ∧ c e = -e := by
  obtain ⟨U, hU⟩ := hω
  have h1 : (ω - c ω) * ↑U⁻¹ = 1 := by rw [← hU]; exact U.mul_inv
  have h2 : (c ω - ω) * c ↑U⁻¹ = 1 := by
    have h3 := congrArg c h1
    rwa [map_mul, map_sub, hc, map_one] at h3
  have hv : c ↑U⁻¹ = -(↑U⁻¹ : A) := by
    linear_combination (-(c ↑U⁻¹)) * h1 + (-(↑U⁻¹ : A)) * h2
  refine ⟨ω * ↑U⁻¹, ω - c ω, ?_, ⟨U, hU⟩, ?_⟩
  · rw [map_mul, hv]
    linear_combination h1
  · rw [map_sub, hc]
    ring

theorem card_fixed_sq (hc : ∀ u, c (c u) = u) {ω : A} (hω : IsUnit (ω - c ω))
    {M : Type} [AddCommGroup M] [Module A M] (σ : M →+ M) (hσ : ∀ x, σ (σ x) = x)
    (hs : ∀ (a : A) x, σ (a • x) = c a • σ x) :
    Nat.card {x : M // σ x = x} ^ 2 = Nat.card M ∧
      Nat.card {x : M // σ x = -x} ^ 2 = Nat.card M := by

  obtain ⟨U, hU⟩ := hω
  have h1 : (ω - c ω) * ↑U⁻¹ = 1 := by rw [← hU]; exact U.mul_inv
  have h2 : (c ω - ω) * c ↑U⁻¹ = 1 := by
    have h3 := congrArg c h1
    rwa [map_mul, map_sub, hc, map_one] at h3
  have hvn : c ↑U⁻¹ = -(↑U⁻¹ : A) := by
    linear_combination (-(c ↑U⁻¹)) * h1 + (-(↑U⁻¹ : A)) * h2
  obtain ⟨v, hv1, hv2⟩ : ∃ v : A, (ω - c ω) * v = 1 ∧ c v = -v := ⟨_, h1, hvn⟩
  have hu : c (ω - c ω) = -(ω - c ω) := by
    rw [map_sub, hc]
    ring
  have hg : ∀ x, σ (v • (x - σ x)) = v • (x - σ x) := by
    intro x
    rw [hs, map_sub, hσ, hv2, neg_smul, ← smul_neg, neg_sub]
  have hab : ω * v = c ω * v + 1 := by linear_combination hv1
  have hf : ∀ x, σ (x - ω • v • (x - σ x)) = x - ω • v • (x - σ x) := by
    intro x
    rw [map_sub, hs, hg, smul_smul, smul_smul, hab, add_smul, one_smul]
    abel
  have e : M ≃ {x : M // σ x = x} × {x : M // σ x = x} :=
    { toFun := fun x => (⟨x - ω • v • (x - σ x), hf x⟩, ⟨v • (x - σ x), hg x⟩)
      invFun := fun p => p.1.1 + ω • p.2.1
      left_inv := fun x => sub_add_cancel _ _
      right_inv := fun p => by
        obtain ⟨⟨f, hf0⟩, ⟨g, hg0⟩⟩ := p
        have key : v • (f + ω • g - σ (f + ω • g)) = g := by
          rw [map_add (f := _), hs, hf0, hg0, add_sub_add_left_eq_sub, ← sub_smul, smul_smul, mul_comm,
            hv1, one_smul]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show f + ω • g - ω • v • (f + ω • g - σ (f + ω • g)) = f
          rw [key, add_sub_cancel_right]
        · exact key }
  have e2 : {x : M // σ x = -x} ≃ {x : M // σ x = x} :=
    { toFun := fun x => ⟨v • x.1, by rw [hs, x.2, hv2, smul_neg, neg_smul, neg_neg]⟩
      invFun := fun y => ⟨(ω - c ω) • y.1, by rw [hs, y.2, hu, neg_smul]⟩
      left_inv := fun x => Subtype.ext (by
        show (ω - c ω) • v • x.1 = x.1
        rw [smul_smul, hv1, one_smul])
      right_inv := fun y => Subtype.ext (by
        show v • (ω - c ω) • y.1 = y.1
        rw [smul_smul, mul_comm, hv1, one_smul]) }
  have hM : Nat.card M = Nat.card {x : M // σ x = x} ^ 2 := by
    rw [Nat.card_congr e, Nat.card_prod, sq]
  exact ⟨hM.symm, by rw [Nat.card_congr e2, hM]⟩

end GlobalTheory.GramCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdFirstBlocksByLayers
section
open Finset

namespace GlobalTheory

theorem prod_interval_mirror_split (a i : ℕ) (hi : i < a) (f : ℕ → ℝ) :
    ∏ p ∈ (Finset.range (2 * a + 1)).filter (fun p => i < p ∧ i + p ≤ 2 * a), f p
      = (∏ k ∈ Finset.Ioo i a, f k * f (2 * a - k)) * (f a * f (2 * a - i)) := by
  have hS : (Finset.range (2 * a + 1)).filter (fun p => i < p ∧ i + p ≤ 2 * a)
      = Finset.Ioo i a ∪ insert a (Finset.Ioo a (2 * a - i) ∪ {2 * a - i}) := by
    ext p
    simp only [mem_filter, mem_range, mem_union, mem_insert, mem_Ioo, mem_singleton]
    omega
  rw [hS, prod_union, prod_insert, prod_union, prod_singleton]
  · have hm : ∏ p ∈ Finset.Ioo a (2 * a - i), f p = ∏ k ∈ Finset.Ioo i a, f (2 * a - k) := by
      refine Finset.prod_nbij' (fun p => 2 * a - p) (fun k => 2 * a - k) ?_ ?_ ?_ ?_ ?_
      · intro x hx
        simp only [mem_Ioo] at hx ⊢
        omega
      · intro x hx
        simp only [mem_Ioo] at hx ⊢
        omega
      · intro x hx
        simp only [mem_Ioo] at hx
        omega
      · intro x hx
        simp only [mem_Ioo] at hx
        omega
      · intro x hx
        simp only [mem_Ioo] at hx
        congr 1
        omega
    rw [hm, prod_mul_distrib]
    ring
  all_goals first
    | (rw [Finset.disjoint_left]
       intro x hx hx'
       simp only [mem_union, mem_insert, mem_Ioo, mem_singleton] at hx hx'
       omega)
    | (simp only [mem_union, mem_Ioo, mem_singleton]
       omega)

private theorem prod_filter_gt_eq_prod_Ioo (a : ℕ) (i : Fin a) (h : ℕ → ℝ) :
    ∏ k ∈ Finset.univ.filter (fun k : Fin a => i < k), h k = ∏ k ∈ Finset.Ioo (i : ℕ) a, h k := by
  refine Finset.prod_nbij (fun k => (k : ℕ)) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk
    simp only [mem_Ioo]
    exact ⟨hk, k.isLt⟩
  · intro x _ y _ hxy
    exact Fin.ext hxy
  · intro k hk
    simp only [Finset.mem_coe, mem_Ioo] at hk
    exact ⟨⟨k, hk.2⟩, Finset.mem_coe.2 (mem_filter.2 ⟨mem_univ _, Fin.lt_def.2 hk.1⟩), rfl⟩
  · intro k _
    rfl

theorem prod_first_blocks_by_layers (a : ℕ) (g : ℕ → ℕ → ℝ) :
    ∏ b ∈ ((Finset.range a) ×ˢ (Finset.range (2 * a + 1))).filter
        (fun b : ℕ × ℕ => b.1 < b.2 ∧ b.1 + b.2 ≤ 2 * a), g b.1 b.2
      = (∏ i : Fin a, ∏ k ∈ Finset.univ.filter (fun k : Fin a => i < k),
          g i k * g i (2 * a - k)) * ∏ i : Fin a, g i a * g i (2 * a - i) := by
  rw [Finset.prod_filter, Finset.prod_product]
  have step : ∀ i ∈ Finset.range a,
      (∏ p ∈ Finset.range (2 * a + 1), if i < p ∧ i + p ≤ 2 * a then g i p else 1)
        = (∏ k ∈ Finset.Ioo i a, g i k * g i (2 * a - k)) * (g i a * g i (2 * a - i)) := by
    intro i hi
    rw [← Finset.prod_filter]
    exact prod_interval_mirror_split a i (mem_range.1 hi) (g i)
  refine (Finset.prod_congr rfl step).trans ?_
  rw [prod_mul_distrib]
  congr 1
  · rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ k ∈ Finset.Ioo i a, g i k * g i (2 * a - k)) a]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    exact (prod_filter_gt_eq_prod_Ioo a i (fun k => g i k * g i (2 * a - k))).symm
  · exact (Fin.prod_univ_eq_prod_range (fun i => g i a * g i (2 * a - i)) a).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RingOfIntegersEqZeroOfNatCastDvdOfNormEmbeddingL
section
open NumberField

namespace GlobalTheory

theorem ringOfIntegers_eq_zero_of_natCast_dvd_of_norm_embedding_le
    (E : Type) [Field E] [NumberField E] (g₀ : ℕ) (B : ℝ) (t : 𝓞 E)
    (hd : (g₀ : 𝓞 E) ∣ t) (hB : ∀ ι : E →+* ℂ, ‖ι (t : E)‖ ≤ B) (hlt : B < g₀) : t = 0 := by
  by_contra ht
  obtain ⟨s, rfl⟩ := hd
  have hs : s ≠ 0 := by
    rintro rfl
    exact ht (mul_zero _)
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hs
  have h1 := hB σ
  have hcast : (((g₀ : 𝓞 E) * s : 𝓞 E) : E) = (g₀ : E) * (s : E) := by
    push_cast
    rfl
  rw [hcast, map_mul, map_natCast, norm_mul, Complex.norm_natCast] at h1
  have h2 : (g₀ : ℝ) ≤ g₀ * ‖σ (s : E)‖ := le_mul_of_one_le_right (Nat.cast_nonneg _) hσ
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SaturatedHasComplement
section
namespace GlobalTheory.SaturatedSublatticeComplement

universe u_1 u_2

open Module

theorem saturated_has_complement {R : Type u_1} {V : Type u_2} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup V] [Module R V] (N M : Submodule R V) (hNM : N ≤ M) (hM : M.FG)
    (hsat : ∀ (r : R) (y : V), r ≠ 0 → y ∈ M → r • y ∈ N → y ∈ N) :
    ∃ A : Submodule R V, A ⊓ N = ⊥ ∧ A ⊔ N = M := by
  classical
  let N' : Submodule R M := N.comap M.subtype
  haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hM
  haveI : IsTorsionFree R (M ⧸ N') := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r q hq
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    obtain ⟨m, rfl⟩ := N'.mkQ_surjective q
    have h1 : r • m ∈ N' := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa using hq
    have h2 : (m : V) ∈ N := hsat r m hr m.2 (by simpa [N'] using h1)
    exact (Submodule.Quotient.mk_eq_zero N').mpr (by simpa [N'] using h2)
  haveI : Module.FinitePresentation R (M ⧸ N') := Module.finitePresentation_of_finite R _
  haveI : Module.Projective R (M ⧸ N') := Module.Flat.projective_of_finitePresentation
  obtain ⟨g, hg⟩ := Module.projective_lifting_property N'.mkQ LinearMap.id N'.mkQ_surjective
  have hg' : ∀ q, N'.mkQ (g q) = q := fun q => LinearMap.congr_fun hg q
  refine ⟨(LinearMap.range g).map M.subtype, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxA, hxN⟩
    obtain ⟨_, ⟨q, rfl⟩, rfl⟩ := hxA
    have hmem : g q ∈ N' := by simpa [N'] using hxN
    have hq0 : q = 0 := by
      rw [← hg' q]
      exact (Submodule.Quotient.mk_eq_zero N').mpr hmem
    simp [hq0]
  · apply le_antisymm
    · exact sup_le (by
        rintro x ⟨y, -, rfl⟩
        exact y.2) hNM
    · intro x hx
      let m : M := ⟨x, hx⟩
      have hd : m - g (N'.mkQ m) ∈ N' := by
        rw [← Submodule.Quotient.mk_eq_zero]
        have := hg' (N'.mkQ m)
        simp only [Submodule.mkQ_apply] at this ⊢
        rw [Submodule.Quotient.mk_sub, this, sub_self]
      have hx' : x = (g (N'.mkQ m) : V) + ((m - g (N'.mkQ m) : M) : V) := by simp [m]
      rw [hx']
      exact Submodule.add_mem_sup ⟨g (N'.mkQ m), ⟨_, rfl⟩, rfl⟩ (by simpa [N'] using hd)

theorem main : ∀ {R : Type u_1} {V : Type u_2} [inst : CommRing R] [IsDedekindDomain R]
    [inst_2 : AddCommGroup V] [inst_3 : Module R V] (N M : Submodule R V), N ≤ M →
    Submodule.FG M → (∀ (r : R) (y : V), r ≠ (0 : R) → y ∈ M → r • y ∈ N → y ∈ N) →
    ∃ (A : Submodule R V), A ⊓ N = ⊥ ∧ A ⊔ N = M :=
  fun N M h1 h2 h3 => saturated_has_complement N M h1 h2 h3

end GlobalTheory.SaturatedSublatticeComplement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SetLIntegralLeMulOfEncardLe
section
open MeasureTheory

namespace GlobalTheory.IndicatorSumEncard

theorem tsum_indicator_one_eq_encard {ι : Type} (A : Set ι) :
    ∑' i : ι, A.indicator (fun _ => (1 : ENNReal)) i = (A.encard : ENNReal) := by
  rw [← tsum_subtype A (fun _ => (1 : ENNReal))]
  exact ENNReal.tsum_set_one A

theorem setLIntegral_le_mul_of_encard_le {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
    [Measure.IsMulLeftInvariant μ] {Γ : Subgroup G} [Countable ↥Γ] {D : Set G}
    (hD : IsFundamentalDomain (↥Γ) D μ) {f : G → ENNReal} (hf : AEMeasurable f μ)
    (hinv : ∀ᵐ (y : G) ∂μ, ∀ (γ : ↥Γ), f ((↑γ : G) * y) = f y) {S : Set G}
    (hS : MeasurableSet S) (N : ENNReal) (hN : N ≠ ⊤)
    (hcount : ∀ (z : G), (↑(Set.encard {γ : ↥Γ | (↑γ : G) * z ∈ S}) : ENNReal) ≤ N) :
    ∫⁻ (y : G) in S, f y ∂μ ≤ N * ∫⁻ (y : G) in D, f y ∂μ := by

  have key : ∀ x : G, ∑' γ : ↥Γ, S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x) ≤ N := by
    intro x
    rw [← (Equiv.inv ↥Γ).tsum_eq (fun γ => S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x))]
    simp only [Equiv.inv_apply, inv_inv]
    calc ∑' γ : ↥Γ, S.indicator (fun _ => (1 : ENNReal)) (γ • x)
        = ∑' γ : ↥Γ, {γ : ↥Γ | (↑γ : G) * x ∈ S}.indicator (fun _ => (1 : ENNReal)) γ := by
          congr 1
      _ = _ := tsum_indicator_one_eq_encard _
      _ ≤ N := hcount x

  calc ∫⁻ y in S, f y ∂μ = ∑' γ : ↥Γ, ∫⁻ x in D, S.indicator f (γ⁻¹ • x) ∂μ := by
        rw [← lintegral_indicator hS]
        exact hD.lintegral_eq_tsum' _
    _ = ∑' γ : ↥Γ, ∫⁻ x in D, S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x) * f x ∂μ := by
        congr 1
        ext γ
        refine lintegral_congr_ae ((ae_restrict_of_ae hinv).mono fun x hx => ?_)
        have h1 : f (γ⁻¹ • x) = f x := hx γ⁻¹
        dsimp only
        by_cases hm : γ⁻¹ • x ∈ S
        · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, one_mul, h1]
        · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, zero_mul]
    _ = ∫⁻ x in D, (∑' γ : ↥Γ, S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x)) * f x ∂μ := by
        rw [← lintegral_tsum]
        · congr 1
          ext x
          rw [ENNReal.tsum_mul_right]
        · intro γ
          exact (((measurable_const.indicator hS).comp (measurable_const_smul γ⁻¹)).aemeasurable).mul
            hf.restrict
    _ ≤ ∫⁻ x in D, N * f x ∂μ := lintegral_mono fun x => by gcongr; exact key x
    _ = N * ∫⁻ x in D, f x ∂μ := lintegral_const_mul' N _ hN

end GlobalTheory.IndicatorSumEncard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanDecay
section
namespace GlobalTheory.SpanDecay

theorem span_decay : (let d1 : {G H : Type} → [inst : NormedAddCommGroup H] → [inst_1 : InnerProductSpace ℂ H] → (G → H →L[ℂ] H) → (G → ℝ) → ℝ → H → H → Prop := @(fun {G H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : G → H →L[ℂ] H) (D : G → ℝ) (c : ℝ) (v u : H) ↦ ∃ (C : ℝ), ∀ (g : G), ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g))); ∀ {G H : Type} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] {ρ : G → H →L[ℂ] H} {D : G → ℝ} {c : ℝ} {S : Set H} {v : H}, (∀ u ∈ S, d1 ρ D c v u) → ∀ u ∈ Submodule.span ℂ S, d1 ρ D c v u) := by
  dsimp only
  intro G H _ _ ρ D c S v hS u hu
  induction hu using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨0, fun g => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C1, h1⟩ := hx
    obtain ⟨C2, h2⟩ := hy
    refine ⟨C1 + C2, fun g => ?_⟩
    rw [map_add (f := _), inner_add_right, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h1 g) (h2 g))
  | smul a x _ hx =>
    obtain ⟨C, h⟩ := hx
    refine ⟨‖a‖ * C, fun g => ?_⟩
    rw [map_smul, inner_smul_right, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h g) (norm_nonneg _)

end GlobalTheory.SpanDecay
end

