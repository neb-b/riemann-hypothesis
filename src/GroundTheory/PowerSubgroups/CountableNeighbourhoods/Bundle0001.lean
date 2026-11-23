module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.DescentPowerSubgroups
section
namespace GroundTheory.Variant₂.N1

theorem exists_pow_apply_eq_self_of_aeval_eq_zero {K : Type*} [Field K] {Ω : Type*} [Field Ω]
    [Algebra K Ω] (σ : Gal(Ω/K)) {p : Polynomial K} (hp : p ≠ 0) {x : Ω}
    (hx : Polynomial.aeval x p = 0) : ∃ N : ℕ, 0 < N ∧ (σ ^ N) x = x := by
  have hmem : ∀ n : ℕ, (σ ^ n) x ∈ p.rootSet Ω := fun n => by
    rw [Polynomial.mem_rootSet_of_ne hp, Polynomial.aeval_algHom_apply, hx, map_zero]
  have : Finite (p.rootSet Ω) := (Polynomial.rootSet_finite p Ω).to_subtype
  let f : ℕ → p.rootSet Ω := fun n => ⟨(σ ^ n) x, hmem n⟩
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : (σ ^ i) x = (σ ^ j) x := congrArg Subtype.val hij
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨j - i, Nat.sub_pos_of_lt h, ?_⟩
    apply (σ ^ i).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le, key]
  · refine ⟨i - j, Nat.sub_pos_of_lt h, ?_⟩
    apply (σ ^ j).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' h.le, key]

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.ExistsMaxMinorNeZeroOfLinearIndependentAlt
section
namespace GroundTheory.Variant₂.N1

def KSubset (n k : ℕ) : Type := { s : Finset (Fin n) // s.card = k }

def KSubset.emb {n k : ℕ} (s : KSubset n k) : Fin k ↪o Fin n :=
  (s.1).orderEmbOfFin s.2

def maxMinor {R : Type*} [CommRing R] {n k : ℕ} (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset n k) : R :=
  (B.submatrix (⇑s.emb) id).det

theorem exists_maxMinor_ne_zero_of_linearIndependent_alt {R : Type*} [CommRing R] {n k : ℕ}
    [IsDomain R] (B : Matrix (Fin n) (Fin k) R) (hB : LinearIndependent R B.col) :
    ∃ s : KSubset n k, maxMinor B s ≠ 0 := by
  classical
  set K := FractionRing R
  set B' : Matrix (Fin n) (Fin k) K := B.map (algebraMap R K) with hB'
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have h1 : LinearIndependent R B'.col := by
    have hker : LinearMap.ker ((Algebra.linearMap R K).compLeft (Fin n)) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      funext i
      exact hinj (congr_fun hxy i)
    have := hB.map' ((Algebra.linearMap R K).compLeft (Fin n)) hker
    have heq : B'.col = ((Algebra.linearMap R K).compLeft (Fin n)) ∘ B.col := by
      funext j i
      rfl
    rw [heq]
    exact this
  have h2 : LinearIndependent K B'.col := (LinearIndependent.iff_fractionRing R K).mp h1
  have hrank : B'.rank = k := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card h2, Fintype.card_fin]
  rw [Matrix.rank_eq_finrank_span_row] at hrank
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K B'.row
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = k := by
    rw [← hrank, ← hspan, finrank_span_eq_card hli]
  let t : Finset (Fin n) := Finset.univ.map ⟨a, ha⟩
  have ht : t.card = k := by simp [t, hcard]
  let s : KSubset n k := ⟨t, ht⟩
  refine ⟨s, ?_⟩
  have hmem : ∀ i : Fin k, ∃ c : κ, a c = s.emb i := by
    intro i
    have h : s.emb i ∈ t := Finset.orderEmbOfFin_mem t ht i
    simp only [t, Finset.mem_map, Finset.mem_univ, true_and] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, hc⟩
  choose e he using hmem
  have he_inj : Function.Injective e := by
    intro i j hij
    apply s.emb.injective
    rw [← he i, ← he j, hij]
  have hrows : LinearIndependent K (B'.submatrix s.emb id).row := by
    have hfam : (B'.submatrix s.emb id).row = (B'.row ∘ a) ∘ e := by
      funext i j
      show B' (s.emb i) j = B' (a (e i)) j
      rw [he i]
    rw [hfam]
    exact hli.comp e he_inj
  have hdet : (B'.submatrix s.emb id).det ≠ 0 := by
    have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  intro h
  apply hdet
  have hmap : B'.submatrix s.emb id = (B.submatrix s.emb id).map (algebraMap R K) := rfl
  rw [hmap]
  show ((algebraMap R K).mapMatrix (B.submatrix s.emb id)).det = 0
  rw [← RingHom.map_det]
  unfold maxMinor at h
  rw [h, map_zero]

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.FontainePhiPowerSubgroups
section
namespace GroundTheory.Variant₂.N1

theorem mem_span_singleton_pow_smul_top_iff {A : Type*} [CommRing A] (a x : A) (n : ℕ) :
    x ∈ ((Ideal.span {a}) ^ n • ⊤ : Submodule A A) ↔ a ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem exists_limit_sum_pow_mul {A : Type*} [CommRing A] {a : A}
    [IsPrecomplete (Ideal.span {a}) A] (b : ℕ → A) :
    ∃ L : A, ∀ n : ℕ, a ^ n ∣ (∑ k ∈ Finset.range n, a ^ k * b k) - L := by
  obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete (Ideal.span {a}) A).prec'
    (fun n => ∑ k ∈ Finset.range n, a ^ k * b k) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff,
        ← Finset.sum_range_add_sum_Ico _ hmn, sub_add_cancel_left, dvd_neg]
      refine Finset.dvd_sum fun k hk => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow a (Finset.mem_Ico.1 hk).1) _)
  exact ⟨L, fun n => (mem_span_singleton_pow_smul_top_iff a _ n).1 ((SModEq.sub_mem).1 (hL n))⟩

theorem exists_eq_add_mul_of_forall' {A : Type*} {R : Type*} {ι : Type*} [CommRing A]
    [CommRing R] {a : A} {r : R} [IsAdicComplete (Ideal.span {a}) A]
    [IsAdicComplete (Ideal.span {r}) R] (f : A →+* R) :
    f a = r →
      ∀ (X : R) (ψ : ι → R),
        (∀ (y : ι), ∃ (b : A) (s : R) (y' : ι), ψ y = f b + X * s + r * ψ y') →
          ∀ (y : ι), ∃ (b : A) (s : R), ψ y = f b + X * s := by
  intro hfa X ψ h
  choose b s nx hstep using h
  intro y
  obtain ⟨B, hB⟩ := exists_limit_sum_pow_mul (a := a) (fun k => b (nx^[k] y))
  obtain ⟨S, hS⟩ := exists_limit_sum_pow_mul (a := r) (fun k => s (nx^[k] y))
  refine ⟨B, S, ?_⟩
  have key : ∀ n : ℕ, ψ y = f (∑ k ∈ Finset.range n, a ^ k * b (nx^[k] y)) +
      X * (∑ k ∈ Finset.range n, r ^ k * s (nx^[k] y)) + r ^ n * ψ (nx^[n] y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := hstep (nx^[n] y)
      rw [Function.iterate_succ_apply', Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [map_add (f := _), map_mul, map_pow, hfa] at ih ⊢
      linear_combination ih + r ^ n * h1
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {r}) _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, mem_span_singleton_pow_smul_top_iff]
  obtain ⟨c, hc⟩ := hB n
  obtain ⟨d, hd⟩ := hS n
  have hfB : f (∑ k ∈ Finset.range n, a ^ k * b (nx^[k] y)) = f B + r ^ n * f c := by
    rw [← hfa, ← map_pow, ← map_mul, ← map_add (f := _)]
    congr 1
    linear_combination hc
  exact ⟨f c + X * d + ψ (nx^[n] y), by linear_combination key n + hfB + X * hd⟩

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.NormZpow
section
namespace GroundTheory.Variant₂.N1

theorem eq_one_of_forall_norm_zpow_sub_one_lt {z : ℂ} (h : ∀ m : ℤ, ‖z ^ m - 1‖ < 1) :
    z = 1 := by
  have hpow : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 := fun n => by simpa using h n
  have hle : ‖z‖ ≤ 1 := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hlt
    have h1 := hpow n
    have h2 : ‖z ^ n‖ - ‖(1 : ℂ)‖ ≤ ‖z ^ n - 1‖ := norm_sub_norm_le _ _
    rw [norm_pow, norm_one] at h2
    linarith
  have hz0 : z ≠ 0 := by
    rintro rfl
    have := hpow 1
    simp at this
  have hge : 1 ≤ ‖z‖ := by
    by_contra hlt
    rw [not_le] at hlt
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have h1 : 1 < ‖z⁻¹‖ := by
      rw [norm_inv]
      exact (one_lt_inv₀ hpos).mpr hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) h1
    have h3 := h (-(n : ℤ))
    rw [zpow_neg, zpow_natCast, ← inv_pow] at h3
    have h2 : ‖z⁻¹ ^ n‖ - ‖(1 : ℂ)‖ ≤ ‖z⁻¹ ^ n - 1‖ := norm_sub_norm_le _ _
    rw [norm_pow, norm_one] at h2
    linarith
  have hn1 : ‖z‖ = 1 := le_antisymm hle hge
  have key : ∀ w : ℂ, ‖w‖ = 1 → ‖w - 1‖ < 1 → 3 * ‖w - 1‖ ^ 2 ≤ ‖w ^ 2 - 1‖ ^ 2 := by
    intro w hw hw1
    have e : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
    rw [e, norm_mul, mul_pow]
    have hw' : w.re ^ 2 + w.im ^ 2 = 1 := by
      have := Complex.sq_norm w
      rw [hw, Complex.normSq_apply] at this
      nlinarith
    have a1 : ‖w - 1‖ ^ 2 = (w.re - 1) ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have a2 : ‖w + 1‖ ^ 2 = (w.re + 1) ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    have a3 : 3 ≤ ‖w + 1‖ ^ 2 := by
      have : ‖w - 1‖ ^ 2 < 1 := by nlinarith [norm_nonneg (w - 1)]
      nlinarith
    nlinarith [sq_nonneg ‖w - 1‖]
  have hk : ∀ k : ℕ, 3 ^ k * ‖z - 1‖ ^ 2 ≤ ‖z ^ (2 ^ k) - 1‖ ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h4 := key (z ^ (2 ^ k)) (by rw [norm_pow, hn1, one_pow]) (hpow _)
      rw [pow_succ 2 k, pow_mul]
      calc (3 : ℝ) ^ (k + 1) * ‖z - 1‖ ^ 2 = 3 * (3 ^ k * ‖z - 1‖ ^ 2) := by ring
        _ ≤ 3 * ‖z ^ (2 ^ k) - 1‖ ^ 2 := by gcongr
        _ ≤ _ := h4
  by_contra hne
  have hd : 0 < ‖z - 1‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) 2
  obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt (1 / ‖z - 1‖ ^ 2) (by norm_num : (1 : ℝ) < 3)
  have h5 := hk k
  have h6 := hpow (2 ^ k)
  have h7 : ‖z ^ (2 ^ k) - 1‖ ^ 2 < 1 := by nlinarith [norm_nonneg (z ^ (2 ^ k) - 1)]
  have h8 : 1 < 3 ^ k * ‖z - 1‖ ^ 2 := by rwa [div_lt_iff₀ hd] at hk'
  linarith

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.PowInvariant
section
namespace GroundTheory.Variant₂.N1

def mulZPowers (U : Subgroup Gal(AlgebraicClosure ℚ/ℚ)) (s : Gal(AlgebraicClosure ℚ/ℚ))
    (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) :
    Subgroup Gal(AlgebraicClosure ℚ/ℚ) where
  carrier := {x | ∃ k : ℤ, ∃ u ∈ U, x = s ^ k * u}
  one_mem' := ⟨0, 1, U.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, u, hu, rfl⟩ ⟨b, v, hv, rfl⟩
    refine ⟨a + b, s ^ (-b) * u * (s ^ (-b))⁻¹ * v, U.mul_mem (hU (-b) u hu) hv, ?_⟩
    rw [zpow_add, zpow_neg, inv_inv]
    group
  inv_mem' := by
    rintro _ ⟨k, u, hu, rfl⟩
    refine ⟨-k, s ^ k * u⁻¹ * (s ^ k)⁻¹, hU k _ (U.inv_mem hu), ?_⟩
    rw [zpow_neg]
    group

theorem le_powerSubgroup₂ (U : Subgroup Gal(AlgebraicClosure ℚ/ℚ))
    (s : Gal(AlgebraicClosure ℚ/ℚ)) (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) :
    U ≤ mulZPowers U s hU := fun u hu => ⟨0, u, hu, by simp⟩

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.PrecompleteOfSurjective
section
namespace GroundTheory.Variant₂.N1

theorem smodEq_span_singleton_pow_iff {R : Type*} [CommRing R] (a : R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • (⊤ : Submodule R R))] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem isPrecomplete_of_surjective {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (a : A) [IsPrecomplete (Ideal.span {a}) A] :
    IsPrecomplete (Ideal.span {f a}) B := by
  refine ⟨fun b hb => ?_⟩
  have hb' : ∀ {m n : ℕ}, m ≤ n → f a ^ m ∣ b m - b n := fun hmn =>
    (smodEq_span_singleton_pow_iff (f a) _ _ _).1 (hb hmn)
  have hstep : ∀ n : ℕ, ∃ x : A, b (n + 1) = b n + f (a ^ n * x) := by
    intro n
    obtain ⟨c, hc⟩ := hb' (Nat.le_add_right n 1)
    obtain ⟨x, rfl⟩ := hf c
    refine ⟨-x, ?_⟩
    rw [map_mul, map_pow, map_neg]
    linear_combination -hc
  choose x hx using hstep
  obtain ⟨y₀, hy₀⟩ := hf (b 0)
  let y : ℕ → A := fun n => y₀ + ∑ k ∈ Finset.range n, a ^ k * x k
  have hy_succ : ∀ n, y (n + 1) = y n + a ^ n * x n := by
    intro n
    simp only [y, Finset.sum_range_succ, add_assoc]
  have hy : ∀ n, f (y n) = b n := by
    intro n
    induction n with
    | zero => simp [y, hy₀]
    | succ n ih => rw [hy_succ, map_add (f := _), ih, hx]
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → a ^ m ∣ y m - y n := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hy_succ, sub_add_eq_sub_sub]
      exact dvd_sub ih (Dvd.dvd.mul_right (pow_dvd_pow a hmn) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {a}) inferInstance (f := y)
    (fun {m n} hmn => (smodEq_span_singleton_pow_iff a m _ _).2 (hcauchy hmn))
  refine ⟨f L, fun n => (smodEq_span_singleton_pow_iff (f a) n _ _).2 ?_⟩
  have h := map_dvd f ((smodEq_span_singleton_pow_iff a n _ _).1 (hL n))
  rwa [map_pow, map_sub, hy] at h

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.RelIndexSup
section
namespace GroundTheory.Variant₂.N1

open Subgroup

theorem relIndex_sup_of_le_normalizer {G : Type*} [Group G] {H N : Subgroup G}
    (hLE : H ≤ Subgroup.normalizer (N : Set G)) : H.relIndex (H ⊔ N) = H.relIndex N := by
  symm
  let f : N →* (H ⊔ N : Subgroup G) := Subgroup.inclusion le_sup_right
  let g : N ⧸ H.subgroupOf N → (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N) :=
    fun q => Quotient.liftOn' q (fun n => ((f n : (H ⊔ N : Subgroup G)) :
        (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N))) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at hab
      rw [QuotientGroup.eq, mem_subgroupOf]
      simpa [f] using hab)
  have hinj : Function.Injective g := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    have h1 : ((f a : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) =
        ((f b : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) := hxy
    rw [QuotientGroup.eq, mem_subgroupOf] at h1
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa [f] using h1
  have hsurj : Function.Surjective g := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H k =>
    obtain ⟨y, hy⟩ := k
    have hy' : y ∈ ((N ⊔ H : Subgroup G) : Set G) := by
      rw [sup_comm]; exact hy
    rw [coe_mul_of_right_le_normalizer_left N H hLE] at hy'
    obtain ⟨n, hn, h, hh, rfl⟩ := hy'
    refine ⟨((⟨n, hn⟩ : N) : N ⧸ H.subgroupOf N), ?_⟩
    change ((f ⟨n, hn⟩ : (H ⊔ N : Subgroup G)) :
        (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) = _
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa [f] using hh
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index]
  exact Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.SingleMemInitialCoordSubspace
section
namespace GroundTheory.Variant₂.N1

def initialCoordSubspace {K : Type*} [Field K] {n : ℕ} (k : ℕ) : Submodule K (Fin n → K) where
  carrier := {v | ∀ i : Fin n, k ≤ (i : ℕ) → v i = 0}
  add_mem' := by
    intro a b ha hb i hi
    simp [ha i hi, hb i hi]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c a ha i hi
    simp [ha i hi]

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.SlopeVcCountableNeighbourhoods
section
namespace GroundTheory.Variant₂.N1

open WeierstrassCurve

def vcX {R : Type*} [CommRing R] (C : WeierstrassCurve.VariableChange R) (x : R) : R :=
  ↑C.u⁻¹ ^ 2 * (x - C.r)

def vcY {R : Type*} [CommRing R] (C : WeierstrassCurve.VariableChange R) (x y : R) : R :=
  ↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)

theorem slope_variableChange {F : Type*} [Field F] (C : WeierstrassCurve.VariableChange F)
    (W : WeierstrassCurve F) [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) (vcY C x₂ y₂) =
      ↑C.u⁻¹ * (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s) := by
  have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ W.toAffine.negY x₁ y₂ := fun h => hxy ⟨rfl, h⟩
    have hyy : y₁ = y₂ := Affine.Y_eq_of_Y_ne h₁ h₂ rfl hy
    subst hyy
    have key : vcY C x₁ y₁ - (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁) =
        (↑C.u⁻¹ : F) ^ 3 * (y₁ - W.toAffine.negY x₁ y₁) := by
      simp only [vcX, vcY, Affine.negY, variableChange_a₁, variableChange_a₃]
      ring
    have hd : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    have hd' : vcY C x₁ y₁ - (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁) ≠ 0 := by
      rw [key]; exact mul_ne_zero (pow_ne_zero _ hv) hd
    have hy' : vcY C x₁ y₁ ≠ (C • W).toAffine.negY (vcX C x₁) (vcY C x₁ y₁) :=
      sub_ne_zero.mp hd'
    rw [Affine.slope_of_Y_ne rfl hy, Affine.slope_of_Y_ne rfl hy', key]
    have num : 3 * vcX C x₁ ^ 2 + 2 * (C • W).toAffine.a₂ * vcX C x₁ + (C • W).toAffine.a₄ -
        (C • W).toAffine.a₁ * vcY C x₁ y₁ =
        (↑C.u⁻¹ : F) ^ 4 * ((3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ -
          W.toAffine.a₁ * y₁) - C.s * (y₁ - W.toAffine.negY x₁ y₁)) := by
      simp only [vcX, vcY, Affine.negY, variableChange_a₁, variableChange_a₂, variableChange_a₄]
      ring
    rw [num]
    set D := y₁ - W.toAffine.negY x₁ y₁
    set N := 3 * x₁ ^ 2 + 2 * W.toAffine.a₂ * x₁ + W.toAffine.a₄ - W.toAffine.a₁ * y₁
    field_simp
  · have hX : vcX C x₁ ≠ vcX C x₂ := by
      intro h
      apply hx
      simp only [vcX] at h
      have := mul_left_cancel₀ (pow_ne_zero 2 hv) h
      exact sub_left_injective this
    rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hX]
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hXd : vcX C x₁ - vcX C x₂ = (↑C.u⁻¹ : F) ^ 2 * (x₁ - x₂) := by
      simp only [vcX]; ring
    have hYd : vcY C x₁ y₁ - vcY C x₂ y₂ =
        (↑C.u⁻¹ : F) ^ 3 * ((y₁ - y₂) - C.s * (x₁ - x₂)) := by
      simp only [vcY]; ring
    rw [hXd, hYd]
    field_simp

end GroundTheory.Variant₂.N1
end

