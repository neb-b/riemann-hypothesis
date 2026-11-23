module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SemilinearLatticeMem
section
theorem UpperTheory.semilinear_lattice_mem :
    ∀ (R K C V W : Type) [CommRing R] [Field K] [Field C] [Algebra R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] [AddCommGroup W] [Module C W] (e : K →+* C) (U : Submodule K V) (Φ : U →ₛₗ[e] W) (A : Set C) (L : AddSubgroup W) (G : Set V), (∀ a ∈ A, ∀ y ∈ L, a • y ∈ L) → (∀ r : R, e (algebraMap R K r) ∈ A) → (∀ g ∈ G, ∃ h : g ∈ U, Φ ⟨g, h⟩ ∈ L) → ∀ (s : R), algebraMap R K s ≠ 0 → e (algebraMap R K s)⁻¹ ∈ A → ∀ v : U, s • (v : V) ∈ Submodule.span R G → Φ v ∈ L := by
  intro R K C V W _ _ _ _ _ _ _ _ _ _ e U Φ A L G hA hR hG s hs hsA v hv
  have key : ∀ x ∈ Submodule.span R G, ∃ h : x ∈ U, Φ ⟨x, h⟩ ∈ L := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hG x hx
    | zero =>
      refine ⟨U.zero_mem, ?_⟩
      have h0 : (⟨0, U.zero_mem⟩ : U) = 0 := rfl
      rw [h0, map_zero]
      exact L.zero_mem
    | add x y _ _ hx hy =>
      obtain ⟨hxU, hx⟩ := hx
      obtain ⟨hyU, hy⟩ := hy
      refine ⟨U.add_mem hxU hyU, ?_⟩
      have h0 : (⟨x + y, U.add_mem hxU hyU⟩ : U) = ⟨x, hxU⟩ + ⟨y, hyU⟩ := rfl
      rw [h0, map_add (f := _)]
      exact L.add_mem hx hy
    | smul r x _ hx =>
      obtain ⟨hxU, hx⟩ := hx
      have hm : r • x ∈ U := by
        rw [← algebraMap_smul K r x]
        exact U.smul_mem _ hxU
      refine ⟨hm, ?_⟩
      have h0 : (⟨r • x, hm⟩ : U) = algebraMap R K r • (⟨x, hxU⟩ : U) :=
        Subtype.ext (algebraMap_smul K r x).symm
      rw [h0, LinearMap.map_smulₛₗ]
      exact hA _ (hR r) _ hx
  obtain ⟨hU, hL⟩ := key _ hv
  have h1 : v = (algebraMap R K s)⁻¹ • (⟨s • (v : V), hU⟩ : U) := by
    apply Subtype.ext
    change (v : V) = (algebraMap R K s)⁻¹ • (s • (v : V))
    rw [← algebraMap_smul K s (v : V), inv_smul_smul₀ hs]
  rw [h1, LinearMap.map_smulₛₗ]
  exact hA _ hsA _ hL
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SeparableOfNewtonPolygon
section
private lemma val_nat_le_one {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (m : ℕ) : w (m : L) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ]
    exact w.map_add_le ih (by simp)

private lemma exists_peak {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (n : ℕ) (t : ℕ → Γ)
    (h0 : ∀ k ≤ n, 0 < t k) (hc : ∀ k, k + 2 ≤ n → t k * t (k + 2) < t (k + 1) * t (k + 1)) :
    ∃ j ≤ n, ∀ k ≤ n, k ≠ j → k + 1 ≠ j → t k < t j := by
  classical
  have hex : ∃ j, n ≤ j ∨ t (j + 1) < t j := ⟨n, Or.inl le_rfl⟩
  set j := Nat.find hex with hj
  have hjn : j ≤ n := Nat.find_min' hex (Or.inl le_rfl)
  have hlo : ∀ k < j, t k ≤ t (k + 1) := fun k hk =>
    not_lt.1 fun h => Nat.find_min hex hk (Or.inr h)
  have hlo' : ∀ k, k + 1 < j → t k < t (k + 1) := by
    intro k hk
    have h1 := hc k (by omega)
    have h2 : t (k + 1) * t (k + 1) ≤ t (k + 1) * t (k + 2) :=
      mul_le_mul_of_nonneg_left (hlo (k + 1) hk) zero_le
    exact lt_of_mul_lt_mul_right (h1.trans_le h2) zero_le
  have hhi : ∀ k, j ≤ k → k < n → t (k + 1) < t k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro h
      rcases Nat.find_spec hex with h' | h'
      · omega
      · exact h'
    | succ k hk ih =>
      intro h
      have h1 := hc k (by omega)
      have h2 : t (k + 1) * t (k + 1) ≤ t k * t (k + 1) :=
        mul_le_mul_of_nonneg_right (ih (by omega)).le zero_le
      exact lt_of_mul_lt_mul_left (h1.trans_le h2) zero_le
  have hle : ∀ k ≤ j, t k ≤ t j := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self => exact le_rfl
    | of_succ k hk ih => exact (hlo k hk).trans ih
  have hgt : ∀ k, j + 1 ≤ k → k ≤ n → t k < t j := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro h; exact hhi j le_rfl (by omega)
    | succ k hk ih => intro h; exact (hhi k (by omega) (by omega)).trans (ih (by omega))
  refine ⟨j, hjn, fun k hk h1 h2 => ?_⟩
  rcases lt_or_gt_of_ne h1 with h | h
  · exact (hlo' k (by omega)).trans_le (hle _ (by omega))
  · exact hgt k h hk

private lemma no_double_zero {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation L Γ) (n : ℕ) (b : ℕ → L) (h0 : ∀ k ≤ n, b k ≠ 0)
    (hc : ∀ k, k + 2 ≤ n → w (b k * b (k + 2)) < w (b (k + 1) * b (k + 1)))
    (h1 : ∑ k ∈ Finset.range (n + 1), b k = 0)
    (h2 : ∑ k ∈ Finset.range (n + 1), (k : L) * b k = 0) : False := by
  have hpos : ∀ k ≤ n, 0 < w (b k) := fun k hk => zero_lt_iff.2 ((map_ne_zero w).2 (h0 k hk))
  obtain ⟨j, hjn, hj⟩ := exists_peak n (fun k => w (b k)) hpos
    (fun k hk => by simpa only [map_mul] using hc k hk)
  have hs : ∑ k ∈ Finset.range (n + 1), (((k + 1 : ℕ) : L) - (j : L)) * b k = 0 := by
    have : ∀ k : ℕ, (((k + 1 : ℕ) : L) - (j : L)) * b k = (k : L) * b k + (1 - (j : L)) * b k := by
      intro k; push_cast; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, mul_zero, add_zero]
  have hjj : (((j + 1 : ℕ) : L) - (j : L)) * b j = b j := by push_cast; ring
  have key := w.map_sum_eq_of_lt (s := Finset.range (n + 1))
    (f := fun k => (((k + 1 : ℕ) : L) - (j : L)) * b k) (j := j)
    (Finset.mem_range.2 (by omega)) (by
      intro k hk
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hk
      rw [hjj]
      by_cases hkj : k + 1 = j
      · rw [hkj, sub_self, zero_mul, map_zero]
        exact hpos j hjn
      · rw [map_mul]
        refine lt_of_le_of_lt ?_ (hj k (by omega) hk.2 hkj)
        exact mul_le_of_le_one_left zero_le
          (w.map_sub_le (val_nat_le_one w _) (val_nat_le_one w _)))
  rw [hs, hjj, map_zero] at key
  exact (hpos j hjn).ne key

private lemma exists_extension {K L Γ : Type} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (f : K →+* L) :
    ∃ A : ValuationSubring L, ∀ x y : K, v x < v y → A.valuation (f x) < A.valuation (f y) := by
  obtain ⟨A, h, hA⟩ := IsLocalRing.exists_factor_valuationRing
    (f.comp v.valuationSubring.subtype)
  refine ⟨A, fun x y hxy => ?_⟩
  have hy : 0 < v y := lt_of_le_of_lt zero_le hxy
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  have hlt : v (x / y) < 1 := by
    rw [map_div₀]
    exact (div_lt_one₀ hy).2 hxy
  let z : v.valuationSubring := ⟨x / y, hlt.le⟩
  have hz : z ∈ IsLocalRing.maximalIdeal v.valuationSubring :=
    (Valuation.mem_maximalIdeal_iff _ _).2 hlt
  haveI : IsLocalRing A.toSubring := inferInstanceAs (IsLocalRing A)
  have hz' := (A.valuation_lt_one_iff _).1 (map_nonunit
    ((f.comp v.valuationSubring.subtype).codRestrict A.toSubring h) z hz)
  have hz'' : A.valuation (f (x / y)) < 1 := hz'
  rw [map_div₀, map_div₀] at hz''
  exact (div_lt_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 ((map_ne_zero f).2 hy0)))).1 hz''

private lemma tail_succ {Γ : Type} [CommMonoid Γ] {n : ℕ} (γ : Fin n → Γ) (k : ℕ) (hk : k < n) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), γ i =
      γ ⟨k, hk⟩ * ∏ i ∈ Finset.univ.filter (fun i : Fin n => k + 1 ≤ i.val), γ i := by
  rw [← Finset.prod_insert (by simp)]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

theorem UpperTheory.separable_of_newton_polygon :
    ∀ {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (n : ℕ) (γ : Fin n → Γ),
        StrictMono γ → (∀ i, γ i ≠ 0) → ∀ p : Polynomial K, p.Monic → p.natDegree = n →
        (∀ k ≤ n, v (p.coeff k) = ∏ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), γ i) → p.Separable := by
  intro K Γ _ _ v n γ hγ hγ0 p _ hn hv
  have hv0 : ∀ k ≤ n, v (p.coeff k) ≠ 0 := fun k hk => by
    rw [hv k hk]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hγ0 i
  have ha0 : ∀ k ≤ n, p.coeff k ≠ 0 := fun k hk => (map_ne_zero v).1 (hv0 k hk)
  have hstep : ∀ k (hk : k < n), v (p.coeff k) = γ ⟨k, hk⟩ * v (p.coeff (k + 1)) := fun k hk => by
    rw [hv k hk.le, hv (k + 1) hk, tail_succ γ k hk]
  have hconc : ∀ k, k + 2 ≤ n →
      v (p.coeff k * p.coeff (k + 2)) < v (p.coeff (k + 1) * p.coeff (k + 1)) := by
    intro k hk
    have e1 := hstep k (by omega)
    have e2 := hstep (k + 1) (by omega)
    have hlt : γ ⟨k, by omega⟩ < γ ⟨k + 1, by omega⟩ := hγ (by simp [Fin.lt_def])
    have hp : 0 < v (p.coeff (k + 1)) * v (p.coeff (k + 2)) :=
      mul_pos (zero_lt_iff.2 (hv0 _ (by omega))) (zero_lt_iff.2 (hv0 _ hk))
    calc v (p.coeff k * p.coeff (k + 2))
        = γ ⟨k, by omega⟩ * (v (p.coeff (k + 1)) * v (p.coeff (k + 2))) := by
          rw [map_mul, e1, mul_assoc]
      _ < γ ⟨k + 1, by omega⟩ * (v (p.coeff (k + 1)) * v (p.coeff (k + 2))) :=
          mul_lt_mul_of_pos_right hlt hp
      _ = v (p.coeff (k + 1) * p.coeff (k + 1)) := by
          rw [map_mul, mul_left_comm, ← e2]
  rw [Polynomial.separable_def,
    Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K)]
  intro r
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨hp, hd⟩ := hcon
  set f := algebraMap K (AlgebraicClosure K) with hf
  obtain ⟨A, hA⟩ := exists_extension v f
  have hr : r ≠ 0 := by
    rintro rfl
    rw [← Polynomial.coeff_zero_eq_aeval_zero'] at hp
    exact ha0 0 (Nat.zero_le _) ((map_eq_zero _).1 hp)
  refine no_double_zero A.valuation n (fun k => f (p.coeff k) * r ^ k)
    (fun k hk => mul_ne_zero ((map_ne_zero f).2 (ha0 k hk)) (pow_ne_zero _ hr)) ?_ ?_ ?_
  · intro k hk
    have e1 : f (p.coeff k) * r ^ k * (f (p.coeff (k + 2)) * r ^ (k + 2)) =
        f (p.coeff k * p.coeff (k + 2)) * r ^ (2 * k + 2) := by rw [map_mul]; ring
    have e2 : f (p.coeff (k + 1)) * r ^ (k + 1) * (f (p.coeff (k + 1)) * r ^ (k + 1)) =
        f (p.coeff (k + 1) * p.coeff (k + 1)) * r ^ (2 * k + 2) := by rw [map_mul]; ring
    rw [e1, e2, map_mul A.valuation, map_mul A.valuation]
    exact mul_lt_mul_of_pos_right (hA _ _ (hconc k hk))
      (zero_lt_iff.2 ((map_ne_zero _).2 (pow_ne_zero _ hr)))
  · rw [Polynomial.aeval_eq_sum_range, hn] at hp
    simpa only [Algebra.smul_def] using hp
  · have hX : Polynomial.aeval r (Polynomial.derivative p * Polynomial.X) = 0 := by rw [map_mul, hd, zero_mul]
    have hcoeff : ∀ k : ℕ, (Polynomial.derivative p * Polynomial.X).coeff k = (k : K) * p.coeff k := by
      intro k
      cases k with
      | zero => simp
      | succ k => rw [Polynomial.coeff_mul_X, Polynomial.coeff_derivative]; push_cast; ring
    have hdeg : (Polynomial.derivative p * Polynomial.X).natDegree < n + 1 := by
      rw [Nat.lt_succ_iff, Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [hcoeff, Polynomial.coeff_eq_zero_of_natDegree_lt (hn ▸ hk), mul_zero]
    rw [Polynomial.aeval_eq_sum_range' hdeg] at hX
    simpa only [hcoeff, Algebra.smul_def, map_mul, map_natCast, mul_assoc] using hX
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SeqEx
section
theorem UpperTheory.Reformulated.B.Qj7.seq_ex :
    ∀ (S : ℕ → Type),
    (∀ (n : ℕ), Finite (S n)) →
      (∀ (n : ℕ), Nonempty (S n)) →
        ∀ (t : (n : ℕ) → S (n + (1 : ℕ)) → S n), ∃ (u : (n : ℕ) → S n), ∀ (n : ℕ), t n (u (n + (1 : ℕ))) = u n := by
  intro S hfin hne t
  classical
  letI : ∀ n, TopologicalSpace (S n) := fun _ => ⊥
  haveI : ∀ n, DiscreteTopology (S n) := fun _ => ⟨rfl⟩
  let C : ℕ → Set ((n : ℕ) → S n) := fun k => {u | ∀ n < k, t n (u (n + 1)) = u n}
  have hclosed : ∀ k, IsClosed (C k) := by
    intro k
    have hC : C k = ⋂ n, ⋂ (_ : n < k), {u : (n : ℕ) → S n | t n (u (n + 1)) = u n} := by
      ext u
      simp [C]
    rw [hC]
    refine isClosed_iInter fun n => isClosed_iInter fun _ => ?_
    exact isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply (n + 1)))
      (continuous_apply n)
  have hstep : ∀ (k : ℕ) (x : S k), ∃ u ∈ C k, u k = x := by
    intro k
    induction k with
    | zero =>
      intro x
      refine ⟨Function.update (fun n => Classical.choice (hne n)) 0 x, ?_, by simp⟩
      intro n hn
      exact absurd hn (Nat.not_lt_zero n)
    | succ k ih =>
      intro x
      obtain ⟨u, hu, hk⟩ := ih (t k x)
      refine ⟨Function.update u (k + 1) x, ?_, by simp⟩
      intro n hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | h
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hu n h
      · subst h
        rw [Function.update_self, Function.update_of_ne (by omega), hk]
  have hnon : ∀ k, (C k).Nonempty := by
    intro k
    obtain ⟨u, hu, _⟩ := hstep k (Classical.choice (hne k))
    exact ⟨u, hu⟩
  have hmono : ∀ k, C (k + 1) ⊆ C k := fun k u hu n hn => hu n (Nat.lt_succ_of_lt hn)
  obtain ⟨u, hu⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hmono hnon
    (hclosed 0).isCompact hclosed
  exact ⟨u, fun n => Set.mem_iInter.mp hu (n + 1) n (Nat.lt_succ_self n)⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SesquilinearFlipConj
section
noncomputable def UpperTheory.Reformulated.B.SesquilinearFlipConj.HasSesq :
    {G V : Type} → [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → Prop :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (π : Representation ℂ G V) ↦
      ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
        B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
          ∀ (g : G) (v w : V),
            ((B : V → V →ₗ⋆[ℂ] ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) w) =
              ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w

namespace UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers

private noncomputable def flipConj {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => starRingEnd ℂ (B w v))
    (by intro v₁ v₂ w; simp [map_add (f := _)])
    (by intro c v w; simp [map_smulₛₗ, smul_eq_mul])
    (by intro v w₁ w₂; simp [map_add (f := _)])
    (by intro c v w; simp [map_smulₛₗ, smul_eq_mul])

private theorem flipConj_apply {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (v w : V) :
    flipConj B v w = starRingEnd ℂ (B w v) := rfl

end UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers

open UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers in
theorem UpperTheory.Reformulated.B.SesquilinearFlipConj.main :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] {ρ : Representation ℂ G V},
      UpperTheory.Reformulated.B.SesquilinearFlipConj.HasSesq ρ →
        ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
          B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
            (∀ (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) w : V → ℂ) v = (starRingEnd ℂ : ℂ → ℂ) (((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w)) ∧
              ∀ (g : G) (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) w) =
                  ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w := by
  intro G V _ _ _ ρ hS
  obtain ⟨B, hB0, hBinv⟩ := hS
  classical
  by_cases hH : B + flipConj B = 0
  · have hrel : ∀ v w, B v w + starRingEnd ℂ (B w v) = 0 := by
      intro v w
      have := congrArg (fun F : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ => F v w) hH
      simpa [flipConj_apply] using this
    refine ⟨Complex.I • B, ?_, ?_, ?_⟩
    · intro h
      apply hB0
      have : (-Complex.I) • (Complex.I • B) = B := by
        rw [smul_smul]; simp
      rw [← this, h, smul_zero]
    · intro v w
      have h1 := hrel v w
      have h2 : starRingEnd ℂ (B v w) = - B w v := by
        have := congrArg (starRingEnd ℂ) h1
        simp at this
        linear_combination this
      simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, h2]
      ring
    · intro g v w
      simp only [LinearMap.smul_apply, smul_eq_mul, hBinv]
  · refine ⟨B + flipConj B, hH, ?_, ?_⟩
    · intro v w
      simp only [LinearMap.add_apply, flipConj_apply, map_add (f := _), Complex.conj_conj]
      ring
    · intro g v w
      simp only [LinearMap.add_apply, flipConj_apply, hBinv]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SetIntegralDifferentiability
section
open MeasureTheory

private theorem UpperTheory.Reformulated.B.SetIntegralDifferentiability.hasFDerivAt_setIntegral
    {X P E F : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K) {a : X → E} (ha : Continuous a)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Ψ : P × E → F)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (p₀ : P) :
    HasFDerivAt (fun p : P ↦ ∫ x in K, Ψ (p, a x) ∂μ)
      (∫ x in K, (fderiv ℝ Ψ (p₀, a x)).comp (ContinuousLinearMap.inl ℝ P E) ∂μ) p₀ := by
  haveI : ProperSpace P := FiniteDimensional.proper_real P
  have hc : Continuous Ψ := hΨ.continuous
  have hd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have hD : Continuous fun z : P × E ↦
      (fderiv ℝ Ψ z).comp (ContinuousLinearMap.inl ℝ P E) :=
    (hΨ.continuous_fderiv (by simp)).clm_comp continuous_const
  have hcomp : IsCompact (Metric.closedBall p₀ 1 ×ˢ (a '' K)) :=
    (isCompact_closedBall p₀ 1).prod (hK.image ha)
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hD.continuousOn
  have hsec : ∀ p : P, Continuous fun x : X ↦ (p, a x) := fun p ↦ continuous_const.prodMk ha
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun p x ↦ Ψ (p, a x))
    (F' := fun p x ↦ (fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E))
    (bound := fun _ ↦ C) (s := Metric.closedBall p₀ 1)
    (Metric.closedBall_mem_nhds p₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun p ↦
      ((hc.comp (hsec p)).continuousOn.integrableOn_compact hK).aestronglyMeasurable
  · exact (hc.comp (hsec p₀)).continuousOn.integrableOn_compact hK
  · exact ((hD.comp (hsec p₀)).continuousOn.integrableOn_compact hK).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx p hp
    exact hC (p, a x) ⟨hp, Set.mem_image_of_mem a hx⟩
  · exact (continuous_const (y := C)).continuousOn.integrableOn_compact hK
  · refine Filter.Eventually.of_forall fun x p _ ↦ ?_
    exact (hd (p, a x)).hasFDerivAt.comp p (hasFDerivAt_prodMk_left p (a x))

theorem UpperTheory.Reformulated.B.SetIntegralDifferentiability.contDiff_setIntegral_nat :
    ∀ {X P E : Type} [inst : TopologicalSpace X] [T2Space X]
    [inst_2 : MeasurableSpace X] [BorelSpace X] [inst_4 : NormedAddCommGroup P] [inst_5 : NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [inst_7 : NormedAddCommGroup E] [inst_8 : NormedSpace ℝ E] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasureOnCompacts μ] {K : Set X},
    IsCompact K →
      ∀ {a : X → E},
        Continuous a →
          ∀ (m : ℕ) {F : Type} [inst : NormedAddCommGroup F] [inst_10 : NormedSpace ℝ F] [CompleteSpace F]
            (Ψ : P × E → F),
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ →
              ContDiff ℝ (↑m : WithTop ℕ∞) fun (p : P) ↦ ∫ (x : X) in K, Ψ (p, a x) ∂μ := by
  intro X P E _ _ _ _ _ _ _ _ _ μ _ K hK a ha m
  induction m with
  | zero =>
    intro F _ _ _ Ψ hΨ
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun p ↦
      (UpperTheory.Reformulated.B.SetIntegralDifferentiability.hasFDerivAt_setIntegral μ hK ha Ψ hΨ p).continuousAt
  | succ n ih =>
    intro F _ _ _ Ψ hΨ
    have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z : P × E ↦
        (fderiv ℝ Ψ z).comp (ContinuousLinearMap.inl ℝ P E) :=
      (contDiff_infty_iff_fderiv.1 hΨ).2.clm_comp contDiff_const
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    exact ⟨_, ih _ hD, fun p ↦ UpperTheory.Reformulated.B.SetIntegralDifferentiability.hasFDerivAt_setIntegral μ hK ha Ψ hΨ p⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SignatureBlockDiagonal
section
open Matrix

open scoped MatrixOrder ComplexOrder in
private theorem UpperTheory.frame_pos {N j : ℕ} (S : Matrix (Fin N) (Fin N) ℂ)
    (K : Submodule ℂ (Fin N → ℂ)) (hS : S.IsHermitian) (hj : j ≤ Module.finrank ℂ K)
    (hK : ∀ y ∈ K, y ≠ 0 → 0 < (dotProduct (star y) (S.mulVec y)).re) :
    ∃ B : Matrix (Fin N) (Fin j) ℂ, Bᴴ * S * B = 1 ∧ ∀ v, B.mulVec v ∈ K := by
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank hj
  have hb' : LinearIndependent ℂ (fun i => (b i : Fin N → ℂ)) :=
    hb.map' K.subtype (Submodule.ker_subtype K)
  let C : Matrix (Fin N) (Fin j) ℂ := Matrix.of fun r i => (b i : Fin N → ℂ) r
  have hC : ∀ v, C.mulVec v = ∑ i, v i • (b i : Fin N → ℂ) := by
    intro v
    ext r
    simp [C, Matrix.mulVec, dotProduct, mul_comm]
  have hmem : ∀ v, C.mulVec v ∈ K := fun v => by
    rw [hC]
    exact K.sum_mem fun i _ => K.smul_mem _ (b i).2
  have hne : ∀ v, v ≠ 0 → C.mulVec v ≠ 0 := fun v hv h => by
    rw [hC] at h
    exact hv (funext (Fintype.linearIndependent_iff.mp hb' v h))
  have hH : (Cᴴ * S * C).IsHermitian := isHermitian_conjTranspose_mul_mul C hS
  have hG : (Cᴴ * S * C).PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
    have h1 := hK _ (hmem x) (hne x hx)
    have h2 := hH.im_star_dotProduct_mulVec_self x
    have h3 : star x ⬝ᵥ (Cᴴ * S * C) *ᵥ x = star (C *ᵥ x) ⬝ᵥ S *ᵥ C *ᵥ x := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
    rw [← h3] at h1
    exact Complex.pos_iff.mpr ⟨h1, Eq.symm h2⟩
  obtain ⟨D, hD, hGD⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hG.isStrictlyPositive
  obtain ⟨E, hE⟩ := hD.exists_right_inv
  refine ⟨C * E, ?_, fun v => ?_⟩
  · calc (C * E)ᴴ * S * (C * E) = Eᴴ * (Cᴴ * S * C) * E := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (D * E)ᴴ * (D * E) := by
          rw [hGD, star_eq_conjTranspose]
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hE]; simp
  · rw [← mulVec_mulVec]
    exact hmem _

theorem UpperTheory.signature_block_diagonal :
    ∀ {N j j' : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (K K' : Submodule ℂ (Fin N → ℂ)),
        S.IsHermitian → j ≤ Module.finrank ℂ K → j' ≤ Module.finrank ℂ K' →
        (∀ y ∈ K, y ≠ 0 → 0 < (dotProduct (star y) (S.mulVec y)).re) →
        (∀ y ∈ K', y ≠ 0 → (dotProduct (star y) (S.mulVec y)).re < 0) →
        (∀ y ∈ K, ∀ y' ∈ K', dotProduct (star y') (S.mulVec y) = 0) →
        ∃ A : Matrix (Fin N) (Fin j ⊕ Fin j') ℂ,
          A.conjTranspose * S * A = Matrix.fromBlocks 1 0 0 (-1) ∧
          (∀ v : Fin j → ℂ, A.mulVec (Sum.elim v (0 : Fin j' → ℂ)) ∈ K) ∧
          ∀ v : Fin j' → ℂ, A.mulVec (Sum.elim (0 : Fin j → ℂ) v) ∈ K' := by
  intro N j j' S K K' hS hj hj' hK hK' hO
  obtain ⟨B, hB, hBK⟩ := UpperTheory.frame_pos S K hS hj hK
  obtain ⟨B', hB', hBK'⟩ := UpperTheory.frame_pos (-S) K' hS.neg hj' (fun y hy h0 => by
    have := hK' y hy h0
    simpa [neg_mulVec] using this)
  have h22 : B'ᴴ * S * B' = -1 := by
    rw [← hB']
    simp
  have h21 : B'ᴴ * S * B = 0 := by
    ext a c
    have h := hO _ (hBK (Pi.single c 1)) _ (hBK' (Pi.single a 1))
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec] at h
    simpa [← Pi.single_star] using h
  have h12 : Bᴴ * S * B' = 0 := by
    have h := congrArg conjTranspose h21
    simpa [conjTranspose_mul, hS.eq, Matrix.mul_assoc] using h
  refine ⟨fromCols B B', ?_, fun v => ?_, fun v => ?_⟩
  · rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols,
      hB, h12, h21, h22]
  · simpa using hBK v
  · simpa using hBK' v
end

