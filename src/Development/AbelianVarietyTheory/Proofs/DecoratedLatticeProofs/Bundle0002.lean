module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqEvalOfDirDerivVanish
section
open scoped ContDiff

namespace GlobalTheory.PolyOfDeriv

theorem taylor_of_chain (N : ℕ) : ∀ (G : ℕ → ℝ → ℂ) (_ : ∀ k t, HasDerivAt (G k) (G (k+1) t) t)
    (_ : G N = 0) (t : ℝ),
    G 0 t = ∑ k ∈ Finset.range N, G k 0 * ((t ^ k / k.factorial : ℝ) : ℂ) := by
  induction N with
  | zero => intro G _ hN t; simp [hN]
  | succ N ih =>
    intro G hG hN t
    have h1 : ∀ s, G 1 s = ∑ k ∈ Finset.range N, G (k+1) 0 * ((s ^ k / k.factorial : ℝ) : ℂ) :=
      fun s => ih (fun k => G (k+1)) (fun k t => hG (k+1) t) hN s
    have hm : ∀ (k : ℕ) (s : ℝ), HasDerivAt
        (fun s : ℝ => ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ))
        ((s ^ k / k.factorial : ℝ) : ℂ) s := by
      intro k s
      have h := (hasDerivAt_pow (k+1) s).div_const ((k+1).factorial : ℝ)
      have e : ((k+1 : ℕ) : ℝ) * s ^ (k + 1 - 1) / ((k+1).factorial : ℝ) = s ^ k / k.factorial := by
        rw [Nat.factorial_succ, Nat.add_sub_cancel, Nat.cast_mul]
        have : ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
        have : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
      rw [e] at h
      exact h.ofReal_comp
    have hH : ∀ s, HasDerivAt (fun s => G 0 s - ∑ k ∈ Finset.range N,
        G (k+1) 0 * ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ)) 0 s := by
      intro s
      have h2 : HasDerivAt (fun s : ℝ => ∑ k ∈ Finset.range N,
          G (k+1) 0 * ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ)) (G 1 s) s := by
        rw [h1 s]
        exact HasDerivAt.fun_sum fun k _ => (hm k s).const_mul _
      have h3 := (hG 0 s).fun_sub h2
      rwa [zero_add, sub_self] at h3
    have hc := is_const_of_deriv_eq_zero (fun s => (hH s).differentiableAt)
      (fun s => (hH s).deriv) t 0
    rw [Finset.sum_range_succ']
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
      zero_div, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero, sub_zero] at hc
    rw [← hc]
    simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_iter {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (k : ℕ) (y x : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ k u (y + t • x) (fun _ => x))
      (iteratedFDeriv ℝ (k+1) u (y + t • x) (fun _ => x)) t := by
  have hk : (k : WithTop ℕ∞) < ∞ := by exact_mod_cast ENat.coe_lt_top k
  have hd := ((hu.differentiable_iteratedFDeriv hk) (y + t • x)).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => y + t • x) x t := by
    simpa using ((hasDerivAt_id t).smul_const x).const_add y
  have h1 := hd.comp_hasDerivAt t hl
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℂ
    (fun _ => x)).hasFDerivAt.comp_hasDerivAt t h1
  rw [iteratedFDeriv_succ_apply_left]
  exact h2

theorem foldr_replicate {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (x : E) (k : ℕ) :
    (List.replicate k x).foldr
      (fun y g => fun z => deriv (fun t : ℝ => g (z + t • y)) 0) u
      = fun y => iteratedFDeriv ℝ k u y (fun _ => x) := by
  induction k with
  | zero => funext y; simp
  | succ k ih =>
    rw [List.replicate_succ, List.foldr_cons, ih]
    funext y
    have := (hasDerivAt_iter hu k y x 0).deriv
    simpa using this

theorem multilinear_diag_poly {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => ι → ℝ) ℂ) :
    ∃ q : MvPolynomial ι ℂ, ∀ x : ι → ℝ,
      M (fun _ => x) = MvPolynomial.eval (fun i => (x i : ℂ)) q := by
  refine ⟨∑ r : Fin k → ι, MvPolynomial.C (M (fun j => Pi.single (r j) (1:ℝ))) *
    ∏ j, MvPolynomial.X (r j), ?_⟩
  intro x
  have hx : (fun _ : Fin k => x) = fun _ => ∑ i, x i • (Pi.single i (1:ℝ) : ι → ℝ) := by
    funext _; ext l; simp [Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, M.map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [M.map_smul_univ (fun j => x (r j)) (fun j => Pi.single (r j) 1)]
  rw [Complex.real_smul, Complex.ofReal_prod, mul_comm]

theorem eq_eval_of_dirDeriv_vanish : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ)
    (u : (ι → ℝ) → ℂ), ContDiff ℝ ∞ u →
    (∀ L : List (ι → ℝ), L.length = N →
      L.foldr (fun y g => fun x => deriv (fun t : ℝ => g (x + t • y)) 0) u = 0) →
    ∃ p : MvPolynomial ι ℂ, ∀ x, u x = MvPolynomial.eval (fun i => (x i : ℂ)) p := by
  intro ι _ _ N u hu hL
  choose q hq using fun k => multilinear_diag_poly (iteratedFDeriv ℝ k u 0)
  refine ⟨∑ k ∈ Finset.range N, MvPolynomial.C ((k.factorial : ℂ)⁻¹) * q k, ?_⟩
  intro x
  have hrep := hL (List.replicate N x) List.length_replicate
  rw [foldr_replicate hu] at hrep
  have key := taylor_of_chain N (fun k t => iteratedFDeriv ℝ k u (0 + t • x) (fun _ => x))
    (fun k t => hasDerivAt_iter hu k 0 x t) (by funext t; exact congrFun hrep _) 1
  simp only [zero_add, one_smul, zero_smul, iteratedFDeriv_zero_apply, hq] at key
  rw [key]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, MvPolynomial.eval_C]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]; simp

end GlobalTheory.PolyOfDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsEqSumIndicator
section
namespace GlobalTheory.DoubleCosetIndicator

def dc {G : Type} [Group G] (R K : Subgroup G) (t : G) : Set G :=
  {x : G | ∃ r ∈ R, ∃ κ ∈ K, x = r * t * κ}

theorem dc_subset {G : Type} [Group G] (R K : Subgroup G) {s t x : G}
    (hs : x ∈ dc R K s) (ht : x ∈ dc R K t) : dc R K s ⊆ dc R K t := by
  rintro y ⟨a, ha, b, hb, rfl⟩
  obtain ⟨r, hr, κ, hκ, hx⟩ := hs
  obtain ⟨r', hr', κ', hκ', hx'⟩ := ht
  have hrs : r * s * κ = r' * t * κ' := hx.symm.trans hx'
  have hs' : s = r⁻¹ * r' * t * κ' * κ⁻¹ := by
    calc s = r⁻¹ * (r * s * κ) * κ⁻¹ := by group
      _ = r⁻¹ * (r' * t * κ') * κ⁻¹ := by rw [hrs]
      _ = r⁻¹ * r' * t * κ' * κ⁻¹ := by group
  refine ⟨a * r⁻¹ * r', R.mul_mem (R.mul_mem ha (R.inv_mem hr)) hr', κ' * κ⁻¹ * b,
    K.mul_mem (K.mul_mem hκ' (K.inv_mem hκ)) hb, ?_⟩
  rw [hs']
  group

theorem exists_eq_sum_indicator {G : Type} [Group G] {M : Type} [AddCommMonoid M]
    (R K : Subgroup G) (T : Finset G) (φ : G → M)
    (hR : ∀ r ∈ R, ∀ x : G, φ (r * x) = φ x) (hK : ∀ κ ∈ K, ∀ x : G, φ (x * κ) = φ x)
    (hT : ∀ x : G, φ x ≠ 0 → ∃ t ∈ T, x ∈ dc R K t) :
    ∃ c : G → M, (∀ t : G, c t = 0 ∨ c t = φ t) ∧
      ∀ x : G, φ x = ∑ t ∈ T, Set.indicator (dc R K t) (fun _ => c t) x := by
  classical

  let S : G → Finset G := fun t => T.filter (fun t' => dc R K t' = dc R K t)
  let rep : G → G := fun t => if h : (S t).Nonempty then h.choose else t
  let c : G → M := fun t => if t ∈ T ∧ rep t = t then φ t else 0
  have hdc_eq : ∀ {s t x : G}, x ∈ dc R K s → x ∈ dc R K t → dc R K s = dc R K t := fun hs ht =>
    Set.Subset.antisymm (dc_subset R K hs ht) (dc_subset R K ht hs)
  have hinv : ∀ {s x : G}, x ∈ dc R K s → φ x = φ s := by
    rintro s x ⟨r, hr, κ, hκ, rfl⟩
    rw [hK κ hκ, hR r hr]
  refine ⟨c, fun t => ?_, fun x => ?_⟩
  · simp only [c]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  by_cases hx : ∃ t ∈ T, x ∈ dc R K t
  · obtain ⟨t0, ht0, hxt0⟩ := hx
    have hS : (S t0).Nonempty := ⟨t0, Finset.mem_filter.mpr ⟨ht0, rfl⟩⟩
    obtain ⟨ht1T, ht1dc⟩ := Finset.mem_filter.mp hS.choose_spec
    have hrep : ∀ t, dc R K t = dc R K t0 → rep t = hS.choose := by
      intro t ht
      have hSt : S t = S t0 := by simp only [S, ht]
      simp only [rep, hSt, dif_pos hS]
    have hxt1 : x ∈ dc R K hS.choose := by rw [ht1dc]; exact hxt0
    rw [Finset.sum_eq_single hS.choose]
    · have hc1 : c hS.choose = φ hS.choose := by
        simp only [c]
        rw [if_pos ⟨ht1T, hrep _ ht1dc⟩]
      rw [Set.indicator_of_mem hxt1, hc1, hinv hxt1]
    · intro t _ hne
      by_cases hxt : x ∈ dc R K t
      · have hc0 : c t = 0 := by
          simp only [c]
          rw [if_neg]
          rintro ⟨-, h⟩
          exact hne (h.symm.trans (hrep t (hdc_eq hxt hxt0)))
        rw [Set.indicator_of_mem hxt, hc0]
      · rw [Set.indicator_of_notMem hxt]
    · intro h
      exact absurd ht1T h
  · push_neg at hx
    have hφ : φ x = 0 := by
      by_contra h
      obtain ⟨t, ht, hxt⟩ := hT x h
      exact hx t ht hxt
    rw [hφ]
    symm
    exact Finset.sum_eq_zero fun t ht => Set.indicator_of_notMem (hx t ht) _

theorem main : (let d1 : {G : Type} → [inst : Group G] → Subgroup G → Subgroup G → G → Set G := @(fun {G : Type} [Group G] (R K : Subgroup G) (t : G) ↦ {x : G | ∃ r ∈ R, ∃ κ ∈ K, x = r * t * κ}); ∀ {G : Type} [inst : Group G] {M : Type} [inst_1 : AddCommMonoid M] (R K : Subgroup G) (T : Finset G) (φ : G → M), (∀ r ∈ R, ∀ (x : G), φ (r * x) = φ x) → (∀ κ ∈ K, ∀ (x : G), φ (x * κ) = φ x) → (∀ (x : G), φ x ≠ (0 : M) → ∃ t ∈ T, x ∈ d1 R K t) → ∃ (c : G → M), (∀ (t : G), c t = (0 : M) ∨ c t = φ t) ∧ ∀ (x : G), φ x = ∑ t ∈ T, Set.indicator (d1 R K t) (fun (x : G) ↦ c t) x) := by
  intro d1 G _ M _ R K T φ hR hK hT
  exact exists_eq_sum_indicator R K T φ hR hK hT

end GlobalTheory.DoubleCosetIndicator
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualMatrix
section
namespace GlobalTheory.IwaFlag

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {ρ : ℕ} {c : R →+* R} {ε : R} {O : AddSubgroup R}
  {h : V →ₗ[R] V →ₛₗ[c] R} {M : AddSubgroup V}

def Princ (ε : R) (O : AddSubgroup R) : Prop :=
  ∀ J : AddSubgroup R, (∀ a ∈ J, ε * a = a) → (∀ o ∈ O, ∀ a ∈ J, o * a ∈ J) → (∃ m : ℕ, 0 < m ∧ (m : R) * ε ∈ J) →
    (∃ N : ℕ, 0 < N ∧ ∀ a ∈ J, (N : R) * a ∈ O) → ∃ α ∈ J, ∃ α', ε * α' = α' ∧ α * α' = ε ∧ ∀ a ∈ J, α' * a ∈ O

theorem smul_mem_of_sd (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hM₁ : ∀ y ∈ M, ε • y = y)
    (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O)) {o : R} (ho : o ∈ O) {y : V} (hy : y ∈ M) : o • y ∈ M := by
  refine (hM₂ _ (by rw [smul_comm, hM₁ y hy])).2 fun x hx => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  exact hmul _ ho _ ((hM₂ y (hM₁ y hy)).1 hy x hx)

theorem exists_triangular (hεc : c ε = ε) (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ε • y = y) (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O))
    (X : (Fin ρ → R) →ₗ[R] V) (f : Fin ρ → V) (hXf : ∀ t k, h (X t) (f k) = t k) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, X (Pi.single k ((N : R) * ε)) ∈ M) (hf : ∀ k, ((N : R) * ε) • f k ∈ M) (i : Fin ρ) :
    ∃ (b : Fin ρ → R) (α' : R), (∀ l, i < l → b l = 0) ∧ X b ∈ M ∧ ε * α' = α' ∧ b i * α' = ε ∧
      ∀ t : Fin ρ → R, (∀ l, i < l → t l = 0) → X t ∈ M → α' * t i ∈ O := by
  have hfix : ∀ t, X t ∈ M → ∀ k, ε * t k = t k := fun t ht k => by
    have := congrArg (fun z => h z (f k)) (hM₁ _ ht)
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, hXf] using this
  let J : AddSubgroup R :=
    { carrier := {a | ∃ t : Fin ρ → R, (∀ l, i < l → t l = 0) ∧ X t ∈ M ∧ t i = a}
      zero_mem' := ⟨0, fun _ _ => rfl, by rw [map_zero]; exact M.zero_mem, rfl⟩
      add_mem' := by
        rintro _ _ ⟨t, h1, h2, rfl⟩ ⟨s, g1, g2, rfl⟩
        exact ⟨t + s, fun l hl => by simp [h1 l hl, g1 l hl], by rw [map_add (f := _)]; exact M.add_mem h2 g2, rfl⟩
      neg_mem' := by
        rintro _ ⟨t, h1, h2, rfl⟩
        exact ⟨-t, fun l hl => by simp [h1 l hl], by rw [map_neg]; exact M.neg_mem h2, rfl⟩ }
  obtain ⟨α, ⟨b, hb1, hb2, rfl⟩, α', h1, h2, h3⟩ := hP J
    (by rintro _ ⟨t, -, h2, rfl⟩; exact hfix t h2 i)
    (by
      rintro o ho _ ⟨t, h1, h2, rfl⟩
      exact ⟨o • t, fun l hl => by simp [h1 l hl], by rw [map_smul]; exact smul_mem_of_sd hmul hM₁ hM₂ ho h2, rfl⟩)
    ⟨N, hN, Pi.single i ((N : R) * ε), fun l hl => Pi.single_eq_of_ne hl.ne' _, he i, Pi.single_eq_same _ _⟩
    ⟨N, hN, by
      rintro _ ⟨t, -, h2, rfl⟩
      have := (hM₂ _ (hM₁ _ h2)).1 h2 _ (hf i)
      rwa [map_smulₛₗ, hXf, map_mul, map_natCast, hεc, smul_eq_mul, mul_assoc, hfix t h2 i] at this⟩
  exact ⟨b, α', hb1, hb2, h1, h2, fun t ht1 ht2 => h3 _ ⟨t, ht1, ht2, rfl⟩⟩

theorem exists_step (hcc : ∀ a, c (c a) = a) (hεε : ε * ε = ε) (hεc : c ε = ε) (hεO : ε ∈ O) (hOε : ∀ a ∈ O, ε * a = a)
    (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hcO : ∀ a ∈ O, c a ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ε • y = y) (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O))
    (X : (Fin ρ → R) →ₗ[R] V) (f : Fin ρ → V) (hXf : ∀ t k, h (X t) (f k) = t k) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, X (Pi.single k ((N : R) * ε)) ∈ M) (hf : ∀ k, ((N : R) * ε) • f k ∈ M)
    (b : Fin ρ → Fin ρ → R) (hb₁ : ∀ i l, i < l → b i l = 0) (hb₂ : ∀ i, X (b i) ∈ M) (j : Fin ρ) (α' : R)
    (hα : b j j * α' = ε) (hJ : ∀ t : Fin ρ → R, (∀ l, j < l → t l = 0) → X t ∈ M → α' * t j ∈ O)
    (ih : ∀ z : Fin ρ → R, (∀ i, z i ∈ O) → ∃ y ∈ M, ∀ i, i < j → h (X (b i)) y = z i) :
    ∃ w ∈ M, (∀ i, i < j → h (X (b i)) w = 0) ∧ h (X (b j)) w = ε := by
  classical
  have hint : ∀ i, ∀ y ∈ M, h (X (b i)) y ∈ O := fun i => (hM₂ _ (hM₁ _ (hb₂ i))).1 (hb₂ i)
  have hsm : ∀ {o : R}, o ∈ O → ∀ {y : V}, y ∈ M → o • y ∈ M := fun ho _ hy => smul_mem_of_sd hmul hM₁ hM₂ ho hy
  let K : AddSubgroup R :=
    { carrier := {a | ∃ y ∈ M, (∀ i, i < j → h (X (b i)) y = 0) ∧ h (X (b j)) y = a}
      zero_mem' := ⟨0, M.zero_mem, fun _ _ => map_zero _, map_zero _⟩
      add_mem' := by
        rintro _ _ ⟨t, h1, h2, rfl⟩ ⟨s, g1, g2, rfl⟩
        exact ⟨t + s, M.add_mem h1 g1, fun l hl => by rw [map_add (f := _), h2 l hl, g2 l hl, add_zero], map_add _ _ _⟩
      neg_mem' := by
        rintro _ ⟨t, h1, h2, rfl⟩
        exact ⟨-t, M.neg_mem h1, fun l hl => by rw [map_neg, h2 l hl, neg_zero], map_neg _ _⟩ }
  have hKO : ∀ o ∈ O, ∀ a ∈ K, o * a ∈ K := by
    rintro o ho _ ⟨t, h1, h2, rfl⟩
    exact ⟨c o • t, hsm (hcO o ho) h1, fun l hl => by rw [map_smulₛₗ, h2 l hl, smul_zero],
      by rw [map_smulₛₗ, hcc, smul_eq_mul]⟩
  have hαN : α' * ((N : R) * ε) ∈ O := by
    have := hJ (Pi.single j ((N : R) * ε)) (fun l hl => Pi.single_eq_of_ne hl.ne' _) (he j)
    rwa [Pi.single_eq_same] at this
  have hNK : (N : R) * ε * b j j ∈ K :=
    ⟨_, hf j, fun i hi => by rw [map_smulₛₗ, hXf, hb₁ i j hi, smul_zero],
      by rw [map_smulₛₗ, hXf, map_mul, map_natCast, hεc, smul_eq_mul]⟩
  obtain ⟨β, hβ, β', h1, h2, h3⟩ := hP K
    (by rintro _ ⟨t, h1, -, rfl⟩; exact hOε _ (hint j t h1)) hKO
    ⟨N * N, Nat.mul_pos hN hN, by
      have e : ((N * N : ℕ) : R) * ε = α' * ((N : R) * ε) * ((N : R) * ε * b j j) := by
        push_cast
        linear_combination (-(N : R) * N * ε * ε) * hα - ((N : R) * N * (ε + 1)) * hεε
      rw [e]; exact hKO _ hαN _ hNK⟩
    ⟨1, one_pos, by rintro _ ⟨t, h1, -, rfl⟩; rw [Nat.cast_one, one_mul]; exact hint j t h1⟩
  choose g hg hg' using fun i : Fin ρ => ih (Pi.single i ε) fun l => by
    by_cases hl : l = i
    · rw [hl, Pi.single_eq_same]; exact hεO
    · rw [Pi.single_eq_of_ne hl]; exact O.zero_mem
  let s := Finset.univ.filter (· < j)
  let t : Fin ρ → R := β' • b j - ∑ i ∈ s, (β' * h (X (b j)) (g i)) • b i
  have hXt : X t = β' • X (b j) - ∑ i ∈ s, (β' * h (X (b j)) (g i)) • X (b i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [t, map_sub, map_sum, map_smul]
  have htM : X t ∈ M := by
    refine (hM₂ _ ?_).2 fun y hy => ?_
    · rw [hXt, smul_sub, Finset.smul_sum, smul_smul, h1]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, ← mul_assoc, h1]
    · have hy' : y - ∑ i ∈ s, c (h (X (b i)) y) • g i ∈ M :=
        M.sub_mem hy (M.sum_mem fun i _ => hsm (hcO _ (hint i y hy)) (hg i))
      have hK : h (X (b j)) (y - ∑ i ∈ s, c (h (X (b i)) y) • g i) ∈ K := by
        refine ⟨_, hy', fun l hl => ?_, rfl⟩
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sub, map_sum, Finset.sum_eq_single l]
        · rw [map_smulₛₗ, hcc, hg' l l hl, Pi.single_eq_same, smul_eq_mul, mul_comm, hOε _ (hint l y hy), sub_self]
        · intro i _ hi
          rw [map_smulₛₗ, hg' i l hl, Pi.single_eq_of_ne hi.symm, smul_zero]
        · intro hl'; exact absurd (by simpa [s] using hl) hl'
      have := h3 _ hK
      convert this using 1
      rw [hXt]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, hcc, mul_sub, Finset.mul_sum, RingHom.id_apply]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
  have hz : ∀ l, j ≤ l → (∑ i ∈ s, (β' * h (X (b j)) (g i)) • b i) l = 0 := fun l hl => by
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero fun i hi => by
      rw [Pi.smul_apply, hb₁ i l (lt_of_lt_of_le (Finset.mem_filter.1 hi).2 hl), smul_zero]
  have hβ' : β' ∈ O := by
    have := hJ t (fun l hl => by
      simp only [t]
      rw [Pi.sub_apply, hz l hl.le, Pi.smul_apply, hb₁ j l hl, smul_zero, sub_zero]) htM
    simp only [t] at this
    rw [Pi.sub_apply, hz j le_rfl, Pi.smul_apply, sub_zero, smul_eq_mul] at this
    have e : α' * (β' * b j j) = β' := by linear_combination β' * hα + h1
    rwa [e] at this
  have := hKO _ hβ' _ hβ
  rw [mul_comm, h2] at this
  exact this

theorem exists_flag_dual (hcc : ∀ a, c (c a) = a) (hεε : ε * ε = ε) (hεc : c ε = ε) (hεO : ε ∈ O)
    (hOε : ∀ a ∈ O, ε * a = a) (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hcO : ∀ a ∈ O, c a ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ε • y = y) (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O))
    (X : (Fin ρ → R) →ₗ[R] V) (f : Fin ρ → V) (hXf : ∀ t k, h (X t) (f k) = t k) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, X (Pi.single k ((N : R) * ε)) ∈ M) (hf : ∀ k, ((N : R) * ε) • f k ∈ M) :
    ∃ b : Fin ρ → Fin ρ → R, (∀ i l, i < l → b i l = 0) ∧ (∀ i l, ε * b i l = b i l) ∧ (∀ i, X (b i) ∈ M) ∧
      ∃ y : Fin ρ → V, (∀ j, y j ∈ M) ∧ ∀ i j, h (X (b i)) (y j) = if i = j then ε else 0 := by
  classical
  choose b α' hb₁ hb₂ _ hα hJ using exists_triangular hεc hmul hP hM₁ hM₂ X f hXf N hN he hf
  have hint : ∀ i, ∀ y ∈ M, h (X (b i)) y ∈ O := fun i => (hM₂ _ (hM₁ _ (hb₂ i))).1 (hb₂ i)
  have key : ∀ n : ℕ, n ≤ ρ → ∀ z : Fin ρ → R, (∀ i, z i ∈ O) → ∃ y ∈ M, ∀ i : Fin ρ, i.1 < n → h (X (b i)) y = z i := by
    intro n
    induction n with
    | zero => exact fun _ z _ => ⟨0, M.zero_mem, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ n ih =>
      intro hn z hz
      let j : Fin ρ := ⟨n, hn⟩
      obtain ⟨w, hw, hw₁, hw₂⟩ := exists_step hcc hεε hεc hεO hOε hmul hcO hP hM₁ hM₂ X f hXf N hN he hf b hb₁ hb₂ j
        (α' j) (hα j) (hJ j) (ih (Nat.le_of_succ_le hn))
      obtain ⟨y, hy, hy'⟩ := ih (Nat.le_of_succ_le hn) z hz
      have ho : z j - h (X (b j)) y ∈ O := O.sub_mem (hz j) (hint j y hy)
      refine ⟨y + c (z j - h (X (b j)) y) • w, M.add_mem hy (smul_mem_of_sd hmul hM₁ hM₂ (hcO _ ho) hw), fun i hi => ?_⟩
      rw [map_add (f := _), map_smulₛₗ, hcc, smul_eq_mul]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · rw [hw₁ i hi, hy' i hi, mul_zero, add_zero]
      · have : i = j := Fin.ext hi
        rw [this, hw₂, mul_comm, hOε _ ho, add_sub_cancel]
  choose y hy hy' using fun j : Fin ρ => key ρ le_rfl (Pi.single j ε) fun l => by
    by_cases hl : l = j
    · rw [hl, Pi.single_eq_same]; exact hεO
    · rw [Pi.single_eq_of_ne hl]; exact O.zero_mem
  refine ⟨b, hb₁, fun i k => ?_, hb₂, y, hy, fun i j => ?_⟩
  · have := congrArg (fun z => h z (f k)) (hM₁ _ (hb₂ i))
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, hXf] using this
  · rw [hy' j i i.2, Pi.single_apply]


open Matrix in
def sesq (c : R →+* R) {n : ℕ} (G : Matrix (Fin n) (Fin n) R) : (Fin n → R) →ₗ[R] (Fin n → R) →ₛₗ[c] R :=
  LinearMap.mk₂'ₛₗ (RingHom.id R) c (fun x y => ∑ i, ∑ j, c (y i) * G i j * x j)
    (fun x x' y => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun a x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    (fun x y y' => by simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib])
    (fun a x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

open Matrix in
theorem sesq_col {n p q : ℕ} (G : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin n) (Fin p) R) (B : Matrix (Fin n) (Fin q) R)
    (i : Fin p) (j : Fin q) : sesq c G (fun k => A k i) (fun k => B k j) = ((B.map c)ᵀ * (G * A)) j i := by
  simp only [sesq, LinearMap.mk₂'ₛₗ_apply, Matrix.mul_apply, transpose_apply, map_apply, Finset.mul_sum, mul_assoc]


open scoped Matrix in
open Matrix in
theorem exists_flag_dual_matrix {n : ℕ} {M : AddSubgroup (Fin n → R)} (G : Matrix (Fin n) (Fin n) R)
    (hcc : ∀ a, c (c a) = a) (hεε : ε * ε = ε) (hεc : c ε = ε) (hεO : ε ∈ O)
    (hOε : ∀ a ∈ O, ε * a = a) (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hcO : ∀ a ∈ O, c a ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ∀ i, ε * y i = y i)
    (hM₂ : ∀ y : Fin n → R, (∀ i, ε * y i = y i) → (y ∈ M ↔ ∀ x ∈ M, ∑ i, ∑ j, c (x i) * G i j * y j ∈ O))
    (E F : Matrix (Fin n) (Fin ρ) R) (hEF : (F.map c)ᵀ * (G * E) = 1) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, (fun l => (N : R) * ε * E l k) ∈ M) (hf : ∀ k, (fun l => (N : R) * ε * F l k) ∈ M) :
    ∃ b : Matrix (Fin ρ) (Fin ρ) R, (∀ i j, j < i → b i j = 0) ∧ (∀ i j, ε * b i j = b i j) ∧
      (∀ i, (fun k => (E * b) k i) ∈ M) ∧ ∃ c' : Matrix (Fin n) (Fin ρ) R, (∀ i, (fun k => c' k i) ∈ M) ∧
        (c'.map c)ᵀ * (G * (E * b)) = ε • (1 : Matrix (Fin ρ) (Fin ρ) R) := by
  classical
  obtain ⟨b, h1, h2, h3, y, h4, h5⟩ := exists_flag_dual (h := sesq c G) (M := M) hcc hεε hεc hεO hOε hmul hcO hP
    (fun y hy => funext (hM₁ y hy)) (fun y hy => hM₂ y (congrFun hy)) E.mulVecLin (fun k l => F l k)
    (fun t k => by
      have := sesq_col (c := c) G (E * Matrix.of fun l (_ : Fin 1) => t l) F 0 k
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ G, hEF, Matrix.one_mul] at this
      exact this) N hN
    (fun k => by
      convert he k using 1
      ext l
      simp [mul_comm]) hf
  refine ⟨Matrix.of fun i j => b j i, fun i j hij => h1 j i hij, fun i j => h2 j i, h3, Matrix.of fun k j => y j k, h4, ?_⟩
  ext j i
  rw [← sesq_col]
  refine (h5 i j).trans ?_
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Matrix.one_apply_ne (Ne.symm hij)]

end GlobalTheory.IwaFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntSmulMemOfFg
section
namespace GlobalTheory.FiniteGenIntegerScalar

theorem exists_int_smul_mem_of_fg {E : Type} [Field E] {V : Type} [AddCommGroup V]
    [Module (NumberField.RingOfIntegers E) V]
    {L M : Submodule (NumberField.RingOfIntegers E) V}
    (h : ∀ x : V, ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ L) (hM : M.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ M, N • x ∈ L := by
  classical
  obtain ⟨S, rfl⟩ := hM
  choose f hf0 hfL using h
  refine ⟨∏ s ∈ S, f s, Finset.prod_ne_zero_iff.mpr fun s _ => hf0 s, ?_⟩
  intro x hx
  let P : Submodule (NumberField.RingOfIntegers E) V :=
    { carrier := {y | (∏ s ∈ S, f s) • y ∈ L}
      add_mem' := fun {a b} ha hb => by
        show _ ∈ L
        rw [smul_add]
        exact L.add_mem ha hb
      zero_mem' := by
        show _ ∈ L
        rw [smul_zero]
        exact L.zero_mem
      smul_mem' := fun c y hy => by
        show _ ∈ L
        rw [smul_comm (∏ s ∈ S, f s) c y]
        exact L.smul_mem c hy }
  have hle : Submodule.span _ (S : Set V) ≤ P := by
    rw [Submodule.span_le]
    intro s hs
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f hs
    show (∏ s ∈ S, f s) • s ∈ L
    rw [hk, mul_comm, mul_smul]
    exact zsmul_mem (hfL s) k
  exact hle hx

end GlobalTheory.FiniteGenIntegerScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Imports
section
namespace GlobalTheory.ExistsPrimeMem

theorem exists_prime_mem {A : Type} [inst : CommRing A] (P : Ideal A) (hP : Ideal.IsPrime P) :
    ∀ (n : ℕ), n ≠ (0 : ℕ) → (↑n : A) ∈ P → ∃ (ℓ : ℕ), Nat.Prime ℓ ∧ (↑ℓ : A) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hnP
    by_cases h1 : n = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one P).2 (by simpa using hnP)) hP.ne_top
    · have hp := Nat.minFac_prime h1
      have hpos : 0 < n := Nat.pos_of_ne_zero hn
      have hsplit : ((n : ℕ) : A) = (n.minFac : A) * ((n / n.minFac : ℕ) : A) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.minFac_dvd n)]
      rw [hsplit] at hnP
      rcases hP.mem_or_mem hnP with h | h
      · exact ⟨n.minFac, hp, h⟩
      · exact ih (n / n.minFac) (Nat.div_lt_self hpos hp.one_lt)
          (Nat.div_pos (Nat.minFac_le hpos) (Nat.minFac_pos n)).ne' h

end GlobalTheory.ExistsPrimeMem
end

