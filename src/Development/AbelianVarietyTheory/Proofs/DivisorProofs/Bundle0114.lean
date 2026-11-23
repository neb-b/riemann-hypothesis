module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableNormMulPowOfBounded
section
namespace GlobalTheory.SummableSeriesBounds

open PowerSeries Filter Topology

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

def bdd (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] :
    Subring (PowerSeries C) where
  carrier := {Φ | ∃ b : ℝ, ∀ n : ℕ, ‖coeff n Φ‖ ≤ b}
  mul_mem' := by
    rintro Φ Ψ ⟨a, ha⟩ ⟨b, hb⟩
    have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
    have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
    refine ⟨a * b, fun n => ?_⟩
    rw [coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha0 hb0) ?_
    intro p _
    rw [norm_mul]
    exact mul_le_mul (ha _) (hb _) (norm_nonneg _) ha0
  one_mem' := ⟨1, fun n => by
    rw [coeff_one]; split_ifs <;> simp⟩
  add_mem' := by
    rintro Φ Ψ ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, fun n => ?_⟩
    rw [map_add (f := _)]
    exact (norm_add_le _ _).trans (add_le_add (ha n) (hb n))
  zero_mem' := ⟨0, fun n => by simp⟩
  neg_mem' := by
    rintro Φ ⟨a, ha⟩
    exact ⟨a, fun n => by simpa using ha n⟩

theorem summable_norm_mul_pow_of_bounded {π : C} (hπ : ‖π‖ < 1) {a : ℕ → C} {b : ℝ} (hb : ∀ n, ‖a n‖ ≤ b) :
    Summable fun n => ‖a n * π ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg π) hπ).mul_left b)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hb n) (by positivity)

theorem summable_norm_bdd {π : C} (hπ : ‖π‖ < 1) (Φ : bdd C) :
    Summable fun n => ‖coeff n (Φ : PowerSeries C) * π ^ n‖ := by
  obtain ⟨b, hb⟩ := Φ.2
  exact summable_norm_mul_pow_of_bounded hπ hb

noncomputable def ev [CompleteSpace C] {π : C} (hπ : ‖π‖ < 1) : bdd C →+* C where
  toFun Φ := ∑' n, coeff n (Φ : PowerSeries C) * π ^ n
  map_one' := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [coeff_one, hn]
  map_zero' := by simp
  map_add' Φ Ψ := by
    rw [← (summable_norm_bdd hπ Φ).of_norm.tsum_add (summable_norm_bdd hπ Ψ).of_norm]
    refine tsum_congr fun n => ?_
    simp [add_mul]
  map_mul' Φ Ψ := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm_bdd hπ Φ)
      (summable_norm_bdd hπ Ψ)]
    refine tsum_congr fun n => ?_
    rw [Subring.coe_mul, coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p.1 + p.2 = n := by simpa using hp
    rw [← hp', pow_add]
    ring

omit [IsUltrametricDist C] in
theorem coeff_zero_lin (π : C) (G : PowerSeries C) :
    coeff 0 ((X - PowerSeries.C π) * G) = -(π * coeff 0 G) := by
  rw [sub_mul, map_sub, coeff_C_mul]
  simp

omit [IsUltrametricDist C] in
theorem coeff_succ_lin (π : C) (G : PowerSeries C) (n : ℕ) :
    coeff (n + 1) ((X - PowerSeries.C π) * G) = coeff n G - π * coeff (n + 1) G := by
  rw [sub_mul, map_sub, coeff_C_mul, coeff_succ_X_mul]

noncomputable def lin (π : C) : bdd C :=
  ⟨X - PowerSeries.C π, ⟨1 + ‖π‖, fun n => by
    rw [map_sub]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [coeff_X]; split_ifs <;> simp
    · rw [coeff_C]; split_ifs <;> simp⟩⟩

theorem lin_ne_zero (π : C) : lin π ≠ 0 := by
  intro h
  have := congrArg (fun Φ : bdd C => coeff 1 (Φ : PowerSeries C)) h
  simp [lin, coeff_C, coeff_X] at this

theorem ev_lin [CompleteSpace C] {π : C} (hπ : ‖π‖ < 1) : ev hπ (lin π) = 0 := by
  change ∑' n, coeff n (X - PowerSeries.C π : PowerSeries C) * π ^ n = 0
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, coeff_C, coeff_X]
  · intro n hn
    have h0 : n ≠ 0 := by rintro rfl; simp at hn
    have h1 : n ≠ 1 := by rintro rfl; simp at hn
    simp [coeff_C, coeff_X, h0, h1]

theorem lin_dvd [CompleteSpace C] {π : C} (hπ : ‖π‖ < 1) (Φ : bdd C) (h : ev hπ Φ = 0) :
    lin π ∣ Φ := by
  obtain ⟨b, hb⟩ := Φ.2
  have hs : ∀ m, Summable fun k => ‖coeff (k + m) (Φ : PowerSeries C) * π ^ k‖ :=
    fun m => summable_norm_mul_pow_of_bounded hπ (a := fun k => coeff (k + m) (Φ : PowerSeries C))
      (fun k => hb _)
  let g : ℕ → C := fun m => ∑' k, coeff (k + m) (Φ : PowerSeries C) * π ^ k
  have hg : ∀ m, g m = coeff m (Φ : PowerSeries C) + π * g (m + 1) := by
    intro m
    simp only [g]
    rw [(hs m).of_norm.tsum_eq_zero_add, ← tsum_mul_left]
    congr 1
    · simp
    · refine tsum_congr fun k => ?_
      rw [show k + 1 + m = k + (m + 1) by ring]
      ring
  have hg0 : g 0 = 0 := h
  have hgb : ∀ m, ‖g m‖ ≤ ∑' k, b * ‖π‖ ^ k := by
    intro m
    refine tsum_of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg π) hπ).mul_left b).hasSum fun k => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hb _) (by positivity)
  refine ⟨⟨PowerSeries.mk fun n => g (n + 1), ⟨_, fun n => by rw [coeff_mk]; exact hgb _⟩⟩, ?_⟩
  apply Subtype.ext
  change (Φ : PowerSeries C) = (X - PowerSeries.C π) * PowerSeries.mk fun n => g (n + 1)
  ext n
  cases n with
  | zero =>
    rw [coeff_zero_lin, coeff_mk]
    have := hg 0
    rw [hg0] at this
    linear_combination -this
  | succ n =>
    rw [coeff_succ_lin, coeff_mk, coeff_mk]
    linear_combination -hg (n + 1)

theorem bound_of_lin_mul {π : C} (hπ : ‖π‖ < 1) {G : PowerSeries C} {b c : ℝ}
    (hc : ∀ n, ‖coeff n G‖ ≤ c) (hb : ∀ n, ‖coeff n ((X - PowerSeries.C π) * G)‖ ≤ b) (m : ℕ) :
    ‖coeff m G‖ ≤ b := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  have key : ∀ k m, ‖coeff m G‖ ≤ max b (‖π‖ ^ k * c) := by
    intro k
    induction k with
    | zero => intro m; simpa using Or.inr (hc m)
    | succ k ih =>
      intro m
      have e : coeff m G = coeff (m + 1) ((X - PowerSeries.C π) * G) + π * coeff (m + 1) G := by
        rw [coeff_succ_lin]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hb _).trans (le_max_left _ _)) ?_)
      rw [norm_mul]
      refine (mul_le_mul_of_nonneg_left (ih (m + 1)) (norm_nonneg _)).trans ?_
      rw [mul_max_of_nonneg _ _ (norm_nonneg _)]
      refine max_le_max (mul_le_of_le_one_left hb0 hπ.le) (le_of_eq (by ring))
  have ht : Tendsto (fun k : ℕ => max b (‖π‖ ^ k * c)) atTop (𝓝 (max b (0 * c))) :=
    tendsto_const_nhds.max ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπ).mul_const c)
  rw [zero_mul, max_eq_left hb0] at ht
  exact ge_of_tendsto' ht fun k => key k m

theorem bound_of_lin_pow_mul {π : C} (hπ : ‖π‖ < 1) {b : ℝ} (n : ℕ) (G : bdd C)
    (hb : ∀ m, ‖coeff m ((lin π ^ n * G : bdd C) : PowerSeries C)‖ ≤ b) (m : ℕ) :
    ‖coeff m (G : PowerSeries C)‖ ≤ b := by
  induction n generalizing m with
  | zero => simpa using hb m
  | succ n ih =>
    refine ih (fun j => ?_) m
    obtain ⟨c, hc⟩ := (lin π ^ n * G).2
    refine bound_of_lin_mul hπ hc (fun i => ?_) j
    have := hb i
    rwa [pow_succ', mul_assoc, Subring.coe_mul] at this

theorem decay {π : C} (hπ : ‖π‖ < 1) {b : ℝ} {G : PowerSeries C} (hb : ∀ m, ‖coeff m G‖ ≤ b)
    (n m : ℕ) : ‖coeff m ((X - PowerSeries.C π) ^ n * G)‖ ≤ ‖π‖ ^ (n - m) * b := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  induction n generalizing m with
  | zero => simpa using hb m
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    cases m with
    | zero =>
      rw [coeff_zero_lin, norm_neg, norm_mul]
      refine (mul_le_mul_of_nonneg_left (ih 0) (norm_nonneg _)).trans (le_of_eq ?_)
      simp only [Nat.sub_zero]; ring
    | succ m =>
      rw [coeff_succ_lin, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · simpa using ih m
      · rw [norm_neg, norm_mul]
        refine (mul_le_mul_of_nonneg_left (ih (m + 1)) (norm_nonneg _)).trans ?_
        rw [← mul_assoc, ← pow_succ']
        refine mul_le_mul_of_nonneg_right ?_ hb0
        exact pow_le_pow_of_le_one (norm_nonneg _) hπ.le (by omega)

theorem eq_zero_of_forall_dvd {π : C} (hπ : ‖π‖ < 1) (Φ : bdd C) (h : ∀ n, lin π ^ n ∣ Φ) :
    Φ = 0 := by
  obtain ⟨b, hb⟩ := Φ.2
  apply Subtype.ext
  ext m
  have key : ∀ n, ‖coeff m (Φ : PowerSeries C)‖ ≤ ‖π‖ ^ n * b := by
    intro n
    obtain ⟨G, hG⟩ := h (n + m)
    have h1 := bound_of_lin_pow_mul hπ (n + m) G (by rw [← hG]; exact hb)
    have h2 := decay hπ h1 (n + m) m
    rw [Nat.add_sub_cancel] at h2
    rw [hG]
    exact h2
  have ht : Tendsto (fun k : ℕ => ‖π‖ ^ k * b) atTop (𝓝 (0 * b)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπ).mul_const b
  rw [zero_mul] at ht
  have := ge_of_tendsto' ht key
  simpa using this

theorem main (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    (π : C) (hπ : ‖π‖ < 1) :
    ∃ (B : Subring (PowerSeries C)) (ev : B →+* C) (t : B),
      (∀ Φ : PowerSeries C, Φ ∈ B ↔ ∃ b : ℝ, ∀ n : ℕ, ‖coeff n Φ‖ ≤ b) ∧
      (∀ Φ : B, ev Φ = ∑' n : ℕ, coeff n (Φ : PowerSeries C) * π ^ n) ∧ t ≠ 0 ∧
      (∀ Φ : B, ev Φ = 0 ↔ t ∣ Φ) ∧ ∀ Φ : B, Φ ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ Φ := by
  refine ⟨bdd C, ev hπ, lin π, fun _ => Iff.rfl, fun _ => rfl, lin_ne_zero π,
    fun Φ => ⟨lin_dvd hπ Φ, ?_⟩, fun Φ hΦ => ?_⟩
  · rintro ⟨G, rfl⟩
    rw [map_mul, ev_lin, zero_mul]
  · by_contra hc
    push_neg at hc
    exact hΦ (eq_zero_of_forall_dvd hπ Φ hc)

end GlobalTheory.SummableSeriesBounds
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportOfQuotientFlatModule
section
namespace GlobalTheory

open PrimeSpectrum

namespace SpanGenLocus

theorem notMem_support_quotient_iff {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (q : PrimeSpectrum R) (N : Submodule R M) :
    q ∉ Module.support R (M ⧸ N) ↔ ∀ x : M, ∃ t ∉ q.asIdeal, t • x ∈ N := by
  rw [Module.notMem_support_iff']
  constructor
  · intro h x
    obtain ⟨t, ht, e⟩ := h (Submodule.Quotient.mk x)
    exact ⟨t, ht, (Submodule.Quotient.mk_eq_zero N).1 (by rw [Submodule.Quotient.mk_smul]; exact e)⟩
  · intro h y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N y
    obtain ⟨t, ht, e⟩ := h x
    exact ⟨t, ht, by rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact e⟩

theorem linIndep_at_of_gen_at {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (q : PrimeSpectrum R) {r : ℕ}
    (hr : Module.rankAtStalk M q = r) (n : Fin r → M)
    (hgen : ∀ x : M, ∃ t ∉ q.asIdeal, t • x ∈ Submodule.span R (Set.range n))
    (c : Fin r → R) (hc : ∑ i, c i • n i = 0) : ∃ t ∉ q.asIdeal, ∀ i, t * c i = 0 := by
  let Rq := Localization.AtPrime q.asIdeal
  let Mq := LocalizedModule q.asIdeal.primeCompl M
  haveI : Module.Free Rq Mq := Module.mem_freeLocus.1 (by rw [Module.freeLocus_eq_univ]; trivial)
  let n' : Fin r → Mq := fun i => LocalizedModule.mk (n i) 1
  have hspan : Submodule.span Rq (Set.range n') = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    induction y using LocalizedModule.induction_on with
    | h x u =>
      obtain ⟨t, ht, hx⟩ := hgen x
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hx
      have e1 : LocalizedModule.mk x u =
          (Localization.mk (1 : R) (⟨t, ht⟩ * u) : Rq) • LocalizedModule.mk (t • x) 1 := by
        rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
        exact (LocalizedModule.mk_cancel_common_left ⟨t, ht⟩ u x).symm
      have e2 : (LocalizedModule.mk (t • x) 1 : Mq) = ∑ i, (algebraMap R Rq (a i)) • n' i := by
        rw [← ha]
        simp only [n', algebraMap_smul]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← LocalizedModule.mkLinearMap_apply, map_sum]
        simp [LocalizedModule.mkLinearMap_apply]
      rw [e1, e2]
      exact Submodule.smul_mem _ _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  let L : (Fin r → Rq) →ₗ[Rq] Mq := Fintype.linearCombination Rq n'
  have hL : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]; exact hspan
  have hrk : Module.finrank Rq Mq = r := hr
  let b := Module.finBasisOfFinrankEq Rq Mq hrk
  have hinj : Function.Injective L := by
    have h2 : Function.Surjective (b.equivFun.toLinearMap ∘ₗ L) :=
      b.equivFun.surjective.comp hL
    have h3 := OrzechProperty.injective_of_surjective_endomorphism _ h2
    exact fun x y hxy => h3 (by simp [hxy])
  have hz : L (fun i => algebraMap R Rq (c i)) = 0 := by
    simp only [L, Fintype.linearCombination_apply, n', algebraMap_smul]
    have h0 : (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) (∑ i, c i • n i) = 0 := by
      rw [hc, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, LocalizedModule.mkLinearMap_apply] using h0
  have hz' : (fun i => algebraMap R Rq (c i)) = 0 := hinj (by rw [hz, map_zero])
  have hi : ∀ i, ∃ τ : q.asIdeal.primeCompl, (τ : R) * c i = 0 := fun i =>
    (IsLocalization.map_eq_zero_iff q.asIdeal.primeCompl Rq (c i)).1 (congrFun hz' i)
  choose τ hτ using hi
  refine ⟨∏ j, (τ j : R), q.asIdeal.primeCompl.prod_mem (fun j _ => (τ j).2), fun i => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun j => (τ j : R)) (Finset.mem_univ i)
  rw [hk, mul_comm (τ i : R) k, mul_assoc, hτ i, mul_zero]

theorem exists_gen_near {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (p : PrimeSpectrum R) {r : ℕ}
    (hr : Module.rankAtStalk M p = r) :
    ∃ m : Fin r → M, ∃ f ∉ p.asIdeal, ∀ x : M, f • x ∈ Submodule.span R (Set.range m) := by
  let Rp := Localization.AtPrime p.asIdeal
  let Mp := LocalizedModule p.asIdeal.primeCompl M
  haveI : Module.Free Rp Mp := Module.mem_freeLocus.1 (by rw [Module.freeLocus_eq_univ]; trivial)
  have hrk : Module.finrank Rp Mp = r := hr
  let b := Module.finBasisOfFinrankEq Rp Mp hrk
  have hmk : ∀ y : Mp, ∃ (x : M) (u : p.asIdeal.primeCompl), LocalizedModule.mk x u = y :=
    fun y => LocalizedModule.induction_on (fun x u => ⟨x, u, rfl⟩) y
  choose m u hmu using fun i => hmk (b i)
  let N := Submodule.span R (Set.range m)
  have htop : Submodule.span Rp (Set.range fun i => (LocalizedModule.mk (m i) 1 : Mp)) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : b i = (Localization.mk (1 : R) (u i) : Rp) • LocalizedModule.mk (m i) 1 := by
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one, hmu]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hgen : ∀ x : M, ∃ t ∉ p.asIdeal, t • x ∈ N := by
    intro x
    have hx : (LocalizedModule.mk x 1 : Mp) ∈
        N.localized' Rp p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) := by
      rw [Submodule.localized'_span, ← Set.range_comp]
      rw [show ((LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) ∘ m) =
        fun i => (LocalizedModule.mk (m i) 1 : Mp) from rfl, htop]
      trivial
    obtain ⟨y, hy, s, hs⟩ := (Submodule.mem_localized' _ _ _ _ _).1 hx
    have h2 : IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) y s =
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) x (1 : p.asIdeal.primeCompl) := by
      rw [IsLocalizedModule.mk'_one, LocalizedModule.mkLinearMap_apply]; exact hs
    rw [IsLocalizedModule.mk'_eq_mk'_iff] at h2
    obtain ⟨c, hc⟩ := h2
    refine ⟨(c : R) * s, p.asIdeal.primeCompl.mul_mem c.2 s.2, ?_⟩
    have e : ((c : R) * s) • x = (c : R) • y := by
      simpa [Submonoid.smul_def, mul_smul] using hc
    rw [e]; exact N.smul_mem _ hy
  have hq : p ∉ Module.support R (M ⧸ N) := (notMem_support_quotient_iff p N).2 hgen
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hq
  obtain ⟨f, hf, hfp⟩ := hq
  refine ⟨m, f, hfp, fun x => ?_⟩
  have := Module.mem_annihilator.1 hf (Submodule.Quotient.mk x)
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this

theorem exists_local_det {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] {r : ℕ}
    (hr : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) (s : Fin r → M)
    (p : PrimeSpectrum R) :
    ∃ f g : R, f ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum R, f ∉ q.asIdeal →
      (q ∉ Module.support R (M ⧸ Submodule.span R (Set.range s)) ↔ g ∉ q.asIdeal) := by
  obtain ⟨m, f, hfp, hfm⟩ := exists_gen_near p (hr p)
  have ha : ∀ i, ∃ a : Fin r → R, ∑ j, a j • m j = f • s i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (hfm (s i))
  choose a ha using ha
  let A : Matrix (Fin r) (Fin r) R := Matrix.of fun j i => a i j
  have hK : ∀ u : Fin r → R, ∑ j, (A.mulVec u) j • m j = f • ∑ i, u i • s i := by
    intro u
    calc ∑ j, (A.mulVec u) j • m j = ∑ j, ∑ i, u i • (a i j • m j) := by
          simp only [A, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul, mul_smul]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => smul_comm _ _ _
      _ = ∑ i, u i • ∑ j, a i j • m j := by rw [Finset.sum_comm]; simp [Finset.smul_sum]
      _ = ∑ i, u i • f • s i := by simp [ha]
      _ = f • ∑ i, u i • s i := by rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  refine ⟨f, A.det, hfp, fun q hfq => ?_⟩
  rw [notMem_support_quotient_iff]
  constructor
  · intro hgen
    have hgm : ∀ x : M, ∃ t ∉ q.asIdeal, t • x ∈ Submodule.span R (Set.range m) :=
      fun x => ⟨f, hfq, hfm x⟩
    have hcol : ∀ j, ∃ τ : R, τ ∉ q.asIdeal ∧ ∃ w : Fin r → R, A.mulVec w = Pi.single j τ := by
      intro j
      obtain ⟨t, ht, hts⟩ := hgen (m j)
      obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hts
      have h1 := hK w
      rw [hw] at h1
      have hsingle : ∑ k, (Pi.single j (f * t) : Fin r → R) k • m k = f • t • m j := by
        rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
        simp [mul_smul]
      obtain ⟨τ, hτ, hτc⟩ := linIndep_at_of_gen_at q (hr q) m hgm
        (A.mulVec w - Pi.single j (f * t)) (by
          simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, hsingle, sub_self])
      refine ⟨τ * (f * t), q.asIdeal.primeCompl.mul_mem hτ
        (q.asIdeal.primeCompl.mul_mem hfq ht), τ • w, ?_⟩
      funext k
      have hk := hτc k
      rw [Pi.sub_apply, mul_sub, sub_eq_zero] at hk
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hk]
      by_cases hkj : k = j
      · subst hkj; simp
      · simp [Pi.single_apply, hkj]
    choose τ hτ w hw using hcol
    let B : Matrix (Fin r) (Fin r) R := Matrix.of fun k j => w j k
    have hAB : A * B = Matrix.diagonal τ := by
      ext k j
      have h := congrFun (hw j) k
      simp only [Matrix.mulVec, dotProduct] at h
      rw [Matrix.mul_apply]
      simp only [B, Matrix.of_apply]
      rw [h, Matrix.diagonal_apply]
      by_cases hkj : k = j
      · subst hkj; simp
      · simp [Pi.single_apply, hkj]
    have hprod : A.det * B.det ∉ q.asIdeal := by
      rw [← Matrix.det_mul, hAB, Matrix.det_diagonal]
      exact q.asIdeal.primeCompl.prod_mem (fun j _ => hτ j)
    exact fun hA => hprod (q.asIdeal.mul_mem_right _ hA)
  · intro hdet x
    obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hfm x)
    have hAu : A.mulVec (A.adjugate.mulVec v) = A.det • v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h1 := hK (A.adjugate.mulVec v)
    rw [hAu] at h1
    have h2 : ∑ j, (A.det • v) j • m j = (A.det * f) • x := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, hv]
    refine ⟨A.det * f, q.asIdeal.primeCompl.mul_mem hdet hfq, ?_⟩
    rw [← h2, h1]
    exact Submodule.smul_mem _ _ ((Submodule.mem_span_range_iff_exists_fun R).2 ⟨_, rfl⟩)

end SpanGenLocus

open SpanGenLocus

theorem isCompact_compl_support_quotient_span :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
      [Module.Flat R M] (r : ℕ), (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) →
      ∀ s : Fin r → M, IsCompact (Module.support R (M ⧸ Submodule.span R (Set.range s)))ᶜ := by
  intro R M _ _ _ _ _ r hr s
  choose f g hf hfg using fun p => exists_local_det hr s p
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p => (basicOpen (f p) : Set (PrimeSpectrum R))) (fun p => (basicOpen (f p)).isOpen)
    (fun p _ => Set.mem_iUnion.2 ⟨p, hf p⟩)
  have heq : (Module.support R (M ⧸ Submodule.span R (Set.range s)))ᶜ =
      ⋃ p ∈ t, (basicOpen (f p * g p) : Set (PrimeSpectrum R)) := by
    ext q
    simp only [Set.mem_compl_iff, Set.mem_iUnion, SetLike.mem_coe, mem_basicOpen, exists_prop]
    constructor
    · intro hq
      obtain ⟨p, hp, hqp⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ q))
      have hqp' : f p ∉ q.asIdeal := hqp
      exact ⟨p, hp, q.asIdeal.primeCompl.mul_mem hqp' ((hfg p q hqp').1 hq)⟩
    · rintro ⟨p, -, hpq⟩
      have h1 : f p ∉ q.asIdeal := fun h => hpq (q.asIdeal.mul_mem_right _ h)
      have h2 : g p ∉ q.asIdeal := fun h => hpq (q.asIdeal.mul_mem_left _ h)
      exact (hfg p q h1).2 h2
  rw [heq]
  exact t.isCompact_biUnion fun p _ => isCompact_basicOpen _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickFibIsPullback
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.SpecialConn

variable {O : Type} [CommRing O] [IsLocalRing O] {Y : Scheme.{0}} (f : Y ⟶ Spec (.of O))

abbrev thickQ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    O →+* O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1) :=
  Ideal.Quotient.mk _

def thickR (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1 + 1) →+* O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

theorem thickR_comp (n : ℕ) : (thickR O n).comp (thickQ O (n + 1)) = thickQ O n := rfl

def thickFib (n : ℕ) : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (thickQ O n)))

def thickι (n : ℕ) : thickFib f n ⟶ Y := pullback.fst _ _

def thickTr (n : ℕ) : thickFib f n ⟶ thickFib f (n + 1) :=
  pullback.map _ _ _ _ (𝟙 Y) (Spec.map (CommRingCat.ofHom (thickR O n))) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, thickR_comp])

theorem thickTr_ι (n : ℕ) : thickTr f n ≫ thickι f (n + 1) = thickι f n :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

end GlobalTheory.SpecialConn
end
end

