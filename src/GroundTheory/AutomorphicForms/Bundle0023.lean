module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0021
public import GroundTheory.AutomorphicForms.Bundle0018

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.AnisotropicHeight
section
set_option maxSynthPendingDepth 1

open NumberField IsDedekindDomain Topology Set Matrix Filter
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

section Local

variable {F : Type*} [NormedField F] {N m d : ℕ}

theorem norm_le_mul_pow_of_homogeneous (hd : 0 < d) (Φ : (Fin N → F) → Fin m → F)
    (hΦ : ∀ (t : F) y, Φ (t • y) = t ^ d • Φ y) {B : ℝ} (hB : ∀ y, ‖y‖ ≤ 1 → ‖Φ y‖ ≤ B)
    (y : Fin N → F) : ‖Φ y‖ ≤ B * ‖y‖ ^ d := by
  by_cases hy : y = 0
  · have h0 : Φ 0 = 0 := by
      have := hΦ 0 0
      rwa [zero_smul, zero_pow hd.ne', zero_smul] at this
    rw [hy, h0, norm_zero, norm_zero, zero_pow hd.ne', mul_zero]
  · obtain ⟨j, -⟩ := Function.ne_iff.1 hy
    have : Nonempty (Fin N) := ⟨j⟩
    obtain ⟨i, hi⟩ := Finite.exists_max fun i => ‖y i‖
    have hyi : ‖y‖ = ‖y i‖ :=
      le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hi) (norm_le_pi_norm y i)
    have ht : y i ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hyi
      exact hy (norm_eq_zero.1 hyi)
    have hy' : ‖(y i)⁻¹ • y‖ ≤ 1 := by
      rw [norm_smul, norm_inv, hyi, inv_mul_cancel₀ (norm_ne_zero_iff.2 ht)]
    have hyy : y = y i • ((y i)⁻¹ • y) := by rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
    calc ‖Φ y‖ = ‖y i‖ ^ d * ‖Φ ((y i)⁻¹ • y)‖ := by
          conv_lhs => rw [hyy]
          rw [hΦ, norm_smul, norm_pow]
      _ ≤ ‖y i‖ ^ d * B := mul_le_mul_of_nonneg_left (hB _ hy') (pow_nonneg (norm_nonneg _) _)
      _ = B * ‖y‖ ^ d := by rw [hyi, mul_comm]

variable {K : Type*} [Field K] [Algebra K F]

theorem norm_aeval_le_sum (p : MvPolynomial (Fin N) K) (y : Fin N → F) (hy : ‖y‖ ≤ 1) :
    ‖MvPolynomial.aeval y p‖ ≤ ∑ s ∈ p.support, ‖algebraMap K F (p.coeff s)‖ := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm y i).trans hy)

theorem norm_aeval_le_one [IsUltrametricDist F] (p : MvPolynomial (Fin N) K)
    (hp : ∀ s ∈ p.support, ‖algebraMap K F (p.coeff s)‖ ≤ 1) (y : Fin N → F) (hy : ‖y‖ ≤ 1) :
    ‖MvPolynomial.aeval y p‖ ≤ 1 := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s hs => ?_
  rw [norm_mul, norm_prod]
  exact mul_le_one₀ (hp s hs) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm y i).trans hy))

end Local

variable {K : Type*} [Field K] [NumberField K] {N m d : ℕ}

theorem exists_adelicNorm_le_mul_pow (hd : 0 < d) (Φ : (Fin N → 𝔸[K]) → Fin m → 𝔸[K])
    (Φv : ∀ v : HeightOneSpectrum (𝓞 K), (Fin N → v.adicCompletion K) → Fin m → v.adicCompletion K)
    (Φw : ∀ w : InfinitePlace K, (Fin N → w.Completion) → Fin m → w.Completion)
    (hv : ∀ v y, Reduction.finComp v (Φ y) = Φv v (Reduction.finComp v y))
    (hw : ∀ w y, Reduction.infComp w (Φ y) = Φw w (Reduction.infComp w y))
    (hvh : ∀ v (t : v.adicCompletion K) y, Φv v (t • y) = t ^ d • Φv v y)
    (hwh : ∀ w (t : w.Completion) y, Φw w (t • y) = t ^ d • Φw w y)
    (hvB : ∀ v, ∃ B : ℝ, ∀ y, ‖y‖ ≤ 1 → ‖Φv v y‖ ≤ B)
    (hv1 : ∀ᶠ v in cofinite, ∀ y, ‖y‖ ≤ 1 → ‖Φv v y‖ ≤ 1)
    (hwB : ∀ w, ∃ B : ℝ, ∀ y, ‖y‖ ≤ 1 → ‖Φw w y‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ y, Reduction.HasFiniteContent y → Reduction.HasFiniteContent (Φ y) →
      Reduction.adelicNorm (Φ y) ≤ C * Reduction.adelicNorm y ^ d := by
  classical
  choose Bv hBv using hvB
  choose Bw hBw using hwB
  set S := (Filter.eventually_cofinite.1 hv1).toFinset with hS
  let Bf : HeightOneSpectrum (𝓞 K) → ℝ := fun v => if v ∈ S then max 1 (Bv v) else 1
  have hBf1 : ∀ v, 1 ≤ Bf v := fun v => by
    simp only [Bf]
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  have hBf : ∀ v y, ‖y‖ ≤ 1 → ‖Φv v y‖ ≤ Bf v := by
    intro v y hy
    simp only [Bf]
    split_ifs with h
    · exact (hBv v y hy).trans (le_max_right _ _)
    · have : v ∉ {v | ¬∀ y, ‖y‖ ≤ 1 → ‖Φv v y‖ ≤ 1} := by
        rwa [hS, Set.Finite.mem_toFinset] at h
      simp only [Set.mem_ofPred_eq, not_not] at this
      exact this y hy
  let cw : InfinitePlace K → ℝ := fun w => max 1 √(m : ℝ) * max 1 (Bw w)
  have hcw1 : ∀ w, 1 ≤ cw w := fun w =>
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
  have hloc_w : ∀ w (z : Fin N → w.Completion),
      Reduction.euclidNorm (Φw w z) ≤ cw w * Reduction.euclidNorm z ^ d := by
    intro w z
    have h1 := norm_le_mul_pow_of_homogeneous hd (Φw w) (hwh w) (B := max 1 (Bw w))
      (fun y hy => (hBw w y hy).trans (le_max_right _ _)) z
    calc Reduction.euclidNorm (Φw w z) ≤ √(m : ℝ) * ‖Φw w z‖ := Reduction.euclidNorm_le_sqrt_mul _
      _ ≤ max 1 √(m : ℝ) * (max 1 (Bw w) * ‖z‖ ^ d) :=
          mul_le_mul (le_max_right _ _) h1 (norm_nonneg _) (by positivity)
      _ ≤ max 1 √(m : ℝ) * (max 1 (Bw w) * Reduction.euclidNorm z ^ d) := by
          gcongr
          exact Reduction.norm_le_euclidNorm_pi z
      _ = cw w * Reduction.euclidNorm z ^ d := by simp only [cw]; ring
  have hloc_v : ∀ v (z : Fin N → v.adicCompletion K), ‖Φv v z‖ ≤ Bf v * ‖z‖ ^ d :=
    fun v z => norm_le_mul_pow_of_homogeneous hd (Φv v) (hvh v) (hBf v) z
  refine ⟨(∏ w, cw w ^ w.mult) * ∏ v ∈ S, Bf v, ?_, ?_⟩
  · exact mul_pos (Finset.prod_pos fun w _ => pow_pos (zero_lt_one.trans_le (hcw1 w)) _)
      (Finset.prod_pos fun v _ => zero_lt_one.trans_le (hBf1 v))
  intro y hy hΦy
  set T := S ∪ hy.finite_mulSupport.toFinset ∪ hΦy.finite_mulSupport.toFinset with hT
  have hfinΦ : ∏ᶠ v, ‖Reduction.finComp v (Φ y)‖ = ∏ v ∈ T, ‖Reduction.finComp v (Φ y)‖ :=
    finprod_eq_prod_of_mulSupport_subset _ (by
      intro v hv'
      simp only [hT, Finset.coe_union, Set.Finite.coe_toFinset]
      exact Or.inr hv')
  have hfiny : ∏ᶠ v, ‖Reduction.finComp v y‖ = ∏ v ∈ T, ‖Reduction.finComp v y‖ :=
    finprod_eq_prod_of_mulSupport_subset _ (by
      intro v hv'
      simp only [hT, Finset.coe_union, Set.Finite.coe_toFinset]
      exact Or.inl (Or.inr hv'))
  have hST : ∏ v ∈ T, Bf v = ∏ v ∈ S, Bf v := by
    refine (Finset.prod_subset (fun v hv' => ?_) fun v _ hvS => ?_).symm
    · rw [hT, Finset.mem_union, Finset.mem_union]
      exact Or.inl (Or.inl hv')
    · simp only [Bf, if_neg hvS]
  have hfin_le : ∏ᶠ v, ‖Reduction.finComp v (Φ y)‖ ≤
      (∏ v ∈ S, Bf v) * (∏ᶠ v, ‖Reduction.finComp v y‖) ^ d := by
    rw [hfinΦ, hfiny, ← hST, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => ?_
    rw [hv]
    exact hloc_v v _
  have hinf_le : ∏ w, Reduction.euclidNorm (Reduction.infComp w (Φ y)) ^ w.mult ≤
      (∏ w, cw w ^ w.mult) * (∏ w, Reduction.euclidNorm (Reduction.infComp w y) ^ w.mult) ^ d := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun w _ => pow_nonneg (Reduction.euclidNorm_nonneg _) _)
      fun w _ => ?_
    rw [hw]
    calc Reduction.euclidNorm (Φw w (Reduction.infComp w y)) ^ w.mult
        ≤ (cw w * Reduction.euclidNorm (Reduction.infComp w y) ^ d) ^ w.mult :=
          pow_le_pow_left₀ (Reduction.euclidNorm_nonneg _) (hloc_w w _) _
      _ = cw w ^ w.mult * (Reduction.euclidNorm (Reduction.infComp w y) ^ w.mult) ^ d := by ring
  unfold Reduction.adelicNorm
  calc _ ≤ ((∏ w, cw w ^ w.mult) *
          (∏ w, Reduction.euclidNorm (Reduction.infComp w y) ^ w.mult) ^ d) *
        ((∏ v ∈ S, Bf v) * (∏ᶠ v, ‖Reduction.finComp v y‖) ^ d) :=
        mul_le_mul hinf_le hfin_le (finprod_nonneg fun _ => norm_nonneg _)
          (mul_nonneg (Finset.prod_nonneg fun w _ => pow_nonneg (zero_le_one.trans (hcw1 w)) _)
            (pow_nonneg (Finset.prod_nonneg fun w _ =>
              pow_nonneg (Reduction.euclidNorm_nonneg _) _) _))
    _ = _ := by ring

theorem exists_adelicNorm_aeval_le (hd : 0 < d) (P : Fin m → MvPolynomial (Fin N) K)
    (hvh : ∀ (v : HeightOneSpectrum (𝓞 K)) (t : v.adicCompletion K)
      (y : Fin N → v.adicCompletion K) k,
      MvPolynomial.aeval (t • y) (P k) = t ^ d * MvPolynomial.aeval y (P k))
    (hwh : ∀ (w : InfinitePlace K) (t : w.Completion) (y : Fin N → w.Completion) k,
      MvPolynomial.aeval (t • y) (P k) = t ^ d * MvPolynomial.aeval y (P k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : Fin N → 𝔸[K], Reduction.HasFiniteContent y →
      Reduction.HasFiniteContent (fun k => MvPolynomial.aeval y (P k)) →
      Reduction.adelicNorm (fun k => MvPolynomial.aeval y (P k)) ≤
        C * Reduction.adelicNorm y ^ d := by
  refine exists_adelicNorm_le_mul_pow hd _ (fun v y k => MvPolynomial.aeval y (P k))
    (fun w y k => MvPolynomial.aeval y (P k)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro v y
    funext k
    show adeleFiniteEval K v (MvPolynomial.aeval y (P k)) = _
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  · intro w y
    funext k
    show adeleInfiniteEval K w (MvPolynomial.aeval y (P k)) = _
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  · intro v t y
    funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hvh v t y k
  · intro w t y
    funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hwh w t y k
  · intro v
    refine ⟨∑ k, ∑ s ∈ (P k).support, ‖algebraMap K (v.adicCompletion K) ((P k).coeff s)‖,
      fun y hy => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_⟩
    exact (norm_aeval_le_sum (P k) y hy).trans
      (Finset.single_le_sum (f := fun k => ∑ s ∈ (P k).support,
        ‖algebraMap K (v.adicCompletion K) ((P k).coeff s)‖)
        (fun k _ => by positivity) (Finset.mem_univ k))
  · have h : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ k, ∀ s ∈ (P k).support,
        ‖algebraMap K (v.adicCompletion K) ((P k).coeff s)‖ ≤ 1 :=
      Filter.eventually_all.2 fun k => (Filter.eventually_all_finset _).2 fun s _ =>
        Reduction.eventually_norm_le_one _
    filter_upwards [h] with v hv y hy
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => norm_aeval_le_one (P k) (hv k) y hy
  · intro w
    refine ⟨∑ k, ∑ s ∈ (P k).support, ‖algebraMap K w.Completion ((P k).coeff s)‖,
      fun y hy => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_⟩
    exact (norm_aeval_le_sum (P k) y hy).trans
      (Finset.single_le_sum (f := fun k => ∑ s ∈ (P k).support,
        ‖algebraMap K w.Completion ((P k).coeff s)‖)
        (fun k _ => by positivity) (Finset.mem_univ k))

end Anisotropic

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.CuspidalSplittingCoeff
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function
open scoped Pointwise

theorem linearMap_finsum {ι M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module ℂ M]
    [Module ℂ N] (L : M →ₗ[ℂ] N) {φ : ι → M} (h : HasFiniteSupport φ) :
    L (∑ᶠ i, φ i) = ∑ᶠ i, L (φ i) :=
  map_finsum L h

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section CentralChar

variable {U : Type*} [AddCommGroup U] [Module ℂ U]

def HasCentralChar (ρ : Representation ℂ (GL (Fin n) F) U) (ω : GL (Fin n) F → ℂ) : Prop :=
  ∀ z ∈ Subgroup.center (GL (Fin n) F), ∀ u, ρ z u = ω z • u

variable {ρ : Representation ℂ (GL (Fin n) F) U} {ω : GL (Fin n) F → ℂ}


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem HasCentralChar.mul (h : HasCentralChar ρ ω) {u : U} (hu : u ≠ 0)
    {z z' : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F))
    (hz' : z' ∈ Subgroup.center (GL (Fin n) F)) : ω (z * z') = ω z * ω z' := by
  have h1 := h _ (mul_mem hz hz') u
  rw [map_mul, Module.End.mul_apply, h z' hz', map_smul, h z hz, smul_smul] at h1
  exact (smul_left_injective ℂ hu h1).symm.trans (mul_comm _ _)


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem HasCentralChar.one (h : HasCentralChar ρ ω) {u : U} (hu : u ≠ 0) : ω 1 = 1 := by
  have h1 : ω 1 • u = (1 : ℂ) • u := by
    rw [one_smul, ← h 1 (Subgroup.one_mem _) u, map_one, Module.End.one_apply]
  exact smul_left_injective ℂ hu h1


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem HasCentralChar.inv_mul (h : HasCentralChar ρ ω) {u : U} (hu : u ≠ 0)
    {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) : ω z⁻¹ * ω z = 1 := by
  rw [← h.mul hu (inv_mem hz) hz, inv_mul_cancel, h.one hu]

end CentralChar

section CenterSup

abbrev centerSup (K : Subgroup (GL (Fin n) F)) : Subgroup (GL (Fin n) F) :=
  Subgroup.center (GL (Fin n) F) ⊔ K

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_centerSup {K : Subgroup (GL (Fin n) F)} {x : GL (Fin n) F} :
    x ∈ centerSup K ↔ ∃ z ∈ Subgroup.center (GL (Fin n) F), ∃ k ∈ K, z * k = x :=
  Subgroup.mem_sup_of_normal_left


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem rightInv_centerSup {X : Type*} {K : Subgroup (GL (Fin n) F)} {Φ : GL (Fin n) F → X}
    (hZ : ∀ g, ∀ z ∈ Subgroup.center (GL (Fin n) F), Φ (g * z) = Φ g)
    (hK : ∀ g, ∀ k ∈ K, Φ (g * k) = Φ g) : ∀ g, ∀ h ∈ centerSup K, Φ (g * h) = Φ g := by
  intro g h hh
  obtain ⟨z, hz, k, hk, rfl⟩ := mem_centerSup.1 hh
  rw [← mul_assoc, hK _ k hk, hZ g z hz]

theorem isOpen_centerSup {K : Subgroup (GL (Fin n) F)} (hKo : IsOpen (K : Set (GL (Fin n) F))) :
    IsOpen (centerSup K : Set (GL (Fin n) F)) :=
  Subgroup.isOpen_mono le_sup_right hKo

theorem finite_support_centerSup {M : Type*} [AddCommMonoid M] {K : Subgroup (GL (Fin n) F)}
    (hKo : IsOpen (K : Set (GL (Fin n) F))) {Φ : GL (Fin n) F → M} {φ : GL (Fin n) F → ℂ}
    (hφ : IsCompactModCenter φ) (h : ∀ g, φ g = 0 → Φ g = 0) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K => Φ q.out := by
  obtain ⟨C, hC, hsupp⟩ := hφ
  exact finite_support_quotSum (isOpen_centerSup hKo) le_sup_left hC
    (fun g hg => hsupp (mt (h g) hg))

end CenterSup

section CoeffSum

variable {V U W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GL (Fin n) F) V) (ρ : Representation ℂ (GL (Fin n) F) U)

def coeffSum (K : Subgroup (GL (Fin n) F)) (f : Module.Dual ℂ V) (u : U) (w : V) : U :=
  quotSum (centerSup K) fun g => f (π g⁻¹ w) • ρ g u

variable {π ρ} {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V} {u : U}
  {ω : GL (Fin n) F → ℂ}


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coeffSum_summand_rightInv (hωπ : HasCentralChar π ω) (hωρ : HasCentralChar ρ ω)
    (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (hu : u ∈ fixedVectors ρ K) (w : V) :
    ∀ g, ∀ h ∈ centerSup K, f (π (g * h)⁻¹ w) • ρ (g * h) u = f (π g⁻¹ w) • ρ g u := by
  refine rightInv_centerSup (Φ := fun g => f (π g⁻¹ w) • ρ g u) (fun g z hz => ?_)
    (fun g k hk => ?_)
  · have e1 : π (g * z)⁻¹ w = ω z⁻¹ • π g⁻¹ w := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply, hωπ _ (inv_mem hz)]
    have e2 : ρ (g * z) u = ω z • ρ g u := by
      rw [map_mul, Module.End.mul_apply, hωρ z hz, map_smul]
    rw [e1, e2, map_smul, smul_eq_mul, smul_smul]
    congr 1
    linear_combination f (π g⁻¹ w) * hω z hz
  · have e1 : π (g * k)⁻¹ w = π k⁻¹ (π g⁻¹ w) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply]
    rw [e1, hf _ (inv_mem hk), map_mul, Module.End.mul_apply, hu k hk]

theorem mem_smoothVectors_dual_of_inv (hKo : IsOpen (K : Set (GL (Fin n) F)))
    (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) : f ∈ smoothVectors (Representation.dual π) :=
  mem_smoothVectors_of_mem_fixedVectors hKo (mem_fixedVectors_dual.2 hf)

theorem finite_support_coeffSum (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (w : V) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K => f (π q.out⁻¹ w) • ρ q.out u :=
  finite_support_centerSup (Φ := fun g => f (π g⁻¹ w) • ρ g u) hKo
    (isCompactModCenter_matrixCoeff hπ hsc w (mem_smoothVectors_dual_of_inv hKo hf)).comp_inv
    fun g h0 => by
      change f (π g⁻¹ w) = 0 at h0
      simp only [h0, zero_smul]

variable (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hKo : IsOpen (K : Set (GL (Fin n) F)))
  (hωπ : HasCentralChar π ω) (hωρ : HasCentralChar ρ ω)
  (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
  (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (hu : u ∈ fixedVectors ρ K)

include hπ hsc hKo hf in
theorem coeffSum_add (w₁ w₂ : V) :
    coeffSum π ρ K f u (w₁ + w₂) = coeffSum π ρ K f u w₁ + coeffSum π ρ K f u w₂ := by
  unfold coeffSum quotSum
  rw [← finsum_add_distrib (finite_support_coeffSum hπ hsc hKo hf w₁)
    (finite_support_coeffSum hπ hsc hKo hf w₂)]
  refine finsum_congr fun q => ?_
  dsimp only
  rw [map_add (f := _), map_add (f := _), add_smul]

include hπ hsc hKo hf in
theorem coeffSum_smul (c : ℂ) (w : V) :
    coeffSum π ρ K f u (c • w) = c • coeffSum π ρ K f u w := by
  unfold coeffSum quotSum
  rw [smul_finsum' c (finite_support_coeffSum hπ hsc hKo hf w)]
  refine finsum_congr fun q => ?_
  dsimp only
  rw [map_smul, map_smul, smul_eq_mul, mul_smul]


include hπ hsc hKo hωπ hωρ hω hf hu in
theorem coeffSum_act (x : GL (Fin n) F) (w : V) :
    coeffSum π ρ K f u (π x w) = ρ x (coeffSum π ρ K f u w) := by
  have hΨ := coeffSum_summand_rightInv hωπ hωρ hω hf hu w
  have hΨ' : ∀ g, ∀ h ∈ centerSup K, ρ x (f (π (g * h)⁻¹ w) • ρ (g * h) u) =
      ρ x (f (π g⁻¹ w) • ρ g u) := fun g h hh => by rw [hΨ g h hh]
  calc coeffSum π ρ K f u (π x w)
      = quotSum (centerSup K) fun g => ρ x (f (π (x⁻¹ * g)⁻¹ w) • ρ (x⁻¹ * g) u) := by
        refine quotSum_congr fun g => ?_
        have h1 : (x⁻¹ * g)⁻¹ = g⁻¹ * x := by group
        rw [map_smul, h1, map_mul π g⁻¹ x, Module.End.mul_apply, ← Module.End.mul_apply (ρ x),
          ← map_mul ρ, mul_inv_cancel_left]
    _ = quotSum (centerSup K) fun g => ρ x (f (π g⁻¹ w) • ρ g u) :=
        quotSum_mul_left (Φ := fun g => ρ x (f (π g⁻¹ w) • ρ g u)) hΨ' x⁻¹
    _ = ρ x (coeffSum π ρ K f u w) :=
        (linearMap_finsum (ρ x) (finite_support_coeffSum hπ hsc hKo hf w)).symm

def coeffMap : Representation.IntertwiningMap π ρ where
  toFun := coeffSum π ρ K f u
  map_add' := coeffSum_add hπ hsc hKo hf
  map_smul' := coeffSum_smul hπ hsc hKo hf
  isIntertwining' x := LinearMap.ext fun w => coeffSum_act hπ hsc hKo hωπ hωρ hω hf hu x w

theorem coeffMap_apply (w : V) :
    coeffMap hπ hsc hKo hωπ hωρ hω hf hu w = coeffSum π ρ K f u w := rfl


omit hωπ hωρ hω hu in
include hπ hsc hKo hf in
theorem map_coeffSum {σ : Representation ℂ (GL (Fin n) F) W}
    (p : Representation.IntertwiningMap ρ σ) (w : V) :
    p (coeffSum π ρ K f u w) = coeffSum π σ K f (p u) w := by
  unfold coeffSum quotSum
  rw [← Representation.IntertwiningMap.toLinearMap_apply,
    linearMap_finsum _ (finite_support_coeffSum hπ hsc hKo hf w)]
  refine finsum_congr fun q => ?_
  rw [Representation.IntertwiningMap.toLinearMap_apply, map_smul,
    Representation.IntertwiningMap.isIntertwining]

end CoeffSum

section Scalar

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V} {v : V} {ω : GL (Fin n) F → ℂ}

theorem exists_coeffSum_eq_smul [π.IsIrreducible] (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hωπ : HasCentralChar π ω)
    (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (hv : v ∈ fixedVectors π K) :
    ∃ c : ℂ, ∀ w, coeffSum π π K f v w = c • w := by
  obtain ⟨u₀, hu₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  obtain ⟨c, hc⟩ := (algebraMap_intertwiningMap_bijective_of_isSmooth hπ).2
    (coeffMap hπ hsc hKo hωπ hωπ (fun z hz => hωπ.inv_mul hu₀ hz) hf hv)
  refine ⟨c, fun w => ?_⟩
  have := congrArg (fun φ : Representation.IntertwiningMap π π => φ w) hc
  simpa [coeffMap_apply] using this.symm

end Scalar

end Parabolic

end GroundTheory.Automorphic
end
end

