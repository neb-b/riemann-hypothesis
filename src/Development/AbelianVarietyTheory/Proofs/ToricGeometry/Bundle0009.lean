module

public import Mathlib
public import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
public import ReciprocityTheory.ThetaQuasiPeriods.Transl
public import ReciprocityTheory.ThetaQuasiPeriods.Change
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsConnectedUnramifiedCoverOfIrreducible
section
open Filter Topology

namespace GlobalTheory.SimpleRoots

open Polynomial

variable {d : ℕ}


open Classical in
noncomputable def partialProd (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (u : Set ((Fin d → ℂ) × ℂ)) (x : Fin d → ℂ) : ℂ[X] := by
  classical
  exact (((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u).map
    fun y => X - C y).prod

theorem card_roots_map {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic) (x : Fin d → ℂ) :
    (p.map (MvPolynomial.eval x)).roots.card = p.natDegree := by
  rw [IsAlgClosed.card_roots_eq_natDegree, hp.natDegree_map]

theorem natDegree_partialProd_le {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    (u : Set ((Fin d → ℂ) × ℂ)) (x : Fin d → ℂ) : (partialProd p u x).natDegree ≤ p.natDegree := by
  classical
  unfold partialProd
  rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, ← card_roots_map hp x]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

theorem partialProd_mul_compl {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    (u : Set ((Fin d → ℂ) × ℂ)) (x : Fin d → ℂ) :
    partialProd p u x * partialProd p uᶜ x = p.map (MvPolynomial.eval x) := by
  classical
  unfold partialProd
  rw [← Multiset.prod_add, ← Multiset.map_add (f := _)]
  convert Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp.map (MvPolynomial.eval x))
    (by rw [card_roots_map hp x, hp.natDegree_map]) using 3
  convert Multiset.filter_add_not (fun y => (x, y) ∈ u) (p.map (MvPolynomial.eval x)).roots using 2
  congr 1

theorem exists_norm_coeff_partialProd_le {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    (u : Set ((Fin d → ℂ) × ℂ)) :
    ∃ (C : ℝ) (m : ℕ), ∀ k x, ‖(partialProd p u x).coeff k‖ ≤ C * (1 + ‖x‖) ^ m := by
  classical
  obtain ⟨C₀, m₀, hC₀, hroot⟩ := exists_norm_root_le hp
  refine ⟨(1 + C₀) ^ p.natDegree, m₀ * p.natDegree, fun k x => ?_⟩
  set R := C₀ * (1 + ‖x‖) ^ m₀ with hR
  have ht : 1 ≤ (1 + ‖x‖) ^ m₀ := one_le_pow₀ (by linarith [norm_nonneg x])
  have hR0 : 0 ≤ R := mul_nonneg hC₀ (by linarith)
  have hbound := norm_coeff_prod_le
    ((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u) hR0
    (fun y hy => hroot x y ((Polynomial.mem_roots (hp.map _).ne_zero).mp
      (Multiset.mem_of_mem_filter hy))) k
  have hcard : Multiset.card ((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u) ≤
      p.natDegree := by
    rw [← card_roots_map hp x]
    exact Multiset.card_le_card (Multiset.filter_le _ _)
  have h1R : 1 + R ≤ (1 + C₀) * (1 + ‖x‖) ^ m₀ := by
    rw [hR]; nlinarith
  calc ‖(partialProd p u x).coeff k‖ ≤ (1 + R) ^ Multiset.card
          ((p.map (MvPolynomial.eval x)).roots.filter fun y => (x, y) ∈ u) := hbound
    _ ≤ (1 + R) ^ p.natDegree := pow_le_pow_right₀ (by linarith) hcard
    _ ≤ ((1 + C₀) * (1 + ‖x‖) ^ m₀) ^ p.natDegree := pow_le_pow_left₀ (by linarith) h1R _
    _ = (1 + C₀) ^ p.natDegree * (1 + ‖x‖) ^ (m₀ * p.natDegree) := by rw [mul_pow, ← pow_mul]

theorem differentiableAt_coeff_partialProd {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    {u : Set ((Fin d → ℂ) × ℂ)} {x₀ : Fin d → ℂ}
    (h : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 →
      (p.map (MvPolynomial.eval x₀)).derivative.eval y ≠ 0)
    (hu : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 → ∀ᶠ w in 𝓝 (x₀, y),
      (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 → (w ∈ u ↔ (x₀, y) ∈ u)) (k : ℕ) :
    DifferentiableAt ℂ (fun x => (partialProd p u x).coeff k) x₀ := by
  classical
  obtain ⟨ψ, hψ, hroots⟩ := exists_analytic_roots hp h
  set R₀ := (p.map (MvPolynomial.eval x₀)).roots with hR₀
  have hψc : ∀ y ∈ R₀, ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ y x) = 0 →
      ((x, ψ y x) ∈ u ↔ (x₀, y) ∈ u) := by
    intro y hy
    have hy0 : (p.map (MvPolynomial.eval x₀)).eval y = 0 :=
      (Polynomial.mem_roots (hp.map _).ne_zero).mp hy
    have ht : Tendsto (fun x => (x, ψ y x)) (𝓝 x₀) (𝓝 (x₀, y)) := by
      have := (continuousAt_id.prodMk (hψ y hy).1.continuousAt).tendsto
      simpa [(hψ y hy).2] using this
    exact ht.eventually (hu y hy0)
  have hall : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ R₀.toFinset,
      (p.map (MvPolynomial.eval x)).eval (ψ y x) = 0 → ((x, ψ y x) ∈ u ↔ (x₀, y) ∈ u) :=
    (Filter.eventually_all_finset _).mpr fun y hy => hψc y (Multiset.mem_toFinset.mp hy)
  have heq : (fun x => (partialProd p u x).coeff k) =ᶠ[𝓝 x₀]
      fun x => ((R₀.filter fun y => (x₀, y) ∈ u).map fun y => X - C (ψ y x)).prod.coeff k := by
    filter_upwards [hroots, hall] with x hx hxa
    have hfilter : (R₀.filter fun y => (x, ψ y x) ∈ u) =
        (R₀.filter fun y => (x₀, y) ∈ u) := by
      refine Multiset.filter_congr fun y hy => ?_
      refine hxa y (Multiset.mem_toFinset.mpr hy) ?_
      have hmem : ψ y x ∈ (p.map (MvPolynomial.eval x)).roots := by
        rw [hx]; exact Multiset.mem_map_of_mem _ hy
      exact (Polynomial.mem_roots (hp.map _).ne_zero).mp hmem
    simp only [partialProd, hx, Multiset.filter_map, Multiset.map_map, Function.comp_def, hfilter]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  exact differentiableAt_coeff_prod _ ψ
    (fun y hy => (hψ y (Multiset.mem_of_mem_filter hy)).1.differentiableAt) k

theorem eq_of_map_eval_eq_of_dense {a b : Polynomial (MvPolynomial (Fin d) ℂ)}
    {U : Set (Fin d → ℂ)} (hU : Dense U)
    (h : ∀ x ∈ U, a.map (MvPolynomial.eval x) = b.map (MvPolynomial.eval x)) : a = b := by
  ext i
  have hfun : (fun x => MvPolynomial.eval x (a.coeff i)) = fun x => MvPolynomial.eval x (b.coeff i) := by
    refine Continuous.ext_on hU (MvPolynomial.continuous_eval _) (MvPolynomial.continuous_eval _) ?_
    intro x hx
    have := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P i) (h x hx)
    simpa [Polynomial.coeff_map] using this
  exact congrArg (fun c => AddMonoidAlgebra.coeff c _) (MvPolynomial.funext fun x => congrFun hfun x)

end GlobalTheory.SimpleRoots

namespace GlobalTheory

open SimpleRoots

theorem isConnected_unramified_cover_of_irreducible :
    (∀ (d : ℕ) (q : MvPolynomial (Fin d) ℂ), q ≠ 0 →
      IsConnected {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} ∧
        Dense {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0}) →
    (∀ (d m : ℕ) (q : MvPolynomial (Fin d) ℂ) (f : (Fin d → ℂ) → ℂ) (C : ℝ), q ≠ 0 →
      DifferentiableOn ℂ f {x | MvPolynomial.eval x q ≠ 0} →
      (∀ x, MvPolynomial.eval x q ≠ 0 → ‖f x‖ ≤ C * (1 + ‖x‖) ^ m) →
      ∃ p : MvPolynomial (Fin d) ℂ, ∀ x, MvPolynomial.eval x q ≠ 0 → f x = MvPolynomial.eval x p) →
    (∀ (d : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ),
      p.Monic → Irreducible p → q ≠ 0 →
      (∀ x y, MvPolynomial.eval x q ≠ 0 → (p.map (MvPolynomial.eval x)).eval y = 0 →
        (p.map (MvPolynomial.eval x)).derivative.eval y ≠ 0) →
      IsConnected {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧
        (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}) := by
  intro H1 H2 d p q hp hirr hq hsimp
  obtain ⟨hΩc, hΩd⟩ := H1 d q hq
  have hΩo : IsOpen {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const
  have hdeg : p.natDegree ≠ 0 := by
    intro h0
    exact hirr.not_isUnit (by rw [hp.natDegree_eq_zero.mp h0]; exact isUnit_one)
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hΩc.nonempty
    obtain ⟨y, hy⟩ := Multiset.card_pos_iff_exists_mem.mp
      (by rw [card_roots_map hp x]; omega : 0 < Multiset.card (p.map (MvPolynomial.eval x)).roots)
    exact ⟨(x, y), hx, (Polynomial.mem_roots (hp.map _).ne_zero).mp hy⟩
  intro u v hu hv hZ hZu hZv
  by_contra hne
  have hdisj : ∀ z : (Fin d → ℂ) × ℂ, MvPolynomial.eval z.1 q ≠ 0 →
      (p.map (MvPolynomial.eval z.1)).eval z.2 = 0 → z ∈ u → z ∉ v :=
    fun z hzq hz0 hzu hzv => hne ⟨z, ⟨hzq, hz0⟩, hzu, hzv⟩
  have hloc : ∀ x₀, MvPolynomial.eval x₀ q ≠ 0 → ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 →
      ∀ᶠ w in 𝓝 (x₀, y), (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 → (w ∈ u ↔ (x₀, y) ∈ u) := by
    intro x₀ hx₀ y hy
    by_cases hyu : (x₀, y) ∈ u
    · filter_upwards [hu.mem_nhds hyu] with w hw _ using iff_of_true hw hyu
    · have hyv : (x₀, y) ∈ v := (@hZ (x₀, y) ⟨hx₀, hy⟩).resolve_left hyu
      filter_upwards [hv.mem_nhds hyv,
        continuous_fst.continuousAt.preimage_mem_nhds (hΩo.mem_nhds hx₀)] with w hwv hwq hw0
      exact iff_of_false (fun hwu => hdisj w hwq hw0 hwu hwv) hyu
  have hpoly : ∀ s : Set ((Fin d → ℂ) × ℂ), (∀ x₀, MvPolynomial.eval x₀ q ≠ 0 → ∀ y,
      (p.map (MvPolynomial.eval x₀)).eval y = 0 → ∀ᶠ w in 𝓝 (x₀, y),
        (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 → (w ∈ s ↔ (x₀, y) ∈ s)) →
      ∃ A : Polynomial (MvPolynomial (Fin d) ℂ), ∀ x, MvPolynomial.eval x q ≠ 0 →
        A.map (MvPolynomial.eval x) = partialProd p s x := by
    intro s hs
    obtain ⟨C₁, m, hC₁⟩ := exists_norm_coeff_partialProd_le hp s
    have hk : ∀ k, ∃ a : MvPolynomial (Fin d) ℂ, ∀ x, MvPolynomial.eval x q ≠ 0 →
        (partialProd p s x).coeff k = MvPolynomial.eval x a := fun k =>
      H2 d m q (fun x => (partialProd p s x).coeff k) C₁ hq
        (fun x hx => (differentiableAt_coeff_partialProd hp (fun y hy => hsimp x y hx hy)
          (hs x hx) k).differentiableWithinAt)
        (fun x _ => hC₁ k x)
    choose a ha using hk
    refine ⟨∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.monomial k (a k), fun x hx => ?_⟩
    ext k
    rw [Polynomial.coeff_map, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial_apply, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hk'
    · exact (ha k x hx).symm
    · have := natDegree_partialProd_le hp s x
      rw [map_zero]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
  obtain ⟨A, hA⟩ := hpoly u hloc
  obtain ⟨B, hB⟩ := hpoly uᶜ fun x₀ hx₀ y hy =>
    (hloc x₀ hx₀ y hy).mono fun w hw h0 => not_congr (hw h0)
  have hAB : A * B = p := eq_of_map_eval_eq_of_dense hΩd fun x hx => by
    rw [Polynomial.map_mul, hA x hx, hB x hx, partialProd_mul_compl hp]
  have hnot : ∀ (s : Set ((Fin d → ℂ) × ℂ)) (A' : Polynomial (MvPolynomial (Fin d) ℂ)),
      (∀ x, MvPolynomial.eval x q ≠ 0 → A'.map (MvPolynomial.eval x) = partialProd p s x) →
      ∀ z : (Fin d → ℂ) × ℂ, MvPolynomial.eval z.1 q ≠ 0 →
        (p.map (MvPolynomial.eval z.1)).eval z.2 = 0 → z ∈ s → ¬ IsUnit A' := by
    intro s A' hA' z hzq hz0 hzs hunit
    classical
    have hu' : IsUnit (A'.map (MvPolynomial.eval z.1)) :=
      hunit.map (Polynomial.mapRingHom (MvPolynomial.eval z.1))
    rw [hA' z.1 hzq] at hu'
    have h2 := Polynomial.natDegree_eq_zero_of_isUnit hu'
    unfold partialProd at h2
    rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_eq_zero] at h2
    exact Multiset.filter_eq_nil.mp h2 z.2 ((Polynomial.mem_roots (hp.map _).ne_zero).mpr hz0) hzs
  obtain ⟨z, ⟨hzq, hz0⟩, hzu⟩ := hZu
  obtain ⟨z', ⟨hzq', hz0'⟩, hzv'⟩ := hZv
  rcases hirr.isUnit_or_isUnit hAB.symm with h | h
  · exact hnot u A hA z hzq hz0 hzu h
  · exact hnot uᶜ B hB z' hzq' hz0' (fun hzu' => hdisj z' hzq' hz0' hzu' hzv') h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.LevelThreeSeparatesPoints
section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ThetaSeparation


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
theorem _root_.GlobalTheory.ThetaSeparation.dense_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {f : E → ℂ} (hf : Differentiable ℂ f) (h0 : ∃ x, f x ≠ 0) :
    Dense {x | f x ≠ 0} := by
  by_contra hd
  obtain ⟨x₀, hx₀⟩ := h0
  rw [dense_iff_inter_open] at hd
  simp only [not_forall] at hd
  obtain ⟨U, hUo, hUne, hU⟩ := hd
  have hEq : Set.EqOn f (fun _ => (0 : ℂ)) Set.univ :=
    _root_.GlobalTheory.SCV.eqOn_of_eqOn_open (g := fun _ => (0 : ℂ)) isOpen_univ isPreconnected_univ
      hf.differentiableOn (differentiableOn_const 0) hUo hUne (Set.subset_univ _)
      (fun y hy => by
        by_contra hne
        exact hU ⟨y, hy, hne⟩)
  exact hx₀ (hEq (Set.mem_univ x₀))

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
private lemma eC_pow_eq_eC_natCast_mul (m : ℕ) (X : ℂ) : _root_.ReciprocityTheory.PTheta.eC X ^ m = _root_.ReciprocityTheory.PTheta.eC ((m : ℂ) * X) := by
  induction m with
  | zero => simp [_root_.ReciprocityTheory.PTheta.eC_zero]
  | succ m ih =>
    rw [pow_succ, ih, ← _root_.ReciprocityTheory.PTheta.eC_add]
    congr 1
    push_cast
    ring

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
private lemma exists_common_ne_zero_of_differentiable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {f₁ f₂ : E → ℂ} (h₁ : Differentiable ℂ f₁)
    (h₂ : Differentiable ℂ f₂) (e₁ : ∃ x, f₁ x ≠ 0) (e₂ : ∃ x, f₂ x ≠ 0) :
    ∃ x, f₁ x ≠ 0 ∧ f₂ x ≠ 0 := by
  have d₁ := _root_.GlobalTheory.ThetaSeparation.dense_ne_zero h₁ e₁
  have d₂ := _root_.GlobalTheory.ThetaSeparation.dense_ne_zero h₂ e₂
  have o₁ : IsOpen {x | f₁ x ≠ 0} := isOpen_ne_fun h₁.continuous continuous_const
  obtain ⟨x, hx₁, hx₂⟩ := (d₁.inter_of_isOpen_left d₂ o₁).nonempty
  exact ⟨x, hx₁, hx₂⟩

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
private lemma exists_multiplier_of_level_sections_lemma {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    {t : (Fin g → ℂ) → ℂ} (ht : Differentiable ℂ t)
    (hq : ∀ (n n' : Fin g → ℤ) x, t (x + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') =
      _root_.ReciprocityTheory.PTheta.eC (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ x)) * t x)
    (hne : ∃ x, t x ≠ 0) {N : ℕ} (hN : 3 ≤ N) {z z' : Fin g → ℂ} {γ : ℂ}
    (hf : ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) x,
      f (x + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') =
        _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ x)) * f x) →
      f z = γ * f z') :
    ∃ h : (Fin g → ℂ) → ℂ, Differentiable ℂ h ∧ (∀ x, h x ≠ 0) ∧
      ∀ x, t (x + (z - z')) = h x * t x := by
  have hk : ((N - 3 : ℕ) : ℂ) = (N : ℂ) - 3 := by
    rw [Nat.cast_sub hN]
    norm_num
  obtain ⟨x₀, hx₀⟩ := hne
  have shiftA : ∀ u, ∃ b, t (u + b) ≠ 0 := fun u => ⟨x₀ - u, by rwa [add_sub_cancel]⟩
  have shiftB : ∀ u v, ∃ b, t (u + -(v + b)) ≠ 0 := fun u v =>
    ⟨u - x₀ - v, by convert hx₀ using 2; abel⟩
  have hdA : ∀ u, Differentiable ℂ (fun b => t (u + b)) := fun u => by fun_prop
  have hdB : ∀ u v, Differentiable ℂ (fun b => t (u + -(v + b))) := fun u v => by fun_prop
  have hF : ∀ a b d, t (z + a) * t (z + b) * t (z + -(((N - 3 : ℕ) : ℂ) • d + a + b)) *
      t (z + d) ^ (N - 3) = γ * (t (z' + a) * t (z' + b) *
        t (z' + -(((N - 3 : ℕ) : ℂ) • d + a + b)) * t (z' + d) ^ (N - 3)) := by
    intro a b d
    refine hf (fun y => t (y + a) * t (y + b) * t (y + -(((N - 3 : ℕ) : ℂ) • d + a + b)) *
      t (y + d) ^ (N - 3)) ⟨by fun_prop, ?_⟩
    intro n n' y
    have key : ∀ s, t (y + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n' + s) =
        _root_.ReciprocityTheory.PTheta.eC (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (y + s))) *
          t (y + s) := by
      intro s
      rw [← hq n n' (y + s)]
      congr 1
      abel
    simp only [key, mul_pow, eC_pow_eq_eC_natCast_mul]
    have harg : -(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (y + a)) +
        -(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (y + b)) +
        -(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 +
          _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (y + -(((N - 3 : ℕ) : ℂ) • d + a + b))) +
        ((N - 3 : ℕ) : ℂ) * (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 +
          _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (y + d))) =
        -(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ y) := by
      simp only [dotProduct_add, dotProduct_neg, dotProduct_smul, smul_eq_mul]
      rw [hk]
      ring
    rw [← harg, _root_.ReciprocityTheory.PTheta.eC_add, _root_.ReciprocityTheory.PTheta.eC_add, _root_.ReciprocityTheory.PTheta.eC_add]
    ring
  obtain ⟨d, hd₁, hd₂⟩ := exists_common_ne_zero_of_differentiable (hdA z) (hdA z') (shiftA z) (shiftA z')
  obtain ⟨a, ha⟩ := shiftA z
  obtain ⟨b, hb₁, hb₂⟩ := exists_common_ne_zero_of_differentiable (hdA z)
    (hdB z (((N - 3 : ℕ) : ℂ) • d + a)) (shiftA z) (shiftB z _)
  have hγ : γ ≠ 0 := by
    intro h0
    have := hF a b d
    rw [h0, zero_mul] at this
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb₁) hb₂) (pow_ne_zero _ hd₁) this
  set Den : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun b x => t (z + b) *
    t (z + -(((N - 3 : ℕ) : ℂ) • d + (x - z') + b)) * t (z + d) ^ (N - 3) with hDen
  set Num : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun b x => γ * (t (z' + b) *
    t (z' + -(((N - 3 : ℕ) : ℂ) • d + (x - z') + b)) * t (z' + d) ^ (N - 3)) with hNum
  have hDenD : ∀ b, Differentiable ℂ (Den b) := by
    intro b
    simp only [hDen]
    fun_prop
  have hNumD : ∀ b, Differentiable ℂ (Num b) := by
    intro b
    simp only [hNum]
    fun_prop
  have hRel : ∀ b x, t (x + (z - z')) * Den b x = t x * Num b x := by
    intro b x
    have h := hF (x - z') b d
    have e₁ : z + (x - z') = x + (z - z') := by abel
    have e₂ : z' + (x - z') = x := by abel
    rw [e₁, e₂] at h
    simp only [hDen, hNum]
    linear_combination h
  have hChoice : ∀ x, ∃ b, Den b x ≠ 0 ∧ Num b x ≠ 0 := by
    intro x
    obtain ⟨b₁, h₁, h₁'⟩ := exists_common_ne_zero_of_differentiable (hdA z) (hdA z') (shiftA z) (shiftA z')
    obtain ⟨b₂, h₂, h₂'⟩ := exists_common_ne_zero_of_differentiable
      (hdB z (((N - 3 : ℕ) : ℂ) • d + (x - z'))) (hdB z' (((N - 3 : ℕ) : ℂ) • d + (x - z')))
      (shiftB z _) (shiftB z' _)
    obtain ⟨b, hb, hb'⟩ := exists_common_ne_zero_of_differentiable
      (f₁ := fun b => t (z + b) * t (z' + b))
      (f₂ := fun b => t (z + -(((N - 3 : ℕ) : ℂ) • d + (x - z') + b)) *
        t (z' + -(((N - 3 : ℕ) : ℂ) • d + (x - z') + b)))
      (by fun_prop) (by fun_prop) ⟨b₁, mul_ne_zero h₁ h₁'⟩ ⟨b₂, mul_ne_zero h₂ h₂'⟩
    obtain ⟨hb₁, hb₂⟩ := mul_ne_zero_iff.mp hb
    obtain ⟨hb₁', hb₂'⟩ := mul_ne_zero_iff.mp hb'
    refine ⟨b, ?_, ?_⟩
    · simp only [hDen]
      exact mul_ne_zero (mul_ne_zero hb₁ hb₁') (pow_ne_zero _ hd₁)
    · simp only [hNum]
      exact mul_ne_zero hγ (mul_ne_zero (mul_ne_zero hb₂ hb₂') (pow_ne_zero _ hd₂))
  choose B hB using hChoice
  have hdense := _root_.GlobalTheory.ThetaSeparation.dense_ne_zero ht ⟨x₀, hx₀⟩
  have cross : ∀ b b' x, Num b x * Den b' x = Num b' x * Den b x := by
    intro b b'
    have hfun : (fun x => Num b x * Den b' x) = (fun x => Num b' x * Den b x) :=
      Continuous.ext_on hdense (((hNumD b).mul (hDenD b')).continuous)
        (((hNumD b').mul (hDenD b)).continuous) (by
          intro x hx
          have hx' : t x ≠ 0 := hx
          have r₁ := hRel b x
          have r₂ := hRel b' x
          apply mul_left_cancel₀ hx'
          linear_combination Den b x * r₂ - Den b' x * r₁)
    intro x
    exact congrFun hfun x
  refine ⟨fun x => Num (B x) x / Den (B x) x, ?_, fun x => div_ne_zero (hB x).2 (hB x).1, ?_⟩
  · intro y
    have hev : (fun x => Num (B y) x / Den (B y) x) =ᶠ[𝓝 y]
        (fun x => Num (B x) x / Den (B x) x) := by
      filter_upwards [(hDenD (B y)).continuous.continuousAt.eventually_ne (hB y).1] with x hx
      rw [div_eq_div_iff hx (hB x).1]
      exact cross (B y) (B x) x
    have hquot : DifferentiableAt ℂ (fun x => Num (B y) x / Den (B y) x) y := by
      simp only [div_eq_mul_inv]
      exact (hNumD (B y) y).mul ((hDenD (B y) y).inv (hB y).1)
    exact hquot.congr_of_eventuallyEq hev.symm
  · intro x
    have r := hRel (B x) x
    show t (x + (z - z')) = Num (B x) x / Den (B x) x * t x
    rw [div_mul_eq_mul_div, eq_div_iff (hB x).1]
    linear_combination r


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
theorem _root_.GlobalTheory.ThetaSeparation.level_three_separates_points :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → (Differentiable ℂ (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) z) ∧ (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ (w : Fin g → ℂ) (h : (Fin g → ℂ) → ℂ), Differentiable ℂ h → (∀ z, h z ≠ 0) → (∀ z, _root_.ReciprocityTheory.PTheta.theta 0 0 (z + w) τ = h z * _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) → w ∈ _root_.ReciprocityTheory.PTheta.periodLattice τ) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (z z' : Fin g → ℂ) (γ : ℂ), (∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * f z) → f z = γ * f z') → z - z' ∈ _root_.ReciprocityTheory.PTheta.periodLattice τ) := by
  intro hA hB g τ hτ N hN z z' γ hf
  obtain ⟨⟨htd, hq⟩, hne⟩ := hA g τ hτ
  have hne' : ∃ x, _root_.ReciprocityTheory.PTheta.theta 0 0 x τ ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
    exact ⟨x, hx⟩
  obtain ⟨h, hd, hnz, hrel⟩ :=
    exists_multiplier_of_level_sections_lemma (t := fun x => _root_.ReciprocityTheory.PTheta.theta 0 0 x τ) htd
      hq hne' hN hf
  exact hB g τ hτ (z - z') h hd hnz hrel

end GlobalTheory.ThetaSeparation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.PrincipalOpenDenseComplexPoints
section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory


open AffinePoints in
theorem algHom_mem_closure_nonvanishing (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] (f : A) (hf : f ≠ 0) :
    {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x 1 ≠ 0} ⊆
      closure {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x f ≠ 0} := by
  rintro _ ⟨φ, rfl, -⟩
  have h := image_closure_subset_closure_image (isEmbedding_coe (R := ℂ) (A := A) (C := ℂ)).continuous
    ⟨φ, dense_nonvanishing hf φ, rfl⟩
  refine closure_mono ?_ h
  rintro _ ⟨ψ, hψ, rfl⟩
  exact ⟨ψ, rfl, hψ⟩

theorem principalOpen_dense_complexPoints :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) → (∀ (d : ℕ) (q : MvPolynomial (Fin d) ℂ), q ≠ 0 → IsConnected {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} ∧ Dense {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0}) → (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x 1 ≠ 0} ⊆ closure {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x f ≠ 0}) :=
  fun _ _ A _ _ _ _ f hf => algHom_mem_closure_nonvanishing A f hf

end GlobalTheory
end

