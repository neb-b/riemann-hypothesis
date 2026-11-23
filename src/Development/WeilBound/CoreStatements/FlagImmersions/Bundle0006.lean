module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.RootModelCurveDegreeNef
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem geoNum_one_linear_in_degree {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) :
    ∃ c : K → ℤ, ∀ a : K → ℤ, geoNum 1 W (fun _ => a) = ∑ k, a k * c k := by
  classical
  refine ⟨fun k => geoNum 1 W (fun _ => Pi.single k 1), fun a => ?_⟩
  have hs : ∀ b : K → ℤ, (Fin.init (fun _ : Fin 1 => b) : Fin 0 → K → ℤ) = fun i => i.elim0 :=
    fun b => Subsingleton.elim _ _
  rw [geoNum.eq_2 (n := 0)]
  simp only [geoNum.eq_2 (n := 0), hs]
  split_ifs with h
  · simp [Pi.single_apply]
  · simp

theorem geoNum_linear_combination {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    {J : Type} [Fintype J] (n : J → ℤ) (b : J → K → ℤ) :
    geoNum 1 W (fun _ => ∑ j, n j • b j) = ∑ j, n j * geoNum 1 W (fun _ => b j) := by
  obtain ⟨c, hc⟩ := geoNum_one_linear_in_degree (K := K) W
  rw [hc]
  simp only [hc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem char_prime_of_prime_ideal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (hW : W.IsPrime) (h : charOf W ≠ 0) : (charOf W).Prime := by
  classical
  set I : Ideal ℤ := Ideal.comap (C : ℤ →+* MRing ι) W with hI
  have hp : I.IsPrime := Ideal.IsPrime.comap _
  have hne : I ≠ ⊥ := by
    intro hb
    apply h
    have : Submodule.IsPrincipal.generator I = 0 :=
      (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mp hb
    simp [charOf, ← hI, this]
  have hg := Submodule.IsPrincipal.prime_generator_of_isPrime I hne
  have : charOf W = (Submodule.IsPrincipal.generator I).natAbs := by
    simp [charOf, ← hI]
  rw [this]
  exact Int.prime_iff_natAbs_prime.mp hg

theorem root_line_a_independent {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) :
    (M.line t j).a = (M.line 1 j).a := by
  cases j with
  | none => rfl
  | some r => simp only [RootModel.line, M.x_deg]

end RootFieldNumerics

theorem RootFieldNumerics.curveDeg_eq_and_nefOnFibres_of_coef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → (∀ W : Ideal (MRing M.ι), (geoNum 1 W (fun _ => (combLine (M.line t) n).a) : ℝ) = q * M.curveDeg lam s W) ∧ (M.NefFib lam s → NefOnFibres M.P (combLine (M.line t) n).a) := by
  intro Ψ _ N M t lam s q n hn
  have key : ∀ W : Ideal (MRing M.ι),
      (geoNum 1 W (fun _ => (combLine (M.line t) n).a) : ℝ) = q * M.curveDeg lam s W := by
    intro W
    rw [show (combLine (M.line t) n).a = ∑ j, n j • (M.line t j).a from rfl,
      geoNum_linear_combination W n (fun j => (M.line t j).a)]
    push_cast
    rw [RootModel.curveDeg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [root_line_a_independent M t j, hn j]
    ring
  refine ⟨key, fun hN W hWp hPW hc hd => ?_⟩
  have hpr := char_prime_of_prime_ideal W hWp.1 hc
  have h0 := hN _ hpr W ⟨hWp, hPW, rfl, hd⟩
  have h1 : (0:ℝ) ≤ geoNum 1 W (fun _ => (combLine (M.line t) n).a) := by
    rw [key]
    exact mul_nonneg (Nat.cast_nonneg _) h0
  exact_mod_cast h1
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.RootModelLineSemipositive
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_nonvanishing_blocks : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem smooth_metric_zpow {A : HermLine ι} (hA : IsSmoothHerm A) (n : ℤ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => A.h z ^ n) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact hA.pow m
  | negSucc m =>
    simp only [zpow_negSucc]
    exact (hA.pow (m + 1)).inv fun z hz => pow_ne_zero _ (A.pos z hz).ne'

theorem combLine_smooth {J : Type} [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ)
    (h : ∀ j, IsSmoothHerm (ℓ j)) : IsSmoothHerm (combLine ℓ n) := by
  show ContDiffOn ℝ _ (fun z => ∏ j, (ℓ j).h z ^ n j) _
  exact contDiffOn_prod fun j _ => smooth_metric_zpow (h j) (n j)

theorem combLine_conj_invariant {J : Type} [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ)
    (h : ∀ j, IsConjInvariantH (ℓ j)) : IsConjInvariantH (combLine ℓ n) := by
  intro z
  show ∏ j, (ℓ j).h _ ^ n j = ∏ j, (ℓ j).h z ^ n j
  exact Finset.prod_congr rfl fun j _ => by rw [h j z]

end

theorem leviForm_congr_eventually {ι : Type} [Fintype ι] {φ ψ : (ι → ℂ) → ℝ} {z : ι → ℂ} (h : φ =ᶠ[𝓝 z] ψ)
    (w : ι → ℂ) : leviForm φ z w = leviForm ψ z w := by
  simp only [leviForm, h.fderiv.fderiv_eq]

theorem leviForm_smul {ι : Type} [Fintype ι] (c : ℝ) (φ : (ι → ℂ) → ℝ) (z w : ι → ℂ) :
    leviForm (c • φ) z w = c * leviForm φ z w := by
  by_cases hc : c = 0
  · subst hc
    simp [leviForm]
  · letI : Invertible c := invertibleOfNonzero hc
    have h1 : fderiv ℝ (c • φ) = c • fderiv ℝ φ :=
      funext fun x => fderiv_const_smul_of_invertible c
    have h2 : fderiv ℝ (c • fderiv ℝ φ) z = c • fderiv ℝ (fderiv ℝ φ) z :=
      fderiv_const_smul_of_invertible c
    simp only [leviForm, h1, h2, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

theorem root_model_line_semipositive : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.Semipos t lam s → IsSemipositiveH M.P (combLine (M.line t) n) ∧ IsConjInvariantH (combLine (M.line t) n) := by
  intro Ψ _ N M t lam s q n hn hS
  have hsm : IsSmoothHerm (combLine (M.line t) n) := by
    refine combLine_smooth _ _ fun j => ?_
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  have hcj : IsConjInvariantH (combLine (M.line t) n) := by
    refine combLine_conj_invariant _ _ fun j => ?_
    cases j with
    | none => exact M.A_conj
    | some r => exact M.x_conj t r
  refine ⟨⟨hsm, fun z hz w hw => ?_⟩, hcj⟩
  have hev : (fun y => Real.log ((combLine (M.line t) n).h y)) =ᶠ[𝓝 z]
      ((q : ℝ) • M.weight t lam s) := by
    filter_upwards [isOpen_nonvanishing_blocks.mem_nhds hz.1] with y hy
    rw [Pi.smul_apply, smul_eq_mul]
    show Real.log (∏ j, (M.line t j).h y ^ n j) =
      (q : ℝ) * ∑ j, M.coef lam s j * Real.log ((M.line t j).h y)
    rw [Real.log_prod (fun j _ => zpow_ne_zero _ ((M.line t j).pos y hy).ne'), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.log_zpow, hn j]
    ring
  rw [leviForm_congr_eventually hev w, leviForm_smul]
  exact mul_nonneg (Nat.cast_nonneg _) (hS z hz w hw)

end RootFieldNumerics
end

