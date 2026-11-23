module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0014
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0015

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.DividedPowerMonomialExpansion
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem monomial_eq_smul_basis {K σ : Type} [CommRing K] (m : σ →₀ ℕ) (c : K) :
    monomial m c = c • (basisMonomials σ K m) := by
  rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem divided_power_monomial {K : Type} [CommRing K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : K) :
    divPow K LL S a b k (monomial m c) = c • divPowMono K LL S a b k m := by
  rw [monomial_eq_smul_basis, map_smul]
  unfold divPow
  rw [Module.Basis.constr_basis]

theorem binomial_operator_monomial {K : Type} [CommRing K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : K) :
    binomPol K LL S a k (monomial m c) = monomial m (c * ((Ring.choose (wtS LL S m a) k : ℤ) : K)) := by
  rw [monomial_eq_smul_basis, map_smul]
  unfold binomPol
  rw [Module.Basis.constr_basis, MvPolynomial.smul_monomial, smul_eq_mul]

def dividedPowerTermCoefficient {ι : Type} {n : ℕ} (LL : Letters ι) (a b : Fin n) (m : ι × Fin n →₀ ℕ) (f : ι →₀ ℕ) (l : ι) : ℤ :=
  if LL.vec l then ((m (l, b)).choose (f l) : ℤ) else (-1 : ℤ) ^ (f l) * ((m (l, a)).choose (f l) : ℤ)

open Classical in
theorem divided_power_monomial_expansion {K : Type} [CommRing K] {ι : Type} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : K) :
    c • divPowMono K LL S a b k m =
      ∑ f ∈ Finset.finsuppAntidiag (Finset.univ.filter (· ∈ S)) k,
        monomial ((m - ∑ l ∈ f.support, Finsupp.single (if LL.vec l then (l, b) else (l, a)) (f l))
          + ∑ l ∈ f.support, Finsupp.single (if LL.vec l then (l, a) else (l, b)) (f l))
          (c * ((∏ l ∈ f.support, dividedPowerTermCoefficient LL a b m f l : ℤ) : K)) := by
  unfold divPowMono
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MvPolynomial.smul_monomial, smul_eq_mul, Int.cast_prod]
  congr 2
  refine Finset.prod_congr rfl fun l _ => ?_
  unfold dividedPowerTermCoefficient
  split_ifs <;> push_cast <;> rfl

theorem integral_formula_stability_holds {p : ℕ} (hp : p.Prime) (hV : ValuationProperties p O) : PolynomialIntegralFormPreservesLattices p O := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro n ι _ LL S
  refine ⟨?_, ?_⟩
  · intro u hu x hx
    refine integral_poly_linear_map_closed u (fun m => ?_) x hx
    rcases hu with ⟨a, b, k, -, rfl⟩ | ⟨a, k, rfl⟩
    · rw [divided_power_monomial, divided_power_monomial_expansion]
      refine Submodule.sum_mem _ fun f _ => ?_
      rw [one_mul]
      exact integer_monomial_mem_integral _ _
    · rw [binomial_operator_monomial, one_mul]
      exact integer_monomial_mem_integral _ _
  · intro u hu F hF
    refine fock_lattice_linear_map_closed hV u (fun m c hmc => ?_) F hF
    rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · rw [divided_power_monomial, divided_power_monomial_expansion]
      refine fock_lattice_sum_mem hV _ _ fun f _ => ?_
      refine fock_lattice_monomial_rescale hV m _ c _ hmc ?_
      exact divided_power_padic_valuation_bound p (fun l => if LL.vec l then (l, b) else (l, a))
        (fun l => if LL.vec l then (l, a) else (l, b))
        (fun l => by split_ifs <;> rfl) (fun l => by split_ifs <;> rfl)
        (fun l => by split_ifs <;> simp [hab, Ne.symm hab]) m f (dividedPowerTermCoefficient LL a b m f)
        (fun l => by unfold dividedPowerTermCoefficient; split_ifs <;> simp [Int.natAbs_mul, Int.natAbs_pow])
    · rw [binomial_operator_monomial]
      exact fock_lattice_monomial_rescale hV m m c _ hmc (Or.inr (Nat.le_add_left _ _))

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsIntegralWeightProjections
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem findim_exists_finite_weights [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V)
    (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤) :
    ∃ F : Finset (Fin n → ℤ), (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu := by
  have hc := (Submodule.fg_iff_compact (⊤ : Submodule (KK O) V)).1 Module.Finite.fg_top
  first
  | exact IsCompactElement.exists_finset_of_le_iSup hc _ hE.ge
  | exact IsCompactElement.exists_finset_of_le_iSup _ hc _ hE.ge
  | exact CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ hc _ hE.ge
  | exact CompleteLattice.IsCompactElement.exists_finset_of_le_iSup hc _ hE.ge

theorem linear_map_ext_on_weights {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {W : Type*} [AddCommGroup W] [Module (KK O) W]
    {A B : V →ₗ[KK O] W} (h : ∀ nu ∈ F, ∀ x ∈ weightSp E nu, A x = B x) : A = B := by
  have hle : (⨆ nu ∈ F, weightSp E nu) ≤ LinearMap.ker (A - B) := by
    refine iSup₂_le fun nu hnu x hx => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact h nu hnu x hx
  ext x
  have hx : x ∈ LinearMap.ker (A - B) := hle (hF (Submodule.mem_top : x ∈ (⊤ : Submodule (KK O) V)))
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
  exact hx

theorem exists_integral_weight_projection [CharZero (KK O)] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (F : Finset (Fin n → ℤ)) :
    ∃ (P : Module.End (KK O) V) (g : (Fin n → ℤ) → ℤ), g mu = 1 ∧ (∀ nu ∈ F, nu ≠ mu → g nu = 0) ∧
      (∀ nu, ∀ x ∈ weightSp E nu, P x = ((g nu : ℤ) : KK O) • x) ∧
      ∀ M : Submodule O V, UZStable (O := O) E M → ∀ x ∈ M, P x ∈ M := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, fun _ => 1, rfl, by simp, by simp, fun M _ x hx => by simpa using hx⟩
  | insert nu0 F _ ih =>
    obtain ⟨P, g, g1, g0, hP, hPM⟩ := ih
    by_cases h : nu0 = mu
    · refine ⟨P, g, g1, ?_, hP, hPM⟩
      intro nu hnu hne
      rcases mem_insert.1 hnu with rfl | h2
      · exact absurd h hne
      · exact g0 nu h2 hne
    · obtain ⟨T, g', g'1, g'0, hT, hTM⟩ := lattice_stable_weight_separator (O := O) E h
      refine ⟨T * P, fun nu => g' nu * g nu, by simp [g1, g'1], ?_, ?_, ?_⟩
      · intro nu hnu hne
        rcases mem_insert.1 hnu with rfl | h2
        · simp [g'0]
        · simp [g0 nu h2 hne]
      · intro nu x hx
        rw [Module.End.mul_apply, hP nu x hx, map_smul, hT nu x hx, smul_smul]
        push_cast
        rw [mul_comm]
      · intro M hM x hx
        exact hTM M hM _ (hPM M hM x hx)

theorem exists_integral_weight_projections [CharZero (KK O)] (E : GLOps n (KK O) V) (F : Finset (Fin n → ℤ)) :
    ∃ P : (Fin n → ℤ) → Module.End (KK O) V,
      (∀ mu, ∀ M : Submodule O V, UZStable (O := O) E M → ∀ x ∈ M, P mu x ∈ M) ∧
      (∀ mu, ∀ x ∈ weightSp E mu, P mu x = x) ∧
      (∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) := by
  choose P g hg1 hg0 hgw hgM using fun mu => exists_integral_weight_projection E mu F
  refine ⟨P, fun mu M hM x hx => hgM mu M hM x hx, fun mu x hx => ?_, fun mu nu hnu hne x hx => ?_⟩
  · rw [hgw mu mu x hx, hg1 mu]
    simp
  · rw [hgw mu nu x hx, hg0 mu nu hnu hne]
    simp

theorem sum_weight_projections_eq_one {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) : ∑ mu ∈ F, P mu = 1 := by
  refine linear_map_ext_on_weights hF fun nu hnu x hx => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single nu (fun mu _ hne => h0 mu nu hnu (Ne.symm hne) x hx)
    (fun h => absurd hnu h)]
  rw [h1 nu x hx]
  rfl

private theorem end_mul_apply' (f g : Module.End (KK O) V) (x : V) : (f * g) x = f (g x) := rfl

private theorem diagonal_apply_of_mem_weightSp {E : GLOps n (KK O) V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) : E a a x = ((mu a : ℤ) : KK O) • x := by
  rw [weightSp, Submodule.mem_iInf] at hx
  have h := LinearMap.mem_ker.1 (hx a)
  rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply] at h
  exact h

theorem diagonal_weight_projection_comm {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) (mu : Fin n → ℤ) (a : Fin n) :
    E a a * P mu = (mu a : KK O) • P mu ∧ P mu * E a a = (mu a : KK O) • P mu := by
  constructor
  · refine linear_map_ext_on_weights hF fun nu hnu x hx => ?_
    by_cases h : nu = mu
    · subst h
      rw [end_mul_apply', LinearMap.smul_apply, h1 _ x hx]
      exact diagonal_apply_of_mem_weightSp hx a
    · rw [end_mul_apply', LinearMap.smul_apply, h0 mu nu hnu h x hx, map_zero, smul_zero]
  · refine linear_map_ext_on_weights hF fun nu hnu x hx => ?_
    rw [end_mul_apply', LinearMap.smul_apply, diagonal_apply_of_mem_weightSp hx a, map_smul]
    by_cases h : nu = mu
    · subst h
      rw [h1 _ x hx]
    · rw [h0 mu nu hnu h x hx, smul_zero, smul_zero]

def adjointEndAction (E : GLOps n (KK O) V) : GLOps n (KK O) (Module.End (KK O) V) :=
  fun a b => LinearMap.mulLeft (KK O) (E a b) - LinearMap.mulRight (KK O) (E a b)

theorem adjointEndAction_apply (E : GLOps n (KK O) V) (a b : Fin n) (f : Module.End (KK O) V) :
    adjointEndAction E a b f = E a b * f - f * E a b := by
  first
  | rfl
  | simp [adjointEndAction]

private theorem end_one_apply {W : Type*} [AddCommGroup W] [Module (KK O) W] (x : W) :
    (1 : Module.End (KK O) W) x = x := rfl

theorem weight_block_adjoint_weight {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) (mu nu : Fin n → ℤ)
    (f : Module.End (KK O) V) : P mu * f * P nu ∈ weightSp (adjointEndAction E) (mu - nu) := by
  rw [weightSp, Submodule.mem_iInf]
  intro a
  obtain ⟨hm, -⟩ := diagonal_weight_projection_comm hF h1 h0 mu a
  obtain ⟨-, hn⟩ := diagonal_weight_projection_comm hF h1 h0 nu a
  have e1 : E a a * (P mu * f * P nu) = ((mu a : ℤ) : KK O) • (P mu * f * P nu) := by
    rw [← mul_assoc, ← mul_assoc, hm, smul_mul_assoc, smul_mul_assoc]
  have e2 : P mu * f * P nu * E a a = ((nu a : ℤ) : KK O) • (P mu * f * P nu) := by
    rw [mul_assoc, hn, mul_smul_comm]
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, adjointEndAction_apply, LinearMap.smul_apply, end_one_apply,
    e1, e2, Pi.sub_apply, Int.cast_sub, sub_smul]

theorem endomorphism_sum_weight_blocks {E : GLOps n (KK O) V} {F : Finset (Fin n → ℤ)}
    (hF : (⊤ : Submodule (KK O) V) ≤ ⨆ nu ∈ F, weightSp E nu) {P : (Fin n → ℤ) → Module.End (KK O) V}
    (h1 : ∀ mu, ∀ x ∈ weightSp E mu, P mu x = x)
    (h0 : ∀ mu, ∀ nu ∈ F, nu ≠ mu → ∀ x ∈ weightSp E nu, P mu x = 0) (f : Module.End (KK O) V) :
    f = ∑ mu ∈ F, ∑ nu ∈ F, P mu * f * P nu := by
  have hs := sum_weight_projections_eq_one hF h1 h0
  calc f = (∑ mu ∈ F, P mu) * f * (∑ nu ∈ F, P nu) := by rw [hs, one_mul, mul_one]
    _ = ∑ mu ∈ F, ∑ nu ∈ F, P mu * f * P nu := by
      rw [Finset.sum_mul, Finset.sum_mul]
      simp_rw [Finset.mul_sum]

theorem adjoint_end_isGLRep [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E) :
    IsGLRep (adjointEndAction E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    refine LinearMap.ext fun f => ?_
    have hr := hE.1 a b c d
    have key : (adjointEndAction E a b * adjointEndAction E c d - adjointEndAction E c d * adjointEndAction E a b) f =
        (E a b * E c d - E c d * E a b) * f - f * (E a b * E c d - E c d * E a b) := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, adjointEndAction_apply]
      noncomm_ring
    rw [key, hr]
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, adjointEndAction_apply] <;> noncomm_ring
  · intro x
    exact ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩
  · obtain ⟨F, hF⟩ := findim_exists_finite_weights E hE.2.2
    obtain ⟨P, -, h1, h0⟩ := exists_integral_weight_projections (O := O) E F
    rw [eq_top_iff]
    intro f _
    rw [endomorphism_sum_weight_blocks hF h1 h0 f]
    refine Submodule.sum_mem _ fun mu _ => Submodule.sum_mem _ fun nu _ => ?_
    exact Submodule.mem_iSup_of_mem (mu - nu) (weight_block_adjoint_weight hF h1 h0 mu nu f)

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionKillsNonzeroWeight
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem invariant_projection_kills_operator (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (a b : Fin n) (x : V) : Inv (E a b x) = 0 := by
  have hs := gl_rep_shifts_weights hE
  have htop := sum_isotypic_top_of_weight_data D h2 E hE hs (findim_weights_bounded E) (weight_projections_integral_findim E)
  have hinv := trivial_isotypic_invariant_holds hE
  have hle : ∀ mu, isoSub E mu ≤ LinearMap.ker (Inv * E a b) := by
    intro mu y hy
    rw [LinearMap.mem_ker, Module.End.mul_apply]
    by_cases hmu : mu = 0
    · subst hmu
      obtain ⟨hy0, hyr⟩ := hinv y hy
      have : E a b y = 0 := by
        rcases lt_trichotomy a b with h | h | h
        · exact hyr a b h
        · subst h
          have := (mem_weightSpace_iff_diagonal_eigen E 0 y).1 hy0 a
          simpa using this
        · exact weight_zero_lowering_kills_raising hE hy0 b a (ne_of_lt h) (hyr b a h)
      rw [this, map_zero]
    · exact hInv.2 mu hmu _ (isotypic_stable_under_gl_operator E mu a b y hy)
  have : (⊤ : Submodule K V) ≤ LinearMap.ker (Inv * E a b) := by
    rw [← htop]
    exact iSup_le hle
  have h3 := this (Submodule.mem_top (x := x))
  rwa [LinearMap.mem_ker, Module.End.mul_apply] at h3

theorem invariant_projection_kills_nonzero_weight (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (μ : Fin n → ℤ) (hμ : μ ≠ 0) (x : V)
    (hx : x ∈ weightSp E μ) : Inv x = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ 0 := by
    by_contra h
    push Not at h
    exact hμ (funext h)
  have h1 := (mem_weightSpace_iff_diagonal_eigen E μ x).1 hx a
  have h2' : (μ a : K) ≠ 0 := by exact_mod_cast ha
  have h3 : x = E a a (((μ a : K))⁻¹ • x) := by
    rw [map_smul, h1, smul_smul, inv_mul_cancel₀ h2', one_smul]
  rw [h3]
  exact invariant_projection_kills_operator D h2 E hE Inv hInv a a _

theorem invariant_projection_through_zero_weight (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E)
    (Inv : Module.End K V) (hInv : IsInvProj E Inv) (Θ : (Fin n → ℤ) → Module.End K V)
    (hΘ : ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0) (x : V) : Inv x = Inv (Θ 0 x) := by
  classical
  obtain ⟨m, hm⟩ := findim_weights_bounded E
  set box : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m with hbox
  have hb : ∀ ν, weightSp E ν ≠ ⊥ → ν ∈ box := by
    intro ν hν
    rw [hbox, Fintype.mem_piFinset]
    intro a
    rw [Finset.mem_Icc]
    exact abs_le.1 (hm ν hν a)
  have hsum := sum_weight_projections_eq_self E hE Θ hΘ box hb x
  have h0 : (0 : Fin n → ℤ) ∈ box := by
    rw [hbox, Fintype.mem_piFinset]
    intro a
    rw [Finset.mem_Icc]
    constructor <;> simp
  conv_lhs => rw [← hsum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single_of_mem 0 h0]
  intro μ _ hμ
  exact invariant_projection_kills_nonzero_weight D h2 E hE Inv hInv μ hμ _ (weight_projection_mem_weightSpace E hE Θ hΘ μ x)

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.LaurentCoefficientsMemProperty
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def laurentUnit (B : Type*) [CommRing B] : (LaurentPolynomial B)ˣ :=
  ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by rw [← LaurentPolynomial.T_add]; simp,
    by rw [← LaurentPolynomial.T_add]; simp⟩

theorem laurentUnit_zpow (B : Type*) [CommRing B] (w : ℤ) :
    (((laurentUnit B) ^ w : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) = LaurentPolynomial.T w := by
  have hinv : (((laurentUnit B)⁻¹ : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) = LaurentPolynomial.T (-1) := rfl
  have hval : (((laurentUnit B) : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) = LaurentPolynomial.T 1 := rfl
  induction w using Int.induction_on with
  | zero => simp [LaurentPolynomial.T_zero]
  | succ i ih => rw [zpow_add_one, Units.val_mul, ih, hval, ← LaurentPolynomial.T_add]
  | pred i ih => rw [zpow_sub_one, Units.val_mul, ih, hinv, ← LaurentPolynomial.T_add]; rfl

theorem binomialOperator_monomial {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : R) :
    binomPol R LL S a k (monomial m c) = monomial m (c * ((Ring.choose (wtS LL S m a) k : ℤ) : R)) := by
  have hm : (monomial m c : MvPolynomial (ι × Fin n) R) = c • (MvPolynomial.basisMonomials (ι × Fin n) R) m := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, LinearMap.map_smul]
  simp only [binomPol]
  rw [Module.Basis.constr_basis, MvPolynomial.smul_monomial, smul_eq_mul]

section fwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι) (j : Fin n)
  (Pr : ℤ → Prop)

def weightEntryPropertySubmodule : Submodule R (MvPolynomial (ι × Fin n) R) where
  carrier := {y | ∀ (k1 : Type) [CommRing k1] (φ : R →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1),
    g0 * g0inv = 1 → ∀ m ∈ (matrixSubst LL S φ g0inv g0 y).support, Pr (wtS LL S m j)}
  zero_mem' := by
    intro k1 _ φ g0 g0inv _ m hm
    simp at hm
  add_mem' := by
    classical
    intro x y hx hy k1 _ φ g0 g0inv h m hm
    rw [map_add (f := _)] at hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h1 | h1
    · exact hx k1 φ g0 g0inv h m h1
    · exact hy k1 φ g0 g0inv h m h1
  smul_mem' := by
    intro c y hy k1 _ φ g0 g0inv h m hm
    rw [MvPolynomial.smul_eq_C_mul, map_mul, matrixSubst_C, ← MvPolynomial.smul_eq_C_mul] at hm
    exact hy k1 φ g0 g0inv h m (MvPolynomial.support_smul hm)

theorem laurent_coefficients_mem_property (y : MvPolynomial (ι × Fin n) R) (K : Finset ℤ) (yk : ℤ → MvPolynomial (ι × Fin n) R)
    (hh : ∀ (k1 : Type) [CommRing k1] (φ : R →+* k1), ∃ h h' : Matrix (Fin n) (Fin n) (LaurentPolynomial k1),
      h' * h = 1 ∧ matrixSubst LL S (LaurentPolynomial.C.comp φ) h h' y =
        ∑ k ∈ K, C (LaurentPolynomial.T k) * MvPolynomial.map (LaurentPolynomial.C.comp φ) (yk k))
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : ∀ k ∈ K, yk k ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical
  intro k hk k1 _ φ g0 g0inv hg m hm
  obtain ⟨h, h', hh1, hE⟩ := hh k1 φ
  set ψ : k1 →+* LaurentPolynomial k1 := LaurentPolynomial.C with hψ
  have h2 : g0.map ψ * g0inv.map ψ = 1 := by
    rw [← Matrix.map_mul, hg, Matrix.map_one ψ (map_zero ψ) (map_one ψ)]
  have hinv : (h' * g0.map ψ) * (g0inv.map ψ * h) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (g0.map ψ), h2, Matrix.one_mul, hh1]
  apply hy (LaurentPolynomial k1) (ψ.comp φ) (h' * g0.map ψ) (g0inv.map ψ * h) hinv m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← matrixSubst_comp, hE, map_sum]
  have hA : ∀ k', matrixSubst LL S (RingHom.id _) (g0inv.map ψ) (g0.map ψ)
      (C (LaurentPolynomial.T k') * MvPolynomial.map (ψ.comp φ) (yk k')) =
      C (LaurentPolynomial.T k') * MvPolynomial.map ψ (matrixSubst LL S φ g0inv g0 (yk k')) := by
    intro k'
    rw [map_mul, matrixSubst_C, RingHom.id_apply, matrixSubst_map, map_matrixSubst]
  simp_rw [hA]
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  intro hz
  apply hm
  rw [MvPolynomial.coeff_sum] at hz
  simp_rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at hz
  have hz2 := congrArg (fun p : LaurentPolynomial k1 => p.coeff k) hz
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at hz2
  have hT : ∀ k' (c : k1), (LaurentPolynomial.T k' * ψ c).coeff k = if k' = k then c else 0 := by
    intro k' c
    rw [hψ, mul_comm, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp_rw [hT, Finset.sum_ite_eq' K k] at hz2
  simpa [hk] using hz2

end fwd

end Formalism.MainNotions.G.GLWeightTheory
end
end

