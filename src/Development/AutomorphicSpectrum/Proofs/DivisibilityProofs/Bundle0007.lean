module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagShiftTotalLinRootPower
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0001
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.WeilBound.CoreStatements.IdealCycleValues.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0071
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AntisymmetricPerturbationBound
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
open RootFieldNumerics

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem inv_linear_eval (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (l : MvPolynomial (Ψ × Fin N) ℝ)
    (hl : l ∈ GroundTheory.Heights₂.Heights.antisymInv Ψ N j) :
    ∃ a b : Ψ → ℝ, ∀ x : Ψ × Fin N → ℝ, eval x l =
      ∑ τ, (a τ - b τ) * ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), x (τ, i) +
        ∑ τ, b τ * ∑ i, x (τ, i) := by
  obtain ⟨h1, h2⟩ := hl
  rw [homogeneousSubmodule_one_eq_span_X] at h1
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 h1
  have hcoef : ∀ p, l.coeff (Finsupp.single p 1) = c p := by
    intro p
    rw [← hc, coeff_sum, Finset.sum_eq_single p]
    · simp
    · intro q _ hq
      rw [coeff_smul, coeff_X, if_neg, smul_zero]
      intro h
      exact hq (Finsupp.single_left_injective one_ne_zero h)
    · simp
  have hinv : ∀ τ (i k : Fin N), ((i : ℕ) < j ↔ (k : ℕ) < j) → c (τ, i) = c (τ, k) := by
    intro τ i k hik
    have hmem : Equiv.swap (τ, i) (τ, k) ∈ GroundTheory.Heights₂.Heights.antisymWeyl Ψ N j := by
      intro p
      rw [Equiv.swap_apply_def]
      split_ifs with e1 e2
      · subst e1
        exact ⟨rfl, hik.symm⟩
      · subst e2
        exact ⟨rfl, hik⟩
      · exact ⟨rfl, Iff.rfl⟩
    have h3 := coeff_rename_mapDomain _ (Equiv.swap (τ, i) (τ, k)).injective l (Finsupp.single (τ, i) 1)
    rw [h2 _ hmem, Finsupp.mapDomain_single, Equiv.swap_apply_left, hcoef, hcoef] at h3
    exact h3.symm
  have ha : ∀ τ, ∃ a : ℝ, ∀ i : Fin N, (i : ℕ) < j → c (τ, i) = a := by
    intro τ
    by_cases h : ∃ i : Fin N, (i : ℕ) < j
    · obtain ⟨i, hi⟩ := h
      exact ⟨c (τ, i), fun k hk => hinv τ k i (by simp [hi, hk])⟩
    · exact ⟨0, fun k hk => absurd ⟨k, hk⟩ h⟩
  have hb : ∀ τ, ∃ b : ℝ, ∀ i : Fin N, ¬ (i : ℕ) < j → c (τ, i) = b := by
    intro τ
    by_cases h : ∃ i : Fin N, ¬ (i : ℕ) < j
    · obtain ⟨i, hi⟩ := h
      exact ⟨c (τ, i), fun k hk => hinv τ k i (iff_of_false hk hi)⟩
    · exact ⟨0, fun k hk => absurd ⟨k, hk⟩ h⟩
  choose a ha using ha
  choose b hb using hb
  refine ⟨a, b, fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hc, map_sum, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eval, eval_X]
  split_ifs with hi
  · rw [ha τ i hi]
    ring
  · rw [hb τ i hi]
    ring

theorem flagDeg_eq_delta (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Ψ × Fin N → ℝ,
      flagDeg (fun τ i => x (τ, i) : Wt Ψ N) = c * eval x (GroundTheory.Heights₂.Heights.antisymDelta Ψ N) := by
  refine ⟨((dimFl Ψ N).factorial : ℝ) * ∏ _τ : Ψ, ∏ i : Fin N, ∏ k ∈ Finset.Ioi i, ((k : ℝ) - (i : ℝ))⁻¹, ?_, ?_⟩
  · refine mul_pos (by positivity) (Finset.prod_pos fun _ _ => Finset.prod_pos fun i _ =>
      Finset.prod_pos fun k hk => inv_pos.2 (sub_pos.2 ?_))
    exact_mod_cast (Finset.mem_Ioi.1 hk)
  · intro x
    rw [(_root_.GlobalTheory.CompanionTheory.Ar.Top.flagDeg_eq_weyl Ψ N _).1, mul_assoc]
    congr 1
    unfold GroundTheory.Heights₂.Heights.antisymDelta
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_filter]
    refine Finset.prod_congr (by ext k; simp) fun k _ => ?_
    rw [map_sub, eval_X, eval_X, div_eq_inv_mul]

theorem cor_b_poly_functional : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (R : RP Ψ N →ₗ[ℝ] ℝ) (v ε : ℝ) (Pl l : MvPolynomial (Ψ × Fin N) ℝ), 0 < v → (∀ lam : Wt Ψ N, eval (fun x => lam x.1 x.2) Pl = R (linRoot lam ^ (dimFl Ψ N + 1))) → Pl.IsHomogeneous (dimFl Ψ N + 1) → l ∈ GroundTheory.Heights₂.Heights.antisymInv Ψ N j → (∀ m, |(Pl - GroundTheory.Heights₂.Heights.antisymDelta Ψ N * l).coeff m| ≤ ε) → ∃ α β : Ψ → ℝ, ∀ m : Ψ × Fin N →₀ ℕ, m.degree = dimFl Ψ N + 1 → |R (monomial m 1) + v * (∑ τ, (α τ - β τ) * Sh j τ (monomial m 1) + ∑ τ, β τ * Tot τ (monomial m 1))| ≤ ε := by
  intro Ψ _ _ N j R v ε Pl l hv hP _ hl hε
  obtain ⟨a, b, hab⟩ := inv_linear_eval Ψ N j l hl
  obtain ⟨c, hc0, hc⟩ := flagDeg_eq_delta Ψ N
  set K : ℝ := v * ((dimFl Ψ N : ℝ) + 1) * c with hK
  have hK0 : K ≠ 0 := by positivity
  refine ⟨fun τ => a τ / K, fun τ => b τ / K, fun m hm => ?_⟩
  let Φ : RP Ψ N →ₗ[ℝ] ℝ :=
    R + v • (∑ τ, (a τ / K - b τ / K) • Lin.shL j τ + ∑ τ, (b τ / K) • Lin.totL τ)
  have hΦ : ∀ F, Φ F = R F + v * (∑ τ, (a τ / K - b τ / K) * Sh j τ F + ∑ τ, b τ / K * Tot τ F) := by
    intro F
    simp only [Φ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, Lin.shL_apply,
      Lin.totL_apply, smul_eq_mul]
  obtain ⟨P', -, hP', -, hle⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.polarisation_functional (Ψ × Fin N) (dimFl Ψ N + 1) Φ
  have heq : P' = Pl - GroundTheory.Heights₂.Heights.antisymDelta Ψ N * l := by
    refine MvPolynomial.funext fun x => ?_
    have e1 : (-∑ y, C (x y) * X y : RP Ψ N) = linRoot (fun τ i => x (τ, i) : Wt Ψ N) := rfl
    have e2 := hP (fun τ i => x (τ, i))
    rw [hP', e1, hΦ, map_sub, map_mul, hab, ← e2]
    simp only [(_root_.GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow Ψ N j _ _).1, (_root_.GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow Ψ N j _ _).2, hc]
    rw [sub_eq_add_neg (eval x Pl)]
    congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hK' : v * ((dimFl Ψ N : ℝ) + 1) * c / K = 1 := div_self hK0
    generalize (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), x (τ, i)) = s
    generalize (∑ i, x (τ, i)) = t
    generalize eval x (GroundTheory.Heights₂.Heights.antisymDelta Ψ N) = d
    linear_combination (-(d * ((a τ - b τ) * s + b τ * t))) * hK'
  have h := hle m hm
  rw [hΦ, heq] at h
  exact h.trans (hε m)

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CutoffCoefficientsBound
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

private theorem card_lt_lemma {N j : ℕ} (hj : j ≤ N) :
    (Finset.univ.filter fun i : Fin N => (i : ℕ) < j).card = j := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (show {i : Fin N // (i : ℕ) < j} ≃ Fin j from
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, lt_of_lt_of_le y.2 hj⟩, y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl })]
  exact Fintype.card_fin j

theorem flag_degree_low_zero {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (j : ℕ) (hj : j ≤ N) (τ : Ψ) (Q : RP Ψ N) :
    degFl (pkLow j τ 0 * Q) = j * degFl Q := by
  have hp : (pkLow j τ 0 : RP Ψ N) = C (j : ℝ) := by
    unfold pkLow
    simp only [pow_zero, Finset.sum_const, card_lt_lemma hj, nsmul_eq_mul, mul_one]
    exact (map_natCast C j).symm
  rw [hp]
  unfold degFl
  simp only [coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem flat_85_bound : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) [Nonempty Ψ] (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C rd Lval : ℝ) (B₀ : ℕ) (A₀ b₀ : ℝ), T.Proportional → I9 (Ψ := Ψ) (N := N) hh → T.PropF II C rd Lval → 128 ≤ B₀ → T.bad.card ≤ B₀ → T.IdentAt II hh frob B₀ A₀ b₀ → |T.j * A₀ + N * b₀| ≤ C * N * bigLam B₀ rd Lval := by
  intro II Ψ _ _ N T _ hh frob C rd Lval B₀ A₀ b₀ hP hI9 hF hB hbad hId
  unfold RootTower.Proportional at hP
  unfold I9 at hI9
  obtain ⟨τ⟩ := ‹Nonempty Ψ›
  obtain ⟨⟨Q, hQ, hdeg⟩, -⟩ := testForms_sh_tot Ψ N T.j τ T.j_pos T.j_lt
  obtain ⟨h, hPP, hbd⟩ := hF
  have hN : 1 ≤ N := le_trans T.j_pos T.j_lt.le
  have hQ' : Q.IsHomogeneous (dimFl Ψ N + 1 - 1) := by simpa using hQ
  have hid := hId τ 1 le_rfl hN Q hQ'
  have hhh : hh (pk τ 1 * Q) = 0 := hI9.2.2 τ Q hQ
  have hSh : ∀ σ, Sh T.j σ (pk τ 1 * Q) = if σ = τ then (T.j : ℝ) else 0 := by
    intro σ
    rw [(RootFieldNumerics.shift_power_sum_mul Ψ N T.j τ σ 1 Q le_rfl).1]
    simp [flag_degree_low_zero T.j T.j_lt.le τ Q, hdeg]
  have hTot : ∀ σ, Tot σ (pk τ 1 * Q) = if σ = τ then (N : ℝ) else 0 := by
    intro σ
    rw [(RootFieldNumerics.shift_power_sum_mul Ψ N T.j τ σ 1 Q le_rfl).2]
    simp [hdeg]
  have hrest : restSum T.j T.bad frob B₀ τ 1 Q = 0 := by
    simp [restSum, restTerm]
  have hL : T.PPt II B₀ (pk τ 1 * Q) = ∑ c, h B₀ c τ * T.vol c := by
    unfold RootTower.PPt
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hPP B₀ (by omega) c τ Q hQ, hdeg, mul_one]
  rw [hL, hhh, hrest] at hid
  simp only [hSh, hTot, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at hid
  have hvol : 0 < T.volT := Finset.sum_pos (fun c _ => hP.1 c) Finset.univ_nonempty
  have hv0 : T.volT ≠ 0 := hvol.ne'
  have key : (T.j : ℝ) * A₀ + N * b₀ = -(∑ c, h B₀ c τ * T.vol c) / T.volT := by
    rw [hid]
    field_simp
    ring
  rw [key, abs_div, abs_neg, abs_of_pos hvol, div_le_iff₀ hvol]
  calc |∑ c, h B₀ c τ * T.vol c| ≤ ∑ c, |h B₀ c τ * T.vol c| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, |h B₀ c τ| * T.vol c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [abs_mul, abs_of_pos (hP.1 c)]
    _ ≤ ∑ c, C * N * bigLam B₀ rd Lval * T.vol c := by
        refine Finset.sum_le_sum fun c _ => ?_
        exact mul_le_mul_of_nonneg_right (hbd B₀ hB hbad c τ) (hP.1 c).le
    _ = C * N * bigLam B₀ rd Lval * T.volT := by
        rw [← Finset.mul_sum]
        rfl

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberLinear
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem cycNum_linear : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ H H' : MvPolynomial σ ℝ, cycNum Z cls (H + H') Q = cycNum Z cls H Q + cycNum Z cls H' Q) ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), cycNum Z cls (C c * H) Q = c * cycNum Z cls H Q) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), cycNum Z cls (∑ a ∈ s, H a) Q = ∑ a ∈ s, cycNum Z cls (H a) Q) ∧ ∀ (μ : σ →₀ ℕ) (c : ℝ), cycNum Z cls (monomial μ c) Q = c * (cycList Z (classList cls μ ++ Q) : ℝ) :=
  @BaseChangeColon.cycNum_linear_in_polynomial

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberRename
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem numbers_rename : (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (Z : Ideal (MRing ι O) → ℤ) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (rename e H) Q = cycNum Z (cls ∘ e) H Q) ∧ (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (V : Ideal (MRing ι F)) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (rename e H) Q = genNum F V (cls ∘ e) H Q) :=
  BaseChangeColon.cycNum_rename_variables

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsMixedDifferenceExpansionStatement
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixed_difference_expansion : ∀ (σ : Type) [Fintype σ] (n : ℕ) (F : MvPolynomial σ ℝ), F.IsHomogeneous n → ∃ Gs, IsMixExpansion (n - 1) (mixDiff F) Gs := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.exists_mixExpansion_mixDiff | exact GlobalTheory.CompanionTheory.Ar.Num.exists_mixExpansion_mixDiff | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.exists_mixExpansion_mixDiff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GapNonnegOfDominant
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem gap_nonneg_of_dominant {Ψ : Type} [Fintype Ψ] {N : ℕ} {j : ℕ} (hj1 : 1 ≤ j) (hjN : j < N)
    {mu : Wt Ψ N} (hd : Dominant mu) (τ : Ψ) : 0 ≤ gap j mu τ := by
  have h1 : j - 1 < N := by omega
  have hle : mu τ ⟨j, hjN⟩ ≤ mu τ ⟨j - 1, h1⟩ := hd τ ⟨j - 1, h1⟩ ⟨j, hjN⟩ (by rw [Fin.mk_le_mk]; omega)
  simp only [gap, ent, dif_pos h1, dif_pos hjN]
  exact sub_nonneg.mpr hle

theorem NefThreshold.mono {Ψ : Type} [Fintype Ψ] {N : ℕ} {j : ℕ} (hj1 : 1 ≤ j) (hjN : j < N)
    {mu : Wt Ψ N} (hd : Dominant mu) {b b' : ℝ} (hb : b ≤ b') (h : NefThreshold j b mu) :
    NefThreshold j b' mu := by
  intro τ
  have hg : 0 ≤ gap j mu τ := gap_nonneg_of_dominant hj1 hjN hd τ
  calc 4 * (Fintype.card Ψ : ℝ) * ‖mu‖ ≤ (b - 2) * gap j mu τ := h τ
    _ ≤ (b' - 2) * gap j mu τ := mul_le_mul_of_nonneg_right (by linarith) hg

theorem RootTower.nefFib_of_nefThreshold :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.ModelNefStatement → T.M2 →
      ∀ (B : ℕ) (c : T.Comp) (mu : Wt Ψ N), Dominant mu → NefThreshold T.j B mu →
        (T.M B c).NefFib mu 0 := by
  intro Ψ _ _ N T h1 h2 B c mu hd hB p hp
  by_cases hS : T.InS B p
  · exact h1 B c p hS mu hd
  · have hBp : B < p := by
      by_contra hc
      exact hS (show p.Prime ∧ (p ≤ B ∨ p ∈ T.bad) from ⟨hp, Or.inl (not_lt.mp hc)⟩)
    refine h2 B c p hp hS mu hd ?_
    exact NefThreshold.mono T.j_pos T.j_lt hd (by exact_mod_cast hBp.le) hB

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenNumLinear
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem genNum_linear : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ H H' : MvPolynomial σ ℝ, genNum F V cls (H + H') Q = genNum F V cls H Q + genNum F V cls H' Q) ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), genNum F V cls (C c * H) Q = c * genNum F V cls H Q) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), genNum F V cls (∑ a ∈ s, H a) Q = ∑ a ∈ s, genNum F V cls (H a) Q) ∧ ∀ (μ : σ →₀ ℕ) (c : ℝ), genNum F V cls (monomial μ c) Q = c * (intNumL F V (classList cls μ ++ Q) : ℝ) := by
  exact @BaseChangeColon.genNum_linear_in_polynomial

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConj
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem combLine_smooth_conj :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), ((∀ j, IsSmoothHerm (ℓ j)) → IsSmoothHerm (combLine ℓ n)) ∧ ((∀ j, IsConjInvariantH (ℓ j)) → IsConjInvariantH (combLine ℓ n)) ∧ IsSmoothHerm (trivLine ι) := by
  intro K _ ι _ J _ ℓ n
  refine ⟨fun hs => ?_, fun hc => ?_, ?_⟩
  · refine contDiffOn_prod fun j _ => ?_
    intro z hz
    have h0 : (ℓ j).h z ≠ 0 := ((ℓ j).pos z hz).ne'
    have hf := hs j z hz
    have key : ∀ m : ℤ, ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (ℓ j).h z ^ m)
        {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} z := by
      intro m
      cases m with
      | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
      | negSucc k =>
        simp only [zpow_negSucc]
        exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)
    exact key _
  · intro z
    show (∏ j, (ℓ j).h _ ^ n j) = ∏ j, (ℓ j).h z ^ n j
    simp only [hc _ z]
  · exact contDiffOn_const

end GlobalTheory.CompanionTheory.Ar.Top
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HomogeneousClassSubstitution
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem subst_abs_list : ∀ (G : Type) [AddCommGroup G] (d : ℕ) (n : List G → ℝ), (∀ l l', l.Perm l' → n l = n l') → (∀ b b' l, l.length + 1 = d → n ((b + b') :: l) = n (b :: l) + n (b' :: l)) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → G) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List G, m + Q.length = d → (∑ μ ∈ H.support, H.coeff μ * n ((μ.toMultiset.map fun t => ∑ i, M t i • cls i).toList ++ Q)) = ∑ μ ∈ (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).support, (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).coeff μ * n ((μ.toMultiset.map cls).toList ++ Q) := by
  exact @BaseChangeColon.homogeneous_sum_linear_change_classes

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalPairValueLinear
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.ValLin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [DecidableEq K]
  {ι : K → Type} {σ : Type}

end GlobalTheory.CompanionTheory.Ar.Num.ValLin

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem locPair_val_linear : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] (T : LocPair ι O σ) (P : Ideal (MRing ι O)), (∀ Gs Hs, T.val P (Gs + Hs) = T.val P Gs + T.val P Hs) ∧ (∀ (c : ℝ) Gs, T.val P (fun i => C c * Gs i) = c * T.val P Gs) ∧ ∀ (α : Type) (s : Finset α) (Gs : α → σ → MvPolynomial (σ ⊕ σ) ℝ), T.val P (fun i => ∑ a ∈ s, Gs a i) = ∑ a ∈ s, T.val P (Gs a) :=
  _root_.UpperTheory.Reformulated.B.Qp9.locPair_val_linear

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogDivPredLe
section
namespace GlobalTheory.CompanionTheory.Ar.Small

theorem sum_log_div_pred_le :
    ∀ (x : ℝ) (S : Finset ℕ), 1 ≤ x → (∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ x) →
      ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ Real.log x + 17 / 5 := by
  intro x S hx hS
  have hsplit : ∀ p ∈ S, Real.log p / ((p : ℝ) - 1)
      = Real.log p / p + Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1.two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have h1 : ∑ p ∈ S, Real.log p / (p : ℝ) ≤ Real.log x + Real.log 4 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (_root_.GlobalTheory.CompanionTheory.Ar.Small.mertens_first_log_four x hx)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Iic]
      exact ⟨Nat.le_floor (hS p hp).2, (hS p hp).1⟩
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have h2 : ∑ p ∈ S, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 :=
    _root_.GlobalTheory.CompanionTheory.Ar.Small.log_tail S (fun p hp => (hS p hp).1.two_le)
  have hl4 : Real.log 4 < 7 / 5 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h := Real.log_two_lt_d9
    norm_num at h
    linarith
  linarith

end GlobalTheory.CompanionTheory.Ar.Small
end

