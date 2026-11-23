module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.WeilBound.CoreStatements.IntegralPointHeights.NegativeIntegralPoints.FlDegFree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerArithAgreement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import Development.WeilBound.CoreStatements.FlagImmersions.TestPolynomialShiftValues

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreePolynomialEval
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_degree_polynomial_eval : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (lam : Wt Ψ N), 2 ≤ N → eval (fun x => lam x.1 x.2) (PB.degFlPoly Ψ N) = flagDeg lam := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IndefiniteRowSideFullHecke.degFlPoly_eval' | exact GlobalTheory.CompanionTheory.Ar.IndefiniteRowSideFullHecke.degFlPoly_eval'
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerConvI2
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.ConvergenceI2

theorem sum_shift_le {N : ℕ} (l : Fin N → ℝ) :
    ∑ i : Fin N, (if h : (i : ℕ) + 1 < N then |l ⟨(i : ℕ) + 1, h⟩| else 0) ≤ ∑ i, |l i| := by
  let F : ℕ → ℝ := fun i => if h : i < N then |l ⟨i, h⟩| else 0
  have hF : ∀ i, 0 ≤ F i := by
    intro i
    simp only [F]
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  have e1 : ∑ i : Fin N, (if h : (i : ℕ) + 1 < N then |l ⟨(i : ℕ) + 1, h⟩| else 0) =
      ∑ i ∈ Finset.range N, F (i + 1) := by
    rw [Finset.sum_range]
  have e2 : ∑ i : Fin N, |l i| = ∑ i ∈ Finset.range N, F i := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [F]
  have e3 : ∑ i ∈ Finset.range (N + 1), F i = ∑ i ∈ Finset.range N, F (i + 1) + F 0 :=
    Finset.sum_range_succ' F N
  have e4 : ∑ i ∈ Finset.range (N + 1), F i = ∑ i ∈ Finset.range N, F i + F N :=
    Finset.sum_range_succ F N
  have e5 : F N = 0 := by simp [F]
  rw [e1, e2]
  linarith [hF 0]

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem abs_gap_le (lam : Wt Ψ N) (τ : Ψ) (i : Fin N) :
    |PB.gap (fun x : Ψ × Fin N => lam x.1 x.2) (τ, i)| ≤
      |lam τ i| + (if h : (i : ℕ) + 1 < N then |lam τ ⟨(i : ℕ) + 1, h⟩| else 0) := by
  by_cases h : (i : ℕ) + 1 < N
  · simp only [PB.gap, PB.gapX, dif_pos h, map_sub, eval_X]
    exact abs_sub _ _
  · simp [PB.gap, PB.gapX, dif_neg h]

theorem sum_abs_gapS_le (lam : Wt Ψ N) (u : ℝ) :
    ∑ o, |PB.gapS (fun x : Ψ × Fin N => lam x.1 x.2) u o| ≤ 2 * l1 lam + |u| := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  have h1 : ∀ τ : Ψ, ∑ i : Fin N, |PB.gapS (fun x : Ψ × Fin N => lam x.1 x.2) u (some (τ, i))| ≤
      2 * ∑ i, |lam τ i| := by
    intro τ
    calc ∑ i : Fin N, |PB.gapS (fun x : Ψ × Fin N => lam x.1 x.2) u (some (τ, i))|
        ≤ ∑ i : Fin N, (|lam τ i| + (if h : (i : ℕ) + 1 < N then |lam τ ⟨(i : ℕ) + 1, h⟩| else 0)) :=
          Finset.sum_le_sum fun i _ => abs_gap_le lam τ i
      _ ≤ 2 * ∑ i, |lam τ i| := by
          rw [Finset.sum_add_distrib]
          linarith [sum_shift_le (lam τ)]
  have h2 := Finset.sum_le_sum fun τ (_ : τ ∈ (Finset.univ : Finset Ψ)) => h1 τ
  rw [← Finset.mul_sum] at h2
  have h3 : PB.gapS (fun x : Ψ × Fin N => lam x.1 x.2) u none = u := rfl
  rw [h3]
  unfold l1
  linarith

theorem l1_sub_smul_le (lam nu : Wt Ψ N) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    l1 (lam - s • nu) ≤ l1 lam + l1 nu := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have e : (lam - s • nu) τ i = lam τ i - s * nu τ i := rfl
  rw [e]
  have h2 : |s * nu τ i| ≤ |nu τ i| := by
    rw [abs_mul, abs_of_nonneg h0]
    exact mul_le_of_le_one_left (abs_nonneg _) h1
  linarith [abs_sub (lam τ i) (s * nu τ i)]

end GlobalTheory.CompanionTheory.Ar.Top.ConvergenceI2

namespace GlobalTheory.CompanionTheory.Ar.Top


open ConvergenceI2 in
theorem real_tower_convergence_I2 : PB.AgreementPos → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), T.Conv II ∧ T.I2 II := by
  intro hAg hIn II hII Ψ _ _ N T R
  have hpos : ∀ c, 0 < (R.Sys c).t₀ := fun c => ((R.Sys c).reg none).1
  refine ⟨fun B c => ?_, fun abelian₂ => ?_⟩
  · obtain ⟨C₃, s₀, -, h⟩ := hAg hIn (dimFl Ψ N) (Option (Ψ × Fin N)) (R.Sys c) 0 (hpos c)
    have hc := (h II hII (T.M B c).K (T.M B c).ι (T.M B c).P (R.tie B c).Re).1
    exact ((_root_.GlobalTheory.CompanionTheory.Ar.Top.RootNum.arith_degrees hIn II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c) 0 0).2.2 hc (hpos c)).1
  · have hex := fun c => hAg hIn (dimFl Ψ N) (Option (Ψ × Fin N)) (R.Sys c) (2 * (abelian₂ + l1 T.nu) + 1) (hpos c)
    choose C₃ s₀ hs₀ h using hex
    have hne : (Finset.univ : Finset T.Comp).Nonempty := Finset.univ_nonempty
    have hinf : 0 < Finset.univ.inf' hne s₀ := (Finset.lt_inf'_iff hne).2 fun c _ => hs₀ c
    refine ⟨min 1 (Finset.univ.inf' hne s₀), lt_min one_pos hinf, ∑ c, |C₃ c|, ?_⟩
    intro B _ c lam s hl hs hs1 _
    have hs_one : s ≤ 1 := hs1.trans (min_le_left _ _)
    have hs_c : s ≤ s₀ c := (hs1.trans (min_le_right _ _)).trans (Finset.inf'_le _ (Finset.mem_univ c))
    have hA := h c II hII (T.M B c).K (T.M B c).ι (T.M B c).P (R.tie B c).Re
    obtain ⟨ht, hb⟩ := hA.2 s hs hs_c
    have key := _root_.GlobalTheory.CompanionTheory.Ar.Top.RootNum.arith_degrees hIn II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c) (T.lamS lam s) s
    have e1 := key.2.1 _ (Real.exp_pos _) ht
    have e2 := (key.2.2 hA.1 (hpos c)).2
    have hk : (1 : ℝ) ≤ ((T.M B c).kA : ℝ) := by exact_mod_cast (T.M B c).kA_pos
    have hu : |s / ((T.M B c).kA : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg hs.le (by linarith))]
      exact (div_le_one (by linarith)).2 (hs_one.trans hk)
    have hsum : ∑ o, |PB.gapS (fun x : Ψ × Fin N => T.lamS lam s x.1 x.2) (s / ((T.M B c).kA : ℝ)) o| ≤
        2 * (abelian₂ + l1 T.nu) + 1 := by
      have h1 := sum_abs_gapS_le (T.lamS lam s) (s / ((T.M B c).kA : ℝ))
      have h2 : l1 (T.lamS lam s) ≤ l1 lam + l1 T.nu := l1_sub_smul_le lam T.nu s hs.le hs_one
      linarith
    have hfin := hb _ hsum
    rw [← e1, ← e2] at hfin
    have hn : (1 : ℝ) ≤ (R.n c : ℝ) := by exact_mod_cast key.1
    have hC : C₃ c ≤ ∑ c, |C₃ c| :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun c => |C₃ c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c))
    set a := (T.M B c).arFun II (Real.exp (-(s ^ 2)⁻¹)) (linA (T.lamS lam s) s ^ (dimFl Ψ N + 1)) with ha
    set p := (T.M B c).PP II (linA (T.lamS lam s) s ^ (dimFl Ψ N + 1)) with hp
    have h3 : |a - p| ≤ (R.n c : ℝ) * |a - p| := le_mul_of_one_le_left (abs_nonneg _) hn
    have h4 : (R.n c : ℝ) * |a - p| = |(R.n c : ℝ) * a - (R.n c : ℝ) * p| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (R.n c : ℝ))]
    have h5 : C₃ c * s ≤ (∑ c, |C₃ c|) * s := mul_le_mul_of_nonneg_right hC hs.le
    show |a - p| ≤ _
    linarith

end GlobalTheory.CompanionTheory.Ar.Top
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerI1
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem linA_eq (c : Option (Ψ × Fin N) → ℝ) :
    linA (fun τ i => c (some (τ, i))) (-c none) = -∑ x, C (c x) * X x := by
  rw [Fintype.sum_option]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [linA, toA, linRoot, map_neg, map_sum, map_mul, rename_C, rename_X, neg_add_rev, C_neg]
  simp only [Prod.mk.eta]
  ring

def scaleNone (u : ℝ) (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) : MvPolynomial (Option (Ψ × Fin N)) ℝ :=
  ∑ m ∈ Q.support, monomial m (u ^ m none * Q.coeff m)

theorem coeff_scaleNone (u : ℝ) (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) :
    (scaleNone u Q).coeff m = u ^ m none * Q.coeff m := by
  classical
  rw [scaleNone, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' Q.support m]
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, mul_zero]

theorem eval_scaleNone (u : ℝ) (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (c : Option (Ψ × Fin N) → ℝ) :
    eval c (scaleNone u Q) = eval (fun o : Option (Ψ × Fin N) => o.elim (u * c none) fun p => c (some p)) Q := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [scaleNone, map_sum, eval_eq']
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [Fintype.prod_option, Option.elim, mul_pow]
  ring

theorem abs_le_coeff (d : ℕ) (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ)
    (h : ∀ (lam : Wt Ψ N) (s : ℝ), (n : ℝ) * Φ (linA lam s ^ d) = eval (PB.gapS (fun x => lam x.1 x.2) (s / k)) Q)
    (m : Option (Ψ × Fin N) →₀ ℕ) (hm : m.degree = d) :
    |Φ (monomial m 1)| ≤ |(PB.toWtS Q).coeff m| := by
  obtain ⟨Pl, -, hev, -, hle⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.polarisation_functional (Option (Ψ × Fin N)) d Φ
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set u : ℝ := -(k : ℝ)⁻¹ with hu
  have heq : C (n : ℝ) * Pl = scaleNone u (PB.toWtS Q) := by
    refine MvPolynomial.funext fun c => ?_
    have hs : -c none / (k : ℝ) = u * c none := by rw [hu]; ring
    rw [eval_scaleNone, map_mul, eval_C, hev, ← linA_eq, h, PB.eval_toWtS_gapS, hs]
  have hco := congrArg (fun p : MvPolynomial (Option (Ψ × Fin N)) ℝ => p.coeff m) heq
  rw [coeff_C_mul, coeff_scaleNone] at hco
  have hu1 : |u| ≤ 1 := by
    rw [hu, abs_neg, abs_of_pos (inv_pos.2 (by linarith))]
    exact inv_le_one_of_one_le₀ hkR
  calc |Φ (monomial m 1)| ≤ |Pl.coeff m| := hle m hm
    _ ≤ (n : ℝ) * |Pl.coeff m| := le_mul_of_one_le_left (abs_nonneg _) hnR
    _ = |(n : ℝ) * Pl.coeff m| := by rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)]
    _ = |u| ^ m none * |(PB.toWtS Q).coeff m| := by rw [hco, abs_mul, abs_pow]
    _ ≤ |(PB.toWtS Q).coeff m| := mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hu1)

theorem PP_monomial_of_ne (II : IntersectionSystem) (M : RootModel Ψ N) (m : Option (Ψ × Fin N) →₀ ℕ)
    (hm : m.degree ≠ dimFl Ψ N + 1) : M.PP II (monomial m 1) = 0 := by
  have h1 : (monomial m 1 : RPA Ψ N) = basisMonomials (Option (Ψ × Fin N)) ℝ m := by simp
  rw [h1, RootModel.PP, Module.Basis.constr_basis]
  have h2 : (fun t => M.arMono II t m) = fun _ => 0 := by
    funext t
    simp [RootModel.arMono, hm]
  rw [h2]
  exact tendsto_const_nhds.limUnder_eq

theorem tower_I1_of_reference_linked : PB.Coefficients → PB.AgreementPos → PB.Inputs → ∀ II : IntersectionSystem,
    IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N)
    (R : RealTower T), R.RefLinked II → T.I1 II := by
  intro hCo hAg hI II hII Ψ _ _ N T R hL
  obtain ⟨Cl, thH, Pfix, hth, hlink⟩ := hL
  have hpos : ∀ c, 0 < (R.Sys c).t₀ := fun c => ((R.Sys c).reg none).1
  choose C₂ hC₂ using fun c => hCo hI (dimFl Ψ N) N Ψ (R.Sys c) (thH c) (hth c)
  set A : ℝ := ∑ c, ∑ m ∈ (Pfix c).support, |(Pfix c).coeff m| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hAle : ∀ c m, |(Pfix c).coeff m| ≤ A := by
    intro c m
    by_cases hm : m ∈ (Pfix c).support
    · calc |(Pfix c).coeff m| ≤ ∑ m ∈ (Pfix c).support, |(Pfix c).coeff m| :=
            Finset.single_le_sum (f := fun m => |(Pfix c).coeff m|) (fun _ _ => abs_nonneg _) hm
        _ ≤ A := Finset.single_le_sum (f := fun c => ∑ m ∈ (Pfix c).support, |(Pfix c).coeff m|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ c)
    · rw [notMem_support_iff.1 hm, abs_zero]
      exact hA0
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hS0 : 0 ≤ ∑ c, |C₂ c| * |Cl| := Finset.sum_nonneg fun _ _ => by positivity
  unfold RootTower.I1
  refine ⟨A / Real.log 2 + ∑ c, |C₂ c| * |Cl|, fun B hB c m => ?_⟩
  have hlogB : Real.log 2 ≤ Real.log B := Real.log_le_log two_pos (by exact_mod_cast hB)
  have hlog0 : 0 ≤ Real.log B := hl2.le.trans hlogB
  by_cases hm : m.degree = dimFl Ψ N + 1
  · obtain ⟨C₃, s₀, -, hag⟩ := hAg hI _ _ (R.Sys c) 0 (hpos c)
    have htend := (hag II hII _ _ _ (R.tie B c).Re).1
    have hnum := _root_.GlobalTheory.CompanionTheory.Ar.Top.RootNum.arith_degrees hI II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c)
    have hle := abs_le_coeff (dimFl Ψ N + 1) ((T.M B c).PP II) (R.n c) (T.M B c).kA (hnum 0 0).1
      (T.M B c).kA_pos ((R.tie B c).Re.PB II) (fun lam s => ((hnum lam s).2.2 htend (hpos c)).2) m hm
    obtain ⟨K, iK, ι, iι, P, Re, Re', Sf, α, H, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hlink B hB c
    have hd := ((hC₂ c II hII K ι P Re).2 Re' Sf α H h3 h4 h5 h6 h7 h8).1 m
    rw [h1, h2] at hd
    have hsum0 : 0 ≤ ∑ p ∈ Sf, α p * Real.log p :=
      Finset.sum_nonneg fun p hp => mul_nonneg (h4 p hp).2 (Real.log_natCast_nonneg p)
    have hd2 : |((R.tie B c).Re.PBs II).coeff m - (Pfix c).coeff m| ≤ |C₂ c| * |Cl| * Real.log B := by
      calc _ ≤ C₂ c * ∑ p ∈ Sf, α p * Real.log p := hd
        _ ≤ |C₂ c| * ∑ p ∈ Sf, α p * Real.log p := mul_le_mul_of_nonneg_right (le_abs_self _) hsum0
        _ ≤ |C₂ c| * (|Cl| * Real.log B) := mul_le_mul_of_nonneg_left
            (h9.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hlog0)) (abs_nonneg _)
        _ = _ := by ring
    have hc1 : |((R.tie B c).Re.PBs II).coeff m| ≤ A + |C₂ c| * |Cl| * Real.log B := by
      have := abs_sub_abs_le_abs_sub (((R.tie B c).Re.PBs II).coeff m) ((Pfix c).coeff m)
      linarith [hAle c m]
    have hA2 : A ≤ A / Real.log 2 * Real.log B := by
      calc A = A / Real.log 2 * Real.log 2 := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hlogB (by positivity)
    have hS : |C₂ c| * |Cl| ≤ ∑ c, |C₂ c| * |Cl| :=
      Finset.single_le_sum (f := fun c => |C₂ c| * |Cl|) (fun _ _ => by positivity) (Finset.mem_univ c)
    have hS2 := mul_le_mul_of_nonneg_right hS hlog0
    calc _ ≤ |((R.tie B c).Re.PBs II).coeff m| := hle
      _ ≤ A + |C₂ c| * |Cl| * Real.log B := hc1
      _ ≤ _ := by rw [add_mul]; linarith
  · rw [PP_monomial_of_ne II _ m hm, abs_zero]
    exact mul_nonneg (add_nonneg (by positivity) hS0) hlog0

end GlobalTheory.CompanionTheory.Ar.Top.TowerOverReals
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialShiftTotal
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem testPoly_facts : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → (testPoly j : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) ∧ 0 < testDeg Ψ N j ∧ (N - j ≤ j → ∀ τ : Ψ, Sh j τ (testPoly j : RP Ψ N) = 0 ∧ Tot τ (testPoly j : RP Ψ N) = ((dimX Ψ N j : ℝ) + 1) * ((N - j : ℕ) : ℝ) * testDeg Ψ N j) ∧ (¬ N - j ≤ j → ∀ τ : Ψ, Sh j τ (testPoly j : RP Ψ N) = -(((dimX Ψ N j : ℝ) + 1) * j * testDeg Ψ N j) ∧ Tot τ (testPoly j : RP Ψ N) = -(((dimX Ψ N j : ℝ) + 1) * j * testDeg Ψ N j)) := by
  exact @RootFieldNumerics.test_polynomial_shift_values

end GlobalTheory.CompanionTheory.Ar.Top
end

