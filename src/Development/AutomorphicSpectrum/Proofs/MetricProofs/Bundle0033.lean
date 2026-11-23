module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.NonvanishingDense

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSncAdaptedChartAtPoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.LocalForm

theorem holoOn_coord {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (i : Fin e) :
    A.HoloOn ψ.source (fun y => ψ y i) := by
  intro j z hz
  exact (analyticAt_pi_iff.1 ((hψ j).1 z hz)) i

theorem exists_local_form : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSNC A L s m W → ∀ x, ∃ (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (S : Finset (Fin e)) (μ : Fin e → ℕ) (v : X → ℂ), IsCompatChart A φ ∧ x ∈ φ.source ∧ Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target ∧ φ x = 0 ∧ φ.source ⊆ L.U x ∧ (∀ i ∈ S, 1 ≤ μ i) ∧ A.HoloOn φ.source v ∧ (∀ y ∈ φ.source, v y ≠ 0) ∧ ∀ y ∈ φ.source, s x y = v y * ∏ i ∈ S, φ y i ^ μ i := by
  intro e X _ A L s nb m W hsnc x
  obtain ⟨ψ, hψ, hxψ, hψU, σ, hinj, -, u, hu, hu0, hs⟩ := hsnc x
  obtain ⟨c, hc⟩ : ∃ c, c = ψ x := ⟨_, rfl⟩
  have hev : ∀ᶠ z in 𝓝 c, z ∈ ψ.target ∧ ∀ i, c i ≠ 0 → z i ≠ 0 := by
    have h1 : ∀ᶠ z in 𝓝 c, z ∈ ψ.target := ψ.open_target.mem_nhds (hc ▸ ψ.map_source hxψ)
    refine h1.and ?_
    rw [eventually_all]
    intro i
    by_cases h : c i = 0
    · simp [h]
    · filter_upwards [((continuous_apply i).continuousAt (x := c)).eventually_ne h] with z hz _
      exact hz
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hV : IsOpen (ψ.source ∩ ψ ⁻¹' Metric.ball c r) :=
    ψ.continuousOn.isOpen_inter_preimage ψ.open_source Metric.isOpen_ball
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have ha : (3 / r : ℂ) ≠ 0 := by simpa using hrC
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (ψ.restrOpen _ hV).transHomeomorph (pa_aff (3 / r : ℂ) ha c) := ⟨_, rfl⟩
  have hφc : IsCompatChart A φ := hφ ▸ pa_compat_aff A _ (pa_compat_restr A _ hψ _ hV) _ ha _
  have hsrc : ∀ y ∈ φ.source, y ∈ ψ.source ∧ ψ y ∈ Metric.ball c r := by
    intro y hy
    subst hφ
    exact ⟨hy.1, hy.2.2⟩
  have hφapp : ∀ y, φ y = (3 / r : ℂ) • (ψ y - c) := by
    intro y
    subst hφ
    rfl
  have hxφ : x ∈ φ.source := by
    subst hφ
    refine ⟨hxψ, hxψ, ?_⟩
    show ψ x ∈ Metric.ball c r
    rw [← hc]
    exact Metric.mem_ball_self hr
  have htarget : Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target := by
    intro z hz
    subst hφ
    set w : Fin e → ℂ := (3 / r : ℂ)⁻¹ • z + c with hw
    have hwb : w ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm, hw, add_sub_cancel_right, norm_smul]
      have hz' : ‖z‖ ≤ 2 := by simpa using hz
      have : ‖(3 / r : ℂ)⁻¹‖ = r / 3 := by
        rw [norm_inv, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
        norm_num
      rw [this]
      nlinarith
    have hwT : w ∈ ψ.target := (hball _ hwb).1
    have hmem : w ∈ (ψ.restrOpen _ hV).target :=
      ⟨hwT, ψ.map_target hwT, by simpa [ψ.right_inv hwT] using hwb⟩
    exact hmem

  let g : Fin nb → X → ℂ := fun k y => (σ k).elim 1 (fun i => ψ y i ^ m k)
  have hg : ∀ k y, (match σ k with
      | some i => ψ y i ^ m k
      | none => 1) = g k y := by
    intro k y
    simp only [g]
    cases σ k <;> rfl
  have hgholo : ∀ k, A.HoloOn ψ.source (g k) := by
    intro k j z hz
    simp only [g]
    cases σ k with
    | none => exact analyticAt_const
    | some i => exact (holoOn_coord A ψ hψ i j z hz).pow (m k)
  let K : Finset (Fin nb) := Finset.univ.filter (fun k => ∃ i, σ k = some i ∧ c i = 0 ∧ 1 ≤ m k)
  let S : Finset (Fin e) := Finset.univ.filter (fun i => c i = 0 ∧ ∃ k, σ k = some i ∧ 1 ≤ m k)
  let μ : Fin e → ℕ := fun i => ∑ k, if σ k = some i then m k else 0
  have hμ : ∀ k i, σ k = some i → μ i = m k := by
    intro k i hk
    refine (Finset.sum_eq_single k (fun b _ hb => if_neg fun h => hb (hinj _ _ i h hk))
      (by simp)).trans (if_pos hk)
  have hKS : ∀ y, ∏ k ∈ K, g k y = ∏ i ∈ S, ψ y i ^ μ i := by
    intro y
    refine Finset.prod_bij (fun k hk => Classical.choose (Finset.mem_filter.1 hk).2) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2, k, h1, h3⟩
    · intro k hk k' hk' hkk
      obtain ⟨h1, -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
      obtain ⟨h1', -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hk').2
      exact hinj k k' _ h1 (hkk ▸ h1')
    · intro i hi
      obtain ⟨-, h0, k, hk, hm⟩ := Finset.mem_filter.1 hi
      have hkK : k ∈ K := Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hk, h0, hm⟩
      refine ⟨k, hkK, ?_⟩
      obtain ⟨h1, -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hkK).2
      exact Option.some.inj (h1.symm.trans hk)
    · intro k hk
      obtain ⟨h1, -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
      have key : ∀ i, σ k = some i → g k y = ψ y i ^ μ i := by
        intro i hi
        simp only [g]
        rw [hi, hμ k i hi]
        rfl
      exact key _ h1
  let T : Finset (Fin nb) := Finset.univ.filter
    (fun k => ¬ ∃ i, σ k = some i ∧ c i = 0 ∧ 1 ≤ m k)
  let C : ℂ := ((r : ℂ) / 3) ^ (∑ i ∈ S, μ i)
  have hC : C ≠ 0 := pow_ne_zero _ (div_ne_zero hrC (by norm_num))
  refine ⟨φ, S, μ, fun y => u y * C * ∏ k ∈ T, g k y, hφc, hxφ, htarget, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hφapp, ← hc, sub_self, smul_zero]
  · exact fun y hy => hψU (hsrc y hy).1
  · intro i hi
    obtain ⟨-, -, k, hk, hm⟩ := Finset.mem_filter.1 hi
    rw [hμ k i hk]
    exact hm
  · intro j z hz
    have hz' : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source := ⟨hz.1, (hsrc _ hz.2).1⟩
    exact ((hu j z hz').mul analyticAt_const).mul
      (Finset.analyticAt_fun_prod _ fun k _ => hgholo k j z hz')
  · intro y hy
    obtain ⟨hy1, hy2⟩ := hsrc y hy
    refine mul_ne_zero (mul_ne_zero (hu0 y hy1) hC) (Finset.prod_ne_zero_iff.2 ?_)
    intro k hk
    have hk' := (Finset.mem_filter.1 hk).2
    simp only [g]
    cases hσ : σ k with
    | none => exact one_ne_zero
    | some i =>
      by_cases hm : m k = 0
      · simp [hm]
      · have hci : c i ≠ 0 := fun h0 => hk' ⟨i, hσ, h0, Nat.one_le_iff_ne_zero.2 hm⟩
        exact pow_ne_zero _ ((hball _ hy2).2 i hci)
  · intro y hy
    obtain ⟨hy1, -⟩ := hsrc y hy
    have hcoord : ∀ i ∈ S, ψ y i = ((r : ℂ) / 3) * φ y i := by
      intro i hi
      obtain ⟨-, h0, -⟩ := Finset.mem_filter.1 hi
      rw [hφapp]
      simp only [Pi.smul_apply, Pi.sub_apply, h0, sub_zero, smul_eq_mul]
      field_simp
    have hsplit : ∏ k, g k y = (∏ k ∈ K, g k y) * ∏ k ∈ T, g k y :=
      (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
    have hmono : ∏ i ∈ S, ψ y i ^ μ i = C * ∏ i ∈ S, φ y i ^ μ i := by
      rw [Finset.prod_congr rfl (fun i hi => by rw [hcoord i hi, mul_pow]),
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have h2 : s x y = u y * ∏ k, g k y := by
      rw [hs y hy1]
      congr 1
      exact Finset.prod_congr rfl (fun k _ => hg k y)
    show s x y = u y * C * (∏ k ∈ T, g k y) * ∏ i ∈ S, φ y i ^ μ i
    rw [h2, hsplit, hKS, hmono]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.LocalForm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeightPolynomialWeightForm
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace FlLines

section Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_integralCombination_of_mem_completedLattice {A B D : Type} [Fintype A] [Fintype B] [Fintype D] (ca : A → ℤ) (bb : A → D → ℤ) (P : B → ℤ)
    (G : D → B → ℤ) :
    ∑ k, (∑ a, ca a * bb a k) * ∑ w, P w * G k w = ∑ a, ∑ w, (P w * ca a) * ∑ k, bb a k * G k w := by
  have h1 : ∀ k, (∑ a, ca a * bb a k) * ∑ w, P w * G k w = ∑ a, ∑ w, (ca a * bb a k) * (P w * G k w) :=
    fun k => Finset.sum_mul_sum _ _ _ _
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun k _ => by ring

theorem geoNum_polar {σ : Type} [Fintype σ] (n : ℕ) (V : Ideal (MRing ι)) (c : Fin n → σ → ℤ) (b : σ → K → ℤ) :
    geoNum n V (fun r k => ∑ a, c r a * b a k) =
      ∑ w : Fin n → σ, (∏ r, c r (w r)) * geoNum n V (fun r => b (w r)) := by
  classical
  induction n generalizing V with
  | zero =>
    have h : ∀ a a' : Fin 0 → K → ℤ, geoNum 0 V a = geoNum 0 V a' := fun a a' => by
      rw [Subsingleton.elim a a']
    simp only [Fintype.sum_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    exact h _ _
  | succ n ih =>
    by_cases hV : IsRelevant V
    · rw [← (Fin.snocEquiv (fun _ => σ)).sum_comp, Fintype.sum_prod_type]
      simp only [geoNum, dif_pos hV]
      have hin : ∀ (a : σ) (w' : Fin n → σ),
          Fin.init (fun r => b ((Fin.snocEquiv (fun _ => σ)) (a, w') r)) = fun r => b (w' r) := by
        intro a w'
        funext r
        simp [Fin.init, Fin.snocEquiv]
      have hla : ∀ (a : σ) (w' : Fin n → σ), (Fin.snocEquiv (fun _ => σ)) (a, w') (Fin.last n) = a := by
        intro a w'
        simp [Fin.snocEquiv]
      have hca : ∀ (a : σ) (w' : Fin n → σ) (r : Fin n),
          (Fin.snocEquiv (fun _ => σ)) (a, w') r.castSucc = w' r := by
        intro a w' r
        simp [Fin.snocEquiv]
      have hi2 : Fin.init (fun r k => ∑ a, c r a * b a k) =
          fun (r : Fin n) k => ∑ a, c r.castSucc a * b a k := by
        funext r k
        simp [Fin.init]
      simp only [hin, hla, Fin.prod_univ_castSucc, hca, hi2]
      have e : ∀ (k : K) (f : Ideal (MRing ι) → ℤ),
          ∑ᶠ W ∈ divSupp V (X ⟨k, (hV k).choose⟩ : MRing ι), f W =
            ∑ W ∈ (divSupp_finite V (X ⟨k, (hV k).choose⟩ : MRing ι)).toFinset, f W :=
        fun k f => finsum_mem_eq_finite_toFinset_sum f (divSupp_finite _ _)
      simp only [e]
      simp only [ih _ (fun r => c r.castSucc)]
      rw [← exists_integralCombination_of_mem_completedLattice (fun a => c (Fin.last n) a) b (fun w' : Fin n → σ => ∏ r, c r.castSucc (w' r))]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun W _ => ?_
      ring
    · have e : ∀ a, geoNum (n + 1) V a = 0 := fun a => by simp only [geoNum, dif_neg hV]
      simp [e]

theorem degSum_polar {σ : Type} [Fintype σ] (e : ℕ) (S : Set (Ideal (MRing ι))) (hS : S.Finite)
    (m : Ideal (MRing ι) → ℝ) (lam : σ → ℤ) (b : σ → K → ℤ) :
    ∑ w : Fin e → σ, (∏ r, (lam (w r) : ℝ)) * ∑ᶠ V ∈ S, m V * (geoNum e V (fun r => b (w r)) : ℝ) =
      ∑ᶠ V ∈ S, m V * (geoNum e V (fun _ k => ∑ a, lam a * b a k) : ℝ) := by
  have e' : ∀ f : Ideal (MRing ι) → ℝ, ∑ᶠ V ∈ S, f V = ∑ V ∈ hS.toFinset, f V :=
    fun f => finsum_mem_eq_finite_toFinset_sum f hS
  have hp : ∀ V : Ideal (MRing ι), geoNum e V (fun _ k => ∑ a, lam a * b a k) =
      ∑ w : Fin e → σ, (∏ r, lam (w r)) * geoNum e V (fun r => b (w r)) :=
    fun V => geoNum_polar e V (fun _ => lam) b
  simp only [e', hp]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun V _ => Finset.sum_congr rfl fun w _ => ?_
  ring

end Geo

section Wt

variable {Ψ : Type} {N : ℕ}

def gapZ (lam : Ψ × Fin N → ℤ) (p : Ψ × Fin N) : ℤ :=
  lam p - if h : (p.2 : ℕ) + 1 < N then lam (p.1, ⟨(p.2 : ℕ) + 1, h⟩) else 0

theorem gap_cast (lam : Ψ × Fin N → ℤ) (p : Ψ × Fin N) :
    gap (fun q => (lam q : ℝ)) p = (gapZ lam p : ℝ) := by
  unfold gap gapX gapZ
  split_ifs <;> simp

theorem formPoly_eq_toWt [Fintype Ψ] (n : ℕ) (ax ay : (Fin n → Ψ × Fin N) → ℝ)
    (h : ∀ lam : Ψ × Fin N → ℤ, ∑ w, (∏ r, (lam (w r) : ℝ)) * ax w = ∑ w, (∏ r, (gapZ lam (w r) : ℝ)) * ay w) :
    formPoly n ax = toWt (formPoly n ay) := by
  refine MvPolynomial.funext_set (fun _ => Set.range (fun z : ℤ => (z : ℝ)))
    (fun _ => Set.infinite_range_of_injective Int.cast_injective) ?_
  intro x hx
  choose lam hlam using fun i => hx i (Set.mem_univ i)
  have hxl : x = fun p => (lam p : ℝ) := funext fun p => (hlam p).symm
  rw [hxl, eval_toWt_gap, (formPoly_isHomogeneous_and_eval _ n ax).2, (formPoly_isHomogeneous_and_eval _ n ay).2]
  simp only [gap_cast]
  simpa only [mul_comm] using h lam

end Wt

section Flag

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

def yDeg (p : Ψ × Fin N) : FlBlock Ψ N → ℤ :=
  fun q => if q.1 = p.1 ∧ (q.2 : ℕ) = p.2 then 1 else 0

variable {Ψ N}

theorem deg_abel (lam : Ψ × Fin N → ℤ) (q : FlBlock Ψ N) :
    ∑ p, lam p * xDeg Ψ N p q = ∑ p, gapZ lam p * yDeg Ψ N p q := by
  classical
  obtain ⟨τ, i⟩ := q
  have hi : (i : ℕ) + 1 < N := by have := i.2; omega
  have hi0 : (i : ℕ) < N := by omega
  have hx : ∀ p : Ψ × Fin N, xDeg Ψ N p (τ, i) =
      (if p = (τ, ⟨(i : ℕ), hi0⟩) then 1 else 0) - (if p = (τ, ⟨(i : ℕ) + 1, hi⟩) then 1 else 0) := by
    rintro ⟨τ', a⟩
    by_cases ht : τ = τ'
    · subst ht
      simp [xDeg, Fin.ext_iff, eq_comm]
    · simp [xDeg, ht, Ne.symm ht]
  have hy : ∀ p : Ψ × Fin N, yDeg Ψ N p (τ, i) = if p = (τ, ⟨(i : ℕ), hi0⟩) then 1 else 0 := by
    rintro ⟨τ', a⟩
    by_cases ht : τ = τ'
    · subst ht
      simp [yDeg, Fin.ext_iff, eq_comm]
    · simp [yDeg, ht, Ne.symm ht]
  simp only [hx, hy, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp [gapZ, hi]

theorem deg_abel_smul (lam : Ψ × Fin N → ℤ) :
    ∑ p, lam p • xDeg Ψ N p = ∑ p, gapZ lam p • yDeg Ψ N p := by
  funext q
  simpa [Finset.sum_apply] using deg_abel lam q

end Flag

end FlLines

open FlLines

theorem flLines_polys : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) → hFlPoly Ψ N II = toWt (formPoly (antisymDegree Ψ N + 1) fun w => II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N + 1) fun r => yLineFl Ψ N (w r)) ∧ degFlPoly Ψ N = toWt (formPoly (antisymDegree Ψ N) fun w => ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) fun _ => 1) := by
  intro hIn II hII Ψ _ _ _ N _ hP
  have hI := hII.1 (FlBlock Ψ N) (FlIdx Ψ N)
  refine ⟨formPoly_eq_toWt _ _ _ fun lam => ?_, formPoly_eq_toWt _ _ _ fun lam => ?_⟩
  · have h1 := FlagHeightMultilinear.I_fsHerm_sum hI hP (fun _ => lam) (xDeg Ψ N)
    have h2 := FlagHeightMultilinear.I_fsHerm_sum hI hP (fun _ => gapZ lam) (yDeg Ψ N)
    rw [deg_abel_smul lam, h2] at h1
    exact h1.symm
  · set S : Set (Ideal (MRing (FlIdx Ψ N))) := divSupp (PFl Ψ N) (C (((2 : ℕ) : ℤ))) with hSdef
    have hS : S.Finite := divSupp_finite _ _
    set m : Ideal (MRing (FlIdx Ψ N)) → ℝ :=
      fun V => (multAt (PFl Ψ N ⊔ Ideal.span {C (((2 : ℕ) : ℤ))}) V : ℝ) with hm
    have hD : ∀ L : Fin (antisymDegree Ψ N) → HermLine (FlIdx Ψ N), (∀ j, IsSmoothHerm (L j)) →
        ptsIntegral (PFl Ψ N) (pot L) (fun _ => 1) = ∑ᶠ V ∈ S, m V * (geoNum _ V (fun j => (L j).a) : ℝ) :=
      fun L hL => hIn.degree _ _ _ _ L 2 hP hL Nat.prime_two
    have hsm : ∀ a : FlBlock Ψ N → ℤ, IsSmoothHerm (fsHerm (FlIdx Ψ N) a) :=
      FlagHeightMultilinear.isSmoothHerm_fsHerm
    have h1 := degSum_polar (antisymDegree Ψ N) S hS m lam (xDeg Ψ N)
    have h2 := degSum_polar (antisymDegree Ψ N) S hS m (gapZ lam) (yDeg Ψ N)
    have hv : (fun (_ : Fin (antisymDegree Ψ N)) k => ∑ a, lam a * xDeg Ψ N a k) =
        fun _ k => ∑ a, gapZ lam a * yDeg Ψ N a k := by
      funext _ k
      exact deg_abel lam k
    rw [hv, ← h2] at h1
    have ex : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N,
        ptsIntegral (PFl Ψ N) (pot fun r => xLine Ψ N (w r)) (fun _ => 1) =
          ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => xDeg Ψ N (w r)) : ℝ) :=
      fun w => hD _ fun _ => hsm _
    have ey : ∀ w : Fin (antisymDegree Ψ N) → Ψ × Fin N,
        ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) (fun _ => 1) =
          ∑ᶠ V ∈ S, m V * (geoNum _ V (fun r => yDeg Ψ N (w r)) : ℝ) :=
      fun w => hD _ fun _ => hsm _
    simp only [ex, ey]
    exact h1

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericFlagAlgebraicallyIndependent
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem IsGenericFlag.indep_twist_mul_genUp : ∀ (Ω Φ : Type) [Field Ω] [Field Φ] [Algebra Ω Φ] (Ψ : Type) (N j : ℕ) (g : Ψ → Matrix (Fin N) (Fin N) Φ) (T : Ψ → Matrix (Fin N) (Fin N) Ω), (∀ τ, IsBlockDiag j (g τ)) → IsGenericFlag Ω j g → (∀ τ, IsBlockDiag j (T τ) ∧ (T τ).det ≠ 0) → AlgebraicIndependent Ω (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ))) * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2) := by
  intro Ω Φ _ _ _ Ψ N j g T hg hgen hT
  have hTu : ∀ τ, IsUnit (T τ).det := fun τ => isUnit_iff_ne_zero.mpr (hT τ).2
  have hM : ∀ τ, IsBlockDiag j ((g τ).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j τ) :=
    fun τ => IsBlockDiag.mul (IsBlockDiag.map (hg τ) (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ))
      (genUp_blockDiag (R := Φ) τ)
  have key : ∀ (R : Type) [CommRing R] [Algebra Ω R] (f : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] R)
      (Z : Ψ → Matrix (Fin N) (Fin N) R), (∀ τ, IsBlockDiag j (Z τ)) →
      (∀ q : inertBlockIndex Ψ N j, f (X q) = Z q.1.1 q.1.2.1 q.1.2.2) →
      ∀ τ c b, f (genericBlockMatrix Ω N j τ c b) = Z τ c b := by
    intro R _ _ f Z hZ hf τ c b
    exact congrFun (congrFun (generic_block_matrix_map f.toRingHom hZ hf τ) c) b
  have hlin : ∀ (R : Type) [CommRing R] [Algebra Ω R] (f : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] R)
      (U : Matrix (Fin N) (Fin N) Ω) (G : Matrix (Fin N) (Fin N) (MvPolynomial (inertBlockIndex Ψ N j) Ω)) (a b : Fin N),
      f ((U.map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)) * G) a b)
        = (U.map (algebraMap Ω R) * G.map f) a b := by
    intro R _ _ f U G a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
  obtain ⟨φ, hφ⟩ : ∃ φ : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] MvPolynomial (inertBlockIndex Ψ N j) Ω,
      ∀ q : inertBlockIndex Ψ N j, φ (X q) = ((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2 :=
    ⟨MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => ((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2), fun q => MvPolynomial.aeval_X _ q⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] MvPolynomial (inertBlockIndex Ψ N j) Ω,
      ∀ q : inertBlockIndex Ψ N j, ψ (X q) = ((T q.1.1).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2 :=
    ⟨MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => ((T q.1.1).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2), fun q => MvPolynomial.aeval_X _ q⟩
  have hZ : ∀ τ, IsBlockDiag j ((T τ).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)) * genericBlockMatrix Ω N j τ) :=
    fun τ => IsBlockDiag.mul (IsBlockDiag.map (hT τ).1 (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)))
      (generic_block_matrix_isBlockDiag (R := Ω) τ)
  have hψg := key _ ψ _ hZ hψ
  have hGψ : ∀ τ, (genericBlockMatrix Ω N j τ).map ψ
      = (T τ).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)) * genericBlockMatrix Ω N j τ :=
    fun τ => Matrix.ext fun c b => by rw [Matrix.map_apply]; exact hψg τ c b
  have hcomp : ∀ p, ψ (φ p) = p := by
    have hc : ψ.comp φ = AlgHom.id Ω _ := by
      apply MvPolynomial.algHom_ext
      intro q
      rw [AlgHom.comp_apply, AlgHom.id_apply, hφ, hlin _ ψ, hGψ, ← Matrix.mul_assoc, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul _ (hTu _),
        show ((1 : Matrix (Fin N) (Fin N) Ω).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))) = 1 from
          (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)).mapMatrix.map_one,
        Matrix.one_mul, generic_block_matrix_apply]
    intro p
    exact DFunLike.congr_fun hc p
  have hx := IsGenericFlag.indep_mul_genUp hg hgen
  have hxg := key _ (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
      ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2)) _ hM
    (fun q => MvPolynomial.aeval_X _ q)
  have hGx : ∀ τ, (genericBlockMatrix Ω N j τ).map (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
      ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2))
      = (g τ).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j τ :=
    fun τ => Matrix.ext fun c b => by rw [Matrix.map_apply]; exact hxg τ c b
  have h1 : ∀ r, MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ)))
        * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2) r
      = MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
        ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2) (φ r) := by
    have hc : (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ)))
        * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2))
      = (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
        ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2)).comp φ := by
      apply MvPolynomial.algHom_ext
      intro q
      rw [AlgHom.comp_apply, MvPolynomial.aeval_X, hφ, hlin, hGx]
    intro r
    exact DFunLike.congr_fun hc r
  rw [algebraicIndependent_iff_injective_aeval] at hx ⊢
  intro p p' hpp
  have h2 : φ p = φ p' := hx (by rw [← h1, ← h1]; exact hpp)
  calc p = ψ (φ p) := (hcomp p).symm
    _ = ψ (φ p') := by rw [h2]
    _ = p' := hcomp p'

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCoversComplexPoints
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem resolution_onto_complex_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e), IsArithVar P (e + 1) → ∀ z ∈ mcPts P, ∃ x, SameOrbit (R.lift x x) z :=
  @PositivityTheory.UnitarySelfGeneration.r_onto

end GlobalTheory.CompanionTheory.Ar.Cmp
end

