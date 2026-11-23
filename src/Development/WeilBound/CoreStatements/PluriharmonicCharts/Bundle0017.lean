module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0016
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorElementaryColumnOp
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsMultiHomogMonoX

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCWArith
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem PositivityTheory.Xgp.t_c_w_arith : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) (d + 3) ∧ IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) (d + 2) ∧ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ≤ mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0) ∧ imageZ (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y ∧ ∀ v₁ : (Σ k, ι k) → (Σ o : Option K, ι (o.getD k₀)), (∀ p : (Σ k, ι k), p.1 ≠ k₀ → v₁ p = ⟨some p.1, p.2⟩) → (∀ m : ι k₀, v₁ ⟨k₀, m⟩ = ⟨none, m⟩) → imageZ v₁ (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M d τ a b k₀ ca cb hb hab hk hca hcb har
  haveI : CharZero Φ := PositivityTheory.Xgp.W.charZero_of_model M
  have hne : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := PositivityTheory.Xgp.W.blocks_of_model M
  choose c hc using hne
  have hpt : PositivityTheory.Xgp.W.IsPt y y := PositivityTheory.Xgp.W.isPt_self (fun k => ⟨c k, hc k⟩)
  obtain ⟨Fr⟩ := PositivityTheory.Xgp.W.exists_penFrame M hb hab hk hca hcb hpt c hc
  have hA := PositivityTheory.Xgp.W.arith_pen hc Fr (d := d + 1) har
  rw [PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb, PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb,
    PositivityTheory.Xgp.W.ideal_pen_zero]
  refine ⟨hA.1, hA.2, PositivityTheory.Xgp.W.pen_le_zero _ _ _ _, PositivityTheory.Xgp.W.image_pen _ _ _ _ _, ?_⟩
  intro v₁ h1 h2
  rw [← PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb]
  exact PositivityTheory.Xgp.W.image_snd M hb hab hk hca hcb v₁ h1 h2
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCWLine
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem PositivityTheory.Xgp.t_c_w_line : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ G : GenFibre (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), ∃ T : Set (MRingOver G.Φ (fibreIdx (fun o : Option K => ι (o.getD k₀)) (some : K → Option K))), (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (some : K → Option K) G = Ideal.span T := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hb hab hk hca hcb
  have hne : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := PositivityTheory.Xgp.W.blocks_of_model M
  choose c hc using hne
  obtain ⟨Fr⟩ := PositivityTheory.Xgp.W.exists_penFrame M hb hab hk hca hcb (PositivityTheory.Xgp.W.isPt_self fun k => ⟨c k, hc k⟩) c hc
  rw [PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb]
  exact fun G => PositivityTheory.Xgp.W.line_pen Fr G
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCWSec
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem PositivityTheory.Xgp.t_c_w_sec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∃ (g h : MRing fun o : Option K => ι (o.getD k₀)) (dg dh : Option K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ g ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ∧ h ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ∧ (∀ o : Option K, (dg o : ℤ) - dh o = o.elim 1 fun k => -(fun k => ∑ p, xiCoef τ a p * M.dy p k) k - (if M.blk (τ, a) = some k then 1 else 0)) ∧ aeval (M.wCo (τ, a) k₀ ca cb RatFunc.X) g = RatFunc.X * algebraMap Φ (RatFunc Φ) (∏ p, (if IsProperStep N j p.2 then 1 else algebraMap M.Ω Φ (M.lam p) * (if (p.2 : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (M.g p.1) (wIdx N j) (wIdx N j) else 1) else minorIJ (M.g p.1) (omIdx N j) (omIdx N j))) ^ xiCoef τ a p) * aeval (M.wCo (τ, a) k₀ ca cb RatFunc.X) h ∧ divCycle (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) g = divCycle (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) h + Finsupp.single (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) 1 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M d τ a b k₀ ca cb hb hab hk hca hcb _
  have hne : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := PositivityTheory.Xgp.W.blocks_of_model M
  obtain ⟨g, h, dg, dh, hg, hh, hgn, hhn, hdeg, haev, hdiv⟩ :=
    PositivityTheory.Xgp.W.sec_pen (B := PositivityTheory.Xgp.W.vecB M τ a k₀ ca cb) (cf := PositivityTheory.Xgp.W.cFac M τ a)
      (e := PositivityTheory.Xgp.W.eDeg M τ a k₀) hne
      (fun E _ z hz c hc => PositivityTheory.Xgp.W.exists_penFrame M hb hab hk hca hcb hz c hc)
  refine ⟨g, h, dg, dh, hg, hh, ?_⟩
  rw [PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb, PositivityTheory.Xgp.W.wCo_eq M hb hab hk hca hcb,
    PositivityTheory.Xgp.W.ideal_pen_zero]
  refine ⟨hgn, hhn, ?_, ?_, hdiv⟩
  · intro o
    rw [hdeg o]
    cases o with
    | none => rfl
    | some k =>
      simp only [PositivityTheory.Xgp.W.totDeg, PositivityTheory.Xgp.W.eDeg, Option.elim, hk, Option.some.injEq]
      by_cases hkk : k = k₀
      · subst hkk
        simp
        ring
      · simp [hkk, Ne.symm hkk]
  · have hI : (PositivityTheory.Xgp.W.intAlg5 : Algebra ℤ (RatFunc Φ)) = RatFunc.instAlgebraOfPolynomial Φ ℤ :=
      Subsingleton.elim _ _
    have key : ∀ f : MRing (PositivityTheory.Xgp.W.iW ι k₀),
        @aeval ℤ (RatFunc Φ) _ _ _ PositivityTheory.Xgp.W.intAlg5
          (PositivityTheory.Xgp.W.penCo y k₀ (fun m => y ⟨k₀, m⟩) (PositivityTheory.Xgp.W.vecB M τ a k₀ ca cb) RatFunc.X) f =
        @aeval ℤ (RatFunc Φ) _ _ _ (RatFunc.instAlgebraOfPolynomial Φ ℤ)
          (PositivityTheory.Xgp.W.penCo y k₀ (fun m => y ⟨k₀, m⟩) (PositivityTheory.Xgp.W.vecB M τ a k₀ ca cb) RatFunc.X) f := by
      intro f
      rw [hI]
    rw [key g, key h] at haev
    exact haev
end

