module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3126
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3130

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

open Finset GlobalTheory.FunObj.SqNum

namespace GlobalTheory.RowClaim

theorem sqRatio_mem_grid {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T)
    (W : G.Weil) (S : GridChoice W Set.univ) (ρ : RealMatch W) (c : Fin D.R.m → Fin D.R.m → T → ℂ)
    (hN : NumbersIn D.what₂.embLL S μ₀)
    (hC : ∀ i j t, SquareNonzero W S.B ρ t i j ∧ c i j t ≠ 0) (hK : ∀ i j t, IsSquareConst W S.B ρ t i j (c i j t))
    (hLN : ∀ i j : Fin D.R.m, (∀ t, ∃ Λ, GlobalTheory.CMVal.IsHeckeL (SqNum.nuH G t i j) Λ ∧
      ∀ s : ℤ, 1 - (GlobalTheory.SqTop.e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → Λ s ≠ 0))
    (hTX : ∀ i j : Fin D.R.m, ∃ (A A' WW : HSp D) (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X ∧ X.IsConst W.ψ W.θ c0)
    (hTW : ∀ (i j : Fin D.R.m) (t : T) (c c₀ : ℂ) (A A' WW : HSp D) (X : Tri T A A' WW)
      (c0 : T → ℂ) (Λ Λ₀ : ℂ → ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c → SquareNonzero W S.B ρ μ₀ i j →
      IsSquareConst W S.B ρ μ₀ i j c₀ → IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 → GlobalTheory.CMVal.IsHeckeL (SqNum.nuH G t i j) Λ →
      GlobalTheory.CMVal.IsHeckeL (SqNum.nuH G μ₀ i j) Λ₀ → ∃ u : Fin (GlobalTheory.SqTop.pp D j + GlobalTheory.SqTop.qq D j) → ℂ,
        (∀ k, GlobalTheory.Square.StepRatio D.what₂.embLL (GlobalTheory.SqTop.Qn G t) G.pl.S0 (SqNum.condExp G.pl)
          (fun v => Ideal.absNorm v.asIdeal) (u k) 1) ∧
        ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (GlobalTheory.SqTop.Qn G t) ζ ∧
          c / c₀ * ∏ k ∈ range (GlobalTheory.SqTop.qq D j), Λ (GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) / Λ₀ (GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) =
            D.what₂.embLL ζ * (∏ k, u k) * (c0 t / c0 μ₀) *
              ∏ k ∈ range (GlobalTheory.SqTop.pp D j), Λ (GlobalTheory.SqTop.eTop D i j + GlobalTheory.SqTop.qq D j - k : ℕ) /
                Λ₀ (GlobalTheory.SqTop.eTop D i j + GlobalTheory.SqTop.qq D j - k : ℕ))
    (hBF : ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
      ∃ lam : T → ℂ, GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam)
    (i j : Fin D.R.m) (t : T) : c i j t / c i j μ₀ ∈ Set.range D.what₂.embLL := by
  have hF : ∀ z : ℂ, z ∈ Set.range D.what₂.embLL ↔ z ∈ D.what₂.embLL.fieldRange := fun z => Iff.rfl

  obtain ⟨A₀, A₀', WW₀, X₀, -, hX₀, -⟩ := hTX i j
  obtain ⟨A, A', WW, X, hX, hS⟩ := hN.bottom i j ⟨A₀, A₀', WW₀, X₀, hX₀⟩
  obtain ⟨lam, hlam⟩ := hBF i j A A' WW X hX
  have hI := hX.is
  have hi' : ∀ t P g, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P g) X.fd' X.m' := fun t P g =>
    (_root_.GlobalTheory.DefSourceInt.theta_integral_source_definite D W.ψ false A' WW _ _ (X.ω' t) X.m' X.fd' _ (hI.weil' t) (GlobalTheory.ConstRatio.posDef_of_std hX.std')
      hI.meas'.1 hI.meas'.2 (GlobalTheory.Chain.InnerSteps.theta_pureTensorO hI.isVac.1 hI.isVac.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
        (GlobalTheory.ConstRatio.theta_f hI t).2 P)).1 g
  have hr := hS.rationalSums (fun t P g => hlam.2.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1 t P g) hi'
  have hrat := GlobalTheory.ConstRatio.ratIn_of_definite hI (GlobalTheory.ConstRatio.posDef_of_std hX.std) (GlobalTheory.ConstRatio.posDef_of_std hX.std')
    (GlobalTheory.ConstRatio.posDef_of_std hX.stdW) hlam hr μ₀
  haveI : Nonempty T := ⟨μ₀⟩
  have hcst : X.IsConst W.ψ W.θ lam := hlam.isConst

  obtain ⟨Λ, hΛ, hΛne⟩ := hLN i j t
  obtain ⟨Λ₀, hΛ₀, hΛ₀ne⟩ := hLN i j μ₀
  obtain ⟨u, hu, ζ, -, heq⟩ := hTW i j t (c i j t) (c i j μ₀) A A' WW X lam Λ Λ₀ (hC i j t).1 (hK i j t) (hC i j μ₀).1
    (hK i j μ₀) hX hcst hΛ hΛ₀
  rw [hF]
  obtain ⟨hn1, -, -, hn4, -, -, -, hn8, hn9⟩ := GlobalTheory.SqTop.Model.tower_numbers (D := D) i j
  have hne : ∀ L : ℂ → ℂ, (∀ s : ℤ, 1 - (GlobalTheory.SqTop.e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → L s ≠ 0) →
      ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D i j → L (n : ℂ) ≠ 0 := fun L h n h1 h2 => by
    have := h n (by omega) (by exact_mod_cast h2)
    simpa using this
  have hs : ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D i j →
      Λ (n : ℂ) / Λ₀ (n : ℂ) ∈ D.what₂.embLL.fieldRange ∧ Λ (n : ℂ) / Λ₀ (n : ℂ) ≠ 0 := fun n h1 h2 =>
    ⟨(hF _).1 (hN.ratios i j t Λ Λ₀ hΛ hΛ₀ n h1 (by omega) (hne Λ₀ hΛ₀ne n h1 h2)),
      div_ne_zero (hne Λ hΛne n h1 h2) (hne Λ₀ hΛ₀ne n h1 h2)⟩
  have hP1 : ∀ k ∈ range (GlobalTheory.SqTop.qq D j), Λ ((GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) : ℂ) /
      Λ₀ ((GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) : ℂ) ∈ D.what₂.embLL.fieldRange ∧
      Λ ((GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) : ℂ) / Λ₀ ((GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) : ℂ) ≠ 0 := fun k hk =>
    hs _ (by omega) (by have := mem_range.1 hk; omega)
  have hP2 : ∀ k ∈ range (GlobalTheory.SqTop.pp D j), Λ ((GlobalTheory.SqTop.eTop D i j + GlobalTheory.SqTop.qq D j - k : ℕ) : ℂ) /
      Λ₀ ((GlobalTheory.SqTop.eTop D i j + GlobalTheory.SqTop.qq D j - k : ℕ) : ℂ) ∈ D.what₂.embLL.fieldRange := fun k hk =>
    (hs _ (by have := mem_range.1 hk; omega) (by omega)).1
  have hU : (∏ k, u k) ∈ D.what₂.embLL.fieldRange := prod_mem fun k _ => by
    obtain ⟨b, g, g', -, -, h⟩ := hu k
    rw [h, mul_one]
    exact RingHom.mem_fieldRange.2 ⟨_, rfl⟩
  have hl : lam t / lam μ₀ ∈ D.what₂.embLL.fieldRange := by
    obtain ⟨-, y, hy⟩ := hrat t
    exact RingHom.mem_fieldRange.2 ⟨_, hy⟩
  rw [eq_div_of_mul_eq (prod_ne_zero_iff.2 fun k hk => (hP1 k hk).2) heq]
  exact div_mem (mul_mem (mul_mem (mul_mem (RingHom.mem_fieldRange.2 ⟨ζ, rfl⟩) hU) hl) (prod_mem hP2))
    (prod_mem fun k hk => (hP1 k hk).1)


end GlobalTheory.RowClaim

end
