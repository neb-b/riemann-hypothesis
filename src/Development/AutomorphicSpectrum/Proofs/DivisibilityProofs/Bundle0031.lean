module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0148
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerArithAgreement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerGeometricAgreement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0030
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0106
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.EvalRhoAntisymDeltaNe
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem eval_formPoly_none_zero {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → Option σ) → ℝ) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) (PB.formPoly n a) =
      eval c (PB.formPoly n fun w => a fun j => some (w j)) := by
  have h : ∀ Q : MvPolynomial (Option σ) ℝ,
      eval c (aeval (fun o : Option σ => o.elim (0 : MvPolynomial σ ℝ) X) Q) =
        eval (fun o : Option σ => o.elim 0 c) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p o hp =>
      rw [map_mul, map_mul, map_mul, hp]
      cases o <;> simp
  rw [← h, PB.killNone_formPoly]

theorem linA_zero_pow {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Wt Ψ N) (k : ℕ) :
    linA lam 0 ^ k = toA (linRoot lam ^ k) := by
  simp [linA, toA, map_pow]

theorem swapWt_uncurry {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (τ : Ψ) (a b : Fin N) (lam : Wt Ψ N) :
    (fun x : Ψ × Fin N => swapWt τ a b lam x.1 x.2) =
      (fun x : Ψ × Fin N => lam x.1 x.2) ∘ Equiv.swap (τ, a) (τ, b) := by
  funext ⟨σ, i⟩
  by_cases hσ : σ = τ
  · subst hσ
    by_cases h1 : i = a
    · subst h1; simp [swapWt]
    · by_cases h2 : i = b
      · subst h2; simp [swapWt]
      · simp [swapWt, Equiv.swap_apply_def, h1, h2]
  · simp [swapWt, Equiv.swap_apply_def, hσ]

theorem eval_rho_antisymDelta_ne {Ψ : Type} [Fintype Ψ] {N : ℕ} :
    eval (fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) (GroundTheory.Heights₂.Heights.antisymDelta Ψ N) ≠ 0 := by
  simp only [GroundTheory.Heights₂.Heights.antisymDelta, map_prod, map_sub, eval_X]
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun a _ =>
    Finset.prod_ne_zero_iff.2 fun b hb => ?_
  have hab : a < b := Finset.mem_Ioi.1 hb
  have hab' : (a : ℕ) < b := hab
  have : ((a : ℕ) : ℝ) < b := by exact_mod_cast hab'
  simp only [rhoWt]
  intro h
  linarith

end GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem Realis_PB_gapS_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {D : ℕ} {σ : Type} [Fintype σ]
    {S : PB.AnSys D (Option σ)} {P : Ideal (MRing ι)} (Re : PB.Realis S P) (II : IntersectionSystem) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) (Re.PB II) = eval c ((Re.comap some).PB II) :=
  eval_formPoly_none_zero _ _ c

theorem AnSys_degPoly_gapS_zero {D : ℕ} {σ : Type} [Fintype σ] (S : PB.AnSys D (Option σ)) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) S.degPoly = eval c (S.comap some).degPoly :=
  eval_formPoly_none_zero _ _ c

end GlobalTheory.CompanionTheory.Ar.Top
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealConditionsStatement
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_real_conditions : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ B a, (T.M B a).EffDiff T.nu := by
  intro _ E _ _ _ _ H D Xo l c Y _ T o _ _ _ _ _ _ B a
  obtain ⟨n₀, N₀, hn, _, hne, hmem⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Small.OriginEps.section_on_model
    E H D l (Xo l) c _ _ Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) T.nu (o.nu_eq a)
  let s : (T.M B a).Ω := (N₀ : (T.M B a).Ω) * (o.Or B a).g (o.Fx a).sE *
    ∏ r, (o.Or B a).e r ^ (o.Fx a).n r
  refine ⟨(o.Fx a).kA * (o.Fx a).q', n₀, Nat.mul_pos ?_ (o.Fx a).q'_pos, hn, s, hne, hmem⟩
  rw [← (o.Or B a).kA_eq]
  exact (T.M B a).kA_pos
end

