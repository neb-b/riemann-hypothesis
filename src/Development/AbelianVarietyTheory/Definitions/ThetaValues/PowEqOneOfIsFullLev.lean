module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatFullLinearLevelStructure
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaForm.Model

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable (Xo : Moduli Dw l) (c : Coeff l)

theorem exists_isNullVal (hL : Laws) {N : ℕ} (hN : Odd N) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (p : ptO Xo y.x ⟶ Xo.univ.t.G) (hp : p ^ (N ^ 2) = 1) : ∃ w, IsNullVal Xo c N y p w := by
  obtain ⟨F, hF⟩ := (GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo N hN _ y.s).1
    (fun t => t = p) (p ^ N) p rfl hp rfl
  obtain ⟨v, hv⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.exists_value _ _ Xo.univ.t.PP.isLB ((N : ℤ) ^ 2) F 1
    (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (ptO Xo y.x) ((N : ℤ) ^ 2)) (GlobalTheory.ThetaReal.NormMul.rigT_isGen Xo.univ.t.PP.rigGen _)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom v, F, hF, ?_⟩
  have : toΓ S ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom v) = v := by
    unfold toΓ
    exact (Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id_apply v
  rw [this]
  exact hv

open GlobalTheory.TranslExist in
theorem isNullVal_unique (hL : Laws) {N : ℕ} (hN : Odd N) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (p : ptO Xo y.x ⟶ Xo.univ.t.G) (hp : p ^ (N ^ 2) = 1) {w w' : S} (h : IsNullVal Xo c N y p w)
    (h' : IsNullVal Xo c N y p w') : w = w' := by
  have hB := Xo.univ.t.PP.isLB
  obtain ⟨F, ⟨_, α₀, α, s₁, U, -, rfl, g₀, n₀, cα, tw, hU, a₁⟩, hv⟩ := h
  obtain ⟨F', ⟨_, β₀, β, r₁, V, -, rfl, gβ, nβ, cβ, tw', hV, b₁⟩, hv'⟩ := h'
  obtain ⟨g₁, -, -, u₀, -⟩ := GlobalTheory.T.universal_normalised_mulByNat_pullback_iso hL E H Dw l Xo N
  obtain rfl : r₁ = s₁ := twist_congr hB (fun z J hJ =>
    (val_corr hJ cβ _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (u₀ β₀ gβ nβ) _).trans
      ((val_corr hJ cα _).trans ((val_pull hJ _ _ _).trans (val_corr hJ (u₀ α₀ g₀ n₀) _))).symm))) tw' tw
  obtain rfl : F = F' := act_congr hB (hU.pt_eq.trans hV.pt_eq.symm)
    ((_root_.GlobalTheory.moduli_univ_symLift_global hL E H Dw l Xo N hN _ _ hp).2 _ _ hU hV) a₁ b₁
  exact Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.toΓ_injective _ (Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.value_unique _ _ hB _ _ _ _ _ _ hv hv')

end GlobalTheory.EtaForm.Model
