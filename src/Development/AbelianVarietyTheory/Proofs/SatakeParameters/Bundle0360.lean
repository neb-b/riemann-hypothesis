module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0358
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0356
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedFormsOperatorDegreesAtKernelSourceStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedForms_operator_degrees_at_kernelSource : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std), ∀ j < D.R.m, Nonempty (Lv.comp (j + 1)) → ∀ (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) (gmS d) j ∧ TieOpS (Y := S.Y) t u μ (clsAt X H) (gmS d) (sO d ι) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j) ∧ KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)) := by
  first | exact @GlobalTheory.TwV.DelA.moved_forms_at_source | exact GlobalTheory.TwV.DelA.moved_forms_at_source | (intros; apply GlobalTheory.TwV.DelA.moved_forms_at_source <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledBackProjCoordinateRatioOverlapDivStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledBackProjCoordinateRatio_overlap_div : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (φ : Z ⟶ PSpace ℂ d) (a i j : Fin (d + 1)), genericPoint Z ∈ φ ⁻¹ᵁ chart d a → genericPoint Z ∈ φ ⁻¹ᵁ chart d i → rat φ a i ≠ 0 ∧ rat φ i j = rat φ a j / rat φ a i := by
  first | (exact @GlobalTheory.PD.XCover.rat_overlap) | (exact GlobalTheory.PD.XCover.rat_overlap) | (intros; apply GlobalTheory.PD.XCover.rat_overlap  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceCechCochainFractionEqSumFibre
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

theorem trF_locCoch_eq_finsum_fib : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ (ρ : F →ₗ[k] k), IsRes k x ρ → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), trF k τ ρ (locCoch k K x h Finset.univ) = ∑ᶠ e : fib k K x, e.1 h := by
  intro k _ _ F K _ _ _ _ _ _ d x hc τ hτ ρ hρ hac hred h
  have hloc : locCoch k K x (h : K) Finset.univ = (h : K) • vol0 k K x := if_pos rfl
  have h1 : trF k τ ρ (locCoch k K x (h : K) Finset.univ) = ρ (Algebra.trace F K (h : K)) := by
    simp only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hloc, map_smul, hτ.1, smul_eq_mul, mul_one]
  rw [h1]
  obtain ⟨e, -⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hc.pd 0
  haveI : IsIntegrallyClosed (rA k x {0}) := IsIntegrallyClosed.of_equiv e.toRingEquiv
  haveI : IsFractionRing (rA k x {0}) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing k F d x hc.pd {0} (Finset.singleton_nonempty _)).1
  haveI := hc.fin
  have hint : IsIntegral (rA k x {0}) (h : K) := h.2
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := rA k x {0}) (K := F)).1 (Algebra.isIntegral_trace (L := F) hint)
  obtain ⟨ev, hev, hker⟩ := GlobalTheory.T.laurentConstantTerm_eq_eval_origin_chart k F d x hc.pd ρ hρ
  have ha' : (a : F) = Algebra.trace F K (h : K) := ha
  rw [← ha', hev, GlobalTheory.T.trace_eval_origin_eq_fibre_trace k F K d x hc ev hker h a ha', GlobalTheory.T.trace_fibreRing_eq_finsum_fibrePoints k F K d x hc hac hred h]

end GlobalTheory.PD
end
end

