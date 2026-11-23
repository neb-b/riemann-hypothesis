module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTypeLevelFamilyIsOpenLeLatticeStabilizer
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

namespace GlobalTheory.TrIdem

theorem levelFam_open_le : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S → ∀ v, IsOpen (levelFam T U v : Set (GLoc D.sp.cm.sig V.gram v)) ∧ levelFam T U v ≤ Kv V v := by
  intro D V T U hu v
  by_cases hvu : v = U.u
  · subst hvu
    rw [levelFam_u]
    exact ⟨U.frame.isOpen_iwahori, U.frame.iwahori_le⟩
  by_cases hv : v ∈ T.S
  · have h := levelFam_of_mem T U hu ⟨v, hv⟩
    simp only at h
    rw [h, kerSub]
    refine ⟨?_, Subgroup.map_subtype_le _⟩
    rw [Subgroup.coe_map]
    exact (isOpen_stabLoc _ _ _ v).isOpenMap_subtype_val _ (T.frame ⟨v, hv⟩).isOpen_ker_red
  · rw [levelFam_of_notMem T U hv hvu]
    exact ⟨isOpen_stabLoc _ _ _ v, le_refl _⟩

end GlobalTheory.TrIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolIntegrableOnIff
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

namespace GlobalTheory.VolIdent

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem vol_nu_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {t : T} (M M' : Vol G)
    (hM : M.Is t) (hM' : M'.Is t) : ∀ X : Node, X.InRange D.R.m → M.ν X = M'.ν X :=
  fun X hX => GlobalTheory.FunObjModel.isAt_unique (hM.vtx X hX) (hM'.vtx X hX)

theorem vol_setIntegral_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {t : T} (M M' : Vol G)
    (hM : M.Is t) (hM' : M'.Is t) {X : Node} (hX : X.InRange D.R.m) (f : GA D (G.V X) → ℂ)
    (hf : ∀ γ ∈ GQ (G.V X), ∀ u, f (γ * u) = f u) :
    ∫ u in M.fd X, f u ∂M.ν X = ∫ u in M'.fd X, f u ∂M'.ν X := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V X)
  have e := vol_nu_eq M M' hM hM' X hX
  have h1 := (hM.vtx X hX).haar_fund
  have h2 := (hM'.vtx X hX).haar_fund
  rw [← e] at h2 ⊢
  have := h1.1
  exact h1.2.setIntegral_eq h2.2 fun γ g => hf γ γ.2 g

theorem vol_integrableOn_iff {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {t : T} (M M' : Vol G)
    (hM : M.Is t) (hM' : M'.Is t) {X : Node} (hX : X.InRange D.R.m) (f : GA D (G.V X) → ℂ)
    (hf : ∀ γ ∈ GQ (G.V X), ∀ u, f (γ * u) = f u) :
    IntegrableOn f (M.fd X) (M.ν X) ↔ IntegrableOn f (M'.fd X) (M'.ν X) := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V X)
  have e := vol_nu_eq M M' hM hM' X hX
  have h1 := (hM.vtx X hX).haar_fund
  have h2 := (hM'.vtx X hX).haar_fund
  rw [← e] at h2 ⊢
  have := h1.1
  exact h1.2.integrableOn_iff h2.2 fun γ g => hf γ γ.2 g

end GlobalTheory.VolIdent

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilThetaLevelPolynomialInHeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise

noncomputable section

namespace GlobalTheory.LevelGrowth

theorem level_poly : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (Φ : WO M X → ℂ) (hΦ : IsThetaFunO ψ (sgn ε M) X Φ)
    (C₁ : Set (GA D M)) (hC₁ : IsCompact C₁),
    ∃ K₀ : Set (WO M X), K₀ ∈ nhds (0 : WO M X) ∧ IsCompact K₀ ∧ ∃ (m : ℝ) (e : ℕ), ∀ y ∈ C₁, ∀ h : GA D X,
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ m * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ e ∧
        ∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ (sgn ε M) X (n • u) (ω (y, h) Φ) = ω (y, h) Φ := by
  intro D ψ θ hθ ε M X χ χ' ω hω Φ hΦ C₁ hC₁
  obtain ⟨U, hU, hΦU⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨K₀, h0, hK₀, m, hlev⟩ := GlobalTheory.KernelSeminorm.exists_level_multiple (S := sgn ε M) (T := X) hU
  obtain ⟨B, hB⟩ := hC₁.bddAbove_image
    ((GlobalTheory.Grow.continuous_height (sgn ε M)).comp (continuous_ofSgn_symm ε M)).continuousOn
  obtain ⟨C, hC, hcmp⟩ := GlobalTheory.Grow.height_comparison X hθ
  refine ⟨K₀, h0, hK₀, m * max B 0 * C, 1, fun y hy h => ?_⟩
  set g := (ofSgn ε M).symm y with hg
  obtain ⟨n, hn, hnle, hmem⟩ := hlev g h
  refine ⟨n, hn, ?_, fun u hu hinf => ?_⟩
  · have hgB : GlobalTheory.Grow.height (sgn ε M) g ≤ max B 0 := (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)
    have hhC : GlobalTheory.Grow.height X h ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := (hcmp h).2
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    have hg0 := (GlobalTheory.Grow.height_pos (sgn ε M) g).le
    have hh0 := (GlobalTheory.Grow.height_pos X h).le
    calc (n : ℝ) ≤ m * (GlobalTheory.Grow.height (sgn ε M) g * GlobalTheory.Grow.height X h) := hnle
      _ ≤ m * (max B 0 * (C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hgB hhC hh0 (le_max_right _ _)) hm0
      _ = m * max B 0 * C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ 1 := by ring
  · have hv : (actO (sgn ε M) X g⁻¹ h⁻¹ (n • u)).map (infPart D) = 0 := by
      have : (n • u).map (infPart D) = 0 := by
        ext i j
        have h3 : infPart D (u i j) = 0 := congrFun (congrFun hinf i) j
        exact (map_nsmul (infPart D) n (u i j)).trans ((congrArg (n • ·) h3).trans (nsmul_zero n))
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, this, Matrix.mul_zero, Matrix.zero_mul]
    have hfix := hΦU.2 _ (hmem u hu hinf) hv
    have e := hω.om_heis g h (actO (sgn ε M) X g⁻¹ h⁻¹ (n • u)) Φ hΦ
    rw [hfix, GlobalTheory.ThetaGrowth.actO_mul, mul_inv_cancel, mul_inv_cancel, GlobalTheory.ThetaGrowth.actO_one] at e
    have e2 : (WRep.toSgn ε ω) (g, h) = ω (y, h) := by
      simp [WRep.toSgn, hg]
    rw [e2] at e
    exact e.symm

end GlobalTheory.LevelGrowth
end
end

