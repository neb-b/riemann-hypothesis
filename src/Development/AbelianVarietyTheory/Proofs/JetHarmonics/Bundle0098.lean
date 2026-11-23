module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxMaps
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyPowerDegree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCongr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0014
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapExistsNonzero
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselShape

theorem bessel_shape : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∃ w ∈ R.sm, ∃ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ≠ 0) → ∃ (l₀ La : R.H → Wp), IsBes R z π l₀ ∧ NzOn R l₀ ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v = (innerSL ℂ (La v)).smulRight (l₀ w) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hG hOK hS hne
  obtain ⟨w₀, hw₀, v₀, hv₀, hne⟩ := hne
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w₀ v₀ ξ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (ContinuousLinearMap.ext hcon)
  have hB := GlobalTheory.T.isBes_bessel_integral_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hG hOK hS
  have hnz : NzOn R (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v₀ ξ₀) := ⟨w₀, hw₀, hξ₀⟩
  set y₀ := be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w₀ v₀ ξ₀ with hy₀
  have hyy : ⟪y₀, y₀⟫_ℂ ≠ 0 := fun h0 => hξ₀ (inner_self_eq_zero.mp h0)
  refine ⟨fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v₀ ξ₀,
    fun v => (starRingEnd ℂ (⟪y₀, y₀⟫_ℂ)⁻¹) •
      ContinuousLinearMap.adjoint (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w₀ v) y₀,
    hB v₀ hv₀ ξ₀, hnz, ?_⟩
  intro w hw v hv
  ext ξ
  obtain ⟨c, hc⟩ := GlobalTheory.BesselLine.bessel_line hH k r ε mu R Wp z π u μW μN μG νq _ _ hDS hS
    (hB v₀ hv₀ ξ₀) hnz (hB v hv ξ)
  have h1 := hc w hw
  have h2 := hc w₀ hw₀
  rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, h2, h1, ← hy₀, inner_smul_right, Complex.conj_conj]
  congr 1
  field_simp

end GlobalTheory.BesselShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingGapDecayStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_orbital_integral_integrable_and_eq_smul : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∃ OO : Mx k r → (Wq →L[ℂ] Wp), ∀ F s, IsCoef R l l' F s → ∀ γ ∈ JF.Om k r D.z D.z', Integrable (JF.integrand D F γ) D.μSS ∧ B.JF D F γ = s • OO γ := by
  first | exact @GlobalTheory.BesselOrbital.bessel_integral_eq_smul | exact GlobalTheory.BesselOrbital.bessel_integral_eq_smul | (intros; apply GlobalTheory.BesselOrbital.bessel_integral_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BoxTupOfColumns
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

theorem boxTup_of_columns : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → BoxTupSt := by
  intro hL hL2 hL4 hT E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P ϖ hϖ Q hQ F _ _ _ _ v g g' π hg hg' hπ τ hτ hEL n D' A' G' _ _ pD pA pG U' PU _ oD' hx hact
    s s₂ t₀ t p w ζ x σ f h
  have hG := hL.globalFns
  have hk : 1 ≤ g' * g := Nat.mul_pos hg' hg
  have hA : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨bx₁, hbx₁⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F g'
  obtain ⟨bx, hbx⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F (g' * g)
  obtain ⟨p', hp'⟩ := BoxQk.exists_isBoxQk hG T.V n P.D.toPre D'.toPre pD F (g' * g) p
  have hw : ∀ i, (w i).IsGen := fun i => (h i).2.2.1
  obtain ⟨w', hw', hΦ⟩ := BoxPhi.phiRel_box hG T.V n P.D.toPre D'.toPre pD F (g' * g) p' p hp' w hw
  obtain ⟨σ', hσ', -⟩ := (expandsG_bijective_of_dvr hL hL2 hL4 hT T.V D' A' G' U' F (g' * g) hk).2 (bx t)
  let x' : TFK (R := T.V) F ⟶ A'.A := pA.lim.lift (Fan.mk _ x)
  have hx' : ∀ i, x' ≫ pA.pr i = x i := fun i => pA.lim.fac (Fan.mk _ x) ⟨i⟩
  have hπ' : star π * star (star π) = (g : 𝓞 E) := by rw [star_star, _root_.mul_comm, hπ]
  refine ⟨bx₁ s, bx s₂, p', w', ∏ i, ζ i, x', bx t₀, bx t, σ', ⟨?_, ?_, ⟨hw', ?_, ?_⟩, ?_, ?_, ?_, ?_, hσ', ?_⟩, hx'⟩
  · have := NuBox.main T.V ϖ hϖ n P.D D' pD Q hQ F v g' s (bx₁ s) ((hbx₁ _ _).2 rfl) (fun _ => 0) (fun i => (h i).1)
    rw [Finset.sum_const_zero] at this
    exact this
  · exact BoxPull.main hL hL2 hL4 hT T.V n P.D D' pD F (𝓞 E) hx P.oD oD' hact (star π) g g' hg hg' hπ' s s₂ _ _
      (fun i => (h i).2.1) ((hbx₁ _ _).2 rfl) ((hbx _ _).2 rfl)
  · exact Finset.prod_ne_zero_iff.2 fun i _ => (h i).2.2.2.1
  · exact finOrd_box hL hL2 hL4 hT T.V n P.D D' pD F (g' * g) hk p' p hp' w w' hw hw' hΦ ζ (fun i => (h i).2.2.2.2.1)
  · exact ProdTorsion.qkToAk_box hL T.V _ n P.D D' P.A A' C.I.G.G G' pD pA pG U' P.U PU
      (expBijF_of_admissible_base hL hL2 T.V _ hA _ _ _ P.U) (expBijF_of_admissible_base hL hL2 T.V _ hA _ _ _ U') F (g' * g) hk
      p' p hp' x' x hx' (fun i => (h i).2.2.2.2.2.1)
  · intro i
    rw [← Category.assoc, hx']
    exact (h i).2.2.2.2.2.2.1
  · exact hΦ s₂ t₀ _ _ (fun i => (h i).2.2.2.2.2.2.2.1) ((hbx _ _).2 rfl) ((hbx _ _).2 rfl)
  · refine (isSmul_iff _ _ _).2 ?_
    calc
      bx t = bx (fun i => ζ i • t₀ i) :=
        congrArg bx (funext fun i => (isSmul_iff _ _ _).1 (h i).2.2.2.2.2.2.2.2.1)
      _ = (∏ i, ζ i) • bx t₀ := by simpa using bx.map_smul_univ ζ t₀
  · exact _root_.GlobalTheory.PowGerm.boxGermSt_holds hL hL2 hL4 hT E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT C.wPT
      C.chartT C.frameT C.primT τ hτ hEL n D' A' G' pD pA pG U' PU F (g' * g) hk σ t f σ' (bx t)
      (fun i => (h i).2.2.2.2.2.2.2.2.2) ((hbx _ _).2 rfl) hσ'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem sup_norm_laws : ∀ (q : ℕ) [Fact q.Prime], (∀ (f g : ℂ_[q]⟦X⟧) (A B : ℝ), Bd A f → Bd B g → Bd (max A B) (f + g) ∧ Bd (A * B) (f * g)) ∧ (∀ (f h : ℂ_[q]⟦X⟧) (A : ℝ), Bd A f → Bd 1 h → constantCoeff h = 0 → Bd A (f.subst h)) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bd 1 f → ‖constantCoeff f‖ = 1 → f * g = 1 → Bd 1 g) ∧ (∀ (f g : ℂ_[q]⟦X⟧) (B : ℝ), Bdd f → Bdd g → Bd B (f * g) → ∀ i j, ‖coeff i f‖ * ‖coeff j g‖ ≤ B) ∧ (∀ (f g : ℂ_[q]⟦X⟧), Bdd f → Bdd g → f * g = 1 → constantCoeff f = 1 → Bd 1 f ∧ Bd 1 g) ∧ (∀ (f v : ℂ_[q]⟦X⟧) (k : ℕ) (B : ℝ), Bd 1 v → ‖constantCoeff v‖ = 1 → Bd B (X ^ k * v * f) → Bd B f) := by
  intro q _
  have R := GlobalTheory.EvenTheta.SerRing.series_ring_laws q
  have hmul : ∀ (f g : ℂ_[q]⟦X⟧) (A B : ℝ), Bd A f → Bd B g → Bd (A * B) (f * g) :=
    fun f g A B hf hg => R.2.2.2.2.2.2 f g A B hf hg
  have hinv : ∀ f : ℂ_[q]⟦X⟧, Bd 1 f → ‖constantCoeff f‖ = 1 → Bd 1 f⁻¹ :=
    fun f hf h0 => R.2.2.2.2.1 f hf h0
  have hinv' : ∀ (f g : ℂ_[q]⟦X⟧), Bd 1 f → ‖constantCoeff f‖ = 1 → f * g = 1 → Bd 1 g := by
    intro f g hf h0 hfg
    have hc : constantCoeff f ≠ 0 := by
      intro h
      rw [h, norm_zero] at h0
      exact zero_ne_one h0
    have hgf : g = f⁻¹ := by
      rw [PowerSeries.eq_inv_iff_mul_eq_one hc, mul_comm]
      exact hfg
    rw [hgf]
    exact hinv f hf h0
  have hgauss : ∀ (f g : ℂ_[q]⟦X⟧) (B : ℝ), Bdd f → Bdd g → Bd B (f * g) →
      ∀ i j, ‖coeff i f‖ * ‖coeff j g‖ ≤ B :=
    fun f g B hf hg hB => GlobalTheory.EvenTheta.sup_norm_mul_padicComplex q f g B hf hg hB
  refine ⟨fun f g A B hf hg => ⟨fun n => GlobalTheory.EvenTheta.SerRing.norm_coeff_add_le f g A B hf hg n,
    hmul f g A B hf hg⟩, fun f h A hf hh h0 => R.2.2.2.2.2.1 f h A hf hh h0, hinv', hgauss, ?_, ?_⟩
  · intro f g hf hg hfg h1
    have hg0 : constantCoeff g = 1 := by
      have hc := congrArg constantCoeff hfg
      rw [map_mul, h1, one_mul, map_one] at hc
      exact hc
    have hB : Bd 1 (f * g) := by
      rw [hfg]
      intro n
      rw [coeff_one]
      split_ifs <;> simp
    have H := hgauss f g 1 hf hg hB
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have hi := H i 0
      rwa [coeff_zero_eq_constantCoeff_apply, hg0, norm_one, mul_one] at hi
    · have hj := H 0 j
      rwa [coeff_zero_eq_constantCoeff_apply, h1, norm_one, one_mul] at hj
  · intro f v k B hv h0 hB
    have hw : Bd B (v * f) := by
      intro m
      have hm := hB (m + k)
      rwa [mul_assoc, coeff_X_pow_mul] at hm
    have hc : constantCoeff v ≠ 0 := by
      intro h
      rw [h, norm_zero] at h0
      exact zero_ne_one h0
    have hvf := hmul v⁻¹ (v * f) 1 B (hinv v hv h0) hw
    rwa [← mul_assoc, PowerSeries.inv_mul_cancel _ hc, one_mul, one_mul] at hvf

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFamThrough
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnitBallBox

section Fam

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

variable {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)

theorem box_secScal {S : Fam D' F k} {s : Fin j → Fam D F k} (hS : IsBoxFam pD F k S s)
    {f' : ∀ α : D'.X, D'.SecB k α} {f : Fin j → ∀ α : D.X, D.SecB k α} (hf : IsBoxFamB pD k f' f) (α' : D'.X)
    (h : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F (pD.xe α' i)) (DegPre.famε k) ((s i).s (pD.xe α' i))
      (D.famφB (pD.xe α' i)) (DegPre.famε k) (f i (pD.xe α' i)) (DegPre.prB D F).left 1) :
    GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' F α') (DegPre.famε k) (S.s α')
      (D'.famφB α') (DegPre.famε k) (f' α') (DegPre.prB D' F).left 1 := by
  obtain ⟨hφ, H⟩ := hS α'
  obtain ⟨hψ, H'⟩ := hf α'
  have e₄ : ∀ i, (DegPre.prB D' F).left ≫ (pD.pw.pr i).left =
      prB pD F i ≫ (DegPre.prB D F).left := fun i => by
    rw [← Over.comp_left, ← Over.comp_left]; congr 1; exact (whiskerLeft_snd _ _).symm
  exact BoxFamScalar.secScal_box D.P.isLB D'.P.isLB pD.w (GC.famφ_eq D' F α') e₄
    (S.s α') (fun i => (s i).s (pD.xe α' i)) (f' α') (fun i => f i (pD.xe α' i))
    (fun y _ _ hJ hJ' => BoxFamScalar.box_sval pD.w hφ (S.s α') (fun i => (s i).s (pD.xe α' i)) _ H (𝟙 _) y hJ hJ')
    (fun y _ _ hJ hJ' => BoxFamScalar.box_sval pD.w hψ (f' α') (fun i => f i (pD.xe α' i)) _ H' _ y hJ hJ')
    (fun _ => 1) 1 (fun y => by simp only [NuBox.gs_one, Finset.prod_const_one]) h

end Fam


end GlobalTheory.UnitBallBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGermLinearMap
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PairingLinear

def linOfComb {F M N : Type} [Field F] [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N] (f : M → N)
    (h : ∀ (l : ℕ) (c : Fin l → F) (s : Fin l → M), f (∑ i, c i • s i) = ∑ i, c i • f (s i)) : M →ₗ[F] N where
  toFun := f
  map_add' a b := by simpa using h 2 ![1, 1] ![a, b]
  map_smul' c a := by simpa using h 1 ![c] ![a]

theorem exists_germ_linearMap (hL : Laws) (hL2 : Laws2) (hL4 : Laws4) (hT : TwistBaseChangeStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
    (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Sp V))
    [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (κ : Type) [Fintype κ] [DecidableEq κ]
    (z : JetPts G κ) (hz : IsUnivJ G κ z) (τ : Frames U.LG.L z) (hτ : τ.Gen) (hτT : τ.Trunc)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F]
    (q : ℕ) (hq : 1 ≤ q) :
    ∃ gm : Fam D.toPre F q →ₗ[F] MvPowerSeries κ F,
      (∀ t σ' h, U.ExpandsG F q σ' t → GermA U.toUnifPre z τ F q σ' h → h = gm t) ∧
      ∀ t, ∃ σ', U.ExpandsG F q σ' t ∧ GermA U.toUnifPre z τ F q σ' (gm t) := by
  obtain ⟨huniq, hlin, hex⟩ := GlobalTheory.GermBasic.main V D A G U κ z hz τ hτ F q
  have hbij := (GlobalTheory.expandsG_bijective_of_dvr hL hL2 hL4 hT V D A G U F q hq).2
  choose S hS hSu using hbij
  choose Γg hΓ using hex hτT
  have key : ∀ t σ' h, U.ExpandsG F q σ' t → GermA U.toUnifPre z τ F q σ' h → h = Γg (S t) := by
    intro t σ' h he hg
    obtain rfl := hSu t σ' he
    exact huniq _ _ _ hg (hΓ _)
  refine ⟨linOfComb (fun t => Γg (S t)) fun l c s => ?_, key, fun t => ⟨S t, hS t, hΓ _⟩⟩
  let σ' : U.SecGF F q := GlobalTheory.ExpansionLinear.secComb
    (fun i => scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (c i)) (fun i => S (s i))
  exact (key _ σ' _
    (GlobalTheory.GroupExpansionLinear.expandsG_sum V D A G U F q l c (fun i => S (s i)) s σ' (fun i => hS _) (fun _ => rfl))
    (hlin l c (fun i => S (s i)) _ σ' (fun i => hΓ _) (fun _ => rfl))).symm

end GlobalTheory.PairingLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueFrameSer
section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PtGermCompare

theorem surjective_cube {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom := by
  have hG := GlobalTheory.globalFns_holds
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    RigidIsoCube.surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have s₂ := surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G A.isAb hg G) s₁
  rw [Over.w (snd G G)] at s₂
  have s₃ := surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G A.isAb hg (G ⊗ G)) s₂
  rw [Over.w (snd G (G ⊗ G))] at s₃
  exact s₃

theorem cubical_unique {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (sj : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom) {L : RigLB G} (c c' : CubicalStr G L) : c = c' := by
  let e : 𝟙_ (Over S) ⟶ G3 G := lift 1 (lift 1 1)
  have h : c.t.s = c'.t.s := JetSer.gen_ext_val L.isLB (φ := thφ G (x3 G)) (ε := thε) c.isGen c'.isGen fun y J hJ =>
    gen_unique L.isLB (φ := thφ G (x3 G)) (ε := thε) (G3 G).hom e.left (Over.w e) sj c.isGen c'.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV c' hJ).face 1 1).symm) _ _ y J hJ
  obtain ⟨⟨t⟩, _⟩ := c
  obtain ⟨⟨t'⟩, _⟩ := c'
  obtain rfl : t = t' := h
  rfl

section Scale
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))}

end Scale

section Bound
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}

end Bound

section Cast
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {L L' : RigLB G}

end Cast

open GlobalTheory.FamGerm

section Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] {F : Type} [Field F] [Algebra (FractionRing V) F]

variable [CharZero F]

end Data

section Statements

end Statements

end GlobalTheory.PtGermCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentGrowthStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowering_scalar_sq_mul_degree_ratio_le : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + 1 ≤ q0 → ∀ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep → NzOn (R ν) (l ν) → ∀ (s : Fin (2 * r + k + 1)) (κ₀ : ℂ), (∀ v ∈ (R ν).sm, l (ν - Pi.single s 1) (∑ c, pr s c (tm (R ν) (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν - Pi.single s 1) ≤ Formalism.QuantumDeterminants.Tz k r z * b ^ 4 := by
  first | exact @GlobalTheory.DualStepBound.dual_step_bound | exact GlobalTheory.DualStepBound.dual_step_bound | (intros; apply GlobalTheory.DualStepBound.dual_step_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImportsTer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm

namespace GlobalTheory.PowThetaFrame

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ThetaFrameF := by
  intro hL hL2 hL4 hT E _ _ _ H Dw l Xo c n T io y _ C P _ g g' _ hg' _ _ _ π π' _ hπ' _ _ _ F _ _ _ _ _ _ v ϖ hϖ hv
    Q hQ D' A' G' _ _ pD pA pG U' PU _ oD' hx hact
  let _ := H.starRing
  obtain ⟨θ, hν, hθ⟩ := exists_thetaFrame hL hL2 hL4 hT T.V ϖ hϖ D' (sumQ pD.xe Q)
    (QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) F v hv
  have hw : TraceFormTwistIso D'.toPre oD' H.w0 :=
    PsiWZeroProd.main T.V n P.D.toPre D'.toPre pD (𝓞 E) (fun a x => funext (hx a x)) P.oD oD' hact H.w0 P.w0
  obtain ⟨f, -, hf⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw (star π') g' 1 hg'.one_le le_rfl
    (by rw [star_star, mul_comm]; exact hπ')
  exact ⟨θ, f θ, hν, hθ, (hf _ _).2 rfl⟩

end GlobalTheory.PowThetaFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowOActOfGlobalFns
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem powOAct_of_globalFns : GlobalFnsSt → PowOActSt := by
  intro hG E _ _ _ H V _ _ _ t P n D' pD
  letI := H.starRing
  letI M : Module (𝓞 E) D'.toPre.X := pD.xe.module (𝓞 E)
  have h : ∀ (a : 𝓞 E) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x := by
    intro a x
    exact pD.xe.apply_symm_apply _
  obtain ⟨oa', hoa'⟩ := powDeg_diagonal_action hG V n P.D.toPre D'.toPre pD (𝓞 E) h P.oD
  exact ⟨M, oa', fun a x i => by rw [h]; rfl, hoa'⟩

end GlobalTheory
end

