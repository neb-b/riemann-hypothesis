module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2145
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianExtensionNormalModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.VanishAtSStatementPf
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2040

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeOfLocal
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem local_of_opens_pullback (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q] {X Y : Scheme.{0}}
    (f : X ⟶ Y) {Ix : Type} (V : Ix → Y.Opens) (hV : ∀ y : Y, ∃ i, y ∈ V i)
    (h : ∀ i, Q (pullback.snd f (V i).ι)) : Q f := by
  have hV' : iSup V = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 (hV y)
  exact IsZariskiLocalAtTarget.of_openCover (P := Q) (Y.openCoverOfIsOpenCover V hV') h

theorem Good.of_opens {g : ℕ} {X Y : Scheme.{0}} (f : X ⟶ Y) {Ix : Type} (V : Ix → Y.Opens)
    (hV : ∀ y : Y, ∃ i, y ∈ V i) (h : ∀ i, Good g (pullback.snd f (V i).ι)) : Good g f := by
  have h1 : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  have h2 : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  exact ⟨local_of_opens_pullback @IsProper f V hV fun i ↦ (h i).proper,
    local_of_opens_pullback (@SmoothOfRelativeDimension g) f V hV fun i ↦ (h i).smooth,
    local_of_opens_pullback @GeometricallyConnected f V hV fun i ↦ (h i).conn⟩

theorem hasRep_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (g : ℕ), IsAbelianScheme A → (∀ s : S, ∃ V : S.Opens, s ∈ V ∧ HasRep A g (Over.mk V.ι)) → HasRep A g (𝟙_ _) := by
  intro S A _ g hA h
  choose V hV hR using h
  obtain ⟨B, P, hP, hG⟩ := _root_.GlobalTheory.DualCon.ZarGlue.zariski_glue S A hA S V (fun _ ↦ g) (fun s ↦ ⟨s, hV s⟩) hR
  exact ⟨B, toUnit B, P, hP, Good.of_opens (Y := S) B.hom V (fun s ↦ ⟨s, hV s⟩) hG⟩

end GlobalTheory.DualCon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFinite
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem fg_addSubgroup_field_finite_or_basis {K : Type} [Field K] (H : AddSubgroup K) (hH : H.FG) :
    (H : Set K).Finite ∨ ∃ (r : ℕ) (f : Fin r → K), (∀ j, f j ∈ H) ∧ LinearIndependent ℤ f ∧
      ∀ x ∈ H, ∃ c : Fin r → ℤ, x = ∑ j, c j • f j := by
  have hfin : Module.Finite ℤ H :=
    Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg H).2 hH)
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | h0
  · left
    have htor : Module.IsTorsion ℤ H := by
      intro x
      refine ⟨⟨(ringChar K : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hq.ne_zero)⟩, ?_⟩
      ext
      simp [ringChar.Nat.cast_ringChar]
    have : Finite H := Module.finite_of_fg_torsion H htor
    exact Set.toFinite _
  · right
    haveI : CharP K 0 := h0 ▸ ringChar.charP K
    haveI : CharZero K := CharP.charP_to_charZero K
    haveI : NoZeroSMulDivisors ℤ H := inferInstance
    haveI : Module.Free ℤ H := Module.free_of_finite_type_torsion_free'
    let bs := Module.finBasis ℤ H
    refine ⟨_, fun j => (bs j : K), fun j => (bs j).2, ?_, ?_⟩
    · exact bs.linearIndependent.map' H.subtype.toIntLinearMap
        (LinearMap.ker_eq_bot.2 Subtype.val_injective)
    · intro x hx
      refine ⟨bs.repr ⟨x, hx⟩, ?_⟩
      have h := congrArg Subtype.val (bs.sum_repr ⟨x, hx⟩)
      calc x = ((⟨x, hx⟩ : H) : K) := rfl
        _ = ((∑ i, bs.repr ⟨x, hx⟩ i • bs i : H) : K) := h.symm
        _ = ∑ j, bs.repr ⟨x, hx⟩ j • (bs j : K) := by
          change H.subtype (∑ i, bs.repr ⟨x, hx⟩ i • bs i) = _
          rw [map_sum]
          rfl

theorem bl_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (R : ℝ), (P.Bl a b R).Finite := by
  intro k _ X _ p D hX P a b R
  rcases fg_addSubgroup_field_finite_or_basis (P.H a b) (_root_.GlobalTheory.HSNef.PairFG.h_fg k X p D hX P a b) with
    hfin | ⟨r, f, hf, hli, hspan⟩
  · exact hfin.subset (fun x hx => hx.1)
  · obtain ⟨C, -, hC⟩ := _root_.GlobalTheory.HSNef.exists_coeff_le_of_linearIndependent k X p D hX P a b r f hf hli
    have hS : {c : Fin r → ℤ | ∀ j, |(c j : ℝ)| ≤ C * R}.Finite := by
      refine (Set.Finite.pi (t := fun _ : Fin r => Set.Icc (-⌈C * R⌉) ⌈C * R⌉)
        (fun _ => Set.finite_Icc _ _)).subset ?_
      intro c hc j _
      have h := abs_le.1 (hc j)
      have hc1 := Int.le_ceil (C * R)
      have h1 : (c j : ℝ) ≤ (⌈C * R⌉ : ℝ) := h.2.trans hc1
      have h2 : -((⌈C * R⌉ : ℤ) : ℝ) ≤ c j := by linarith
      exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩
    refine (hS.image (fun c => ∑ j, c j • f j)).subset ?_
    intro x hx
    obtain ⟨c, rfl⟩ := hspan x hx.1
    exact ⟨c, fun j => hC c R hx j, rfl⟩

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinFourierExpansionSupport
section
set_option autoImplicit false

noncomputable section

open NumberField
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion qClass qRel)
open GlobalTheory.PairFourier (pairPt pairCoef qClass_eq tsum_natCast_eq pairPt_ne_zero)

namespace GlobalTheory.HilbFam

theorem fourier_with_support :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (G : (Emb F → ℂ) → ℂ),
      HasExpansion 𝔞 𝔟 k G → ∃ (Z : ℂ → ℂ) (a : F → ℂ), IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧
        a 0 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) ∧ (∀ ξ, ξ ≠ 0 → ∃ n : ℤ, a ξ = n) ∧
        (∀ ξ, ξ ≠ 0 → a ξ ≠ 0 → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ i : Emb F, 0 < i ξ) ∧
        ∀ w ∈ upperHalf F, HasSum (fun ξ : F ↦ a ξ * qPow ξ w)
          ((cK F k : ℂ) * G w / (omegaFactor 𝔞 : ℂ) ^ k) := by
  classical
  intro F _ _ _ k 𝔞 𝔟 G hG
  obtain ⟨Z, hZ, hE⟩ := hG
  set C : ℂ := (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) with hC
  let p : Quotient (qRel 𝔞 𝔟) → F := fun c ↦ (pairPt 𝔞 𝔟 c : F)
  let a' : F → ℂ := fun ξ ↦ ∑' c : p ⁻¹' {ξ}, (pairCoef 𝔞 𝔟 k c : ℂ)
  have ha' : ∀ ξ, a' ξ = ∑' c : p ⁻¹' {ξ}, (pairCoef 𝔞 𝔟 k c : ℂ) := fun _ ↦ rfl
  have hfib : ∀ (z : Emb F → ℂ) (ξ : F) (c : p ⁻¹' {ξ}),
      qClass 𝔞 𝔟 k z c = (pairCoef 𝔞 𝔟 k c : ℂ) * qPow ξ z := by
    rintro z ξ ⟨c, hc⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hc
    subst hc
    exact qClass_eq 𝔞 𝔟 k z c
  refine ⟨Z, fun ξ ↦ a' ξ + if ξ = 0 then C else 0, hZ, ?_, ?_, ?_, ?_⟩
  · show a' 0 + (if (0 : F) = 0 then C else 0) = C
    rw [if_pos rfl]
    have : IsEmpty (p ⁻¹' {0}) :=
      ⟨fun ⟨c, hc⟩ ↦ pairPt_ne_zero 𝔞 𝔟 c
        (Subtype.ext (Set.mem_singleton_iff.1 (Set.mem_preimage.1 hc)))⟩
    rw [ha']
    simp only [tsum_empty, zero_add]
  · intro ξ hξ
    set z₀ : Emb F → ℂ := fun _ ↦ Complex.I
    have hz₀ : z₀ ∈ upperHalf F := fun _ ↦ by simp [z₀]
    have hq : qPow ξ z₀ ≠ 0 := Complex.exp_ne_zero _
    have hsum : Summable (fun c : p ⁻¹' {ξ} ↦ (pairCoef 𝔞 𝔟 k c : ℂ)) := by
      have := ((hE z₀ hz₀).1.subtype (fun c ↦ c ∈ p ⁻¹' {ξ})).mul_right (qPow ξ z₀)⁻¹
      refine this.congr fun c ↦ ?_
      simp only [Function.comp_apply]
      rw [hfib z₀ ξ c, mul_assoc, mul_inv_cancel₀ hq, mul_one]
    obtain ⟨m, hm⟩ := tsum_natCast_eq _ hsum
    refine ⟨m, ?_⟩
    show a' ξ + (if ξ = 0 then C else 0) = _
    rw [if_neg hξ, add_zero, ha']
    simp only [hm]
    simp
  · intro ξ hξ hne
    have hne' : a' ξ ≠ 0 := by
      intro h
      apply hne
      show a' ξ + (if ξ = 0 then C else 0) = 0
      rw [if_neg hξ, h, add_zero]
    by_cases hem : IsEmpty (p ⁻¹' {ξ})
    · exact absurd (by rw [ha']; exact tsum_empty) hne'
    obtain ⟨c, hc⟩ := not_isEmpty_iff.1 hem
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hc
    subst hc
    exact ⟨(pairPt 𝔞 𝔟 c).2, c.out.2.2.2⟩
  · intro z hz
    obtain ⟨hs, heq⟩ := hE z hz
    have h1 := hs.hasSum.tsum_fiberwise p
    have h2 : (fun ξ ↦ ∑' c : p ⁻¹' {ξ}, qClass 𝔞 𝔟 k z c) = fun ξ ↦ a' ξ * qPow ξ z := by
      funext ξ
      rw [ha', ← tsum_mul_right]
      exact tsum_congr (hfib z ξ)
    rw [h2] at h1
    have h3 : HasSum (fun ξ : F ↦ (if ξ = 0 then C else 0) * qPow ξ z) C := by
      convert hasSum_ite_eq (0 : F) C using 1
      funext ξ
      split_ifs with h
      · subst h; simp [qPow]
      · simp
    have hv : (cK F k : ℂ) * G z / (omegaFactor 𝔞 : ℂ) ^ k =
        (∑' c, qClass 𝔞 𝔟 k z c) + C := by rw [heq]; ring
    show HasSum (fun ξ : F ↦ (a' ξ + if ξ = 0 then C else 0) * qPow ξ z)
      ((cK F k : ℂ) * G z / (omegaFactor 𝔞 : ℂ) ^ k)
    rw [hv]
    simp only [add_mul]
    exact h1.add h3

end GlobalTheory.HilbFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundleGeneratedOfModelIso
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.HodgeGenDesc

theorem exists_iso_of_extensions {U X : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X)
    (hX : Geo.Tor.IsNormalScheme X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    {A : Over U} [GrpObj A] {G G' : Over X} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    {φ : A.left ⟶ G.left} {ψ : A.left ⟶ G'.left} (hφ : IsGrpPullback A G j φ) (hψ : IsGrpPullback A G' j ψ) :
    ∃ e : G ≅ G', IsMonHom e.hom := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  have := hG.smooth
  have := hG'.smooth
  have := hG.separated
  have := hG'.separated
  obtain ⟨a, ha, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G j)
  obtain ⟨b, hb, -⟩ := grpPullback_iso hψ (isGrpPullback_pullback G' j)
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
    GlobalTheory.homExtension_semiAbelian_dvr X U j hX G G' hG hG' (a.inv ≫ b.hom) inferInstance
  obtain ⟨F₁, ⟨-, hF₁⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
    GlobalTheory.homExtension_semiAbelian_dvr X U j hX G' G hG' hG (b.inv ≫ a.hom) inferInstance
  obtain ⟨h₁, h₂⟩ := ExtUnique.comp_eq_id_of_pullback j (a.symm ≪≫ b) F F₁ hF' hF₁
  exact ⟨⟨F, F₁, h₁, h₂⟩, hF⟩

theorem lbIso_hodge_pull {S T : Scheme.{0}} {G : Over S} {G' : Over T} [GrpObj G] [GrpObj G'] [QuasiSeparated G.hom]
    {f : T ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {g : ℕ} (hg : GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega G) g) :
    LBIso ((hodge G g).pull f) (hodge G' g) :=
  (hg.lbIso_det_pullback f).trans (pull_isLB hg.isLB_det f) (hg.pullback f).isLB_det
    (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback h hg).isLB_det
    ((hg.pullback f).lbIso_det_of_iso (asIso (GlobalTheory.LieVB.omegaBase h)))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {R : Type} [CommRing R] {ω : R →+* c.F}

end GlobalTheory.HodgeGenDesc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicWeightedSquareIntegrableVanishes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff

namespace GlobalTheory

theorem holo_vanish_of_critical_integrable : ∀ {n : ℕ}, 0 < n → ∀ (u : V n → ℂ) (ρ : ℝ), 0 < ρ → DifferentiableOn ℂ u (Metric.ball 0 ρ) → ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) < ⊤ → u 0 = 0 := by
  intro n hn u ρ hρ hu hint
  by_contra hne
  have hb : Metric.ball (0 : V n) ρ ∈ nhds (0 : V n) := Metric.ball_mem_nhds 0 hρ
  set a := ‖u 0‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr hne
  have hc : ContinuousAt u 0 := hu.continuousOn.continuousAt hb
  have ev1 : ∀ᶠ z in nhds (0 : V n), a / 2 < ‖u z‖ :=
    hc.norm.eventually (Ioi_mem_nhds (by show a / 2 < a; linarith))
  obtain ⟨δ0, hδ0, hall⟩ := Metric.eventually_nhds_iff.mp (ev1.and (Filter.eventually_of_mem hb fun z hz => hz))
  set δ := min δ0 ρ with hδ
  have hδpos : 0 < δ := lt_min hδ0 hρ
  have hsub : Metric.ball (0 : V n) δ ⊆ Metric.ball (0 : V n) ρ := Metric.ball_subset_ball (min_le_right _ _)
  have hpt : ∀ z ∈ Metric.ball (0 : V n) δ,
      ENNReal.ofReal ((a / 2) ^ 2) * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤
        ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) := by
    intro z hz
    have hz0 : dist z 0 < δ0 := by
      rw [Metric.mem_ball] at hz; exact lt_of_lt_of_le hz (min_le_left _ _)
    have h1 := (hall hz0).1
    rw [← ENNReal.ofReal_mul (by positivity), neg_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    have hr : 0 ≤ ‖z‖ ^ (-(2 * (n : ℝ))) := Real.rpow_nonneg (norm_nonneg _) _
    have h2 : (a / 2) ^ 2 ≤ ‖u z‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1.le 2
    exact mul_le_mul_of_nonneg_right h2 hr
  have hlow : ENNReal.ofReal ((a / 2) ^ 2) * ∫⁻ z in Metric.ball (0 : V n) δ, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ)))
      ≤ ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ∫⁻ z in Metric.ball (0 : V n) δ, ENNReal.ofReal ((a / 2) ^ 2) * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ)))
        ≤ ∫⁻ z in Metric.ball (0 : V n) δ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) :=
          setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
      _ ≤ _ := lintegral_mono_set hsub
  rw [ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.crit_div hn hδpos,
    ENNReal.mul_top (by simp [ENNReal.ofReal_eq_zero, not_le]; positivity)] at hlow
  exact absurd (lt_of_le_of_lt hlow hint) (lt_irrefl _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomSpecPointsLevels
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem exists_spMap_affPt {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)
    {C : Type} [CommRing C] (x : Sp C ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U.1) :
    ∃ g : Sec s U.1 →+* C, spMap g ≫ affPt s U = x := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec x U.2 (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  refine ⟨(x.appLE U.1 ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom, ?_⟩
  change Spec.map (x.appLE U.1 ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom) ≫ U.2.fromSpec = x
  rw [Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem eq_of_spMap_eq {A C : Type} [CommRing A] [CommRing C] {g g' : A →+* C} (h : spMap g = spMap g') : g = g' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem eq_of_spMap_affPt {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)
    {C : Type} [CommRing C] {g g' : Sec s U.1 →+* C} (h : spMap g ≫ affPt s U = spMap g' ≫ affPt s U) : g = g' := by
  have : Mono (affPt s U) := @IsOpenImmersion.mono _ _ _ (IsAffineOpen.isOpenImmersion_fromSpec U.2)
  exact eq_of_spMap_eq ((cancel_mono _).1 h)

theorem red_over (D : Data) : D.i ≫ D.s = D.t := by
  obtain ⟨s₀, hpb, ht⟩ := D.red
  rw [ht, hpb.w]

variable {D : Data} (Λ : Lift D)

theorem Lift.isDPMorphism (U : AffOp D.X) (T : Thick D.κ D.t) (φ : (Λ.L.obj U).B →ₐ[D.R] T.B) :
    IsDPMorphism (Λ.L.obj U).δ T.δ (φ : (Λ.L.obj U).B →+* T.B) := by
  have hI : ∀ r ∈ D.I, algebraMap D.R T.B r ∈ T.J := fun r hr ↦ T.dp.1 (Ideal.mem_map_of_mem _ hr)
  refine IsDPMorphism.on_span (S := algebraMap D.R (Λ.L.obj U).B '' D.I) _ _ (Λ.gen U) ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    simpa using hI r hr
  · rintro n _ ⟨r, hr, rfl⟩
    rw [(Λ.L.obj U).dp.2 r hr]
    simpa using (T.dp.2 (n := n) r hr).symm

theorem Lift.hom_iff (U : AffOp D.X) (T : Thick D.κ D.t) (y : Sec D.s U.unop.1 →ₐ[D.R] T.B) :
    spMap (T.π.comp (y : Sec D.s U.unop.1 →+* T.B)) ≫ affPt D.s U.unop = T.x ≫ D.i ↔
      ∃ b : Λ.L.obj U ⟶ T, ∀ a, b.φ (Λ.e U a) = y a := by
  constructor
  · intro h
    let φ : (Λ.L.obj U).B →ₐ[D.R] T.B := y.comp (Λ.e U).symm.toAlgHom
    have hφ : ∀ a, φ (Λ.e U a) = y a := fun a ↦ by simp [φ]
    have hd := Λ.isDPMorphism U T φ
    let φ₀ : (Λ.L.obj U).B₀ →+* T.B₀ := RingHom.liftOfSurjective (Λ.L.obj U).π (Λ.L.obj U).surj
      ⟨T.π.comp (φ : (Λ.L.obj U).B →+* T.B), fun b hb ↦
        (T.ker _).2 (hd.1 (Ideal.mem_map_of_mem _ (((Λ.L.obj U).ker b).1 hb)))⟩
    have hc : ∀ b, φ₀ ((Λ.L.obj U).π b) = T.π (φ b) := fun b ↦
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ b
    refine ⟨⟨φ, φ₀, hc, hd, ?_⟩, hφ⟩
    have := D.mono_i
    rw [← cancel_mono D.i, Category.assoc, ← Λ.pt U, ← h, ← Category.assoc, ← Cris.spMap_comp]
    congr 2
    exact RingHom.ext fun a ↦ (hc _).trans (congrArg T.π (hφ a))
  · rintro ⟨b, hb⟩
    rw [← b.pt, Category.assoc, ← Λ.pt U, ← Category.assoc, ← Cris.spMap_comp]
    congr 2
    exact RingHom.ext fun a ↦ ((b.comm _).trans (congrArg T.π (hb a))).symm

theorem Lift.hom_spec : ∀ (D : Data) (Λ : Lift D), (∀ (U : AffOp D.X) (T : Thick D.κ D.t) (y : Sec D.s U.unop.1 →ₐ[D.R] T.B), spMap (T.π.comp (y : Sec D.s U.unop.1 →+* T.B)) ≫ affPt D.s U.unop = T.x ≫ D.i ↔ ∃ b : Λ.L.obj U ⟶ T, ∀ a, b.φ (Λ.e U a) = y a) ∧ (∀ (U : AffOp D.X) (T : Thick D.κ D.t), ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ g : Sec D.s U.unop.1 →+* T.B₀, spMap g ≫ affPt D.s U.unop = T.x ≫ D.i ∧ ∀ r, g (algebraMap D.R _ r) = T.π (algebraMap D.R T.B r)) ∧ (∀ (U : AffOp D.X) (C : Type) [CommRing C] (g g' : Sec D.s U.unop.1 →+* C), spMap g ≫ affPt D.s U.unop = spMap g' ≫ affPt D.s U.unop → g = g') ∧ ∃ N₀, ∀ N, N₀ ≤ N → ∀ U, IsLev (Λ.L.obj U).δ N := by
  intro D Λ
  refine ⟨Λ.hom_iff, fun U T h ↦ ?_, fun U C _ g g' h ↦ eq_of_spMap_affPt _ _ h, ?_⟩
  · obtain ⟨g, hg⟩ := exists_spMap_affPt D.s U.unop _ h
    refine ⟨g, hg, fun r ↦ ?_⟩
    have : spMap (g.comp (algebraMap D.R (Sec D.s U.unop.1))) = spMap (T.π.comp (algebraMap D.R T.B)) := by
      rw [Cris.spMap_comp, ← affPt_w, ← Category.assoc, hg, Category.assoc, red_over, T.w]
    exact RingHom.congr_fun (eq_of_spMap_eq this) r
  · obtain ⟨N₀, h⟩ := (isDPNilpotent_iff_exists_isLevel D.κ).1 D.nil
    refine ⟨N₀, fun N hN U ↦ ?_⟩
    have h' : fil D.κ N = ⊥ := eq_bot_iff.2 (le_of_le_of_eq (ExpBij.dpFil_anti D.κ hN) h)
    have := fil_le_map_fil _ _ D.κ _ _ (Λ.L.obj U).δ _ (Λ.L.obj U).dp (Λ.gen U) N
    rw [h', Ideal.map_bot] at this
    exact eq_bot_iff.2 this

end GlobalTheory.PDForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormKilledByPowerOfTripleChartProduct
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

namespace GlobalTheory.FormalAlg.TripleKill

theorem rs_rs {X : Scheme} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    rs X h2 (rs X h1 x) = rs X (h2.trans h1) x := by
  simp only [rs]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem ev_triple_kill : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e d : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous d → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → ∀ i j l, rs (Y e).left (inf_le_left.trans inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i) (C.ev e i F) = 0 → ∃ L : ℕ, ∀ m, C.ev e m ((MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X l) ^ L * F) = 0 := by
  intro R _ I Y β hpb n C e d F hF hI i j l h0
  have hlev := (_root_.GlobalTheory.FormalAlg.LiftRatios.lifted_ratios_mod R I Y β hpb n C).1
  have htr := GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hpb n C e d F hF hI
  have key : ∀ m, ∃ L : ℕ, (C.ρ e m i * C.ρ e m j * C.ρ e m l) ^ L * C.ev e m F = 0 := by
    intro m
    apply exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen _ (C.aff e m)
    have hb : (Y e).left.basicOpen (C.ρ e m i * C.ρ e m j * C.ρ e m l) =
        (C.D e m ⊓ C.D e i) ⊓ (C.D e m ⊓ C.D e j) ⊓ (C.D e m ⊓ C.D e l) := by
      rw [Scheme.basicOpen_mul, Scheme.basicOpen_mul, hlev, hlev, hlev]
    have hW1 : (Y e).left.basicOpen (C.ρ e m i * C.ρ e m j * C.ρ e m l) ≤ C.D e m ⊓ C.D e i :=
      hb.le.trans (inf_le_left.trans inf_le_left)
    have hW2 : (Y e).left.basicOpen (C.ρ e m i * C.ρ e m j * C.ρ e m l) ≤ C.D e i ⊓ C.D e j ⊓ C.D e l :=
      hb.le.trans (le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
        (inf_le_left.trans (inf_le_right.trans inf_le_right))) (inf_le_right.trans inf_le_right))
    change rs (Y e).left ((Y e).left.basicOpen_le _) (C.ev e m F) = 0
    have h1 := (htr m i).2.2
    have h2 : rs (Y e).left hW1 (rs (Y e).left (inf_le_left : C.D e m ⊓ C.D e i ≤ C.D e m) (C.ev e m F)) = 0 := by
      rw [h1, map_mul, rs_rs, ← rs_rs (inf_le_left.trans inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i) hW2, h0,
        map_zero, mul_zero]
    rw [rs_rs] at h2
    exact h2
  choose Lf hL using key
  refine ⟨Finset.univ.sup Lf, fun m => ?_⟩
  have hle : Lf m ≤ Finset.univ.sup Lf := Finset.le_sup (Finset.mem_univ m)
  have hev : C.ev e m ((MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X l) ^ Finset.univ.sup Lf * F) =
      (C.ρ e m i * C.ρ e m j * C.ρ e m l) ^ Finset.univ.sup Lf * C.ev e m F := by
    simp [Charts.ev, map_mul, map_pow]
  rw [hev, ← Nat.sub_add_cancel hle, pow_add (C.ρ e m i * C.ρ e m j * C.ρ e m l), mul_assoc, hL m, mul_zero]

end GlobalTheory.FormalAlg.TripleKill
end

