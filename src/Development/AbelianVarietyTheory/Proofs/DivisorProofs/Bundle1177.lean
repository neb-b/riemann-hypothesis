module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1135
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicLeviProjectionUnipotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTauFixedUnitCentralizerIsNormStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_tauFixed_unit_centralizer_is_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G (β : G.C) = β →
    ∀ (Y : G.Cˣ) (s : ℚ), (Y : G.C) * β * sh G (Y : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (Y : G.C)).Separable → (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) →
      IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) → IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) →
      inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) = m →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  first | (exact @GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep) | (exact GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep) | (intros; apply GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWhittakerEquivariantBumpMirabolicStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_whittaker_equivariant_bump_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1)) := by
  first | exact @GlobalTheory.WhitBump.exists_bump | exact GlobalTheory.WhitBump.exists_bump | (intros; apply GlobalTheory.WhitBump.exists_bump <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineBoundaryFunctionsOfIsProjOver
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open ProjSpace

theorem IsAmpleLB.exists_affine_boundary_functions {Y : Scheme.{0}} {L : LB Y} (h : IsAmpleLB L) (U : Y.Opens)
    (x : Y) (hx : x ∈ U) : ∃ (V : Y.Opens) (n : ℕ) (u : Fin n → Γ(Y, V)), x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧
      ∀ z : Y, ∃ (Q : Y.Opens) (η : Γ(Y, Q)) (l : Fin n), z ∈ Q ∧ Y.basicOpen η = Q ⊓ V ∧
        resG Y (inf_le_right : Q ⊓ V ≤ V) (u l) * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1 := by
  obtain ⟨k, hk, hg⟩ := h.exists_isGenerated_pow
  obtain ⟨d, -, t, hxt, hle, ha⟩ := ((isAmpleLB_pow_iff h.isLB hk).2 h).exists_affine_le hx
  obtain ⟨n, s, hs⟩ := hg.pow d
  refine ⟨nonzeroLocus t, n, fun l => secRatio t (s l), hxt, hle, ha, fun z => ?_⟩
  obtain ⟨l, hl⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ z))
  refine ⟨nonzeroLocus (s l), secRatio (s l) t, l, hl, basicOpen_secRatio _ _, ?_⟩
  rw [secRatio_mul_secRatio t (s l) t inf_le_right inf_le_left, secRatio_self, map_one]

theorem exists_affine_boundary_functions_of_isProjOver :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProjOver p → ∀ (U : Y.Opens) (x : Y), x ∈ U →
      ∃ (V : Y.Opens) (n : ℕ) (u : Fin n → Γ(Y, V)), x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧
        ∀ z : Y, ∃ (Q : Y.Opens) (η : Γ(Y, Q)) (l : Fin n), z ∈ Q ∧ Y.basicOpen η = Q ⊓ V ∧
          resG Y (inf_le_right : Q ⊓ V ≤ V) (u l) * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1 := by
  rintro Y p ⟨N, i, hi, -⟩ U x hx
  exact ((isAmple_projective_O_one ℂ N).pull_of_isAffineHom i).exists_affine_boundary_functions U x hx

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteFreeNbhd
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.GenFinEtField

theorem finrank_app_eq_residueDegree {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    (h : f (genericPoint Y) = genericPoint X) {U : X.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen (f ⁻¹ᵁ U)) (hxU₀ : genericPoint X ∈ U) :
    letI := (f.app U).hom.toAlgebra
    Module.finrank Γ(X, U) Γ(Y, f ⁻¹ᵁ U) = f.residueDegree (genericPoint Y) := by
  have hxU : f (genericPoint Y) ∈ U := h ▸ hxU₀
  letI := (f.app U).hom.toAlgebra
  letI := (X.evaluation U _ hxU).hom.toAlgebra
  letI : Algebra Γ(Y, f ⁻¹ᵁ U) (Y.residueField (genericPoint Y)) :=
    (Y.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Y)).hom.toAlgebra
  letI : Algebra Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (f.app U ≫ Y.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) Γ(Y, f ⁻¹ᵁ U) (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(X, U) (X.residueField (f (genericPoint Y)))
      (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' congr($(Scheme.evaluation_naturality f _ hxU).hom).symm
  haveI := GlobalTheory.ProjFin.isFractionRing_evaluation X hU h hxU
  haveI := GlobalTheory.ProjFin.isFractionRing_evaluation Y hU' rfl hxU
  exact (IsFractionRing.finrank_eq Γ(X, U) (X.residueField (f (genericPoint Y)))
    Γ(Y, f ⁻¹ᵁ U) (Y.residueField (genericPoint Y))).symm

theorem exists_affine_finite_etale_free : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k], IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧ (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = π.residueDegree (genericPoint Y)) := by
  intro k _ X Y _ _ p q _ hX hY π hπ hg hδ
  have hpP : IsProper p := by
    obtain ⟨N, j, _, hj⟩ := hX
    have := isProper_str k N
    exact hj ▸ inferInstance
  have hqP : IsProper q := by
    obtain ⟨N, j, _, hj⟩ := hY
    have := isProper_str k N
    exact hj ▸ inferInstance
  have : IsSeparated (π ≫ p) := hπ ▸ (inferInstance : IsSeparated q)
  have hsep : IsSeparated π := IsSeparated.of_comp π p
  have : LocallyOfFiniteType (π ≫ p) := hπ ▸ (inferInstance : LocallyOfFiniteType q)
  have hlft : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨U₀, hU₀, hxU₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X))
  have hyU₀ : genericPoint Y ∈ π ⁻¹ᵁ U₀ := by
    show π (genericPoint Y) ∈ U₀
    rw [hg]; exact hxU₀
  obtain ⟨V₀, hV₀, hyV₀, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hyU₀
  haveI : Nonempty U₀ := ⟨⟨_, hxU₀⟩⟩
  haveI : Nonempty V₀ := ⟨⟨_, hyV₀⟩⟩
  letI : Algebra Γ(X, U₀) Γ(Y, V₀) := (π.appLE U₀ V₀ hVle).hom.toAlgebra
  haveI : IsNoetherianRing Γ(X, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  haveI : CharZero Γ(X, U₀) :=
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U₀ le_top).hom.charZero_iff
      (RingHom.injective (R := k) _)).1 ‹CharZero k›
  haveI : FaithfulSMul Γ(X, U₀) Γ(Y, V₀) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (GlobalTheory.appLE_injective_of_genericPoint_map π hg ⟨_, hyV₀⟩ hVle)
  haveI : Algebra.FiniteType Γ(X, U₀) Γ(Y, V₀) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType π hlft ⟨U₀, hU₀⟩ ⟨V₀, hV₀⟩ hVle
  haveI : Algebra.IsAlgebraic Γ(X, U₀) Γ(Y, V₀) := GlobalTheory.GenDegAlg.isAlgebraic_appLE π hg hδ hU₀ ⟨_, hyV₀⟩ hVle
  obtain ⟨a₁, ha₁, H₁⟩ := GlobalTheory.finite_away_of_isAlgebraic_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  obtain ⟨a₂, ha₂, H₂⟩ := GlobalTheory.free_away_mul_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  obtain ⟨a₃, ha₃, H₃⟩ := GlobalTheory.GenericEtale.exists_etale_away_of_isAlgebraic (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  have ha : a₁ * a₂ * a₃ ≠ 0 := mul_ne_zero (mul_ne_zero ha₁ ha₂) ha₃
  have hUU₀ : X.basicOpen (a₁ * a₂ * a₃) ≤ U₀ := X.basicOpen_le _
  have hUa : IsAffineOpen (X.basicOpen (a₁ * a₂ * a₃)) := hU₀.basicOpen _
  have hxU : genericPoint X ∈ X.basicOpen (a₁ * a₂ * a₃) := by
    have hne : X.basicOpen (a₁ * a₂ * a₃) ≠ ⊥ := fun h => ha ((basicOpen_eq_bot_iff _).1 h)
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen (a₁ * a₂ * a₃)).isOpen).2
      ⟨z, trivial, hz⟩
  set U : X.Opens := X.basicOpen (a₁ * a₂ * a₃) with hU_def
  set V : Y.Opens := Y.basicOpen (π.appLE U₀ V₀ hVle (a₁ * a₂ * a₃)) with hV_def
  have hVV₀ : V ≤ V₀ := Y.basicOpen_le _
  have hVe : V = V₀ ⊓ π ⁻¹ᵁ U := Scheme.basicOpen_appLE π V₀ U₀ hVle _
  have hVU : V ≤ π ⁻¹ᵁ U := by rw [hVe]; exact inf_le_right
  have hVa : IsAffineOpen V := hV₀.basicOpen _
  have hyV : genericPoint Y ∈ V := by
    rw [hVe]; exact ⟨hyV₀, show π (genericPoint Y) ∈ U from hg ▸ hxU⟩
  letI iA : Algebra Γ(X, U₀) Γ(X, U) := (X.presheaf.map (homOfLE hUU₀).op).hom.toAlgebra
  letI iB : Algebra Γ(Y, V₀) Γ(Y, V) := (Y.presheaf.map (homOfLE hVV₀).op).hom.toAlgebra
  letI iAB : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V hVU).hom.toAlgebra
  letI iAB' : Algebra Γ(X, U₀) Γ(Y, V) := (π.appLE U₀ V (hVV₀.trans hVle)).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U₀) Γ(X, U) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.map_appLE hVU (homOfLE hUU₀).op).symm)
  haveI : IsScalarTower Γ(X, U₀) Γ(Y, V₀) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.appLE_map hVle (homOfLE hVV₀).op).symm)
  haveI hlA : IsLocalization.Away (a₁ * a₂ * a₃) Γ(X, U) :=
    hU₀.isLocalization_of_eq_basicOpen _ (homOfLE hUU₀) rfl
  haveI hlB : IsLocalization.Away (algebraMap Γ(X, U₀) Γ(Y, V₀) (a₁ * a₂ * a₃)) Γ(Y, V) :=
    hV₀.isLocalization_of_eq_basicOpen _ (homOfLE hVV₀) rfl
  have e1 : a₁ * (a₂ * a₃) = a₁ * a₂ * a₃ := (mul_assoc _ _ _).symm
  have e2 : a₂ * (a₁ * a₃) = a₁ * a₂ * a₃ := by ring
  have e3 : a₃ * (a₁ * a₂) = a₁ * a₂ * a₃ := by ring
  have hfin : Module.Finite Γ(X, U) Γ(Y, V) :=
    H₁ (a₂ * a₃) Γ(X, U) Γ(Y, V) (by rw [e1]; exact hlA) (by rw [e1]; exact hlB)
  have hfree : Module.Free Γ(X, U) Γ(Y, V) :=
    H₂ (a₁ * a₃) Γ(X, U) Γ(Y, V) (by rw [e2]; exact hlA) (by rw [e2]; exact hlB)
  have het : Algebra.Etale Γ(X, U) Γ(Y, V) :=
    H₃ (a₁ * a₂) Γ(X, U) Γ(Y, V) (by rw [e3]; exact hlA) (by rw [e3]; exact hlB)
  have hpre : π ⁻¹ᵁ U = V := GlobalTheory.preimage_eq_of_finite_appLE π hUa hVa ⟨_, hyV⟩ hVU hfin
  have key : ∀ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U → (π.appLE U W hW).hom.Etale →
      (π.appLE U W hW).hom.Finite →
      (letI := (π.appLE U W hW).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, W)) →
      (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧
      (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) := by
    rintro W hW rfl h1 h2 h3
    rw [Scheme.Hom.app_eq_appLE]
    exact ⟨h1, h2, h3⟩
  obtain ⟨h1, h2, h3⟩ := key V hVU hpre.symm het hfin hfree
  exact ⟨U, hUa, hxU, hpre ▸ hVa, h1, h2, h3, finrank_app_eq_residueDegree π hg hUa (hpre ▸ hVa) hxU⟩

end GlobalTheory.GenFinEtField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgEquivFractionFieldOfLocalRingOfVarietyP
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem locModel_fracField_algEquiv : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ]
  (R : Subring K) (π : R →+* κ), IsLocModel (algebraMap ℂ K) R →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) → Function.Injective π →
  ∃ e : K ≃ₐ[ℂ] κ, ∀ r : R, e r = π r := by
  intro K κ _ _ _ _ R π hR hc hsurj hinj
  haveI : FaithfulSMul R K :=
    (faithfulSMul_iff_algebraMap_injective R K).mpr Subtype.val_injective
  haveI : IsFractionRing R K := IsFractionRing.of_field R K (fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hR.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change z = a / b
    rw [eq_div_iff hb0, e])
  let φ : K →+* κ := IsFractionRing.lift hinj
  have hφ : ∀ r : R, φ (algebraMap R K r) = π r := fun r => IsFractionRing.lift_algebraMap hinj r
  have hφc : ∀ a : ℂ, φ (algebraMap ℂ K a) = algebraMap ℂ κ a := by
    intro a
    have := hφ ⟨algebraMap ℂ K a, hR.const_mem a⟩
    rw [← hc a (hR.const_mem a)]
    exact this
  let ψ : K →ₐ[ℂ] κ := { φ with commutes' := hφc }
  have hbij : Function.Bijective ψ := by
    refine ⟨ψ.toRingHom.injective, fun f => ?_⟩
    obtain ⟨a, b, hb, e⟩ := hsurj f
    have hb' : (b : K) ≠ 0 := by
      intro h
      apply hb
      have : b = 0 := Subtype.ext h
      rw [this, map_zero]
    refine ⟨(a : K) / b, ?_⟩
    change φ ((a : K) / b) = f
    rw [map_div₀]
    have ha := hφ a
    have hb2 := hφ b
    change φ (a : K) = π a at ha
    change φ (b : K) = π b at hb2
    rw [ha, hb2, div_eq_iff hb, e]
  refine ⟨AlgEquiv.ofBijective ψ hbij, fun r => ?_⟩
  exact hφ r

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionClearingRationalFunctionDenomi
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSNef.DenOne

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.LBGerm

variable {X : Scheme.{0}} [IsIntegral X]

theorem isRatSec_lbPow {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) (τ : ℕ) :
    IsRatSec (lbPow L τ) fun c => r (c PUnit.unit) ^ τ := fun c c' h => by
  have l : (lbPow L τ).U c ⊓ (lbPow L τ).U c' ≤ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have e : (lbPow L τ).g c c' = res l (L.g (c PUnit.unit) (c' PUnit.unit)) ^ τ := by
    change ∏ _k : PUnit, _ = _
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rfl
  rw [e, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
    ← mul_pow, hr _ _ (l h)]
  exact congrArg (fun a => (a * _) ^ τ) (fnOf_resG l h _).symm

theorem res_mem_secOn (L : LB X) (V : X.Opens) (a : Γ(X, V)) :
    (fun J : PUnit → L.ι => resG X (inf_le_left : V ⊓ powChart L J ≤ V) a) ∈ secOn (lbPow L 0) V :=
  mem_secOn_of_germ _ fun y i j hV hi hj => by
    rw [gm_lbPow_g 0 (𝟙 X) y i j hi hj, pow_zero, Units.val_one, one_mul]
    exact (gs_res (𝟙 X) y _ (⟨hV, hi⟩ : y ∈ V ⊓ (lbPow L 0).U i) a).trans
      (gs_res (𝟙 X) y _ (⟨hV, hj⟩ : y ∈ V ⊓ (lbPow L 0).U j) a).symm

theorem unitAt_ne_zero {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : UnitAt x f) : f ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  exact (hc.map (algebraMap _ X.functionField)).ne_zero

theorem exists_den_one : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (f : X.functionField),
    ∃ (c : ℕ) (g : X.functionField), 0 < c ∧ g ≠ 0 ∧ g ∈ P.H 0 c ∧ g * f ∈ P.H 0 c := by
  intro k _ X _ p D _ P hA f
  haveI := hA.compactSpace
  haveI := hA.quasiSeparatedSpace
  have hL := hA.isLB
  obtain ⟨n, hn, s, hgs, haff⟩ := hA.exists_affine (genericPoint X)
  haveI : Nonempty (nonzeroLocus s) := ⟨⟨_, hgs⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X (nonzeroLocus s) haff
  obtain ⟨a, b, hb, hf⟩ := IsFractionRing.div_surjective (A := Γ(X, nonzeroLocus s)) f
  change fnOf _ hgs a / fnOf _ hgs b = f at hf
  have hβ : fnOf _ hgs b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  obtain ⟨Na, ha⟩ := exists_sec_eq_pow_mul hL s _ (res_mem_secOn P.A.B (nonzeroLocus s) a)
  obtain ⟨Nb, hb'⟩ := exists_sec_eq_pow_mul hL s _ (res_mem_secOn P.A.B (nonzeroLocus s) b)
  obtain ⟨u, hu⟩ := ha (max Na Nb + 1) (by omega)
  obtain ⟨v, hv⟩ := hb' (max Na Nb + 1) (by omega)
  have hρ := isRatSec_lbPow P.hr' (0 + n * (max Na Nb + 1))
  obtain ⟨e, he⟩ := RepDict.exists_quot (isLB_lbPow hL (0 + n * (max Na Nb + 1))) hρ
  have hmem : ∀ w : (lbPow P.A.B (0 + n * (max Na Nb + 1))).Sec,
      e w ∈ P.H 0 ((0 + n * (max Na Nb + 1) : ℕ) : ℤ) := by
    intro w x i j _ hj
    have hJ : x ∈ (lbPow P.A.B (0 + n * (max Na Nb + 1))).U (fun _ => j) := mem_powChart.2 hj
    have h1 := he w (fun _ => j) (gen_mem hJ)
    simp only [Pair.loc, zpow_zero, mul_one, zpow_natCast]
    rw [← Units.val_pow_eq_pow_val, h1]
    exact regAt_fnOf hJ _ _
  obtain ⟨j₀, hj₀⟩ := exists_chart hL (genericPoint X)
  have hJ₀ : genericPoint X ∈ powChart P.A.B (fun _ => j₀) := mem_powChart.2 hj₀
  have hVJ : genericPoint X ∈ nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) := ⟨hgs, hJ₀⟩
  have key : ∀ (w : (lbPow P.A.B (0 + n * (max Na Nb + 1))).Sec) (a' : Γ(X, nonzeroLocus s)),
      resG X (inf_le_right : nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) ≤ powChart P.A.B (fun _ => j₀))
          (powFn w (fun _ => j₀)) =
        resG X (inf_le_right : nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) ≤ powChart P.A.B (fun _ => j₀))
          (powFn s (fun _ => j₀)) ^ (max Na Nb + 1) *
        resG X (inf_le_left : nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) ≤ nonzeroLocus s) a' →
      e w * (P.r' j₀ : X.functionField) ^ (0 + n * (max Na Nb + 1)) =
        fnOf _ hJ₀ (powFn s (fun _ => j₀)) ^ (max Na Nb + 1) * fnOf _ hgs a' := by
    intro w a' h
    have h' := congrArg (fnOf _ hVJ) h
    rw [map_mul, map_pow, fnOf_resG, fnOf_resG, fnOf_resG] at h'
    rw [← Units.val_pow_eq_pow_val]
    exact (he w _ hJ₀).trans h'
  have eu := key u a (hu _)
  have ev := key v b (hv _)
  have hS : fnOf _ hJ₀ (powFn s (fun _ => j₀)) ≠ 0 := by
    exact unitAt_ne_zero ((unitAt_fnOf_iff hJ₀ hJ₀ _).2 ((mem_nonzeroLocus_iff_basicOpen s hJ₀).1 hgs))
  have hR : (P.r' j₀ : X.functionField) ^ (0 + n * (max Na Nb + 1)) ≠ 0 := pow_ne_zero _ (P.r' j₀).ne_zero
  refine ⟨0 + n * (max Na Nb + 1), e v, by positivity, fun h0 => ?_, hmem v, ?_⟩
  · rw [h0, zero_mul] at ev
    exact mul_ne_zero (pow_ne_zero _ hS) hβ ev.symm
  · have e1 : e u = _ := eq_div_of_mul_eq hR eu
    have e2 : e v = _ := eq_div_of_mul_eq hR ev
    have : e v * f = e u := by
      rw [e1, e2, ← hf]
      field_simp
    rw [this]
    exact hmem u

end GlobalTheory.HSNef.DenOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementNegativeAtTwoEmbeddingsStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_element_negative_at_two_embeddings : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L], Module.finrank K L = 2 → ∀ σ : L →+* L, σ ≠ RingHom.id L → (∀ x : K, σ (algebraMap K L x) = algebraMap K L x) → (∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ ε ε' : L →+* ℂ, ε ≠ ε' → ε ≠ ComplexEmbedding.conjugate ε' → ∃ h : K, h ≠ 0 ∧ (ε (algebraMap K L h)).re < 0 ∧ (ε' (algebraMap K L h)).re < 0 ∧ (∀ φ : L →+* ℂ, φ ≠ ε → φ ≠ ComplexEmbedding.conjugate ε → φ ≠ ε' → φ ≠ ComplexEmbedding.conjugate ε' → 0 < (φ (algebraMap K L h)).re) ∧ ∀ v : HeightOneSpectrum (𝓞 K), ∃ z : v.adicCompletion K ⊗[K] L, Algebra.norm (v.adicCompletion K) z = algebraMap K (v.adicCompletion K) h := by
  first | (exact @GlobalTheory.QuadSigns.exists_signs) | (exact GlobalTheory.QuadSigns.exists_signs) | (intros; apply GlobalTheory.QuadSigns.exists_signs  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicLeviProjectionUnipotentStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockUpperParabolic_levi_projection_unipotent : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E), ∃ (s : GLw a w × GLw b w →* GlobalTheory.LeviDesc.parP a n w) (π : GlobalTheory.LeviDesc.parP a n w →* GLw a w × GLw b w) (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) →* GlobalTheory.LeviDesc.parP a n w), (∀ m, (s m : GLw n w) = blk h w m 0) ∧ (∀ X, (u X : GLw n w) = blk h w 1 (Multiplicative.toAdd X)) ∧ (∀ m, π (s m) = m) ∧ Function.Injective u ∧ (∀ p, π p = 1 ↔ ∃ X, u X = p) ∧ (∀ k ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)), s k ∈ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ∧ (∀ k ∈ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w), π k ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) ∧ (∀ X, u X ∈ (GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w) ↔ X ∈ intMat a b w) := by
  first | exact @GlobalTheory.LeviDesc.LeviHoms.levi_homs | exact GlobalTheory.LeviDesc.LeviHoms.levi_homs | (intros; apply GlobalTheory.LeviDesc.LeviHoms.levi_homs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffOfMemColSpan
section
open Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.StdPar
open scoped TensorProduct

namespace GlobalTheory.ColumnSpanCoefficients

theorem exists_coeff_of_mem_colSpan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n r s : ℕ} (hs : s ≤ r) (X : Matrix (Fin n) (Fin r) E) (I : Set (Fin r)) (P : Fin s → Prop)
    (hI : ∀ i ∈ I, ∃ j : Fin s, Fin.castLE hs j = i ∧ P j) {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colSpan F X I) :
    ∃ a : Fin s → AF F ⊗[F] E, (∀ j, ¬ P j → a j = 0) ∧ adMat F (X.submatrix id (Fin.castLE hs)) *ᵥ a = y := by
  classical
  rw [colSpan] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, rfl, hj⟩ := hI i hi
    refine ⟨Pi.single j 1, fun j' hj' => ?_, ?_⟩
    · rw [Pi.single_apply, if_neg]
      rintro rfl
      exact hj' hj
    · rw [Matrix.mulVec_single_one]
      ext r
      rfl
  | zero => exact ⟨0, fun _ _ => rfl, Matrix.mulVec_zero _⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hz
    exact ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], Matrix.mulVec_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨c • a, fun j hj => by simp [ha j hj], Matrix.mulVec_smul _ _ _⟩

end GlobalTheory.ColumnSpanCoefficients
end

