module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2495
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosureCompleteNormalFiniteExtensi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_integralClosure_isCN_finite_local : ∀ (V₀ : Type) [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀], IsCN V₀ → ∀ (L : Type) [Field L] [Algebra (FractionRing V₀) L] [FiniteDimensional (FractionRing V₀) L], ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V₀ →+* V₁) (σ : L →+* FractionRing V₁), IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ ∀ x : V₀, σ (algebraMap (FractionRing V₀) L (algebraMap V₀ (FractionRing V₀) x)) = algebraMap V₁ (FractionRing V₁) (ρ x) := by
  intro V₀ _ _ _ hV L _ _ _
  obtain ⟨hN, hIC, hC, hCZ⟩ := hV
  haveI := hN
  haveI := hIC
  haveI := hC
  haveI := hCZ
  let K₀ := FractionRing V₀
  letI : Algebra V₀ L := ((algebraMap K₀ L).comp (algebraMap V₀ K₀)).toAlgebra
  haveI : IsScalarTower V₀ K₀ L := .of_algebraMap_eq fun _ => rfl
  haveI : CharZero K₀ := IsFractionRing.charZero_of_isFractionRing V₀
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K₀ L).injective
  haveI : Algebra.IsSeparable K₀ L := inferInstance
  let V₁ := integralClosure V₀ L
  haveI : Module.Finite V₀ V₁ := IsIntegralClosure.finite V₀ K₀ L V₁
  haveI hN₁ : IsNoetherianRing V₁ := IsIntegralClosure.isNoetherianRing V₀ K₀ L V₁
  haveI : IsFractionRing V₁ L := IsIntegralClosure.isFractionRing_of_finite_extension V₀ K₀ L V₁
  haveI : IsIntegrallyClosed V₁ := integralClosure.isIntegrallyClosedOfFiniteExtension K₀
  haveI : HenselianLocalRing V₀ := GlobalTheory.henselianLocalRing_of_isAdicComplete V₀
  haveI : IsLocalRing V₁ := GlobalTheory.TameKummer.isLocalRing_of_finite V₀ V₁
  have hinj : Function.Injective (algebraMap V₀ V₁) := by
    intro a b h
    have h' := congrArg (algebraMap V₁ L) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply V₀ K₀ L, IsScalarTower.algebraMap_apply V₀ K₀ L b] at h'
    exact IsFractionRing.injective V₀ K₀ ((algebraMap K₀ L).injective h')
  haveI : CharZero V₁ := charZero_of_injective_algebraMap hinj
  haveI : IsLocalHom (algebraMap V₀ V₁) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : (maximalIdeal V₁).comap (algebraMap V₀ V₁) = maximalIdeal V₀ :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := V₀) (maximalIdeal V₁))
    have hmem : a ∈ (maximalIdeal V₁).comap (algebraMap V₀ V₁) := by
      rw [hm]; exact hna
    exact hmem ha
  have hcompl : IsAdicComplete (maximalIdeal V₁) V₁ :=
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local V₀ V₁
  let e : L ≃ₐ[V₁] FractionRing V₁ := IsLocalization.algEquiv (nonZeroDivisors V₁) L (FractionRing V₁)
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, algebraMap V₀ V₁, e.toRingEquiv.toRingHom,
    ⟨hN₁, inferInstance, hcompl, inferInstance⟩, hinj, RingHom.finite_algebraMap.mpr inferInstance,
    inferInstance, fun x => ?_⟩
  have hx : algebraMap K₀ L (algebraMap V₀ K₀ x) = algebraMap V₁ L (algebraMap V₀ V₁ x) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv]
  rw [hx, AlgEquiv.commutes]

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCoefficientSectionCoordinateRigStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_coefficient_section_coordinate_rig : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : GtPt D (𝟙_ (Over (Sp R)))) (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, g.b.left] (DegPre.lineε 1))), t.IsGen → ∀ (k : ℕ) (α : D.X) (s : D.SecB k α), ∃ a : R, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → sval s (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z a * (val (L := D.P.L) D.rig r z J ^ k).val := by
  first | exact @GlobalTheory.GtCoeff.exists_coeff_gt | exact GlobalTheory.GtCoeff.exists_coeff_gt | (intros; apply GlobalTheory.GtCoeff.exists_coeff_gt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedDataCompleteDVRExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralFramedData_completeDVR_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V), (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ (G' : SAB H (Sp T'.V)) (t'' : SAB H (Sp T'.Fr)) (_ : SABMap t'' t' (spMap iT)) (_ : SABMap t'' G' (spMap (algebraMap T'.V T'.Fr))) (n' : ℕ) (w' : Fin n' → (epsR T'.V ⟶ G'.G)) (θ' : G'.PP.L.Sec) (k' : KeyIn T'.Fr), IsLieBasis w' ∧ Generates (X := G'.G) θ' ∧ IsFibreOf k' G'.G G'.PP.L G'.PP.rig θ' w' (algebraMap T'.V T'.Fr) ∧ KeyPB k' k iT := by
  first | exact @GlobalTheory.FramedExt.exists_framed_ext | exact GlobalTheory.FramedExt.exists_framed_ext | (intros; apply GlobalTheory.FramedExt.exists_framed_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorRigidificationAllLevelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_generator_rigidification_all_levels : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (h : 𝟙_ (Over (Sp V)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp V)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g → ∀ f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1)), f.IsGen → ∃ t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, g.b.left] (DegPre.lineε 1)), t.IsGen ∧ ∀ e : ℕ, GlobalTheory.Poinc.IntEval.TRel U h g.b f t e := by
  first | exact @GlobalTheory.Poinc.IntEval.exists_integral_frame | exact GlobalTheory.Poinc.IntEval.exists_integral_frame | (intros; apply GlobalTheory.Poinc.IntEval.exists_integral_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIrreducibleZeroSetSectionClosedIrreducible
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KrullZero

theorem coheight_le_one {Y : Scheme.{0}} [IsLocallyNoetherian Y] {N : LB Y} (hN : N.IsLB) (t : N.Sec) (w : Y)
    (hw : w ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t)
    (hgen : ∀ y : Y, w < y → y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t) : Order.coheight w ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_chart hN w
  obtain ⟨V, hV, hwV, hle⟩ := exists_isAffineOpen_mem_and_subset hk
  have hle' : V ≤ N.U k := hle
  set g : Γ(Y, V) := Y.presheaf.map (homOfLE hle').op (t.f k) with hg
  have hbo : Y.basicOpen g = V ⊓ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
    rw [hg, Scheme.basicOpen_res, ← GlobalTheory.nonzeroLocus_inf_chart, inf_comm _ (N.U k), ← inf_assoc,
      inf_eq_left.2 hle']
  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum Γ(Y, V), hV.fromSpec P = w := by
    have : w ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hwV
    exact this
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hmemb : ∀ Q : PrimeSpectrum Γ(Y, V), g ∈ Q.asIdeal ↔ hV.fromSpec Q ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
    intro Q
    have h1 : Q ∈ PrimeSpectrum.basicOpen g ↔ hV.fromSpec Q ∈ Y.basicOpen g := by
      rw [← hV.fromSpec_preimage_basicOpen]; rfl
    have h2 : hV.fromSpec Q ∈ V := by
      have := Set.mem_range_self (f := hV.fromSpec) Q
      rwa [hV.range_fromSpec] at this
    rw [hbo] at h1
    constructor
    · intro hgQ hQ
      exact (PrimeSpectrum.mem_basicOpen _ _).1 (h1.2 ⟨h2, hQ⟩) hgQ
    · intro hQ
      by_contra hgQ
      exact hQ (h1.1 ((PrimeSpectrum.mem_basicOpen _ _).2 hgQ)).2
  have hgP : g ∈ P.asIdeal := (hmemb P).2 (hP ▸ hw)
  have hmin : P.asIdeal ∈ (Ideal.span {g}).minimalPrimes := by
    refine ⟨⟨P.isPrime, (Ideal.span_singleton_le_iff_mem _).mpr hgP⟩, fun Q hQ hQP => ?_⟩
    have hgQ : g ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.2
    by_contra hne
    let Q' : PrimeSpectrum Γ(Y, V) := ⟨Q, hQ.1⟩
    have hsp : Q' ⤳ P := (PrimeSpectrum.le_iff_specializes Q' P).1 hQP
    have hsp' : hV.fromSpec Q' ⤳ w := hP ▸ hsp.map hV.fromSpec.continuous
    have hneq : hV.fromSpec Q' ≠ w := by
      rw [← hP]
      intro h
      have := hV.fromSpec.isOpenEmbedding.injective h
      exact hne (by rw [← this])
    have hlt : w < hV.fromSpec Q' := lt_of_le_not_ge (show w ≤ hV.fromSpec Q' from hsp') fun h => hneq (hsp'.antisymm h).eq
    exact (hmemb Q').1 hgQ (hgen _ hlt)
  have hh : P.asIdeal.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  let x : Spec Γ(Y, V) := P
  have eS := (asIso (hV.fromSpec.stalkMap x) ≪≫ Spec.stalkIso Γ(Y, V) x).commRingCatIsoToRingEquiv
  have hPh : (P.asIdeal.height : WithBot ℕ∞) = Order.coheight w := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal (Localization.AtPrime P.asIdeal),
      ← ringKrullDim_eq_of_ringEquiv eS, ← ringKrullDim_stalk_eq_coheight, hP]
  have : ((Order.coheight w : ℕ∞) : WithBot ℕ∞) ≤ ((1 : ℕ∞) : WithBot ℕ∞) := by
    rw [← hPh]; exact_mod_cast hh
  exact_mod_cast this

end GlobalTheory.KrullZero

namespace GlobalTheory.KrullZero


open GlobalTheory.MixHt in
theorem exists_irreducible_zero : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (M : LB X) (s : M.Sec) (C : Set X), M.IsLB → IsIrreducible C → IsClosed C →
    (C ∩ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X)).Nonempty → ¬ C ⊆ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X) →
    ∃ C' : Set X, IsIrreducible C' ∧ IsClosed C' ∧ C' ⊆ C \ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s : Set X) ∧
      topologicalKrullDim C ≤ topologicalKrullDim C' + 1 := by
  intro k _ X _ p D hX M s C hM hC hCc hmeet hnot
  set Z := ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s with hZ
  have hamb : IsAmb p := isAmb_of_isArithVar hX
  haveI : IsNoetherian X := hamb.isNoetherian
  obtain ⟨η, hη⟩ := QuasiSober.sober hC hCc
  have hηC : closure ({η} : Set X) = C := hη
  let i := cloι η
  have hambY : IsAmb (i ≫ p) := hamb.sub i
  haveI : IsNoetherian (clo η) := hambY.isNoetherian
  have hgi : i (genericPoint (clo η)) = η := cloι_genericPoint η
  have hWm : ∀ y : clo η, y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s i) ↔ i y ∈ Z := fun y => by
    rw [GlobalTheory.nonzeroLocus_secPull]; rfl
  have basic := hasDim_basic k X p hamb
  have basicY := hasDim_basic k (clo η) (i ≫ p) hambY
  obtain ⟨m, hm⟩ := basicY.1
  obtain ⟨d, -, hd⟩ := hm (genericPoint (clo η))
  have hdY : topologicalKrullDim (clo η) = d := (basicY.2.2.2.2.2 (clo η) d).1 hd
  have hdC : topologicalKrullDim C = d := by
    have h := (basic.2.2.2.2.1 (clo η) i (genericPoint (clo η)) d).2 hd
    rw [hgi] at h
    rw [← hηC]; exact h

  have hrange : C ⊆ Set.range i := by
    rw [← hηC]
    refine closure_minimal ?_ i.isClosedEmbedding.isClosed_range
    rintro _ rfl
    exact ⟨_, hgi⟩

  obtain ⟨x, hxC, hxZ⟩ := Set.not_subset.1 hnot
  obtain ⟨y₀, rfl⟩ := hrange hxC
  have hηZ : η ∈ Z := by
    obtain ⟨x', hx'C, hx'Z⟩ := hmeet
    rw [← hηC] at hx'C
    exact (specializes_iff_mem_closure.2 hx'C).mem_open Z.isOpen hx'Z

  obtain ⟨w, hw, hwmin⟩ := (InvImage.wf (Order.coheight : clo η → ℕ∞) wellFounded_lt).has_min
    {y | y ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s i)} ⟨y₀, fun h => hxZ ((hWm y₀).1 h)⟩
  obtain ⟨e, -, he⟩ := hm w
  have hce : Order.coheight w + (e : ℕ∞) = d := GlobalTheory.DimCoheight.coheight_add_eq k (clo η) (i ≫ p) hambY d hdY w e he
  have hfin : Order.coheight w < ⊤ := by
    refine lt_of_le_of_lt (le_self_add) (hce ▸ ENat.natCast_lt_top d)
  have hgen : ∀ y : clo η, w < y → y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (GlobalTheory.secPull s i) := by
    intro y hlt
    by_contra hy
    exact hwmin y hy (Order.coheight_strictAnti hlt ((Order.coheight_anti hlt.le).trans_lt hfin))
  have h1 : Order.coheight w ≤ 1 := coheight_le_one (LB.isLB_pull hM i) (GlobalTheory.secPull s i) w hw hgen
  have h0 : Order.coheight w ≠ 0 := by
    intro h0
    have hmax : IsMax w := Order.coheight_eq_zero.1 h0
    have hsp : genericPoint (clo η) ⤳ w := genericPoint_specializes w
    have hle : genericPoint (clo η) ≤ w := hmax (show w ≤ genericPoint (clo η) from hsp)
    have heq : w = genericPoint (clo η) := (hsp.antisymm hle).eq.symm
    have hgW := (hWm (genericPoint (clo η))).2 (by rw [hgi]; exact hηZ)
    rw [← heq] at hgW
    exact hw hgW
  have hc1 : Order.coheight w = 1 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h0)
  rw [hc1] at hce
  have hde : d = e + 1 := by
    have : ((e + 1 : ℕ) : ℕ∞) = d := by push_cast; rw [← hce, add_comm]
    exact_mod_cast this.symm
  refine ⟨closure {i w}, isIrreducible_singleton.closure, isClosed_closure, ?_, ?_⟩
  · refine closure_minimal ?_ (hCc.sdiff Z.isOpen)
    rintro _ rfl
    refine ⟨?_, fun h => hw ((hWm w).2 h)⟩
    have hs := (genericPoint_specializes w).map i.continuous
    rw [hgi] at hs
    rw [← hηC]
    exact specializes_iff_mem_closure.1 hs
  · have hC' : topologicalKrullDim (closure ({i w} : Set X)) = e := (basic.2.2.2.2.1 (clo η) i w e).2 he
    rw [hdC, hC', hde]
    push_cast
    exact le_rfl

end GlobalTheory.KrullZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionInverseRootTwistingSectionSpread
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.KeyRootTw

namespace GlobalTheory.KeyRootSpread

theorem exists_twSec_keyRoot_spread : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → UnramPts Xo c (badPrimes H l) → Nonempty (GlobalTheory.ShFam.KeySec Xo c) ∧ ∀ Z : Comp Xo c, ∃ t : TwSec U x Z (wtOf Dw 0 1), IntOff (badPrimes H l) t.hi ∧ ∀ w, t.hi w - t.lo w ≤ ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) := by
  intro E _ _ _ H Dw l Xo c r U hU x hx hF hpq hg hun
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := _root_.GlobalTheory.KeyFourth.exists_unit_secZ_keyRule κ k₁ k₂ k₆ E H Dw l Xo c _ e hpq
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨⟨ρ, hρmem⟩, hρ⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hU _ hσ0) hF hpq hKmem hKval
  have hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  have hval := _root_.GlobalTheory.KeyIntegralVal.key_valuation_bounds κ hkr E H Dw l Xo c _ e K hpq hg hKmem hKval
  have hC := fun σ : c.F →+* ℂ => _root_.GlobalTheory.KeyArchNorm.homN_key_const κ k₁ k₂ k₅ E H Dw l Xo c _ e (goodOf c σ) r (U (goodOf c σ)) x K
    (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) (hx _ (goodEmb_goodOf c σ)) ⟨⟨ρ, hρmem⟩⟩ hpq hKmem hKval
  choose C hCpos hClog hCeq using hC
  have hgE := card_frame_index Dw e
  have hsum : ∑ τ : E →+* ℂ, Dw.mult τ = Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) := by
    simp [Fintype.card_sigma]
  have hwt : ∀ (m : ℤ) (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → (wtOf Dw 0 m).1 (τ, i) = -m :=
    wtOf_zero_fst E H Dw
  have hex : exZ Dw (wtOf Dw 0 1) = -keyEx Dw := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · rfl
    · simp only [exZ, keyEx, Pi.neg_apply]
      exact hwt 1 τ i i.2
  have hadd : wtOf Dw 0 1 + wtOf Dw 0 (-1) = 0 := by
    rw [← wtOf_add, add_zero, add_neg_cancel, wtOf_zero]
  refine ⟨⟨⟨ρ, hρmem⟩⟩, fun Z => ?_⟩
  obtain ⟨a, ha, haK⟩ := hρ Z
  have hP : HasPts U Z := hasPts U hpq hg hU Z
  set s : Rul Xo c := idem Z * ((ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) with hs
  set s' : Rul Xo c := idem Z * (ρ : Rul Xo c) with hs'
  have hsm : s ∈ secZ Xo c (exZ Dw (wtOf Dw 0 1)) := by
    have := mul_mem_secZ (idem_mem_secZ Z) (inv_mem_secZ hρmem)
    rwa [zero_add, ← hex] at this
  have hsm' : s' ∈ secZ Xo c (exZ Dw (wtOf Dw 0 (-1))) := by
    have := mul_mem_secZ (idem_mem_secZ Z) hρmem
    have h2 : exZ Dw (wtOf Dw 0 (-1)) = keyEx Dw := by
      have h3 := exZ_add_eq (Dw := Dw) (wtOf Dw 0 1) (wtOf Dw 0 (-1))
      rw [hadd, hex] at h3
      have h4 : exZ Dw (0 : WTZ E) = 0 := by funext i; cases i <;> rfl
      rw [h4] at h3
      exact (neg_add_eq_zero.1 h3.symm).symm
    rwa [zero_add, ← h2] at this
  have hsupp : s ∈ suppOn Z := by rw [hs, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hsupp' : s' ∈ suppOn Z := by rw [hs', mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hnorm := fun σ : c.F →+* ℂ => fun z (hz : z ∈ framesOn (U (goodOf c σ)) Z) =>
    homN_root E H Dw l Xo c (goodOf c σ) r (U (goodOf c σ)) x Z ρ K a (C σ) ha (hCpos σ) haK (hCeq σ) z hz
      ((hP.1 σ).2 z hz)
  have hgood : ∀ σ, GoodEmb c σ → goodOf c σ = σ := fun σ h => if_pos h
  have hmono : ∀ (m : ℤ) (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ →
      (wtOf Dw 0 m).1 (τ, j) ≤ (wtOf Dw 0 m).1 (τ, i) := fun m τ i j hij hj => by
    rw [hwt m τ i (lt_of_le_of_lt hij hj), hwt m τ j hj]
  have hbd : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 1) s z ≤ D := by
    intro σ hσ
    refine ⟨(‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ), fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).1.le
  have hbd' : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 (-1)) s' z ≤ D := by
    intro σ hσ
    refine ⟨(‖σ a‖ * C σ) ^ ((1 / 4) : ℝ), fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).2.le
  let B : HeightOneSpectrum (𝓞 c.F) → ℝ := fun w =>
    ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ)
  have hbnd := fun w (v : Rul Xo c → EReal) (hv : v ∈ valOn Z w) =>
    val_root E H Dw l Xo c Z w v hv ρ K a (B w) ha haK (hval w v (valOn_subset Z w hv)).1
      (hval w v (valOn_subset Z w hv)).2
  let t : TwSec U x Z (wtOf Dw 0 1) :=
    { even := even_wtOf _ _
      sig := s
      inv := s'
      sig_mem := hsm
      inv_mem := by
        have h5 := exZ_neg_eq (Dw := Dw) (wtOf Dw 0 1)
        have h6 : -wtOf Dw 0 1 = wtOf Dw 0 (-1) := neg_eq_of_add_eq_zero_right hadd
        rw [← h5, h6]; exact hsm'
      idem_sig := by rw [hs, ← mul_assoc, idem_mul_idem]
      idem_inv := by rw [hs', ← mul_assoc, idem_mul_idem]
      mul_inv := by rw [hs, hs', mul_mul_mul_comm, idem_mul_idem, Units.inv_mul, mul_one]
      cInf := fun σ => (‖σ a‖ * C σ) ^ (-(1 / 4) : ℝ)
      cInf_pos := fun σ => Real.rpow_pos_of_pos (mul_pos (norm_pos_iff.2 ((map_ne_zero σ).2 ha)) (hCpos σ)) _
      norm_inf := fun σ z hz => by
        rw [(hnorm σ z hz).1, norm_goodOf]
      cusp_sig := fun G hG f hf =>
        _root_.GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z (wtOf Dw 0 1) s ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono 1) hsm hsupp hbd G hG f hf
      cusp_inv := fun G hG f hf => by
        have h7 := _root_.GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z (wtOf Dw 0 (-1)) s' ⟨⟨ρ, hρmem⟩⟩ hU hpq (even_wtOf _ _) (hmono (-1))
          hsm' hsupp' hbd' (G + wtOf Dw 0 1) (hG.add (even_wtOf _ _)) f hf
        rwa [add_assoc, hadd, add_zero] at h7
      lo := fun w => -(vAdd w a : ℝ) / 4 - B w
      hi := fun w => -(vAdd w a : ℝ) / 4
      lo_le := fun w v hv => (hbnd w v hv).1
      le_hi := fun w v hv => (hbnd w v hv).2
      finite_lo := by
        refine ((finite_vAdd ha).union (Set.finite_iUnion fun τ => finite_ord (embF c τ))).subset fun w hw => ?_
        by_contra hn
        simp only [Set.mem_union, Function.mem_support, Set.mem_iUnion, not_or, not_exists, not_not] at hn
        apply hw
        simp [B, hn.1, hn.2]
      finite_hi := by
        refine (finite_vAdd ha).subset fun w hw => ?_
        by_contra hn
        simp only [Function.mem_support, not_not] at hn
        apply hw
        simp [hn]
      pts := hP }
  refine ⟨t, ?_, fun w => ?_⟩
  · intro w hw
    obtain ⟨v, hv, hint⟩ := hun Z w hw
    have hB : B w = 0 := by
      refine Finset.sum_eq_zero fun τ _ => ?_
      rw [ord_conjDifferent_eq_zero c.F E (embF c τ) w fun p hp hd => hw p (mem_badPrimes.2 ⟨hp, Or.inr (Or.inr (Or.inl hd))⟩)]
      simp
    obtain ⟨h1, h2⟩ := hbnd w v hv
    rw [hB, sub_zero] at h1
    rcases hint s with h | ⟨n, hn⟩
    · rw [h] at h2; exact absurd h2 (by simp)
    · refine ⟨n, ?_⟩
      show -(vAdd w a : ℝ) / 4 = n
      rw [hn] at h1 h2
      exact le_antisymm (EReal.coe_le_coe_iff.1 h1) (EReal.coe_le_coe_iff.1 h2)
  · show -(vAdd w a : ℝ) / 4 - (-(vAdd w a : ℝ) / 4 - B w) ≤ B w
    linarith

end GlobalTheory.KeyRootSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPairsLowerBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_point_pairs_lower_base : ∀ {o : Type} [CommRing o] {ζ : o} {n : ℕ} (L : LowBase ζ n), 1 ≤ n → ∀ (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (J' : Ideal V) (D₀ : DegData R J) (D₁ D₂ : DegData V J') (ω : L.W →+* R) (β : D₀.toPre.P.A.left ⟶ L.T.B.left), IsGrpPullback D₀.toPre.P.A L.T.B (spMap ω) β → ∀ (f₁ f₂ : R →+* V) (hD₁ : IsPullDeg f₁ D₀.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ D₀.toPre D₂.toPre) (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j₁ j₂ : F₀ →+* F) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Ext f₁ j₁ → Ext f₂ j₂ → (∀ p₀ : QkPt D₀.toPre F₀ n, ∃ (p₁ : QkPt D₁.toPre F n) (p₂ : QkPt D₂.toPre F n), p₁.y = hD₁.xe.symm p₀.y ∧ Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ QImg b φ p₁ p₂) → (∀ l : Fin L.h ⊕ Fin L.h → ℤ, ∃ (p₁ : QkPt D₁.toPre F n) (p₂ : QkPt D₂.toPre F n), p₁.y = 0 ∧ p₁.g.b.left ≫ ((hD₁.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f₁)) ≫ β) ≫ L.β = (TF (R := V) F).hom ≫ spMap (f₁.comp ω) ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ p₂.y = 0 ∧ p₂.g.b.left ≫ ((hD₂.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f₂)) ≫ β) ≫ L.β = (TF (R := V) F).hom ≫ spMap (f₂.comp ω) ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ QImg b φ p₁ p₂) := by
  exact @GlobalTheory.TInj.exists_level_pairs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCanonicalMapPrimitiveDeRhamRigExtStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_canonical_map_primitiveDeRham_rigExt : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A), IsAbelianScheme A → ∃ L : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))), ∀ c x, IsCan t c x ↔ L c = x := by
  first | exact @GlobalTheory.PtExt.exists_canMap | exact GlobalTheory.PtExt.exists_canMap | (intros; apply GlobalTheory.PtExt.exists_canMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPulledBackPowerSectionOfLocalLiftsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pulledBackPowerSection_of_local_lifts : ∀ {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α) (k : ℕ), (∀ U : X'.Opens, Function.Injective (a.app U).hom) → ∀ (s : SecK L α k) (n : ℕ) (j : Fin n → L.ι) (W : Fin n → X'.Opens), (⨆ b, W b = ⊤) → ∀ (hW : ∀ b, W b ≤ f ⁻¹ᵁ L.U (j b)), (∀ b, ∃ y : Γ(X', W b), (a.app (W b)).hom y = (Y.presheaf.map (homOfLE (extLI_le_chart L f a α e (W b) (j b) (hW b))).op).hom (s.f (fun _ => j b))) → ∃ σ : SecK L f k, ∀ j' : Fin 1 → L.ι, (a.app (LB.wchart L (K := Fin 1) (fun _ => f) j')).hom (σ.f j') = (Y.presheaf.map (homOfLE (extLI_le_wchart L f a α e j')).op).hom (s.f j') := by
  first | exact @GlobalTheory.Mum.secK_lift_of_local_lift | exact GlobalTheory.Mum.secK_lift_of_local_lift | (intros; apply GlobalTheory.Mum.secK_lift_of_local_lift <;> assumption)
end

