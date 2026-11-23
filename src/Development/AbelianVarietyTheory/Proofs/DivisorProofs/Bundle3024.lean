module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AutomorphicArithmetic.LocalEmbeddings.BadRepAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalShareSumBound
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2849
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2975
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2568
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GensOfPsiUnitOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2931
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2898

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormsOfArchimedeanStatementsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithIntersection_forms_of_archimedean_statements : ArchInteg → ArchRecip → GlobalTheory.Published.ArFormExists ∧ GlobalTheory.Published.ArMix ∧ GlobalTheory.Published.HeightProjection := by
  first | exact @GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection | exact GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection | (intros; apply GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadAtFromInputs
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.BadIndef

theorem finiteDimensional_of_lat {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hL : L.FG)
    (hs : Submodule.span K (L : Set V) = ⊤) : FiniteDimensional K V := by
  obtain ⟨s, rfl⟩ := hL
  refine Module.finite_def.2 ⟨s, ?_⟩
  rw [← Submodule.span_span_of_tower (𝓞 K) K (s : Set V)]
  exact hs


end GlobalTheory.BadIndef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleArchimedeanConstant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ReadMatch

theorem gbig_and {Q1 Q2 Q : GlobalTheory.SqTop.GP} (h1 : GlobalTheory.SqTop.GBig Q1) (h2 : GlobalTheory.SqTop.GBig Q2)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q1 G μ₀ C x b → Q2 G μ₀ C x b → Q G μ₀ C x b) : GlobalTheory.SqTop.GBig Q := by
  obtain ⟨A1, h1⟩ := h1
  obtain ⟨A2, h2⟩ := h2
  refine ⟨max A1 A2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, h1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, h2⟩ := h2 ε CF (le_of_max_le_right hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hL G => h G μ₀ C _ _
    (h1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G)
    (h2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G)⟩

end GlobalTheory.ReadMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyLatticeIdentificationEqId
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.LatId

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem second_diff_bal {X Y K I : Type} [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y] [Field K]
    [Fintype I] (e : X ≃ₗ[𝓞 E] Y) (s : I → K) (hs : ∀ k, s k ≠ 0) (ε : I → LinearMap.BilinForm ℤ Y)
    (hε : ∀ k, ε k ∈ balForms H.bar Y) (n : ℤ) (g : X → Kˣ)
    (hg : ∀ y, (((g y)⁻¹ : Kˣ) : K) = ∏ k, s k ^ (n * ε k (e y) (H.w0 • e y))) (a a' : X) :
    (((g (a + a'))⁻¹ * g a * g a' : Kˣ) : K) = ∏ k, s k ^ (n * ε k (e a) (e a')) := by
  have hw : H.w0 + H.bar H.w0 = 1 := GlobalTheory.PelPrim.cmHostUnit_add_conj_eq_one H
  have hg' : ∀ y, (g y : K) = (∏ k, s k ^ (n * ε k (e y) (H.w0 • e y)))⁻¹ := fun y => by
    rw [← hg, Units.val_inv_eq_inv_val, inv_inv]
  rw [Units.val_mul, Units.val_mul, hg, hg', hg', ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ (hs k), ← zpow_add₀ (hs k)]
  congr 1
  have h1 : ε k (e a') (H.w0 • e a) = ε k (e a) (H.bar H.w0 • e a') := by rw [(hε k).1, (hε k).2]
  have h2 : ε k (e a) (H.w0 • e a') + ε k (e a) (H.bar H.w0 • e a') = ε k (e a) (e a') := by
    rw [← map_add (f := _), ← add_smul, hw, one_smul]
  simp only [map_add (f := _), smul_add, LinearMap.add_apply, h1]
  rw [← h2]
  ring


set_option maxHeartbeats 1000000 in
theorem lattice_eq_id : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (∀ (x : 𝓞 E) (y : C.P.D.toPre.X), hD₂.xe (φ' (hD₁.xe.symm (x • y))) = x • hD₂.xe (φ' (hD₁.xe.symm y))) → (∀ p₀ : QkPt C.P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) l.M') (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) l.M'), p₁.y = hD₁.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ GlobalTheory.TInj.QImg b φ' p₁ p₂) → ∀ y : C.P.D.toPre.X, hD₂.xe (φ' (hD₁.xe.symm y)) = y := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns R _ _ _ hR C Cn V _ _ _ _ hVc f₁ f₂ hf₁ hf₂ lf₁ lf₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b ph hE₁ hE₂
    hM hlin hpairs
  letI := H.starRing
  have hn : 3 ≤ l.M' := l.three_le.trans (Nat.le_of_dvd (Nat.lcm_pos (by have := l.three_le; omega) l.A_pos)
    (Nat.dvd_lcm_left _ _))
  have hn1 : 1 ≤ l.M' := by omega
  set iw := Cn.ψ.comp MvPolynomial.C with hiwd
  have hiw : Function.Injective iw := by
    have hfl : iw.Flat := RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance) Cn.compl.2.2.1
    letI := iw.toAlgebra
    have : Module.Flat Cn.L.W R := hfl
    have : IsLocalHom (algebraMap Cn.L.W R) := Cn.ψ_loc
    have : Module.FaithfullyFlat Cn.L.W R := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective Cn.L.W R
  let s : Fin C.m ⊕ Fin Cn.N → R := fun k => Cn.ψ (MvPolynomial.X k)
  have hs0 : ∀ k, s k ≠ 0 := by
    rintro (k | k)
    · exact (Cn.bd k).trans_ne (C.s_ne_zero k)
    · exact (Cn.tor k).ne_zero
  obtain ⟨hev, hbi, hgen, -⟩ := GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws Cn.L.W Cn.L.D (𝓞 E) Cn.L.oa H.w0 l.M' Cn.L.even Cn.L.bimult Cn.L.w0 Cn.L.gen
  obtain ⟨T, ib, β₀, ββ₀, w₀, hF₀⟩ := _root_.GlobalTheory.TInjBase.main Cn.L.b Cn.L.D Cn.L.bimult Cn.L.gen l.M'
  obtain ⟨g, hD, hg, hxe, -⟩ := Cn.data
  let ε : Fin C.m ⊕ Fin Cn.N → LinearMap.BilinForm ℤ (Fin T.r → ℤ) := fun k =>
    (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X).compl₁₂ ib.symm.toIntLinearEquiv.toLinearMap ib.symm.toIntLinearEquiv.toLinearMap
  have hε : ∀ k a b, ε k (ib a) (ib b) = (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) a b := fun k a b =>
    congrArg₂ (fun x y => (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) x y) (ib.symm_apply_apply a) (ib.symm_apply_apply b)
  let e : C.P.D.toPre.X ≃+ (Fin T.r → ℤ) := Cn.e.toAddEquiv.trans ib
  have he : ∀ y, e y = ib (Cn.e y) := fun _ => rfl
  obtain ⟨β, ββ, w, hF⟩ := _root_.GlobalTheory.TInj.from_rescale_pull T l.M' (mulDeg Cn.L.D l.M') hev hbi hgen ib β₀ ββ₀ w₀ hF₀ R iw hiw C.P.D.toPre g hD
    s ε e (fun y => congrArg ib (hxe y).symm) (fun a a' => by
      simp only [he, hε]
      exact second_diff_bal Cn.e _ (fun k => (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (hs0 k)) _
        (fun k => (Cn.ε k).2) _ g hg a a')
  obtain ⟨ββ₁, w₁, hF₁⟩ := GlobalTheory.TInj.from_pull T ε l.M' R V _ C.P.D iw s e β ββ w f₁ D₁.toPre hD₁ hf₁ hF
  obtain ⟨ββ₂, w₂, hF₂⟩ := GlobalTheory.TInj.from_pull T ε l.M' R V _ C.P.D iw s e β ββ w f₂ D₂.toPre hD₂ hf₂ hF

  let ga : C.P.D.toPre.X ≃ₗ[𝓞 E] C.P.D.toPre.X :=
    { (hD₁.xe.symm.trans ph).trans hD₂.xe with map_smul' := hlin }
  have hga : ∀ y, ga y = hD₂.xe (ph (hD₁.xe.symm y)) := fun _ => rfl

  have hcong : ∀ y, ∃ z, ga y = y + l.M' • z := by
    intro y
    obtain ⟨p₀, hp₀y, -⟩ := GlobalTheory.TInj.exists_qkPt_tautPt T ε l.M' R C.P.D.toPre iw s e β ββ w C.P.D.tau_bimult hF hs0
      (AlgebraicClosure (FractionRing R)) (e y)
    obtain ⟨p₁, p₂, hy₁, -, hy₂, -, p', hp', -, z, hz, -⟩ := hpairs p₀
    rw [hp₀y, AddEquiv.symm_apply_apply] at hy₁ hy₂
    have h : hD₂.xe p₂.y = hD₂.xe (ph p₁.y) + l.M' • hD₂.xe z := by rw [hz, map_add (f := _), hp', map_nsmul]
    rw [hy₂, hy₁, AddEquiv.apply_symm_apply] at h
    refine ⟨-(hD₂.xe z), ?_⟩
    rw [smul_neg, hga, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h.symm

  have hbd : ∀ f : R →+* V, Function.Injective f → IsLocalHom f → ∀ k, f (s (.inl k)) ∈ maximalIdeal V ∧ f (s (.inl k)) ≠ 0 :=
    fun f hf hl k => ⟨map_nonunit f _ (show Cn.ψ _ ∈ maximalIdeal R from (Cn.bd k).symm ▸ C.s_mem k),
      (map_ne_zero_iff f hf).2 (hs0 _)⟩
  have hpu := _root_.GlobalTheory.TInj.PerUnit.monomial_ratio_unit T ε l.M' V D₁.toPre D₂.toPre _ _ _ _ ββ₁ w₁ _ _ _ _ ββ₂ w₂ b ph _ D₁.tau_bimult D₂.tau_bimult
    hF₁ hF₂ hM
  let gz : (Fin T.r → ℤ) ≃ₗ[ℤ] (Fin T.r → ℤ) := ((e.symm.trans ga.toAddEquiv).trans e).toIntLinearEquiv
  have hgz : ∀ y, gz (e y) = e (ga y) := fun y => by
    show e (ga (e.symm (e y))) = e (ga y)
    rw [AddEquiv.symm_apply_apply]
  obtain ⟨d₁, d₂, hd₁, hd₂, hsum⟩ := _root_.GlobalTheory.TInj.coneval V T.r C.m Cn.N l.M' hn1 ε (fun k => f₁ (s k)) (fun k => f₂ (s k))
    gz (hbd f₁ hf₁ lf₁) (fun k => (Cn.tor k).map f₁) (hbd f₂ hf₂ lf₂)
    (fun k => (Cn.tor k).map f₂) (fun a a' => by
      obtain ⟨u, hu⟩ := hpu (hD₁.xe.symm (e.symm a)) (hD₁.xe.symm (e.symm a'))
      simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply] at hu
      exact ⟨u, hu⟩)
  have hδ : ∀ k a a', C.δ k a a' = ε (.inl k) (e a) (e a') := fun k a a' => by rw [he, he, hε, Cn.cone]; rfl
  have hform : ∀ y z, ∑ i, (d₂ i : ℤ) * C.δ i (ga y) (ga z) = ∑ i, (d₁ i : ℤ) * C.δ i y z := by
    intro y z
    have h := LinearMap.congr_fun₂ hsum (e y) (e z)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, pull_apply, LinearEquiv.coe_coe, hgz, nsmul_eq_mul] at h
    simp only [hδ]
    exact h.symm
  have hpos : ∀ y, y ≠ 0 → 0 < ∑ i, C.δ i y y := by
    intro y hy
    obtain ⟨i, hi⟩ := C.mono.exists_pos (maximalIdeal.isMaximal _).ne_top hy
    have hi' : 0 < C.δ i y y :=
      (mul_pos_iff_of_pos_left (show (0 : ℤ) < l.M' by exact_mod_cast (by omega : 0 < l.M'))).1 hi
    exact Finset.sum_pos' (fun j _ => C.cone.nonneg j y) ⟨i, Finset.mem_univ _, hi'⟩
  have hid := GlobalTheory.UCanon.eq_self_of_cone_congMod H φ (min Dw.p Dw.q) hφ hns C.P.D.toPre.X C.rank C.m C.δ C.cone hpos ga
    d₂ d₁ hd₂ hd₁ hform l.M' hn hcong
  intro y
  exact hid y

end GlobalTheory.UCanon.LatId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyPeriodsInCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.PerCoord

theorem comp_C_injective {W R σ : Type} [CommRing W] [IsLocalRing W] [CommRing R] [IsLocalRing R]
    (ψ : MvPolynomial σ W →+* R) (hf : ψ.Flat) (hl : IsLocalHom (ψ.comp MvPolynomial.C)) :
    Function.Injective (ψ.comp MvPolynomial.C) := by
  have hC : (MvPolynomial.C : W →+* MvPolynomial σ W).Flat := by
    show (algebraMap W (MvPolynomial σ W)).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have h := RingHom.Flat.comp hC hf
  letI := (ψ.comp MvPolynomial.C).toAlgebra
  haveI : Module.Flat W R := h
  haveI : IsLocalHom (algebraMap W R) := hl
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := W) (B := R)
  exact FaithfulSMul.algebraMap_injective W R

theorem prod_zpow_add {K Ix : Type} [Field K] [Fintype Ix] (c : Ix → K) (hc : ∀ k, c k ≠ 0) (A B C D : Ix → ℤ)
    (h : ∀ k, A k = D k + B k + C k) :
    ∏ k, c k ^ A k = (∏ k, c k ^ D k) * (∏ k, c k ^ B k) * ∏ k, c k ^ C k := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [h k, zpow_add₀ (hc k), zpow_add₀ (hc k)]

end GlobalTheory.UCanon.PerCoord

namespace GlobalTheory.UCanon.PerCoord

theorem second_diff {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X Y : Type} [AddCommGroup X]
    [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y] (e : X ≃ₗ[𝓞 E] Y) {β : LinearMap.BilinForm ℤ Y}
    (hβ : β ∈ balForms H.bar Y) (a b : X) :
    β (e (a + b)) (H.w0 • e (a + b)) = β (e a) (e b) + β (e a) (H.w0 • e a) + β (e b) (H.w0 • e b) := by
  have h1 : β (e b) (H.w0 • e a) = β (e a) (H.bar H.w0 • e b) := (hβ.1 _ _).trans (hβ.2 _ _ _)
  have h2 : β (e a) (H.w0 • e b) + β (e a) (H.bar H.w0 • e b) = β (e a) (e b) := by
    rw [← map_add (f := _), ← add_smul, ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.cmHostUnit_add_conj_eq_one, one_smul]
  simp only [map_add (f := _), smul_add, LinearMap.add_apply]
  rw [h1]
  linarith

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∃ (ε' : Module.Basis (Fin C.m ⊕ Fin Cn.N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre), (∀ k, (ε' k : LinearMap.BilinForm ℤ C.P.D.toPre.X) = pull Cn.e.toLinearMap (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X)) ∧ FromBase C.P.D.toPre τ₀ (Cn.ψ.comp MvPolynomial.C) ∧ TauIn C.P.D.toPre τ₀ (fun k => Cn.ψ (MvPolynomial.X (finSumFinEquiv.symm k))) (fun k => (l.M' : ℤ) • (ε' (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hR C Cn
  classical
  obtain ⟨g, hD, hg, -, -⟩ := Cn.data
  have hinj := comp_C_injective Cn.ψ Cn.compl.2.2.1 Cn.ψ_loc
  obtain ⟨-, hb, hU, -⟩ := letI := H.starRing
    GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws Cn.L.W Cn.L.D (𝓞 E) Cn.L.oa H.w0 l.M' Cn.L.even Cn.L.bimult Cn.L.w0 Cn.L.gen
  obtain ⟨τ₁, hτ, hF⟩ := GlobalTheory.UTautData.gens_fromBase _ hinj _ _ hD hb hU
  refine ⟨Cn.ε.map (pullBalEquiv H.bar Cn.e), τ₁, fun k => rfl, hF, fun a b => ?_⟩
  have hs : ∀ k, algebraMap R (FractionRing R) (Cn.ψ (MvPolynomial.X k)) ≠ 0 := by
    intro k
    refine (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 ?_
    rcases k with i | k
    · rw [Cn.bd i]; exact C.s_ne_zero i
    · exact (Cn.tor k).ne_zero
  refine ⟨(hτ a b).1, g a * g b * (g (a + b))⁻¹, ?_, fun z J hJ => ?_⟩
  · have hsplit := prod_zpow_add _ hs
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e (a + b)) (H.w0 • Cn.e (a + b)))
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e a) (H.w0 • Cn.e a))
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e b) (H.w0 • Cn.e b))
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e a) (Cn.e b))
      (fun k => by simp only [second_diff H Cn.e (Cn.ε k).2 a b]; ring)
    have hne : ∀ y, (((g y)⁻¹ : (FractionRing R)ˣ) : FractionRing R) ≠ 0 := fun y => Units.ne_zero _
    have e1 : (((g a * g b * (g (a + b))⁻¹ : (FractionRing R)ˣ)) : FractionRing R) =
        (((g (a + b))⁻¹ : (FractionRing R)ˣ) : FractionRing R) * ((((g a)⁻¹ : (FractionRing R)ˣ) : FractionRing R))⁻¹ *
          ((((g b)⁻¹ : (FractionRing R)ˣ) : FractionRing R))⁻¹ := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, inv_inv]; ring
    have hA := hne a
    have hB := hne b
    rw [hg a] at hA
    rw [hg b] at hB
    rw [e1, hg (a + b), hsplit, hg a, hg b]
    beta_reduce at hA hB ⊢
    have canc : ∀ T x y : FractionRing R, x ≠ 0 → y ≠ 0 → T * x * y * x⁻¹ * y⁻¹ = T := fun T x y hx hy => by
      field_simp
    rw [canc _ _ _ hA hB]
    refine Eq.trans ?_ (Equiv.prod_comp finSumFinEquiv.symm (fun k => algebraMap R (FractionRing R)
      (Cn.ψ (MvPolynomial.X k)) ^ (((l.M' : ℤ) • ((Cn.ε.map (pullBalEquiv H.bar Cn.e)) k :
        LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b))).symm
    exact Finset.prod_congr rfl fun k _ => rfl
  · have h1 := GlobalTheory.TauTwist.val_tau_rescale (D := C.P.D.toPre) g (a := a) (b := b)
      (x := (g a * g b)⁻¹ * g (a + b)) (by group) (𝟙 _) hJ
    have h2 := (hτ a b).2 z J hJ
    have hx : g a * g b * (g (a + b))⁻¹ = ((g a * g b)⁻¹ * g (a + b))⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    rw [hx]
    show _ = GlobalTheory.TauTwist.unitAt (𝟙 _) z _ * _
    rw [map_inv]
    exact eq_inv_mul_of_mul_eq (h1.symm.trans h2)

end GlobalTheory.UCanon.PerCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterValueMemLocalUnitsMulSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterValue_mem_localUnits_mul_subfield : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (a : D.X) (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N₁ = 1 → DefOver k₀ (spMap ev ≫ b.left ≫ β) →
    ∀ χ : LB.Gen (LB.LinComb D.P.L ![(D.c a * b).left, (D.c a).left, b.left, (η[D.P.A]).left] DegPre.gtε),
      (χ.IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c a) (toUnit T ≫ b ^ i) (toUnit T ≫ b) = val χ T.hom z J ^ N₁) →
    ∃ c ∈ k₀, (val χ (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a * b).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ b.left))⁻¹ *
        GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (η[D.P.A]).left)).val * toStk z c := by
  first | exact @GlobalTheory.USep.EvG.chi_mem | exact GlobalTheory.USep.EvG.chi_mem | (intros; apply GlobalTheory.USep.EvG.chi_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreCechCocycleInTangentSpan
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.FibreSpan

theorem pull_cocycle {Y Z : Scheme.{0}} (ι : Y ⟶ Z) {J : Type} (W : J → Z.Opens) (d : ∀ i i' : J, Γ(Z, W i ⊓ W i'))
    (hd : ∀ i i' i'', resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (d i i') + resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (d i' i'') = resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (d i i'')) :
    ∀ i i' i'', resG Y (inf_le_left : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') ((ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (d i i')) + resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'') ((ι.appLE (W i' ⊓ W i'') (ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'') (fun _ hx => hx)).hom (d i' i'')) = resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i'') ((ι.appLE (W i ⊓ W i'') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i'') (fun _ hx => hx)).hom (d i i'')) := by
  intro i i' i''
  have e0 : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ⊓ ι ⁻¹ᵁ W i'' ≤ ι ⁻¹ᵁ (W i ⊓ W i' ⊓ W i'') := fun _ hx => hx
  have := congrArg (ι.appLE (W i ⊓ W i' ⊓ W i'') _ e0).hom (hd i i' i'')
  simp only [map_add (f := _), ← CommRingCat.comp_apply, Scheme.Hom.map_appLE] at this
  simp only [← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_map, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
  exact this

theorem sum_divisible_eq_sum_mul {R : Type} [CommRing R] {n : ℕ} (a : R) (x F : Fin n → R) :
    ∑ b, -(a * x b) * F b = -a * ∑ b, x b * F b := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring


set_option maxHeartbeats 1600000 in
theorem fibre_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ θ : Fin n → Γ(X, U.1), ∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i' - ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i') := by
  intro E _ _ _ H X t hP hA hK U n v hv hu δ hδ hδR hδT J W j hW hcov hWU hj m hm A _ ι hpb c hc
  have hκ := _root_.GlobalTheory.KappaCoc.kappa_cocycle E H X t U n δ hδ J W j hW hcov hWU hj
  have hz := _root_.GlobalTheory.FibreScalar.fibre_scalar_zero E H X t U m A ι hpb
  have hind : ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', ∑ b, (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b)) * (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∀ b, r b ∈ m :=
    fun r h'' hr => GlobalTheory.T.fibreIndependence_logDerivatives_closedFibre E H X t hP hA hK U n v hv hu δ hδ hδR hδT J W j hW hcov hWU hj m hm A ι hpb r h''
      (fun i i' => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        exact (Finset.sum_congr rfl fun b _ => map_mul _ _ _).trans (hr i i'))
  obtain ⟨r, ⟨b₀, hb₀⟩, h', hh⟩ := _root_.GlobalTheory.FibreH1.fibre_dim E H X t hP hA U n v hv hu J W hW hcov hWU m hm A ι hpb
    (Fin.cons (fun i i' => (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i')) (fun b i i' => (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)))
    (fun b => Fin.cases (pull_cocycle ι W c hc) (fun b => pull_cocycle ι W _ (hκ b)) b)
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hh
  have hr0 : r 0 ∉ m := by
    intro h0
    have := hind (fun b => r b.succ) h' (fun i i' => by
      have h1 := hh i i'
      rw [hz (W i ⊓ W i') (inf_le_left.trans (hWU i)) (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx) (r 0) h0, zero_mul, zero_add] at h1
      exact h1)
    refine hb₀ ?_
    cases b₀ using Fin.cases with
    | zero => exact h0
    | succ b => exact this b
  have hex := hm.exists_inv hr0
  choose y i₀ hi₀ hy using hex
  refine ⟨fun b => -(y * r b.succ), fun i => (ι.appLE (W i) (ι ⁻¹ᵁ W i) le_rfl).hom ((t.G.hom.appLE U.1 (W i) (hWU i)).hom y) * h' i, fun i i' => ?_⟩
  have key1 : ∀ (O : t.G.left.Opens) (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (O' : A.left.Opens) (hO' : O' ≤ ι ⁻¹ᵁ O)
      (x : Γ(X, U.1)), (ι.appLE O O' hO').hom ((t.G.hom.appLE U.1 O hO).hom x) =
        ((ι ≫ t.G.hom).appLE U.1 O' (hO'.trans fun _ h => hO h)).hom x := by
    intro O hO O' hO' x
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key2 : ∀ (O O' : A.left.Opens) (h : O' ≤ O) (hO : O ≤ (ι ≫ t.G.hom) ⁻¹ᵁ U.1) (x : Γ(X, U.1)),
      resG A.left h (((ι ≫ t.G.hom).appLE U.1 O hO).hom x) = ((ι ≫ t.G.hom).appLE U.1 O' (h.trans hO)).hom x := by
    intro O O' h hO x
    have e := Scheme.Hom.appLE_map (ι ≫ t.G.hom) hO (homOfLE h).op
    exact congrArg (fun φ => φ.hom x) e
  have hle : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ≤ (ι ≫ t.G.hom) ⁻¹ᵁ U.1 := fun x hx => hWU i hx.1
  have h1 := hh i i'
  have hy' : ((ι ≫ t.G.hom).appLE U.1 _ hle).hom y * ((ι ≫ t.G.hom).appLE U.1 _ hle).hom (r 0) = 1 := by
    have := congrArg ((ι ≫ t.G.hom).appLE U.1 _ hle).hom hy
    rw [map_add (f := _), map_mul, map_one] at this
    have h0 : ((ι ≫ t.G.hom).appLE U.1 _ hle).hom i₀ = 0 :=
      (key1 (W i ⊓ W i') (inf_le_left.trans (hWU i)) (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx) i₀).symm.trans
        (hz (W i ⊓ W i') (inf_le_left.trans (hWU i)) (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx) i₀ hi₀)
    rw [h0, add_zero] at this
    exact this
  have hA1 : ∀ x : Γ(X, U.1), (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom x) =
      ((ι ≫ t.G.hom).appLE U.1 _ hle).hom x := fun x => key1 _ _ _ _ x
  have hB1 : resG A.left (inf_le_left : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ≤ ι ⁻¹ᵁ W i) ((ι.appLE (W i) (ι ⁻¹ᵁ W i) le_rfl).hom ((t.G.hom.appLE U.1 (W i) (hWU i)).hom y)) = ((ι ≫ t.G.hom).appLE U.1 _ hle).hom y := by
    rw [key1, key2]
  have hB2 : resG A.left (inf_le_right : ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i' ≤ ι ⁻¹ᵁ W i') ((ι.appLE (W i') (ι ⁻¹ᵁ W i') le_rfl).hom ((t.G.hom.appLE U.1 (W i') (hWU i')).hom y)) = ((ι ≫ t.G.hom).appLE U.1 _ hle).hom y := by
    rw [key1, key2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum]
  simp only [map_neg, map_mul, hA1, hB1, hB2] at h1 ⊢
  rw [sum_divisible_eq_sum_mul]
  linear_combination (((ι ≫ t.G.hom).appLE U.1 _ hle).hom y) * h1 + (-((ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i'))) * hy'

end GlobalTheory.FibreSpan
end

