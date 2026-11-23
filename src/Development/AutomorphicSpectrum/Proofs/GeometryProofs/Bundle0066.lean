module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0016
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0059
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0011
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.WeilBound.CoreStatements.IdealCycleValues.IsModelOverRamifiedBaseChange
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointLiftAlongIso
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem eq_of_isIso_restrict {W X' : Scheme.{0}} (f : X' ⟶ W) (U : W.Opens) (hU : IsIso (f ∣_ U)) {y y' : X'}
    (hy : f y ∈ U) (hy' : f y' ∈ U) (e : f y = f y') : y = y' := by
  haveI := IsOpenImmersion.of_isIso (f ∣_ U)
  let a : (f ⁻¹ᵁ U : Scheme) := ⟨y, hy⟩
  let a' : (f ⁻¹ᵁ U : Scheme) := ⟨y', hy'⟩
  have h : (f ∣_ U) a = (f ∣_ U) a' :=
    Subtype.ext (by rw [morphismRestrict_base_coe, morphismRestrict_base_coe]; exact e)
  exact congrArg Subtype.val ((f ∣_ U).isOpenEmbedding.injective h)

private theorem eq_closedPoint_of_isField {R : Type} [CommRing R] [IsLocalRing R] (hR : IsField R)
    (z : PrimeSpectrum R) : z = IsLocalRing.closedPoint R := by
  apply PrimeSpectrum.ext
  have h := (IsLocalRing.isField_iff_maximalIdeal_eq (R := R)).1 hR
  have h1 : z.asIdeal ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal z.isPrime.ne_top
  show z.asIdeal = IsLocalRing.maximalIdeal R
  rw [h] at h1 ⊢
  exact le_bot_iff.1 h1

private theorem eq_genPt_of_specializes_of_bijective {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) (y : X) (hy : y ⤳ genPt ξ) :
    y = genPt ξ := by
  have hF : IsField (X.presheaf.stalk (genPt ξ)) :=
    MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ hb).toMulEquiv
  have hy' : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]; exact hy
  obtain ⟨q, rfl⟩ := hy'
  rw [eq_closedPoint_of_isField hF q, Scheme.fromSpecStalk_closedPoint]

private theorem surjective_stalkClosedPointTo_of_comp {X Y : Scheme.{0}} {Ω : Type} [Field Ω]
    (g : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y) (ξ : Spec (CommRingCat.of Ω) ⟶ Y) (h : g ≫ f = ξ)
    (hξ : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) :
    Function.Surjective (Scheme.stalkClosedPointTo g).hom := by
  subst h
  rw [Scheme.stalkClosedPointTo_comp] at hξ
  intro z
  obtain ⟨a, ha⟩ := hξ z
  exact ⟨(Scheme.Hom.stalkMap f _).hom a, ha⟩

theorem exists_lift_isCptGen : ∀ (W X' : Scheme.{0}) (f : X' ⟶ W) (U : W.Opens) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ W),
    IsIso (f ∣_ U) → genPt ξ ∈ U → IsCptGen ξ → (∀ x : X', IsDomain (X'.presheaf.stalk x)) →
    ∃ ξ' : Sp Ω ⟶ X', ξ' ≫ f = ξ ∧ IsCptGen ξ' := by
  intro W X' f U Ω _ ξ hiso hU hξ hdom
  obtain ⟨hb, -⟩ := hξ
  have hr : Set.range ξ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [eq_closedPoint_of_isField (Field.toIsField Ω) z]
    exact hU
  let ξ' : Sp Ω ⟶ X' := IsOpenImmersion.lift U.ι ξ hr ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι
  have hfac : ξ' ≫ f = ξ := by
    simp only [ξ', Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]
  have hfg : f (genPt ξ') = genPt ξ := by
    have h3 := Scheme.Hom.comp_apply ξ' f (IsLocalRing.closedPoint Ω)
    rw [hfac] at h3
    exact h3.symm
  have hmem : genPt ξ' ∈ f ⁻¹ᵁ U := by
    show f (genPt ξ') ∈ U
    rw [hfg]; exact hU
  refine ⟨ξ', hfac, ?_⟩
  refine isCptGen_of_maximal_of_surjective hdom ξ' ?_ ?_
  · intro y hy
    have hyU : y ∈ f ⁻¹ᵁ U := hy.mem_open (f ⁻¹ᵁ U).isOpen hmem
    have h1 : f y ⤳ genPt ξ := by
      have h2 := hy.map f.continuous
      rwa [hfg] at h2
    exact eq_of_isIso_restrict f U hiso hyU hmem ((eq_genPt_of_specializes_of_bijective ξ hb (f y) h1).trans hfg.symm)
  · exact surjective_stalkClosedPointTo_of_comp ξ' f ξ hfac hb.2

end GlobalTheory.CompanionTheory.Ar.SncBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointMemDenseOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem genPt_mem_of_dense_open : ∀ (W : Scheme.{0}) [IsLocallyNoetherian W] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ W) (U : W.Opens), IsCptGen ξ → Dense (U : Set W) → genPt ξ ∈ U := by
  intro W _ Ω _ ξ U hξ hU
  have hcl := GlobalTheory.T.isClopen_specializations_genPt W Ω ξ hξ
  obtain ⟨q, hq, hqU⟩ := hU.inter_open_nonempty _ hcl.isOpen ⟨genPt ξ, specializes_rfl⟩
  exact hq.mem_open U.isOpen hqU

end GlobalTheory.CompanionTheory.Ar.SncBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBlockRefinement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem HodgeCpt.Flag.exists_recoord_rootLines : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (κ : K → K') (v : ∀ k, J k ≃ J' (κ k)) (tie' : CoordTie ℤ 𝔐.ξ fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) (xdeg : CMType H × Fin (D.p + D.q) → K' → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), Function.Injective κ ∧ (∀ k i, y' ⟨κ k, v k i⟩ = y ⟨k, i⟩) ∧ ∀ r, (Fl.rootLat r).IsDegOn Set.univ y' (xdeg r) (e r) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl
  classical
  haveI : Fintype (CMType H) := Fintype.ofFinite _
  have hlin : ∀ s, LinearIndependent Ω (Fl.b s) := by
    intro s
    letI := 𝔐.fn.toAlgebra
    obtain ⟨_, _, _, _, _, h4, _⟩ := Fl.generic
    exact h4 s
  have hgr : ∀ s i, ((𝔐.V s).gr (Fl.b s) i).IsVBOn Set.univ 1 ⊤ := fun s i =>
    (Lat.IsFlagVBOn.isVBOn_gr_inter _ _ _ _ _ _ _ (Fl.b s) (hlin s) (Fl.sub s)).2.1 i
  have hroot : ∀ r, (Fl.rootLat r).IsVB 1 ⊤ := fun r =>
    (GlobalTheory.T.lattice_tensor_power_line_bundle _ _ _ Unit _ Set.univ (fun _ => hgr _ _) _).1
  obtain ⟨K', fK, J', fJ, y', κ, v, hκ, hv, tie', h⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.exists_addBlocks_isDegOn 𝔐.X Ω 𝔐.ξ K J y (CMType H × Fin (D.p + D.q)) Fl.rootLat 𝔐.tie hroot
  choose xdeg e hdeg using h
  exact ⟨K', fK, J', fJ, y', κ, v, tie', xdeg, e, hκ, hv, hdeg⟩

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptIn

def IsPullWedge {Ω₀ Ω V₀ V : Type} [Field Ω₀] [Field Ω] [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V]
    (i : Ω₀ →+* Ω) (j : V₀ →+ V) {n : ℕ} (a : ⋀[Ω₀]^n V₀) (a' : ⋀[Ω]^n V) : Prop :=
  ∀ (b : Fin n → V₀) (α : Ω₀), a = α • exteriorPower.ιMulti Ω₀ n b →
    a' = i α • exteriorPower.ιMulti Ω n fun k => j (b k)

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : Set (Xo.XF c)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

def IsTie (Z : CptOver Y U) (𝔐 : HodgeCpt Y S y) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) : Prop :=
  Dominates 𝔐.ξ (Z.ξ₀ ≫ Y.j) 𝔐.f i ∧ i.comp Z.inc = 𝔐.cst ∧ IsExtOver i j ∧
    ∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (Z.M.pt e).left

end Comparison₂

end GlobalTheory.CompanionTheory.Ar.Flat.CptIn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsoLineOnEquivalence
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines

theorem isoLineOn_comb_trans_symm_pull : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)), IsMultiProjPrime P → Xo ⊆ mcPts P → (∀ (J : Type) [Fintype J] (ℓ ℓ' : J → HermLine ι) (n : J → ℤ), (∀ j, IsoLineOn P Xo (ℓ j) (ℓ' j)) → IsoLineOn P Xo (Top.combLine ℓ n) (Top.combLine ℓ' n)) ∧ (∀ A B C : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B C → IsoLineOn P Xo A C) ∧ (∀ A B : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B A) ∧ ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ : K₁ → K) (v : (Σ k, ι₁ k) → Σ k, ι k) (J : Type) [Fintype J] (ℓ : J → HermLine ι₁) (ℓ' : J → HermLine ι) (n : J → ℤ), IsBlockMap κ v → (∀ j, IsPullHerm κ v (ℓ j) (ℓ' j)) → IsPullHerm κ v (Top.combLine ℓ n) (Top.combLine ℓ' n) :=
  @PositivityTheory.UnitarySelfGeneration.i_comb

end GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeAction
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ActBC

theorem exists_act_extends : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap e) φ → ∀ (O : Type) [CommRing O] (act : OAct O G) (act' : OAct O G'), (∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) → ∀ (V V' : Type) [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V'] (MV : LieModel G (𝟙 (Sp L)) V) (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) → Submodule.span L' (Set.range j) = ⊤ → ∀ ρ : O →+* Module.End L V, MV.IsActOf act.act ρ → ∃ ρ' : O →+* Module.End L' V', MV'.IsActOf act'.act ρ' ∧ ∀ a x, ρ' a (j x) = j (ρ a x) := by
  intro L L' _ _ e G G' _ _ φ hpb O _ act act' hcomm V V' _ _ _ _ MV MV' j hj hspan ρ hρ
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act _ _ _ _ _ MV' _ act'.act act'.hom act'.one
    act'.mul act'.add
  refine ⟨ρ', hρ', fun a x => ?_⟩
  apply MV'.inj
  apply Over.OverMorphism.ext
  apply hpb.1.hom_ext
  · rw [hρ' a (j x), Over.comp_left, Category.assoc, hcomm a, ← Category.assoc, hj x, Category.assoc,
      ← Over.comp_left, ← hρ a x, hj (ρ a x)]
  · rw [Over.w, Over.w]

end GlobalTheory.CompanionTheory.Ar.ActBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogHermitianSumBounded
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.CancelBound

theorem log_h_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun p => c p.1 * z p) = (∑ k, (A.a k : ℝ) * Real.log ‖c k‖) + Real.log (A.h z) := by
  have hne : ∀ k, ‖c k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [A.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => hne k) (A.pos z hz).ne',
    Real.log_prod (fun k _ => hne k)]
  congr 1
  exact Finset.sum_congr rfl fun k _ => Real.log_zpow _ _

theorem continuousOn_log_h {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι)
    (hA : IsSmoothHerm A) :
    ContinuousOn (fun z => Real.log (A.h z)) {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
  ContinuousOn.log (ContDiffOn.continuousOn hA) fun z hz => (A.pos z hz).ne'

theorem log_metrics_bounded (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) (A : HermLine ι)
    (B : J → HermLine ι) (T : Finset J) (hA : IsSmoothHerm A) (hB : ∀ j, IsSmoothHerm (B j))
    (hdeg : A.a = -∑ j ∈ T, (B j).a) :
    ∃ C : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) →
      |Real.log (A.h z) + ∑ j ∈ T, Real.log ((B j).h z)| ≤ C := by
  classical
  let f : ((Σ k, ι k) → ℂ) → ℝ := fun z => Real.log (A.h z) + ∑ j ∈ T, Real.log ((B j).h z)
  let n : K → ((Σ k, ι k) → ℂ) → ℝ := fun k z => ∑ i, ‖z ⟨k, i⟩‖
  let S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, n k z = 1}
  have hcn : ∀ k, Continuous (n k) := fun k =>
    continuous_finsetSum _ fun i _ => (continuous_apply _).norm
  have hnpos : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ k, 0 < n k z := by
    intro z hz k
    obtain ⟨i, hi⟩ := hz k
    exact Finset.sum_pos' (fun _ _ => norm_nonneg _) ⟨i, Finset.mem_univ _, norm_pos_iff.mpr hi⟩
  have hSU : S ⊆ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    intro z hz k
    by_contra hcon
    push Not at hcon
    have h0 : n k z = 0 := Finset.sum_eq_zero fun i _ => by simp [hcon i]
    have h1 : n k z = 1 := hz k
    rw [h0] at h1
    exact zero_ne_one h1
  have hScl : IsClosed S := by
    have hS : S = ⋂ k, {z | n k z = 1} := by
      ext z
      simp [S]
    rw [hS]
    exact isClosed_iInter fun k => isClosed_eq (hcn k) continuous_const
  have hSb : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : (Σ k, ι k) → ℂ)) (r := 1)).subset ?_
    intro z hz
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    rintro ⟨k, i⟩
    calc ‖z ⟨k, i⟩‖ ≤ n k z :=
          Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      _ = 1 := hz k
  have hScpt : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSb
  have hfc : ContinuousOn f S := by
    refine ContinuousOn.mono ?_ hSU
    exact (continuousOn_log_h A hA).add
      (continuousOn_finsetSum _ fun j _ => continuousOn_log_h (B j) (hB j))
  obtain ⟨C, hC⟩ := hScpt.exists_bound_of_continuousOn hfc
  refine ⟨C, fun z hz => ?_⟩
  let c : K → ℂ := fun k => (((n k z)⁻¹ : ℝ) : ℂ)
  let w : (Σ k, ι k) → ℂ := fun p => c p.1 * z p
  have hc : ∀ k, c k ≠ 0 := fun k =>
    Complex.ofReal_ne_zero.mpr (inv_ne_zero (hnpos z hz k).ne')
  have hwS : w ∈ S := by
    intro k
    have hn := (hnpos z hz k).ne'
    have hterm : ∀ i, ‖w ⟨k, i⟩‖ = (n k z)⁻¹ * ‖z ⟨k, i⟩‖ := by
      intro i
      simp only [w, c, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (inv_pos.mpr (hnpos z hz k))]
    change ∑ i, ‖w ⟨k, i⟩‖ = 1
    simp only [hterm]
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ hn
  have hdegk : ∀ k, (A.a k : ℝ) + ∑ j ∈ T, ((B j).a k : ℝ) = 0 := by
    intro k
    have hk : A.a k = -∑ j ∈ T, (B j).a k := by
      rw [hdeg]
      simp [Finset.sum_apply]
    rw [hk]
    push_cast
    ring
  have hfw : f w = f z := by
    simp only [f, w]
    rw [log_h_scale A c z hc hz,
      Finset.sum_congr rfl fun j _ => log_h_scale (B j) c z hc hz, Finset.sum_add_distrib,
      Finset.sum_comm]
    have hz0 : (∑ k, (A.a k : ℝ) * Real.log ‖c k‖) + ∑ k, ∑ j ∈ T, ((B j).a k : ℝ) * Real.log ‖c k‖ = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [← Finset.sum_mul, ← add_mul, hdegk k, zero_mul]
    linarith
  have hb := hC w hwS
  rwa [hfw, Real.norm_eq_abs] at hb

end GlobalTheory.CompanionTheory.Ar.CancelBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOverRamifiedExtension
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem numbers_divCycle_baseChange_dvr : ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O) (ϖ' : O') (u : O'ˣ) (e : ℕ), Irreducible ϖ → Irreducible ϖ' → 0 < e → algebraMap O O' ϖ = u * ϖ' ^ e → ∀ (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MvPolynomial (Σ k, J k) O)) (d : ℕ), IsModelOver P d → IsModelOver (P.map (MvPolynomial.map (algebraMap O O'))) d → ∀ (a : K → ℕ) (f : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = d → cycList (divCycle (P.map (MvPolynomial.map (algebraMap O O'))) (MvPolynomial.map (algebraMap O O') f)) l = e * cycList (divCycle P f) l :=
  BaseChangeColon.isModelOver_ramified_base_change

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogCoveringForms
section
open MvPolynomial

namespace GlobalTheory.CompanionTheory.TwistLine

theorem twisted_hermitian_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a b : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) → (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (v j) b) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A → ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A → ∃ A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, A'.a = (fun k => A.a k + (a k : ℤ) - (b k : ℤ)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A' ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A' ∧ ∀ z : ((Σ k, ι k) → ℂ), A'.h z = A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) / (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) :=
  @PositivityTheory.Xgn.multihomogeneous_line_bundle

end GlobalTheory.CompanionTheory.TwistLine
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogRatioInduction
section
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.TwistLine

theorem finite_pairs_common_bidegree : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : (K → ℕ) → (K → ℕ) → MvPolynomial (Σ k, ι k) ℤ → MvPolynomial (Σ k, ι k) ℤ → Prop) (bf bg : K → ℕ), (∀ (a b d : K → ℕ) (u v m : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog m d → Q (a + d) (b + d) (u * m) (v * m)) → (∀ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0) → ∃ (A B : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), A + bf = B + bg ∧ (∀ j, Q A B (u j) (v j)) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) :=
  @PositivityTheory.Xgn.multihomogeneous_twist_finite

end GlobalTheory.CompanionTheory.Ar.TwistLine
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCptIffNormalScheme
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem component_whole_isIntegral_and_normal : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → IsIntegral X ∧ (Flat.NormalCpt ξ ↔ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) :=
  PositivityTheory.HtPt.Mf.xr_normal

end GlobalTheory.CompanionTheory.Ar.XR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneMemChartLatNm
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.Diag

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
open GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem hasVal_unique {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {L : Type} [Field L] {z : (Σ k, ι k) → L}
    (hz : z ∈ ptsOver L (mCoordIdeal y)) {w w' : L} (h : HasVal y a s z w) (h' : HasVal y a s z w') : w = w' := by
  obtain ⟨dg, dh, g, h₁, hg, hh, hd, hy, hz0, hzw⟩ := h
  obtain ⟨dg', dh', g', h₁', hg', hh', hd', hy', hz0', hzw'⟩ := h'
  have e : dg + dh' = dg' + dh := by
    funext k
    simp only [Pi.add_apply]
    have h1 := hd k
    have h2 := hd' k
    omega
  have hh2 : IsMultiHomog (g' * h₁) (dg + dh') := by
    rw [e]
    exact GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.homog_mul hg' hh
  have hF : g * h₁' - g' * h₁ ∈ mCoordIdeal y := by
    refine GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.mem_of_aeval_eq_zero
      (GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.homog_sub (GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.homog_mul hg hh') hh2) ?_
    rw [map_sub, map_mul, map_mul, hy, hy']
    ring
  have h0 := hz.2 _ hF
  rw [map_sub, map_mul, map_mul, hzw, hzw'] at h0
  have h2 : (w - w') * ((MvPolynomial.aeval z) h₁ * (MvPolynomial.aeval z) h₁') = 0 := by
    linear_combination h0
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 (mul_ne_zero hz0 hz0')

end General

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

end GlobalTheory.CompanionTheory.Ar.Ht.Diag
end
end

