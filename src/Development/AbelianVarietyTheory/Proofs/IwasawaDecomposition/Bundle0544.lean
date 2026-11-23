module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0530
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperOfCompleteDVRLiftGenericPoint
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.TraitProper


open GlobalTheory.ArcProper in
theorem isProper_of_lift_genericPoint : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp R) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f], (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Sp R), Set.range x ⊆ {genericPoint X} → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  intro k _ _ Y _ s _ _ _ H
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have hA : ∀ y : Y, ∃ A : Y.Opens, IsAffineOpen A ∧ y ∈ A := fun y ↦ by
    obtain ⟨A, h₁, h₂, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    exact ⟨A, h₁, h₂⟩
  choose A₀ hA₀ hyA using hA
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (A₀ y : Set Y))
    (fun y ↦ (A₀ y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyA y⟩)
  let A : T → Y.Opens := fun i ↦ A₀ i
  have hcov : ∀ y : Y, ∃ i : T, y ∈ A i := fun y ↦ by
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, h⟩
  have hP := fun i : T ↦ (have : IsAffine (A i).toScheme := hA₀ i
    exists_isOpenImmersion_isProper ((A i).ι ≫ s))
  choose P t j ht hj hjt using hP
  let U : Y.Opens := Finset.univ.inf A
  have hUA : ∀ i, U ≤ A i := fun i ↦ Finset.inf_le (Finset.mem_univ i)
  have hU : genericPoint Y ∈ U := by
    have : ∀ i, genericPoint Y ∈ A i := fun i ↦
      ((genericPoint_spec Y).mem_open_set_iff (A i).isOpen).2 ⟨i, trivial, hyA i⟩
    refine Finset.inf_induction (p := fun V : Y.Opens ↦ genericPoint Y ∈ V) trivial
      (fun _ h _ h' ↦ ⟨h, h'⟩) fun i _ ↦ this i
  have : Nonempty U.toScheme := ⟨⟨_, hU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨Q, q, ψ, _, hψ, hp⟩ := exists_isProper_factor P t ht (U.ι ≫ s)
    (fun i ↦ Y.homOfLE (hUA i) ≫ j i) (fun i ↦ by rw [Category.assoc, hjt, Y.homOfLE_ι_assoc])
    Finset.univ
  choose p hpt hψp using fun i ↦ hp i (Finset.mem_univ i)
  obtain ⟨i₀, -⟩ := hcov (genericPoint Y)
  have : IsImmersion (ψ ≫ p i₀) := by rw [hψp]; infer_instance
  have : IsImmersion ψ := IsImmersion.of_comp ψ (p i₀)
  have : QuasiCompact (ψ ≫ q) := by rw [hψ]; infer_instance
  have : QuasiCompact ψ := QuasiCompact.of_comp ψ q
  have : IsIntegral ψ.image := isIntegral_image ψ
  let z : ψ.image ⟶ Sp k := ψ.imageι ≫ q
  have hz : ψ.toImage ≫ z = U.ι ≫ s := by rw [ψ.toImage_imageι_assoc, hψ]
  have : IsLocallyNoetherian ψ.image := LocallyOfFiniteType.isLocallyNoetherian z
  let V : T → ψ.image.Opens := fun i ↦ (ψ.imageι ≫ p i) ⁻¹ᵁ (j i).opensRange
  let η : U.toScheme := ⟨_, hU⟩
  have hη : ∀ u : U.toScheme, η ⤳ u := fun u ↦
    (U.ι.isEmbedding.isInducing.specializes_iff).1 (genericPoint_specializes (U.ι u))
  have hs : ∀ x : ψ.image, ψ.toImage η ⤳ x := by
    intro x
    rw [specializes_iff_mem_closure]
    refine closure_minimal ?_ isClosed_closure (ψ.toImage.denseRange x)
    rintro _ ⟨u, rfl⟩
    exact specializes_iff_mem_closure.1 ((hη u).map ψ.toImage.continuous)
  have key : ∀ x : ψ.image, ∃ i, x ∈ V i := by
    intro x
    by_cases hne : ψ.toImage η = x
    · refine ⟨i₀, Y.homOfLE (hUA i₀) η, ?_⟩
      rw [← hne, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ψ.toImage_imageι_assoc, hψp]
    obtain ⟨O, _, _, _, c, hc₀, hcx⟩ :=
      exists_complete_discreteValuationRing_of_specializes (hs x) hne
    have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective _ _
    have : IsDominant (spMap (algebraMap O (FractionRing O))) := by
      refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
      exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
    have hpt' : (spMap (algebraMap O (FractionRing O)) ≫ c)
        (IsLocalRing.closedPoint (FractionRing O)) = ψ.toImage η := by
      refine Eq.trans (congrArg c (PrimeSpectrum.ext ?_)) hc₀
      change Ideal.comap (algebraMap O (FractionRing O)) (IsLocalRing.maximalIdeal _) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ hinj
    obtain ⟨l, hl, hlη⟩ := ValuativeGeneric.exists_lift_of_surjectiveOnStalks ψ.toImage
      (FractionRing O) _ η hpt'
    have hls : (l ≫ U.ι) ≫ s = spMap (algebraMap O (FractionRing O)) ≫ c ≫ z := by
      rw [Category.assoc, ← hz, reassoc_of% hl]
    obtain ⟨b, hb⟩ := H O (FractionRing O) (l ≫ U.ι) (c ≫ z) (by
      rintro _ ⟨v, rfl⟩
      rw [Scheme.Hom.comp_apply, hlη]
      rfl) hls
    have hbs : b ≫ s = c ≫ z := by
      refine ext_of_isDominant (spMap (algebraMap O (FractionRing O))) ?_
      rw [← Category.assoc, hb, hls]
    obtain ⟨i, hi⟩ := hcov (b (IsLocalRing.closedPoint O))
    have hr : Set.range b ⊆ Set.range (A i).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨v, rfl⟩
      exact ((IsLocalRing.specializes_closedPoint v).map b.continuous).mem_open (A i).isOpen hi
    obtain ⟨b', hb'⟩ : ∃ b', b' ≫ (A i).ι = b := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
    have e : b' ≫ j i = c ≫ ψ.imageι ≫ p i := by
      refine ext_of_isDominant_of_isSeparated (t i) ?_
        (spMap (algebraMap O (FractionRing O))) ?_
      · rw [Category.assoc, hjt, reassoc_of% hb', hbs, Category.assoc, Category.assoc, hpt]
      · rw [← reassoc_of% hl, ψ.toImage_imageι_assoc, hψp, ← Category.assoc, ← Category.assoc]
        congr 1
        rw [← cancel_mono (A i).ι, Category.assoc, hb', hb, Category.assoc, Y.homOfLE_ι]
    refine ⟨i, b' (IsLocalRing.closedPoint O), ?_⟩
    have e' : (b' ≫ j i) (IsLocalRing.closedPoint O) =
        (c ≫ ψ.imageι ≫ p i) (IsLocalRing.closedPoint O) := by rw [e]
    exact e'.trans (congrArg (ψ.imageι ≫ p i) hcx)
  have hV : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 (key x)
  have hm : ∀ i, ∃ m : (V i).toScheme ⟶ A i, m ≫ j i = (V i).ι ≫ ψ.imageι ≫ p i := fun i ↦
    ⟨_, IsOpenImmersion.lift_fac (j i) _ (by rintro _ ⟨v, rfl⟩; exact v.2)⟩
  choose m hm using hm
  obtain ⟨g, hg, hgU⟩ := exists_extension_of_cover z s ψ.toImage U.ι V hV
    (fun i ↦ m i ≫ (A i).ι)
    (fun i ↦ by rw [Category.assoc, ← hjt, reassoc_of% hm, hpt])
    (fun i T a b e ↦ by
      rw [← Y.homOfLE_ι (hUA i), ← Category.assoc, ← Category.assoc]
      congr 1
      rw [← cancel_mono (j i), Category.assoc, hm, ← reassoc_of% e, ψ.toImage_imageι_assoc, hψp,
        Category.assoc])
  have : IsProper (g ≫ s) := by rw [hg]; infer_instance
  have : IsProper g := IsProper.of_comp g s
  have : IsDominant g := ⟨(U.isOpen.dense ⟨_, hU⟩).mono (by rwa [Scheme.Opens.range_ι] at hgU)⟩
  have : Surjective g := surjective_of_isDominant_of_isClosed_range g g.isClosedMap.isClosed_range
  have : UniversallyClosed s := .of_comp_surjective g s
  exact {}

end GlobalTheory.TraitProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyAtIffExistsKeyAtVia
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def KeyAtVia {Y : Model Xo c β} (M : GChart Y) {R : Type} [CommRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    (x : KeyIn R) (φ : x.P.A.left ⟶ Y.t.G.left) : Prop :=
  ∃ (he : eSec x.P.A ≫ φ = z ≫ eSec Y.t.G) (w : LB.Iso x.P.L (Y.t.PP.L.pull φ)) (hg : x.P.g = M.n),
    IsGrpPullback x.P.A Y.t.G z φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ z he Y.t.PP.L Y.t.PP.rig) ∧
    (∀ (j : (Y.t.PP.L.pull φ).ι) (i : x.P.L.ι)
      (h : (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U (j PUnit.unit))),
      (φ.appLE _ _ h).hom (M.θ (j PUnit.unit)) =
        (show Γ(x.P.A.left, (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x.th.f i)) ∧
    ∀ i, (x.v i).left ≫ φ = spMap (dualMap (ev z M.U hz)) ≫ M.v₀ (i.cast hg)

def ArcFib (Y : Model Xo c β) (bF : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left) (u : HolUnif x.P.A x.P.L g) : Prop :=
  ∀ z, ∃ ψ : Sp ℂ ⟶ Y.oF.t.G.left, ψ ≫ Y.m0.toSABMap.φ = (Fu.ex i P z).left ∧
    ψ ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF ∧ (u.ex z).left ≫ φ = ψ ≫ Y.m.φ

end GlobalTheory.ArcNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LUnifAtDat
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult


set_option maxHeartbeats 1000000 in
theorem lUnif_atDat : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram →
    GlobalTheory.Mem.Top.Bl.AtDat fun _ B f T w Z hX Wt z => z.R.toRealDat.LUnif := by
  intro _ _ _
  refine StepW.of_all fun K B f T w _ _ _ Z hX Wt z _ _ hEx hIn => ?_
  have hch := z.pins.char
  have hC : GlobalTheory.RealGeo.PreChar z.R.toRealDat :=
    ⟨hch.base.lev, hch.base.grp.red_R, hch.base.grp.red_L, hch.base.grp.record, hch.base.fam, hch.base.models,
      RealDat.chain_of_weak hch.base.chain hEx, RealDat.thP_of_weak hch.base.thP hEx⟩
  have hχ : z.R.toRealDat.grp_chiW := hch.base.grp.chiW
  have ht : TieIn z.core z.R.toRealDat z.geo.κ z.geo.v₀ :=
    ⟨z.geo.fw.laws, z.geo.fw.alg_eq, z.geo.fw.kap, z.geo.fw.hv₀, z.geo.fw.chiR, z.geo.fw.x0⟩
  have hp : z.core.pb = z.R.toRealDat.C.P.pb :=
    GlobalTheory.PinsFixHalf.pb_eq_of_pins z.core z.R.toRealDat z.geo.κ z.geo.v₀ z.geo.O hC.lev z.geo.fw.laws z.geo.pins
  have hx := _root_.GlobalTheory.EquivConst.exists_equivariant_constants z.core z.R.toRealDat z.geo.κ z.geo.v₀ z.geo.O hC.lev ht hp z.geo.pins
  have hU := hIn.jUnif
  intro i σ
  exact ⟨(GlobalTheory.TiedUnif.indep_span_of_tie z.geo.fw hC.models.HW z.geo.bar hU i σ).1,
    (GlobalTheory.TiedUnif.indep_span_of_tie z.geo.fw hC.models.HW z.geo.bar hU i σ).2,
    GlobalTheory.TiedUnif.rhoIs_of_eqAt z.geo.fw hC.models.HW hC.models.gW hχ z.geo.bar z.geo.rhoGeo hU i σ
      (fun h hV => z.geo.equivAll i _ h hV (hx i _ h hV))
      fun h hV => z.geo.equivAll i _ (good_resC z.core h) hV (hx i _ (good_resC z.core h) hV)⟩

end GlobalTheory.Mem.Top.Bl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapInnerEqLambdaLabelPartBaseLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamMetric

theorem inner_theta_eq_lam : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix), Used0 D (Y.tup t) → ∀ x ∈ (LinearMap.ker (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1)))ᗮ, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x) ∈ R.Wp3 i p → ∀ x', ⟪D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x, D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) x'⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪x, x'⟫_ℂ := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i t p _ x hx hW x'
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  have hK := GlobalTheory.T.liftThetaMap_orthogonalKernel_eq_rationalSpan D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t
  set K := (LinearMap.ker θ)ᗮ with hKdef
  have hS := GlobalTheory.T.liftThetaMap_labelPartPreimage_rationalSpan D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t p x (hK ▸ hx) hW

  have hkerK : ∀ z, z - K.starProjection z ∈ LinearMap.ker θ := by
    intro z
    have := K.sub_starProjection_mem_orthogonal z
    rwa [Submodule.orthogonal_orthogonal] at this
  have hKperp : ∀ z, z - K.starProjection z ∈ Kᗮ := fun z => K.sub_starProjection_mem_orthogonal z

  have hgoodK : ∀ a, Y.mj.eW i (θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ∀ q ∈ K,
      ⟪θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), θ q⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), q⟫_ℂ := by
    intro a ha q hq
    rw [hK] at hq
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact GlobalTheory.T.liftThetaMap_inner_eq_lambda_mul_rationalVectors D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t p a b ha
    | zero => simp
    | add y z _ _ h1 h2 => rw [map_add (f := _), inner_add_right, inner_add_right, h1, h2, mul_add]
    | smul c y _ h => rw [map_smul, inner_smul_right, inner_smul_right, h]; ring
  have hgood : ∀ a, Y.mj.eW i (θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ∀ x',
      ⟪θ (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), θ x'⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x'⟫_ℂ := by
    intro a ha x'
    have huK : D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)) ∈ K := by rw [hK]; exact Submodule.subset_span ⟨a, rfl⟩
    have e1 : θ x' = θ (K.starProjection x') := by
      have := hkerK x'
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this; exact this
    have e2 : ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x'⟫_ℂ = ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), K.starProjection x'⟫_ℂ := by
      have h0 : ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), x' - K.starProjection x'⟫_ℂ = 0 :=
        Submodule.inner_right_of_mem_orthogonal huK (hKperp x')
      rw [inner_sub_right, sub_eq_zero] at h0; exact h0
    rw [e1, e2]
    exact hgoodK a ha _ (K.starProjection_apply_mem x')
  clear hx hW
  induction hS using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    exact hgood a ha x'
  | zero => simp
  | add y z _ _ h1 h2 => rw [map_add (f := _), inner_add_left, inner_add_left, h1, h2, mul_add]
  | smul c y _ h => rw [map_smul, inner_smul_left, inner_smul_left, h]; ring

end GlobalTheory.Mem.R3.LamMetric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralLeadingMinorFlagDensityPosDef
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre.FlagInt

theorem isEmpty_low_one : IsEmpty (Low 1) :=
  ⟨fun s => by have h := s.2; rw [Subsingleton.elim s.1.1 s.1.2] at h; exact lt_irrefl _ h⟩

theorem isEmpty_low_zero : IsEmpty (Low 0) := ⟨fun s => s.1.1.elim0⟩

theorem volume_univ_of_isEmpty {ι : Type} [Fintype ι] [IsEmpty ι] : (volume : Measure (ι → ℂ)) Set.univ = 1 := by
  rw [volume_pi, Measure.pi_univ]; simp

theorem dens_one (A : Matrix (Fin 1) (Fin 1) ℂ) (y : Low 1 → ℂ) : dens A y = 1 := by
  simp only [dens, lminor, Fin.prod_univ_one]
  have : IsEmpty (Fin ((0 : Fin 1).castSucc : ℕ)) := ⟨fun x => x.elim0⟩
  rw [det_isEmpty]; simp

theorem re_facts {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (h : H.PosDef) :
    0 < H.det.re ∧ H.det = (H.det.re : ℂ) := by
  have := Complex.pos_iff.1 h.det_pos
  exact ⟨this.1, Complex.ext (by simp) (by simp [← this.2])⟩

theorem lintegral_dens : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), A.PosDef →
    ∫⁻ y : Low m → ℂ, ENNReal.ofReal (dens A y) = ENNReal.ofReal (A.det.re ^ (1 - (m : ℤ)) / flagConst m) := by
  intro m
  induction m with
  | zero =>
    intro A _
    have := isEmpty_low_zero
    simp [dens, flagConst, volume_univ_of_isEmpty]
  | succ p ih =>
    intro A hA
    have := isEmpty_low_one
    obtain ⟨e, he⟩ := exists_isBlockOrderedSumEquiv p 1
    have hA' : (reindex e e A).PosDef := hA.submatrix e.symm.injective
    have hd : (reindex e e A).det = A.det := det_reindex_self e A
    have hm : Measurable fun y : Low (p + 1) → ℂ => ENNReal.ofReal (dens A y) := (measurable_dens A).ennreal_ofReal
    have hm2 : Measurable fun w => ENNReal.ofReal (dens A (glue e w)) := hm.comp (continuous_glue e).measurable
    obtain ⟨hDpos, hD⟩ := re_facts hA
    have hf := flagConst_pos p
    have hc : 0 ≤ A.det.re ^ (1 - (p : ℤ)) / flagConst p := by positivity
    rw [← (GlobalTheory.T.measurePreserving_glueLowerUnitriangularBlocks _ _ _ e he).lintegral_comp hm, Measure.volume_eq_prod, lintegral_prod _ hm2.aemeasurable]
    have key : ∀ v : Fin p × Fin 1 → ℂ,
        ∫⁻ w : (Low 1 → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, w))) =
        ENNReal.ofReal (A.det.re ^ (1 - (p : ℤ)) / flagConst p) *
          ENNReal.ofReal ((shear (reindex e e A) (toMat v)).toBlocks₂₂.det.re ^ (-((p + 1 : ℕ) : ℤ))) := by
      intro v
      have hS := posDef_shear hA' (toMat v)
      obtain ⟨-, h2, h3⟩ := posDef_blocks hS
      have hu := h2.det_pos.ne'.isUnit
      have hm3 : Measurable fun w : (Low 1 → ℂ) × (Low p → ℂ) => ENNReal.ofReal (dens A (glue e (v, w))) :=
        hm2.comp measurable_prodMk_left
      rw [Measure.volume_eq_prod, lintegral_prod _ hm3.aemeasurable]
      have hg := fun (y1 : Low 1 → ℂ) (y2 : Low p → ℂ) => _root_.GlobalTheory.FlagFibre.dens_glue _ _ _ e he A (v, y1, y2) hu
      simp only [dens_one, one_mul] at hg
      simp only [hg]
      have hdet := det_eq_mul_schur hu
      rw [det_shear, hd] at hdet
      obtain ⟨hp2, he2⟩ := re_facts h2
      obtain ⟨hp3, he3⟩ := re_facts h3
      have hI := ih _ h3
      set S := shear (reindex e e A) (toMat v)
      have hn : ‖S.toBlocks₂₂.det‖ = S.toBlocks₂₂.det.re := by
        conv_lhs => rw [he2, Complex.norm_real, Real.norm_of_nonneg hp2.le]
      have hre : A.det.re = S.toBlocks₂₂.det.re * (schur S).det.re := by
        rw [hdet]; conv_lhs => rw [he2, he3, ← Complex.ofReal_mul, Complex.ofReal_re]
      rw [lintegral_const, volume_univ_of_isEmpty, mul_one, hn]
      simp only [ENNReal.ofReal_mul (zpow_nonneg hp2.le _)]
      rw [lintegral_const_mul _ (measurable_dens _).ennreal_ofReal, hI, ← ENNReal.ofReal_mul (zpow_nonneg hp2.le _),
        ← ENNReal.ofReal_mul hc, hre, mul_zpow]
      congr 1
      have : S.toBlocks₂₂.det.re ^ (-(2 * p : ℤ)) =
          S.toBlocks₂₂.det.re ^ (1 - (p : ℤ)) * S.toBlocks₂₂.det.re ^ (-((p + 1 : ℕ) : ℤ)) := by
        rw [← zpow_add₀ hp2.ne']; congr 1; push_cast; ring
      rw [this]; ring
    simp only [key]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, _root_.GlobalTheory.HuaQuadric.quadric p 1 _ hA', ← ENNReal.ofReal_mul hc, hd,
      flagConst_add p 1]
    congr 1
    have h1 : flagConst 1 = 1 := by simp [flagConst]
    have : A.det.re ^ (1 - ((p + 1 : ℕ) : ℤ)) = A.det.re ^ (1 - (p : ℤ)) * A.det.re ^ (-((1 : ℕ) : ℤ)) := by
      rw [← zpow_add₀ hDpos.ne']; congr 1; push_cast; ring
    rw [this, h1]; ring

end GlobalTheory.FlagFibre.FlagInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfPluckerProportional
section
noncomputable section

namespace GlobalTheory.FlagEmb

theorem adjugate_mul_eq_plk {K : Type} [Field K] {M k : ℕ} (D : Fin k → Fin (M + 1) → K) (r : Fin k → Fin (M + 1))
    (i : Fin k) (s : Fin (M + 1)) :
    ((Matrix.of fun l l' => D l (r l')).adjugate * Matrix.of D) i s =
      plk D id ((plE M k).symm (Function.update r i s)) := by
  have h1 : ((Matrix.of fun l l' => D l (r l')).adjugate * Matrix.of D) i s =
      ((Matrix.of fun l l' => D l (r l')).adjugate.mulVec fun j => D j s) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, ← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
  simp only [plk, Equiv.apply_symm_apply, id]
  congr 1
  ext l l'
  by_cases h : l' = i
  · subst h
    simp [Matrix.updateCol_apply]
  · simp [Matrix.updateCol_apply, Function.update_of_ne h, h]

theorem mem_span_of_plk_eq_smul (K : Type) [Field K] (M k : ℕ) (c c' : Fin k → Fin (M + 1) → K) (a : K)
    (h0 : plk c' id ≠ 0) (h : plk c' id = a • plk c id) (l : Fin k) :
    c' l ∈ Submodule.span K (Set.range c) := by
  obtain ⟨q, hq⟩ := Function.ne_iff.1 h0
  set r := plE M k q with hr
  set A : Matrix (Fin k) (Fin k) K := Matrix.of fun l l' => c l (r l') with hA
  set A' : Matrix (Fin k) (Fin k) K := Matrix.of fun l l' => c' l (r l') with hA'
  have hdet : A'.det ≠ 0 := hq
  have hadj : A'.adjugate * Matrix.of c' = a • (A.adjugate * Matrix.of c) := by
    ext i s
    rw [hA, hA', adjugate_mul_eq_plk, Matrix.smul_apply, adjugate_mul_eq_plk, h]
    rfl
  have hC : A'.det • (Matrix.of c' : Matrix (Fin k) (Fin (M + 1)) K) = a • (A' * A.adjugate * Matrix.of c) := by
    have := congrArg (fun X => A' * X) hadj
    simp only [← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul] at this
    simpa [Matrix.smul_mul] using this
  have hrow : c' l = ∑ j, ((A'.det)⁻¹ * (a * (A' * A.adjugate) l j)) • c j := by
    funext s
    have h2 := congrFun (congrFun hC l) s
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.mul_apply (M := A' * A.adjugate)] at h2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [eq_inv_mul_iff_mul_eq₀ hdet |>.2 h2, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hrow]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.FlagEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothBaseAndNormalCoordinateRing
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem smooth_cbase {X : Scheme.{0}} {T : Type} [Finite T] (m : T → ℕ) (U : X.affineOpens) : Smooth (cbase m U) := by
  have h : Smooth (spMap (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) := by
    refine (HasRingHomProperty.Spec_iff (P := @Smooth)).2 ?_
    exact RingHom.smooth_algebraMap.2 (⟨inferInstance, inferInstance⟩ : Algebra.Smooth Γ(X, U.1) (MvPolynomial (CellVar m) Γ(X, U.1)))
  have h' : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have h'' : Smooth U.2.fromSpec := inferInstance
  exact MorphismProperty.comp_mem @Smooth _ _ h h''

theorem cell_smooth_normal : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Type) [Finite T] (m : T → ℕ) (U : X.affineOpens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → Smooth (cbase m U) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp (CR m U)) := by
  intro X _ T _ m U hX
  have := smooth_cbase m U
  exact ⟨this, forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (cbase m U) hX⟩

end GlobalTheory.FlagEmb
end

