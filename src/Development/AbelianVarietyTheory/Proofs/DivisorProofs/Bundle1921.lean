module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

variable {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] {k : Type} [CommRing k]

theorem functionFieldMap_comp_constFn (p : W ⟶ Sp k) (f : M ⟶ W) [IsDominant f] :
    (functionFieldMap f).comp (Cartier.constFn p) = Cartier.constFn (f ≫ p) := by
  ext a
  simp only [RingHom.comp_apply, Cartier.constFn]
  have h1 := algebraMap_germ (X := W) (U := ⊤) (x := f (genericPoint M)) trivial (algX p ⊤ a)
  have h2 := algebraMap_germ (X := M) (U := ⊤) (x := genericPoint M) trivial (algX (f ≫ p) ⊤ a)
  rw [← h1, ← h2, functionFieldMap_algebraMap]
  congr 1
  have e : f.app ⊤ (algX p ⊤ a) = algX (f ≫ p) ⊤ a := by
    simp only [algX, RingHom.comp_apply, Scheme.Hom.appLE,
      ← CommRingCat.comp_apply, Scheme.Hom.comp_app, Category.assoc]
    rw [f.naturality]
    rfl
  rw [← e]
  exact Scheme.Hom.germ_stalkMap_apply f ⊤ _ trivial _

def ratPull (p : W ⟶ Sp k) (f : M ⟶ W) [IsDominant f] (n : ℕ) :
    RatForms p n →ₛₗ[functionFieldMap f] RatForms (f ≫ p) n :=
  TopForm.formMap n (functionFieldMap f) (functionFieldMap_comp_constFn p f)

end GlobalTheory.EtaleKlt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericThetaExpansionScalarNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyScalarNe

theorem polAVSectionInverseImage_ne_zero {K : Type} [Field K] (P : PolAV (Sp K)) (T : Over (Sp K)) (t₀ : T.left) (s : P.L.Sec)
    (hs : ∃ p, p ∈ nonzeroLocus s) (t : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) (h : IsPolAVSectionInverseImage P T s t) :
    t ≠ 0 := by
  rintro rfl
  obtain ⟨z, hz⟩ := hs
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz
  have hpb : IsPullback (fst T P.A).left (snd T P.A).left T.hom P.A.hom := by
    rw [Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback _ _
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨y, -, hy⟩ := Scheme.exists_preimage_of_isPullback hpb t₀ z (Subsingleton.elim _ _)
  have hle : (LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => k) ≤ (snd T P.A).left ⁻¹ᵁ P.L.U k :=
    LB.wchart_le P.L _ (fun _ : Fin 1 => k) 0
  have hyU : y ∈ (LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => k) := by
    show y ∈ LB.wchart P.L _ _
    refine Set.mem_iInter.2 fun _ => ?_
    show (snd T P.A).left y ∈ (P.L.U k : Set P.A.left)
    rw [hy]; exact hk
  subst hy
  have e := congrArg (gs (𝟙 _) y _) (h k hle)
  rw [gs_appLE _ _ _ hle (𝟙 _) y hyU, Category.id_comp, gs_stalkMap (snd T P.A).left y _ hk] at e
  have u' := u.map ((snd T P.A).left.stalkMap y).hom
  rw [← e] at u'
  have h0 : gs (𝟙 _) y ((LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => k)) ((0 : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)).f (fun _ => k)) = 0 := by
    have z0 : (0 : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)).f (fun _ => k) = 0 := rfl
    rw [z0, gs_eq _ y _ hyU, map_zero, map_zero]
  rw [h0] at u'
  exact not_isUnit_zero u'

end GlobalTheory.KeyScalarNe

theorem GlobalTheory.KeyScalarNe.scalar_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre), GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N) (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → c ≠ 0 := by
  intro V _ _ _ _ _ D x G _ _ _ U w₀ hw C _ _ _ _ _ _ _ N ν th ϑ c hon hex hv
  rintro rfl
  rw [zero_smul] at hv
  have h0 : ν.FamV (0 : Fam D.toPre C 1) 0 := by
    have := GlobalTheory.WeilValues.famV_smul ν hv 0
    rwa [zero_smul, zero_smul] at this
  have hϑ : ϑ = 0 := GlobalTheory.Ex.FamVal.famV_inj ν hv h0
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF GlobalTheory.allSixLaws.1.globalFns U C (k := 1) le_rfl w₀ hw.1
  have ht : th = 0 := by
    have h1 := (he th ϑ).1 hex
    rw [hϑ] at h1
    exact e.map_eq_zero_iff.1 h1
  obtain ⟨z, -, hz⟩ := x.th_ne (IsLocalRing.closedPoint _)
  exact GlobalTheory.KeyScalarNe.polAVSectionInverseImage_ne_zero x.P (TFK (R := V) C) (IsLocalRing.closedPoint C) x.th ⟨z, hz⟩ th hon ht
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermMemRangeStalkOfPullbackMulLocalIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory

theorem germToFunctionField_mem_range_stalk_of_mul_pull : ∀ (k : Type) [CommRing k] (Y X : Scheme.{0}) [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ Sp k) (σ : X ⟶ Y) (U : Y.Opens) [IsIso (σ ∣_ U)] [Nonempty U] (L : LB Y) (P N : LB X)
    (C : ProdChart P (L.pull σ) N) (J : H0 (σ ≫ p) P ⊤) (g : H0 (σ ≫ p) N ⊤) (s : H0 p L U),
    C.mul (H0.restr le_top J) (H0.pull σ le_rfl s) = H0.restr le_top g → ∀ x : X,
      Function.Bijective (σ.stalkMap x).hom → (∀ (a : P.ι) (ha : x ∈ P.U a), IsUnit (H0.germ a x (memTop x) ha J)) →
      ∀ (i : L.ι) (hi : σ x ∈ L.U i) [Nonempty (U ⊓ L.U i : Y.Opens)],
        Y.germToFunctionField (U ⊓ L.U i) (s.loc i) ∈ (algebraMap (Y.presheaf.stalk (σ x)) Y.functionField).range := by
  intro k _ Y X _ _ p σ U _ _ L P N C J g s hrel x hbij hJ i hi _
  obtain ⟨t, ha, hb, hc⟩ := C.cover x
  have hjx : σ x ∈ L.U (C.b t PUnit.unit) := mem_pull.1 hb
  have hξx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hne : Nonempty (σ ⁻¹ᵁ U) := by
    obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty U›
    obtain ⟨z, -⟩ := (σ ∣_ U).surjective ⟨y, hy⟩
    exact ⟨z⟩
  have hξU : genericPoint X ∈ σ ⁻¹ᵁ U := genericPoint_mem_opens _
  have hσξη : σ (genericPoint X) ⤳ genericPoint Y := by
    obtain ⟨z, hz⟩ := (σ ∣_ U).surjective ⟨genericPoint Y, genericPoint_mem_opens U⟩
    have e : σ z.1 = genericPoint Y := (morphismRestrict_base_coe σ U z).symm.trans (congrArg Subtype.val hz)
    rw [← e]
    exact σ.base.hom.map_specializes ((genericPoint_spec X).specializes trivial)
  have hσξ : σ (genericPoint X) ∈ U ⊓ L.U (C.b t PUnit.unit) :=
    ⟨hξU, (σ.base.hom.map_specializes hξx).mem_open (L.U _).isOpen hjx⟩
  have haξ := hξx.mem_open (P.U (C.a t)).isOpen ha
  have hbξ := hξx.mem_open ((L.pull σ).U (C.b t)).isOpen hb
  have hcξ := hξx.mem_open (N.U (C.c t)).isOpen hc
  have e1 := congrArg (H0.germ (C.c t) (genericPoint X) hξU hcξ) hrel
  rw [C.germ_mul _ _ t _ hξU haξ hbξ hcξ, H0.germ_restr, H0.germ_restr, H0.germ_pull] at e1
  have hsp (B : LB X) (f : H0 (σ ≫ p) B ⊤) (a : B.ι) (hx : x ∈ B.U a) (hξ : genericPoint X ∈ B.U a) :
      H0.germ a (genericPoint X) (memTop _) hξ f =
        X.presheaf.stalkSpecializes hξx (H0.germ a x (memTop x) hx f) := by
    rw [H0.germ_apply, H0.germ_apply]
    exact (X.presheaf.germ_stalkSpecializes_apply _ hξx _).symm
  have hJu := hJ (C.a t) ha
  obtain ⟨h, hh⟩ := hbij.2 (H0.germ (C.c t) x (memTop x) hc g * ↑hJu.unit⁻¹)
  have : Nonempty (L.U (C.b t PUnit.unit)) := ⟨⟨σ x, hjx⟩⟩
  have := nonempty_inf_of_isIntegral U (L.U (C.b t PUnit.unit))
  refine germToFunctionField_mem_range_stalk_of_secOn (LB.coord_mem s) hi hjx ⟨h, ?_⟩
  let φ : Y.functionField →+* X.presheaf.stalk (genericPoint X) :=
    (σ.stalkMap (genericPoint X)).hom.comp (Y.presheaf.stalkSpecializes hσξη).hom
  refine φ.injective ?_
  have eA : φ (algebraMap _ _ h) = X.presheaf.stalkSpecializes hξx (σ.stalkMap x h) := by
    change (σ.stalkMap _).hom ((Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫
      Y.presheaf.stalkSpecializes hσξη).hom h) = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    exact Scheme.Hom.stalkSpecializes_stalkMap_apply σ _ _ hξx h
  have eB : φ (Y.germToFunctionField _ (LB.coord s (C.b t PUnit.unit))) =
      (σ.stalkMap (genericPoint X)).hom (H0.germ (C.b t PUnit.unit) (σ (genericPoint X)) hσξ.1 hσξ.2 s) := by
    change (σ.stalkMap _).hom (Y.presheaf.stalkSpecializes hσξη
      (Y.presheaf.germ _ (genericPoint Y) _ (LB.coord s _))) = _
    rw [Y.presheaf.germ_stalkSpecializes_apply _ hσξη]
    rfl
  rw [eA, eB, hh]
  rw [hsp P J (C.a t) ha haξ, hsp N g (C.c t) hc hcξ] at e1
  have hu : IsUnit (X.presheaf.stalkSpecializes hξx (H0.germ (C.a t) x (memTop x) ha J)) := hJu.map _
  apply hu.mul_left_cancel
  rw [e1, ← map_mul]
  exact congrArg _ (by rw [mul_left_comm, hJu.mul_val_inv, mul_one])

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFrMulInv
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.FlipTranslate

open GlobalTheory.ExportSeries.Model (ct)

variable {D : D7}

def gramFr (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Datum.EAf D) :=
  ct β.val * V.gram.map (eToEAf D) * β.val

def gramFrInv (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Datum.EAf D) :=
  (β⁻¹).val * (V.gram⁻¹).map (eToEAf D) * ct (β⁻¹).val

def diagW (D : D7) (n r : ℕ) (a : D.host.E) : Matrix (Fin n) (Fin n) (Datum.EAf D) :=
  Matrix.diagonal fun k => if k.val < r then 1 else eToEAf D a

def IsFlipElt (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) (r : ℕ) (e : AE D) (a : D.host.E) (g : GA D V) : Prop :=
  SuppAt e V g ∧ toEAf D e • ((β⁻¹).val * (mt V g).map (toEAf D) * β.val) = toEAf D e • (diagW D V.rank r a * gramFr V β)

def conjK (PP : Pl D.host.E) : kP PP →+* kP (conjPl PP) :=
  Ideal.quotientMap (conjPl PP).asIdeal starOHom fun a ha => by
    show starO (starO a) ∈ PP.asIdeal
    rwa [starO_starO]

theorem conjK_mk (PP : Pl D.host.E) (a : 𝓞 D.host.E) :
    conjK PP (Ideal.Quotient.mk PP.asIdeal a) = Ideal.Quotient.mk (conjPl PP).asIdeal (starO a) := rfl

theorem resS_conj (PP : Pl D.host.E) (s s' : Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : (s' : Datum.EAf D) = GlobalTheory.AdelicLatMove.cF D (s : Datum.EAf D)) :
    resS D.host.F (conjPl PP) s' = conjK PP (resS D.host.F PP s) := by
  have e : s' = sigS D.sp.cm s := Subtype.ext (h.trans (sigS_coe _ _).symm)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (resS D.host.F PP s)
  have h0 : resS D.host.F PP (s - oToS D.host.F D.host.E a) = 0 := by rw [map_sub, resS_oToS, ha, sub_self]
  have h1 := (resS_sigS_eq_zero_iff D.sp.cm (isConjPl_conjPl PP) _).2 h0
  rw [map_sub, map_sub, sigS_oToS, resS_oToS, sub_eq_zero] at h1
  rw [e, h1, ← ha, conjK_mk]

theorem gramFr_mul_inv (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) : gramFr V β * gramFrInv V β = 1 := by
  have h1 : ct β.val * ct (β⁻¹).val = 1 := by
    rw [← GlobalTheory.ExportSeries.Model.ct_mul, Units.inv_mul]
    simp [ct]
  unfold gramFr gramFrInv
  calc _ = ct β.val * (V.gram.map (eToEAf D) * (β.val * (β⁻¹).val) * (V.gram⁻¹).map (eToEAf D)) * ct (β⁻¹).val := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, GlobalTheory.PlaceVec.gram_map_mul_inv, Matrix.mul_one, h1]

theorem gramFr_int {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (Datum.EAf D)}
    (hV : IsSelfDualC V Λ) (f : Formalism.L2.DIV.IsFrame β Λ) : IsIntM (gramFr V β) ∧ IsIntM (gramFrInv V β) :=
  GlobalTheory.ExportSeries.Model.gram_frame_int V hV f

theorem diagW_mul (n r : ℕ) (a b : D.host.E) : diagW D n r a * diagW D n r b = diagW D n r (a * b) := by
  unfold diagW
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  split_ifs
  · rw [one_mul]
  · rw [map_mul]

theorem diagW_one (n r : ℕ) : diagW D n r 1 = 1 := by
  unfold diagW
  simp only [map_one, ite_self, Matrix.diagonal_one]

theorem diagW_int (n r : ℕ) (a : 𝓞 D.host.E) : IsIntM (diagW D n r (a : D.host.E)) := by
  intro i j
  unfold diagW
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact one_mem _
  · exact Subring.subset_closure (Or.inl ⟨⟨(a : D.host.E), ⟨a, rfl⟩⟩, rfl⟩)
  · exact zero_mem _

end GlobalTheory.FlipTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentUniqueness
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstDeform

theorem objMap_const : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ o : Obj Dw l (baseKA l) (x' ≫ Xo.s), Nonempty (ObjMap o Xo.univ x') → Nonempty (ObjMap o Xo.univ (constPt x')) := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq hT A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o ⟨m⟩
  have hw : m.cm.F ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ x' := m.cart.1.w
  let g : o.t.G.left ⟶ A'.left := hπ'.1.lift m.cm.F o.t.G.hom hw
  have hg : g ≫ π' = m.cm.F := hπ'.1.lift_fst _ _ _
  have hgw : g ≫ A'.hom = o.t.G.hom := hπ'.1.lift_snd _ _ _
  have hgc : IsGrpPullback o.t.G A' (𝟙 _) g :=
    hπ'.cancel (m.cart.congr (Category.id_comp _).symm hg.symm) (by rw [hgw, Category.comp_id])
  have hred : spMap (algebraMap K (DualNumber K)) ≫ y.x = constPt x' := by
    rw [← hT.2]; rfl
  have hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π) :=
    (hgc.comp (hq.comp hπ)).congr (by rw [Category.id_comp, hred]) rfl
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hgq := hgc.comp hq
  have hcomm : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x := by
    intro T x y
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · have e1 := hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl
      have e2 := hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl
      rw [← e1, ← e2, _root_.mul_comm]
    · rw [Over.w (x * y), Over.w (y * x)]

  have key : ∀ (σ : 𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (n : ℕ),
      0 < n → σ ^ n = 1 → σ.left ≫ m.cm.F = x' ≫ τ.left →
      σ.left ≫ (g ≫ q ≫ π) = constPt x' ≫ τ.left := by
    intro σ τ n hn hσ hστ
    let u := pushHom hgq (𝟙_ (Over (Sp (DualNumber K)))) σ
    have hu : u ^ n = 1 := by rw [← map_pow, hσ, map_one]
    have e := _root_.GlobalTheory.TorsConst.torsion_eq_const K A _ (by simp) (hcomm _) u n hn hu
    have hul : u.left = σ.left ≫ g ≫ q := by
      show σ.left ≫ (g ≫ q) = _; rfl
    rw [hul] at e
    let w := spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ g
    have hw' : w ≫ A'.hom = 𝟙 _ ≫ GlobalTheory.DeRham.epsRed K := by
      simp only [w, Category.assoc, hgw, Category.id_comp]
      rw [Over.w σ]; rfl
    let s₀ := hi.1.lift w (𝟙 _) hw'
    have hs₀ : s₀ ≫ i = w := hi.1.lift_fst _ _ _
    calc σ.left ≫ (g ≫ q ≫ π) = (σ.left ≫ g ≫ q) ≫ π := by simp only [Category.assoc]
      _ = (spMap (algebraMap K (DualNumber K)) ≫ w ≫ q) ≫ π := by rw [e]; simp only [w, Category.assoc]
      _ = spMap (algebraMap K (DualNumber K)) ≫ s₀ ≫ i ≫ π' := by
          rw [← hs₀]; simp only [Category.assoc]; rw [reassoc_of% hiq, hiπ]
      _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ m.cm.F := by
          rw [reassoc_of% hs₀]; simp only [w, Category.assoc, hg]
      _ = constPt x' ≫ τ.left := by rw [hστ]; rfl
  have hpow : ∀ (f : Dw.La → (𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G)), (∀ a b, f (a + b) = f a * f b) →
      ∀ (n : ℕ) a, f (n • a) = f a ^ n := by
    intro f hf n a
    induction n with
    | zero =>
      have h0 := hf 0 0
      rw [add_zero] at h0
      rw [zero_smul, pow_zero]
      exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
    | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h1
  exact ⟨{
    cm := cubeMapOf hF
    cart := hF
    base := rfl
    act := _root_.GlobalTheory.ConstDeform.act_const hP hGD E H Dw l Xo c K y x' hpq hT A A' π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF
    lin := _root_.GlobalTheory.ConstDefCub.isPullCubical_constPt hP hGD E H Dw l Xo c K y x' hpq hT A A' π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF
    eta := fun a => key (o.eta a) (Xo.univ.eta a) l.M (by have := l.three_le; omega)
      (by rw [← hpow _ o.eta_add]; exact o.eta_ker _ (by
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact Submodule.smul_mem_smul hM Submodule.mem_top))
      (m.eta a)
    etaA := fun a => key (o.etaA a) (Xo.univ.etaA a) l.A l.A_pos
      (by rw [← hpow _ o.etaA_add]; exact o.etaA_ker a) (m.etaA a) }⟩

end GlobalTheory.ConstDeform
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueGeLocalDepthPrimeToPStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_value_ge_local_depth_prime_to_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmA (Dw := Dw) c w n → (∀ k, (ρ : EReal) ≤ nuLocOf C e k (MvPolynomial.map io P)) → ∀ (N : ℕ), Odd N → IsUnit (N : T.V) → ∀ (x₂ : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ b, x₂ b ^ (N ^ 2) = 1 ∧ IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) 1 (x₂ b) (F b)) → letI := io.toAlgebra; (ρ : EReal) ≤ nval T.V e (hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F b)) P) := by
  first | exact @GlobalTheory.RefSum.TermLoc.harmonic_value_ge_local_depth | exact GlobalTheory.RefSum.TermLoc.harmonic_value_ge_local_depth | (intros; apply GlobalTheory.RefSum.TermLoc.harmonic_value_ge_local_depth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingPreservingTransportOfRankZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.RankZero

theorem eq_zero_of_half_mem {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [hd : DiscreteTopology Λ]
    (h : ∀ z ∈ Λ, (2⁻¹ : ℝ) • z ∈ Λ) (z : Fin g → ℂ) (hz : z ∈ Λ) : z = 0 := by
  have hn : ∀ n : ℕ, ((2⁻¹ : ℝ) ^ n) • z ∈ Λ := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih => rw [pow_succ', mul_smul]; exact h _ ih
  have ht : Filter.Tendsto (fun n : ℕ => ((2⁻¹ : ℝ) ^ n) • z) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num) (by norm_num)).smul_const z
    simpa using this
  have ht' : Filter.Tendsto (fun n : ℕ => (⟨_, hn n⟩ : Λ)) Filter.atTop (nhds 0) :=
    tendsto_subtype_rng.2 ht
  rw [nhds_discrete, Filter.tendsto_pure] at ht'
  obtain ⟨n, hn'⟩ := ht'.exists
  have h0 : ((2⁻¹ : ℝ) ^ n) • z = 0 := congrArg Subtype.val hn'
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 (by positivity)
  · exact h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem subsingleton_lattice (D : Datum H) (hD : D.p + D.q = 0) : Subsingleton D.La := by
  haveI := D.fin
  haveI := D.proj
  by_contra hne
  have hnt : Nontrivial D.La := not_subsingleton_iff_nontrivial.1 hne
  have := (Module.finrank_pos_iff (R := 𝓞 E) (M := D.La)).2 hnt
  rw [D.rank, hD] at this
  exact lt_irrefl _ this

theorem subsingleton_unif {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {s : Sp ℂ ⟶ Sp B}
    (hD : D.p + D.q = 0) (o : Obj D l b s) {g : ℕ} (u : HolUnif o.t.G o.t.PP.L g) :
    Subsingleton (Fin g → ℂ) := by
  haveI := subsingleton_lattice D hD
  obtain ⟨-, I, -⟩ := o.geom ℂ (𝟙 _) (Spec.preimage s).hom (by simp [spMap])
  have h1 : I.ev 2 0 = 1 := (I.ker 2 two_pos 0).2 ⟨0, Subsingleton.elim _ _⟩
  have htor : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G, x * x = 1 → x = 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := (I.onto 2 two_pos x).1 (by rw [pow_two]; exact hx)
    rw [Subsingleton.elim a 0, h1] at ha
    exact ha.symm
  haveI := u.discrete
  have hΛ : ∀ z ∈ u.Λ, z = 0 := by
    refine eq_zero_of_half_mem u.Λ (fun z hz => (u.ker _).1 (htor _ ?_))
    rw [← u.ex_add, ← add_smul, u.ker]
    norm_num
    exact hz
  refine subsingleton_of_forall_eq 0 (fun z => ?_)
  have hz : z ∈ Submodule.span ℝ (u.Λ : Set (Fin g → ℂ)) := by rw [u.full]; trivial
  have : Submodule.span ℝ (u.Λ : Set (Fin g → ℂ)) = ⊥ := Submodule.span_eq_bot.2 hΛ
  rwa [this, Submodule.mem_bot] at hz

theorem hasTransport_of_rank_zero (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l)
    (U : Set (Xo.XF c)) (e : c.F →+* ℂ) (hD : D.p + D.q = 0) : HasTransport Xo c U e := by
  intro y y' _ _ _ _ o o' _ _ g g' u u' Hm Hm' κ κ' _ _
  haveI := subsingleton_unif hD o u
  haveI := subsingleton_unif hD o' u'
  haveI : Subsingleton (𝟙_ (Over (Sp ℂ)) ⟶ o'.t.G) := u'.ex_onto.subsingleton
  refine ⟨LinearEquiv.ofSubsingleton _ _, fun z => ?_, fun _ _ _ _ => Subsingleton.elim _ _, fun z w => ?_,
    fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  · rw [Subsingleton.elim z 0, map_zero]
    simp
  · rw [Subsingleton.elim z 0, map_zero]
    simp [HermitianCompactForm.herm]

end GlobalTheory.DetLine.RankZero
end

