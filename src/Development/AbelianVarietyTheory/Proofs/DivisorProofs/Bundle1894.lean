module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Mathlib
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0399
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1861
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianKeyValueAdaptedVectorsFieldIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TrAdapt

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  RingHom.ext fun z => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R) F'] (e : F ≃+* F')
  (he : ∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x)

include he in
theorem toF_comp : (e : F →+* F').comp (toF R F) = toF R F' :=
  RingHom.ext fun r => by simp [toF, he]


include he in
def rhoE : TE R F' ⟶ TE R F :=
  Over.homMk (spMap (dualMap (e : F →+* F'))) (by
    show spMap (dualMap (e : F →+* F')) ≫ spMap (algebraMap F (DualNumber F)) ≫
        spMap (algebraMap (FractionRing R) F) ≫ spMap (algebraMap R (FractionRing R)) =
      spMap (algebraMap F' (DualNumber F')) ≫ spMap (algebraMap (FractionRing R) F') ≫
        spMap (algebraMap R (FractionRing R))
    simp only [← spMap_comp']
    apply congrArg spMap
    ext r <;> simp [dualMap, he, TrivSqZeroExt.algebraMap_eq_inl])


include he in
def sigE : TF (R := R) F' ⟶ TF (R := R) F :=
  Over.homMk (spMap (e : F →+* F')) (by
    show spMap (e : F →+* F') ≫ spMap (algebraMap (FractionRing R) F) ≫ spMap (algebraMap R (FractionRing R)) =
      spMap (algebraMap (FractionRing R) F') ≫ spMap (algebraMap R (FractionRing R))
    simp only [← spMap_comp']
    congr 1
    exact RingHom.ext fun r => by simp [he])

theorem rhoE_left : (rhoE e he).left = spMap (dualMap (e : F →+* F')) := rfl

theorem sigE_left : (sigE e he).left = spMap (e : F →+* F') := rfl

theorem red_comm : (sigE e he).left ≫ redE F = redE F' ≫ (rhoE e he).left := by
  rw [sigE_left, rhoE_left]
  show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
  rw [← spMap_comp', ← spMap_comp']
  congr 1
  exact RingHom.ext fun z => by simp [dualMap]

include he in
theorem bKey_map (κ : Rule) (hκ : Funct κ) [CharZero F] [CharZero F'] (D : DegPre R) {N : NumD F} (ν : NumOf D F N)
    {N' : NumD F'} (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N') (hh : ∀ x, I.h x = 1) (hl : I.lam = 1)
    (hth : ν'.th = ν.th) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (k : F) (hk : BKey κ ν vB k) :
    BKey κ ν' vB (e k) := by
  refine ⟨fun h0 => ?_, fun hg hr th hth' hv x' hres hpb => ?_⟩
  · have h1 := I.th_eq 1
    rw [map_one, hh, hl] at h1
    rw [h1, Units.val_mul, Units.val_one, _root_.one_mul, _root_.one_mul, ← map_pow, RingEquiv.coe_toRingHom, ← map_mul, hk.1 h0,
      map_one]
  · obtain ⟨x, hx⟩ := GlobalTheory.KeyPow.exists_keyPB x' (e.symm : F' →+* F)
    have hc : (e.symm : F' →+* F).comp ((algebraMap (FractionRing R) F').comp (algebraMap R (FractionRing R))) =
        (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) :=
      RingHom.ext fun r => by simp [← he]
    have hpb' := GlobalTheory.keyPB_trans _ _ _ _ x' x _ _ hpb hx
    rw [hc] at hpb'
    have hkx := hk.2 hg hr th hth' hv x (by rw [← hth]; exact hres) hpb'
    have hf := hκ F' F (e.symm : F' →+* F) x' x hx
    rw [hkx] at hf
    rw [hf]
    simp

include he in
theorem adapted_map [CharZero F] [CharZero F'] (D : DegPre R) {N : NumD F} (ν : NumOf D F N)
    {N' : NumD F'} (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N') (heX : ∀ χ, ν'.eX (I.e χ) = ν.eX χ)
    (hpull : ∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' →
      ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J))
    (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r)
    (gm : Fin g → GtPt D (TE R F)) (had : Adapted ν vB bX σ gm) :
    ∃ gm' : Fin g → GtPt D (TE R F'), (∀ j, GtPt.IsPull (spMap (dualMap (e : F →+* F'))) (gm j) (gm' j)) ∧
      Adapted ν' vB (bX.map I.e.toIntLinearEquiv) σ gm' := by
  obtain ⟨hv, hz, hb, ht⟩ := had
  choose gm' hgm' using fun j => GlobalTheory.ConstLie.exists_isPullGt (rhoE e he) (gm j)
  have hzT : rhoE e he ≫ DegPre.zeroT D (TE R F) = DegPre.zeroT D (TE R F') := by
    simp only [DegPre.zeroT, ← Category.assoc, comp_toUnit]
  have hzF : sigE e he ≫ DegPre.zeroF D F = DegPre.zeroF D F' := by
    simp only [DegPre.zeroF, ← Category.assoc, comp_toUnit]
  refine ⟨gm', hgm', hv, fun j => ?_, fun i => ?_, fun l => ⟨?_, fun χ => ?_⟩⟩
  · obtain ⟨o, ho, hpo⟩ := hz j
    obtain ⟨o', ho'⟩ := GlobalTheory.ConstLie.exists_isPullGt (sigE e he)
      (⟨o.b, o.s, o.isGen, o.s_zero, o.mult⟩ : GtPt D (TF (R := R) F))
    refine ⟨⟨o'.b, o'.s, o'.isGen, o'.s_zero, o'.mult⟩, ⟨?_, fun χ => ?_⟩, ?_, fun χ => ?_⟩
    · exact Over.OverMorphism.ext (ho'.1.trans ((congrArg (fun q => (sigE e he).left ≫ q.left) ho.1).trans
        (congrArg Over.Hom.left hzF)))
    · refine corr_of_val D.P.isLB fun y J hJ => ?_
      exact ((val_corr hJ (ho'.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (ho.2 χ) _).trans
        (val_one _)))).trans (val_one _).symm
    · refine ho'.1.trans ((congrArg ((sigE e he).left ≫ ·) hpo.1).trans ?_)
      rw [← Category.assoc, red_comm, Category.assoc, ← (hgm' j).1]
    · refine corr_of_val D.P.isLB fun y J hJ => ?_
      refine ((val_corr hJ (ho'.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (hpo.2 χ) _).trans
        (val_pull hJ _ _ _)))).trans (Eq.trans ?_ ((val_pull hJ _ _ _).trans ((val_corr hJ ((hgm' j).2 χ) _).trans
        (val_pull hJ _ _ _))).symm)
      rw [Category.id_comp, Category.id_comp, red_comm]
  · refine (hgm' _).1.trans ?_
    rw [hb i, ← Category.assoc, rhoE_left, ← spMap_comp', dualMap_comp, toF_comp e he]
  · exact Over.OverMorphism.ext ((hgm' _).1.trans ((congrArg (fun q => (rhoE e he).left ≫ q.left) (ht l).1).trans
      (congrArg Over.Hom.left hzT)))
  · obtain ⟨χ₀, rfl⟩ := I.e.surjective χ
    rw [heX, hpull _ _ (hgm' _), (ht l).2 χ₀, Module.Basis.map_repr]
    simp [dualMap]

end GlobalTheory.MBLow.TrAdapt

theorem GlobalTheory.MBLow.bKey_adapted_map : ∀ κ : Rule, Funct κ → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Field F'] [CharZero F] [CharZero F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (e : F ≃+* F'), (∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ (N : NumD F) (ν : NumOf D F N) (N' : NumD F') (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N'), (∀ x, I.h x = 1) → I.lam = 1 → (∀ χ, ν'.eX (I.e χ) = ν.eX χ) → ν'.th = ν.th → (∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J)) → ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ k, BKey κ ν vB k → BKey κ ν' vB (e k)) ∧ ∀ (r g : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R F)), Adapted ν vB bX σ gm → ∃ gm' : Fin g → GtPt D (TE R F'), (∀ j, GtPt.IsPull (spMap (dualMap (e : F →+* F'))) (gm j) (gm' j)) ∧ Adapted ν' vB (bX.map I.e.toIntLinearEquiv) σ gm' := by
  intro κ hκ R _ _ D F F' _ _ _ _ _ _ e he N ν N' ν' I hh hl heX hth hpull vB
  exact ⟨fun k hk => GlobalTheory.MBLow.TrAdapt.bKey_map e he κ hκ D ν ν' I hh hl hth vB k hk,
    fun r g bX σ gm had => GlobalTheory.MBLow.TrAdapt.adapted_map e he D ν ν' I heX hpull vB r g bX σ gm had⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActCCoe
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
open Formalism.IndefR.FWT

noncomputable section

namespace GlobalTheory.DefHalf

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

def sigC (p : PtAt ex Csz) : p.T.Q.c.F →+* ℂ := D.what₂.embLL.comp (algebraMap p.T.Q.c.F D.what₂.LL)

abbrev CF (p : PtAt ex Csz) (i : Fin D.R.m) : Submodule p.T.Q.c.F (p.T.R ((i : ℕ) + 1)) :=
  p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n

end GlobalTheory.DefHalf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Vert

namespace GlobalTheory.FlagChain

section Sub

variable {C C' : Type*} [Category C] [Category C'] {A B A' E E' : C}

variable {f : A ⟶ E} {g : B ⟶ E} {f' : A' ⟶ E}

end Sub

section Bundles

variable {X Y Z : Scheme.{0}} {A B E E' H : X.Modules} {r : ℕ}

end Bundles

section Covers

variable {k : Type} [CommRing k] {D : ℕ} {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  [IsIntegral Z] {p : X ⟶ Sp k} {A E L H : X.Modules} {r : ℕ}

def IsCov (p : X ⟶ Sp k) (D : ℕ) (ρ : Y ⟶ X) : Prop :=
  IsArithVar (ρ ≫ p) D ∧ ρ (genericPoint Y) = genericPoint X ∧ ρ.residueDegree (genericPoint Y) ≠ 0

end Covers

end GlobalTheory.FlagChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingCubeProductValueFderivAtZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.AltJet

def thI (s : Finset (Fin 3)) : thK.{0} := ULift.up s

@[simp] theorem thI_down (s : Finset (Fin 3)) : (thI s).down = s := rfl

theorem prod_thK {M : Type*} [CommMonoid M] (f : thK.{0} → M) :
    ∏ I : thK.{0}, f I = f (thI ∅) * (f (thI {0}) * (f (thI {1}) * (f (thI {2}) *
      (f (thI {0, 1}) * (f (thI {0, 2}) * (f (thI {1, 2}) * f (thI {0, 1, 2}))))))) := by
  refine (Fintype.prod_equiv (Equiv.ulift.symm : Finset (Fin 3) ≃ thK.{0}) (fun I => f (thI I)) f
    (fun _ => rfl)).symm.trans ?_
  have hu : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  rw [hu]
  simp (config := {decide := true}) [Finset.prod_insert]

theorem sum_thK {M : Type*} [AddCommMonoid M] (f : thK.{0} → M) :
    ∑ I : thK.{0}, f I = f (thI ∅) + (f (thI {0}) + (f (thI {1}) + (f (thI {2}) +
      (f (thI {0, 1}) + (f (thI {0, 2}) + (f (thI {1, 2}) + f (thI {0, 1, 2}))))))) := by
  refine (Fintype.sum_equiv (Equiv.ulift.symm : Finset (Fin 3) ≃ thK.{0}) (fun I => f (thI I)) f
    (fun _ => rfl)).symm.trans ?_
  have hu : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  rw [hu]
  simp (config := {decide := true}) [Finset.sum_insert]

theorem thε_thI_empty : thε (thI ∅) = -1 := by decide
theorem thε_thI_0 : thε (thI {0}) = 1 := by decide
theorem thε_thI_1 : thε (thI {1}) = 1 := by decide
theorem thε_thI_2 : thε (thI {2}) = 1 := by decide
theorem thε_thI_01 : thε (thI {0, 1}) = -1 := by decide
theorem thε_thI_02 : thε (thI {0, 2}) = -1 := by decide
theorem thε_thI_12 : thε (thI {1, 2}) = -1 := by decide
theorem thetaCubeSign_full : thε (thI {0, 1, 2}) = 1 := by decide

theorem hasFDerivAt_prod_zpow_of_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {κ : Type*} [DecidableEq κ] (s : Finset κ) (h : κ → E → ℂ) (h' : κ → E →L[ℂ] ℂ) (n : κ → ℤ) (x : E)
    (hd : ∀ i ∈ s, HasFDerivAt (h i) (h' i) x) (hn : ∀ i ∈ s, h i x ≠ 0)
    (h1 : ∏ i ∈ s, h i x ^ n i = 1) :
    HasFDerivAt (fun z => ∏ i ∈ s, h i z ^ n i) (∑ i ∈ s, ((n i : ℂ) / h i x) • h' i) x := by
  have hz : ∀ i ∈ s, HasFDerivAt (fun z => h i z ^ n i)
      (((n i : ℂ) * h i x ^ (n i - 1)) • h' i) x := by
    intro i hi
    exact (hasDerivAt_zpow (n i) (h i x) (Or.inl (hn i hi))).comp_hasFDerivAt x (hd i hi)
  have := HasFDerivAt.finsetProd (g := fun i z => h i z ^ n i) hz
  refine this.congr_fderiv (Finset.sum_congr rfl fun i hi => ?_)
  have hm := Finset.mul_prod_erase s (fun j => h j x ^ n j) hi
  rw [h1] at hm
  have hne : h i x ^ n i ≠ 0 := zpow_ne_zero _ (hn i hi)
  have he : ∏ j ∈ s.erase i, h j x ^ n j = (h i x ^ n i)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hm)
  rw [he, smul_smul, zpow_sub_one₀ (hn i hi)]
  congr 1
  field_simp

section
variable {E : Type*} [AddCommMonoid E] (a b c : E)
@[simp] theorem vsum_empty : ∑ i ∈ (∅ : Finset (Fin 3)), ![a, b, c] i = 0 := Finset.sum_empty
@[simp] theorem vsum_0 : ∑ i ∈ ({0} : Finset (Fin 3)), ![a, b, c] i = a := Finset.sum_singleton _ _
@[simp] theorem vsum_1 : ∑ i ∈ ({1} : Finset (Fin 3)), ![a, b, c] i = b := Finset.sum_singleton _ _
@[simp] theorem vsum_2 : ∑ i ∈ ({2} : Finset (Fin 3)), ![a, b, c] i = c := Finset.sum_singleton _ _
@[simp] theorem vsum_01 : ∑ i ∈ ({0, 1} : Finset (Fin 3)), ![a, b, c] i = a + b :=
  Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)
@[simp] theorem vsum_02 : ∑ i ∈ ({0, 2} : Finset (Fin 3)), ![a, b, c] i = a + c :=
  Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)
@[simp] theorem vsum_12 : ∑ i ∈ ({1, 2} : Finset (Fin 3)), ![a, b, c] i = b + c :=
  Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)
@[simp] theorem sum_univ_finThree_vecThree : ∑ i ∈ ({0, 1, 2} : Finset (Fin 3)), ![a, b, c] i = a + (b + c) := by
  rw [Finset.sum_insert (by decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3))), vsum_12]
  rfl
end

theorem value_and_fderiv_at_zero : ∀ {g : ℕ} (x y W : Fin g → ℂ) (fr : thK.{0} → (Fin g → ℂ) → ℂ) (F : (Fin g → ℂ) → ℂ),
    F =ᶠ[nhds 0] (fun z => ∏ I : thK.{0}, fr I (∑ i ∈ I.down, ![x, y, z] i) ^ thε I) →
    (∀ I : thK.{0}, DifferentiableAt ℂ (fr I) (∑ i ∈ I.down, ![x, y, 0] i)) →
    (∀ I : thK.{0}, fr I (∑ i ∈ I.down, ![x, y, 0] i) ≠ 0) →
    (∀ I : thK.{0}, 2 ∉ I.down → fr (ULift.up (insert 2 I.down)) = fr I) →
    F 0 = 1 ∧ fderiv ℂ F 0 W =
      fderiv ℂ (fr (ULift.up {0, 1, 2})) (x + y) W / fr (ULift.up {0, 1, 2}) (x + y) +
        fderiv ℂ (fr (ULift.up {2})) 0 W / fr (ULift.up {2}) 0 -
        fderiv ℂ (fr (ULift.up {0, 2})) x W / fr (ULift.up {0, 2}) x -
        fderiv ℂ (fr (ULift.up {1, 2})) y W / fr (ULift.up {1, 2}) y := by
  intro g x y W fr F hF hd hn hpair
  show F 0 = 1 ∧ fderiv ℂ F 0 W =
      fderiv ℂ (fr (thI {0, 1, 2})) (x + y) W / fr (thI {0, 1, 2}) (x + y) +
        fderiv ℂ (fr (thI {2})) 0 W / fr (thI {2}) 0 -
        fderiv ℂ (fr (thI {0, 2})) x W / fr (thI {0, 2}) x -
        fderiv ℂ (fr (thI {1, 2})) y W / fr (thI {1, 2}) y
  have hw : ∀ I : thK.{0}, HasFDerivAt (fun z : Fin g → ℂ => ∑ i ∈ I.down, ![x, y, z] i)
      (∑ i ∈ I.down, ![0, 0, ContinuousLinearMap.id ℂ (Fin g → ℂ)] i) 0 := by
    intro I
    refine HasFDerivAt.fun_sum (A := fun i (z : Fin g → ℂ) => ![x, y, z] i) (fun i _ => ?_)
    fin_cases i
    · exact hasFDerivAt_const x (0 : Fin g → ℂ)
    · exact hasFDerivAt_const y (0 : Fin g → ℂ)
    · exact hasFDerivAt_id (0 : Fin g → ℂ)
  have hc : ∀ I : thK.{0}, HasFDerivAt (fun z : Fin g → ℂ => fr I (∑ i ∈ I.down, ![x, y, z] i))
      ((fderiv ℂ (fr I) (∑ i ∈ I.down, ![x, y, 0] i)).comp
        (∑ i ∈ I.down, ![0, 0, ContinuousLinearMap.id ℂ (Fin g → ℂ)] i)) 0 :=
    fun I => (hd I).hasFDerivAt.comp (0 : Fin g → ℂ) (hw I)
  have p0 : fr (thI {2}) = fr (thI ∅) := hpair (thI ∅) (by decide)
  have p1 : fr (thI {0, 2}) = fr (thI {0}) :=
    (congrArg (fun s => fr (thI s)) (by decide : ({0, 2} : Finset (Fin 3)) = insert 2 {0})).trans
      (hpair (thI {0}) (by decide))
  have p2 : fr (thI {1, 2}) = fr (thI {1}) :=
    (congrArg (fun s => fr (thI s)) (by decide : ({1, 2} : Finset (Fin 3)) = insert 2 {1})).trans
      (hpair (thI {1}) (by decide))
  have p3 : fr (thI {0, 1, 2}) = fr (thI {0, 1}) :=
    (congrArg (fun s => fr (thI s)) (by decide : ({0, 1, 2} : Finset (Fin 3)) = insert 2 {0, 1})).trans
      (hpair (thI {0, 1}) (by decide))
  have n0 := hn (thI ∅)
  have n1 := hn (thI {0})
  have n2 := hn (thI {1})
  have n3 := hn (thI {0, 1})
  simp only [thI_down, vsum_empty, vsum_0, vsum_1, vsum_01] at n0 n1 n2 n3
  have hP0 : ∏ I : thK.{0}, fr I (∑ i ∈ I.down, ![x, y, 0] i) ^ thε I = 1 := by
    rw [prod_thK]
    simp only [thI_down, vsum_empty, vsum_0, vsum_1, vsum_2, vsum_01, vsum_02, vsum_12, sum_univ_finThree_vecThree,
      thε_thI_empty, thε_thI_0, thε_thI_1, thε_thI_2, thε_thI_01, thε_thI_02, thε_thI_12,
      thetaCubeSign_full, p0, p1, p2, p3, add_zero, zpow_one, _root_.zpow_neg, zpow_one]
    field_simp
  refine ⟨by rw [hF.eq_of_nhds]; exact hP0, ?_⟩
  classical
  have hPd := hasFDerivAt_prod_zpow_of_eq_one (Finset.univ : Finset thK.{0})
    (fun (I : thK.{0}) (z : Fin g → ℂ) => fr I (∑ i ∈ I.down, ![x, y, z] i)) _ thε 0
    (fun I _ => hc I) (fun I _ => hn I) hP0
  rw [hF.fderiv_eq (𝕜 := ℂ), hPd.fderiv]
  rw [ContinuousLinearMap.sum_apply, sum_thK]
  simp only [thI_down, vsum_empty, vsum_0, vsum_1, vsum_2, vsum_01, vsum_02, vsum_12, sum_univ_finThree_vecThree,
      thε_thI_empty, thε_thI_0, thε_thI_1, thε_thI_2, thε_thI_01, thε_thI_02, thε_thI_12,
      thetaCubeSign_full, add_zero, zero_add, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply, map_zero, smul_zero,
      smul_eq_mul, Int.cast_one, Int.cast_neg]
  ring

end GlobalTheory.AltJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFormsSpanInvariant
section
open NumberField

namespace GlobalTheory.IntFormsRank

variable {LL : Type} [Field LL] [NumberField LL] {n : ℕ}

theorem smul_eq_algebraMap_smul (r : 𝓞 LL) (z : Fin n → LL) : r • z = (algebraMap (𝓞 LL) LL r) • z :=
  (algebraMap_smul LL r z).symm

theorem exists_den_smul_mem (T : Set (Fin n → LL)) (x : Fin n → LL) (hx : x ∈ Submodule.span LL T) :
    ∃ d : 𝓞 LL, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 LL) T := by
  first
  | exact @_root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span
  | exact _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span
  | (apply _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span ..)

theorem span_inf_eq (T : Set (Fin n → LL)) (hT : Submodule.span LL T = ⊤) (S : Submodule LL (Fin n → LL)) :
    Submodule.span LL ((Submodule.span (𝓞 LL) T ⊓ S.restrictScalars (𝓞 LL) : Submodule (𝓞 LL) (Fin n → LL)) :
      Set (Fin n → LL)) = S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro x hx
    have hxT : x ∈ Submodule.span LL T := by rw [hT]; exact Submodule.mem_top
    obtain ⟨d, hd, hdx⟩ := exists_den_smul_mem T x hxT
    have hdL : algebraMap (𝓞 LL) LL d ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 LL) LL)]; exact hd
    have hmem : d • x ∈ (Submodule.span (𝓞 LL) T ⊓ S.restrictScalars (𝓞 LL) : Submodule (𝓞 LL) (Fin n → LL)) := by
      refine ⟨hdx, ?_⟩
      show d • x ∈ S
      rw [smul_eq_algebraMap_smul]; exact S.smul_mem _ hx
    have hx' : x = (algebraMap (𝓞 LL) LL d)⁻¹ • (d • x) := by
      rw [smul_eq_algebraMap_smul, smul_smul, inv_mul_cancel₀ hdL, one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.IntFormsRank

theorem GlobalTheory.IntFormsRank.rkK_Mall : ∀ (LL Ks : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] (n : ℕ)
    (Wσ : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (Wσ σ)] [∀ σ, InnerProductSpace ℂ (Wσ σ)]
    (G0 : Type) [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks (Fin n → LL) Wσ G0) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) (f : (Fin n → LL) →ₗ[LL] (Fin n → LL)),
    Submodule.span LL (A.MK : Set (Fin n → LL)) = ⊤ →
    Formalism.HN.rkK (A.Mall J0 lam0) = Module.finrank LL (A.typeP J0 lam0) ∧
    Formalism.HN.rkK (A.Mall J0 lam0 ⊓ (LinearMap.ker f).restrictScalars (𝓞 LL)) =
      Module.finrank LL (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)) := by
  intro LL Ks _ _ _ _ _ n Wσ _ _ G0 _ _ A J0 lam0 f hsp
  constructor
  · unfold Formalism.HN.rkK Formalism.IndefR.Arith.FormsL.Mall
    rw [GlobalTheory.IntFormsRank.span_inf_eq _ hsp]
  · unfold Formalism.HN.rkK Formalism.IndefR.Arith.FormsL.Mall
    have e : (Submodule.span (𝓞 LL) (A.MK : Set (Fin n → LL)) ⊓ (A.typeP J0 lam0).restrictScalars (𝓞 LL) ⊓
        (LinearMap.ker f).restrictScalars (𝓞 LL)) =
        Submodule.span (𝓞 LL) (A.MK : Set (Fin n → LL)) ⊓
          (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)).restrictScalars (𝓞 LL) := by
      rw [inf_assoc]; rfl
    rw [e, GlobalTheory.IntFormsRank.span_inf_eq _ hsp]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedPeriodSlopeMulRamificationIndexStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balancedPeriodSlope_mul_ramificationIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io') (r : ℕ), 0 < r → (letI := io.toAlgebra; letI := io'.toAlgebra; ∃ ψ : T.Fr →ₐ[c.F] T'.Fr, (∀ x, x ≠ 0 → vV T'.V (ψ x) = (r : ℤ) * vV T.V x) ∧ FrMap ψ y.1 y'.1) → ∀ φ φ' : ℝ, HasPhi y φ → HasPhi y' φ' → φ' = r * φ := by
  first | exact @GlobalTheory.SlopeRec.phi_eq_mul_of_frMap | exact GlobalTheory.SlopeRec.phi_eq_mul_of_frMap | (intros; apply GlobalTheory.SlopeRec.phi_eq_mul_of_frMap <;> assumption)
end

