module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0486
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointsUniformisationsWeilPairingGal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

namespace GlobalTheory.GenRestrict

theorem exists_genericPoints_equiv_any : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ g : R →+* V, Function.Injective g → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G'), LBIso U'.LG.L (U.LG.L.pull β) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F],
      (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r))) →
      ∃ e : (TFK (R := V) F ⟶ A'.A) ≃* (TFK (R := R) F ⟶ A.A),
        (∀ (k : ℕ) (x y : TFK (R := V) F ⟶ A'.A) (c : Fˣ), WeilIs A'.A A'.L (k : ℤ) x y (unitOn c) → WeilIs A.A A.L (k : ℤ) (e x) (e y) (unitOn c)) ∧
        (∀ (σ : F →ₐ[FractionRing V] F) (x x' : TFK (R := V) F ⟶ A'.A), x'.left = spMap σ.toRingHom ≫ x.left → (e x').left = spMap σ.toRingHom ≫ (e x).left) ∧
        ∀ x : TFK (R := V) F ⟶ A'.A, (e x).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = x.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) ≫ β := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV hDVR g hinj G' _ _ β h hG' D' A' U' hL F _ _ _ _ hc
  obtain ⟨gR, lR⟩ := unifPre_generic U.toUnifPre
  obtain ⟨gV, lV⟩ := unifPre_generic U'.toUnifPre
  have gVG : IsGrpPullback A'.A G (jK V ≫ spMap g) ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) ≫ β) :=
    gV.comp h
  have hcomp : jFK (R := V) F ≫ jK V ≫ spMap g = jFK (R := R) F ≫ jK R := by
    have e1 : (algebraMap (FractionRing V) F).comp ((algebraMap V (FractionRing V)).comp g) =
        (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) := RingHom.ext fun r => (hc r).symm
    calc jFK (R := V) F ≫ jK V ≫ spMap g
        = spMap ((algebraMap (FractionRing V) F).comp ((algebraMap V (FractionRing V)).comp g)) := by
          rw [spMap_comp_eq (algebraMap (FractionRing V) F), spMap_comp_eq (algebraMap V (FractionRing V)) g]
      _ = spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) := by rw [e1]
      _ = jFK (R := R) F ≫ jK R := spMap_comp_eq _ _
  obtain ⟨eV, heV⟩ := GlobalTheory.LiePull.exists_pushEquiv gVG (TFK (R := V) F) (jFK (R := V) F ≫ jK V ≫ spMap g) rfl
  obtain ⟨eR, heR⟩ := GlobalTheory.LiePull.exists_pushEquiv gR (TFK (R := R) F) (jFK (R := V) F ≫ jK V ≫ spMap g) hcomp
  obtain ⟨eR₀, heR₀⟩ := GlobalTheory.LiePull.exists_pushEquiv gR (TFK (R := R) F) (jFK (R := R) F ≫ jK R) rfl
  have hlast : ∀ x, (eR.symm (eV x)).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      x.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) ≫ β := fun x => by
    rw [← heR, MulEquiv.apply_symm_apply, heV]
    simp only [Category.assoc]
  have lVG : LBIso A'.L (U.LG.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) ≫ β)) :=
    LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB U.LG.isLB _) lV
      (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull U'.LG.L _ _ rfl)
        (chartPullSame U.LG.L _ (fun _ => β) _ (U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) fun _ => rfl) hL)
  refine ⟨eV.trans eR.symm, fun k x y c hw => ?_, fun σ x x' hx => ?_, fun x => ?_⟩
  · have h1 := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ G A'.A _ _ U.LG.L A'.L U.LG.isLB A'.isLB gVG lVG
      (TFK (R := V) F) k x y (eV x) (eV y) (unitOn c) (heV x) (heV y)).1 hw
    have h2 := (weilIs_congr_base G U.LG.L k hcomp (eV x) (eV y) (eR₀ (eR.symm (eV x))) (eR₀ (eR.symm (eV y)))
      (by rw [heR₀, ← heR, MulEquiv.apply_symm_apply]) (by rw [heR₀, ← heR, MulEquiv.apply_symm_apply]) _).1 h1
    exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ G A.A _ _ U.LG.L A.L U.LG.isLB A.isLB gR lR
      (TFK (R := R) F) k _ _ _ _ (unitOn c) (heR₀ _) (heR₀ _)).2 h2
  · have hσ : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
      simp only [RingHom.comp_apply, AlgHom.coe_toRingHom]
      rw [hc r]
      exact σ.commutes _
    refine gR.1.hom_ext ?_ ?_
    · simp only [MulEquiv.trans_apply, Category.assoc, hlast, hx]
    · rw [Over.w, Category.assoc, Over.w]
      show jFK (R := R) F = spMap σ.toRingHom ≫ jFK (R := R) F
      rw [← spMap_comp_eq, hσ]
  · exact hlast x

end GlobalTheory.GenRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueCopiesOfSchemeCocycle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GlueCopies

theorem desc_of_compat (D : Scheme.GlueData.{0}) {S : Scheme.{0}} (p : ∀ i, D.U i ⟶ S)
    (h : ∀ i j, D.f i j ≫ p i = (D.t i j ≫ D.f j i) ≫ p j) :
    ∃ F : D.glued ⟶ S, ∀ i, D.ι i ≫ F = p i :=
  ⟨Multicoequalizer.desc D.toGlueData.diagram S p (by rintro ⟨i, j⟩; exact h i j),
    fun i => Multicoequalizer.π_desc _ _ _ _ _⟩

theorem exists_glue_copies : ∀ (Y : Scheme.{0}) (J : Type) (V : J → J → Y.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ Y), (∀ i, V i i = ⊤) → (∀ i, τ i i = (V i i).ι) → (∀ (i j k : J) (x : (V i j).toScheme), (V i j).ι x ∈ V i k → τ i j x ∈ V j k) → (∀ (i j k : J) (T : Scheme.{0}) (x : T ⟶ (V i j).toScheme) (y : T ⟶ (V i k).toScheme) (w : T ⟶ (V j k).toScheme), x ≫ (V i j).ι = y ≫ (V i k).ι → x ≫ τ i j = w ≫ (V j k).ι → w ≫ τ j k = y ≫ τ i k) → ∃ (G : Scheme.{0}) (ψ : J → (Y ⟶ G)), (∀ j, IsOpenImmersion (ψ j)) ∧ (∀ g : G, ∃ j, g ∈ Set.range (ψ j)) ∧ (∀ i j, IsPullback (V i j).ι (τ i j) (ψ i) (ψ j)) ∧ ∀ (Z : Scheme.{0}) (g : J → (Y ⟶ Z)), (∀ i j, (V i j).ι ≫ g i = τ i j ≫ g j) → ∃ F : G ⟶ Z, ∀ j, ψ j ≫ F = g j := by
  intro Y J V τ hV hτ hr hc
  have mem_of : ∀ (U : Y.Opens) {T : Scheme.{0}} (f : T ⟶ U.toScheme) (p : T), (f ≫ U.ι) p ∈ U :=
    fun U T f p => by
      have h := Set.mem_range_self (f := ⇑U.ι) (f p)
      rw [Scheme.Opens.range_ι] at h
      rw [Scheme.Hom.comp_apply]; exact h
  have hs : ∀ i, ∃ s : Y ⟶ (V i i).toScheme, s ≫ (V i i).ι = 𝟙 _ := fun i =>
    ⟨IsOpenImmersion.lift (V i i).ι (𝟙 _) (by
      rw [Scheme.Opens.range_ι, hV]; intro x _; simp), IsOpenImmersion.lift_fac _ _ _⟩
  choose s hs using hs
  have ht : ∀ i j, ∃ t : (V i j).toScheme ⟶ (V j i).toScheme, t ≫ (V j i).ι = τ i j := fun i j =>
    ⟨IsOpenImmersion.lift (V j i).ι (τ i j) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hr i j i x (by rw [hV]; simp)), IsOpenImmersion.lift_fac _ _ _⟩
  choose t ht using ht
  have htb : ∀ i j, t i j ≫ τ j i = (V i j).ι := fun i j => by
    have h1 := hc i j i _ (𝟙 _) ((V i j).ι ≫ s i) (t i j) (by simp [hs]) (by simp [ht])
    rw [h1, hτ, Category.assoc, hs, Category.comp_id]
  have hu : ∀ i j k, ∃ u : pullback (V i j).ι (V i k).ι ⟶ (V j k).toScheme,
      u ≫ (V j k).ι = pullback.fst _ _ ≫ τ i j := fun i j k =>
    ⟨IsOpenImmersion.lift (V j k).ι (pullback.fst _ _ ≫ τ i j) (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
      apply hr i j k
      rw [← Scheme.Hom.comp_apply, pullback.condition]
      exact mem_of _ _ _), IsOpenImmersion.lift_fac _ _ _⟩
  choose u hu using hu
  have hub : ∀ i j k, u i j k ≫ τ j k = pullback.snd _ _ ≫ τ i k := fun i j k =>
    hc i j k _ (pullback.fst _ _) (pullback.snd _ _) (u i j k) pullback.condition (hu i j k).symm
  let D : Scheme.GlueData.{0} :=
    { J := J
      U := fun _ => Y
      V := fun p => (V p.1 p.2).toScheme
      f := fun i j => (V i j).ι
      f_mono := fun i j => inferInstance
      f_id := fun i => ⟨s i, by rw [← cancel_mono (V i i).ι, Category.assoc, hs]; simp, hs i⟩
      t := t
      t_id := fun i => by rw [← cancel_mono (V i i).ι, ht, hτ, Category.id_comp]
      t' := fun i j k => pullback.lift (u i j k) (pullback.fst _ _ ≫ t i j) (by simp [hu, ht])
      t_fac := fun i j k => pullback.lift_snd _ _ _
      cocycle := fun i j k => by
        rw [← cancel_mono (pullback.fst (V i j).ι (V i k).ι), ← cancel_mono (V i j).ι]
        simp only [Category.assoc, pullback.lift_fst_assoc, hu, hub, pullback.lift_snd_assoc, htb,
          Category.id_comp]
      f_open := fun i j => inferInstance }
  have hP : ∀ i j, IsPullback (V i j).ι (τ i j) (D.ι i) (D.ι j) := fun i j => by
    rw [← ht]
    exact IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)
  refine ⟨D.glued, D.ι, fun j => D.ι_isOpenImmersion j, fun g => ?_, hP, fun Z g hg => ?_⟩
  · obtain ⟨j, y, rfl⟩ := D.ι_jointly_surjective g
    exact ⟨j, y, rfl⟩
  · refine desc_of_compat D g fun i j => ?_
    change (V i j).ι ≫ g i = (t i j ≫ (V j i).ι) ≫ g j
    rw [ht, hg]

end GlobalTheory.GlueCopies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLawTranslateDerivationInvariantForms
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.InvForm

section Alg
variable {R C E : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing E] [Algebra R E]

theorem dVal_smul_left (φ : C →ₐ[R] DualNumber E) (c : C) (x : Ω[C⁄R]) :
    dVal φ (c • x) = (φ c).fst * dVal φ x := by
  letI : Algebra C E := (redHom φ).toAlgebra
  haveI : IsScalarTower R C E := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  unfold dVal
  simp only [LinearMap.coe_restrictScalars]
  rw [LinearMap.map_smul]
  rfl

def semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x) :
    C →ₐ[R] DualNumber E where
  toFun c := TrivSqZeroExt.inl (σ c) + TrivSqZeroExt.inr (θ (KaehlerDifferential.D R C c))
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [hθ, MulOpposite.smul_eq_mul_unop]; ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x)
    (c : C) : (semiDerHom σ θ hθ c).fst = σ c := by simp [semiDerHom]

theorem dVal_semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x) :
    dVal (semiDerHom σ θ hθ) = θ := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using GlobalTheory.CechDR.ind1 with
  | h b c =>
    rw [dVal_smul_left, dVal_D, hθ, fst_semiDerHom]
    simp [semiDerHom]
  | h0 => simp
  | ha x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end Alg
end GlobalTheory.InvForm

namespace GlobalTheory.InvForm

theorem exists_transl_val : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U V : AffOp A.left)
    (θ : Ω[Sec A.hom V.unop.1⁄R] →ₗ[R] Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1),
    (∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) →
    ∃ ψ : Sec A.hom U.unop.1 →ₐ[R] DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1),
      (∀ b, (ψ b).fst = b ⊗ₜ 1) ∧
      ∀ w : GlobalTheory.InvForm.InvForm A, θ (evForm A.hom V w.1) = GlobalTheory.InvForm.dVal ψ (evForm A.hom U w.1) := by
  intro R _ A _ U V θ hθ
  let T := Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1
  let σ : Sec A.hom V.unop.1 →ₐ[R] T := Algebra.TensorProduct.includeRight
  let τ : Sec A.hom U.unop.1 →ₐ[R] T := Algebra.TensorProduct.includeLeft
  have hθ' : ∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = σ c * θ x := hθ
  let φ := semiDerHom σ θ hθ'
  let aV : Over.mk (spMap (algebraMap R (Sec A.hom V.unop.1))) ⟶ A :=
    Over.homMk (affPt A.hom V.unop) (affPt_w A.hom V.unop)
  let aU : Over.mk (spMap (algebraMap R (Sec A.hom U.unop.1))) ⟶ A :=
    Over.homMk (affPt A.hom U.unop) (affPt_w A.hom U.unop)
  let p := GlobalTheory.DeRham.spOver φ ≫ aV
  let x₀ := GlobalTheory.DeRham.spOver τ ≫ aU
  let y₀ := GlobalTheory.DeRham.spOver σ ≫ aV
  let q' := y₀⁻¹ * x₀
  let dualInclusion := TrivSqZeroExt.inlAlgHom R T T
  let dualProjection := TrivSqZeroExt.fstHom R T T
  let q := GlobalTheory.DeRham.spOver dualInclusion ≫ q'
  let red := GlobalTheory.DeRham.spOver dualProjection
  have h1 : red ≫ p = y₀ := by
    have hφ : dualProjection.comp φ = σ := AlgHom.ext fun c ↦ fst_semiDerHom σ θ hθ' c
    simp only [red, p, y₀, ← Category.assoc, GlobalTheory.DeRham.spOver_comp, hφ]
  have h2 : red ≫ q = q' := by
    have hsection : dualProjection.comp dualInclusion = AlgHom.id R T := AlgHom.ext fun _ ↦ rfl
    have hid : GlobalTheory.DeRham.spOver (AlgHom.id R T) = 𝟙 (Over.mk (spMap (algebraMap R T))) := by
      apply Over.OverMorphism.ext
      simp only [GlobalTheory.DeRham.spOver, Over.homMk_left, Over.id_left]
      exact Cris.spMap_id T
    simp only [red, q, ← Category.assoc, GlobalTheory.DeRham.spOver_comp, hsection, hid, Category.id_comp]
  have h3 : red ≫ (p * q) = x₀ := by
    rw [MonObj.comp_mul, h1, h2, mul_inv_cancel_left]
  have h3Left : spMap dualProjection.toRingHom ≫ (p * q).left = spMap τ.toRingHom ≫ affPt A.hom U.unop := by
    simpa only [Over.comp_left, red, x₀, aU, GlobalTheory.DeRham.spOver, Over.homMk_left,
      AlgHom.toRingHom_eq_coe]
      using congrArg (fun f ↦ f.left) h3
  have htop : ⊤ ≤ (p * q).left ⁻¹ᵁ U.unop.1 := by
    have hsurj : Function.Surjective (spMap dualProjection.toRingHom) :=
      GlobalTheory.PtExt.surjective_spMap_of_sq _ TrivSqZeroExt.fst_surjective fun a ha ↦ by
        have ha' : a.fst = 0 := ha
        ext <;> simp [ha']
    intro x _
    obtain ⟨t, rfl⟩ := hsurj x
    change ((spMap dualProjection.toRingHom ≫ (p * q).left).base t) ∈ U.unop.1
    rw [h3Left]
    change U.unop.2.fromSpec.base ((spMap τ.toRingHom).base t) ∈ U.unop.1
    exact (Set.ext_iff.mp U.unop.2.range_fromSpec _).1 ⟨_, rfl⟩
  have hs : (p * q).left ≫ A.hom = spMap (algebraMap R (DualNumber T)) := Over.w (p * q)
  let ψ := GlobalTheory.CechKS.FormLocal.valHom (s := A.hom) (U := U.unop.1) (p * q).left htop hs
  have hψ : spMap ψ.toRingHom ≫ affPt A.hom U.unop = (p * q).left :=
    GlobalTheory.CechKS.FormLocal.valHom_pt U.unop.2 _ htop hs
  have hfst : dualProjection.toRingHom.comp ψ.toRingHom = τ.toRingHom := by
    apply GlobalTheory.CechKS.FormLocal.ringHom_ext_affPt (s := A.hom) U.unop.2
    change spMap _ ≫ affPt A.hom U.unop = spMap _ ≫ affPt A.hom U.unop
    rw [Cris.spMap_comp, Category.assoc, hψ]
    exact h3Left
  refine ⟨ψ, fun b ↦ RingHom.congr_fun hfst b, fun w ↦ ?_⟩
  have hp : p.left = spMap φ.toRingHom ≫ affPt A.hom V.unop := by
    simp only [p, aV, Over.comp_left, GlobalTheory.DeRham.spOver, Over.homMk_left, AlgHom.toRingHom_eq_coe]
  have hq : q.left = spMap (algebraMap T (DualNumber T)) ≫ q'.left := by
    have hι : (dualInclusion : T →+* DualNumber T) = algebraMap T (DualNumber T) := RingHom.ext fun _ ↦ rfl
    simp only [q, Over.comp_left, GlobalTheory.DeRham.spOver, Over.homMk_left, hι]
  have key := w.2 T V.unop U.unop φ ψ p q q'.left hp hq hψ.symm
  rw [dVal_semiDerHom] at key
  exact key

end GlobalTheory.InvForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolyLocalInvariantNonposChar0
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

namespace GlobalTheory.ResZeroDepth

theorem exists_harmA_nuLocOf_nonpos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∃ P₁ ∈ harmA (Dw := Dw) c a n, ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → ∀ e k : ℕ, 0 < e → GlobalTheory.FactorDepth.nuLocOf C e k (MvPolynomial.map io P₁) ≤ 0 := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro a n ha hn
  classical
  have hcard : Fintype.card (Lt1 Dw) ≤ n := by
    refine le_trans ?_ hn
    rw [Fintype.card_eq_sum_ones]
    exact Finset.sum_le_sum fun f _ => by unfold rk; omega
  have hdom : Formalism.L2.Pj.DomW Dw a := fun τ i j hij => ha τ hij
  have hinj : Function.Injective (Formalism.L2.Pj.colP Dw hcard) := fun p q h =>
    (Fintype.equivFin _).injective (Fin.castLE_injective hcard h)
  refine ⟨MvPolynomial.map (Int.castRingHom c.F)
      (Formalism.L2.Pj.Crude.Pmin Dw.mult n (Formalism.L2.Pj.colP Dw hcard) fun τ i => a (τ, i)),
    Formalism.L2.Pj.Crude.Pmin_mem Dw.mult n c.F _ _ _ _ _ (fun τ _ => Formalism.L2.Pj.conj_ne_self_of_CM τ) hinj hdom, ?_⟩
  intro T io y C hres e k _
  letI := io.toAlgebra
  have hmap : MvPolynomial.map io (MvPolynomial.map (Int.castRingHom c.F)
      (Formalism.L2.Pj.Crude.Pmin Dw.mult n (Formalism.L2.Pj.colP Dw hcard) fun τ i => a (τ, i))) =
      Formalism.L2.Pj.P1 Dw T a hcard := by
    rw [MvPolynomial.map_map, RingHom.ext_int (io.comp _) (Int.castRingHom T.Fr)]
    rfl
  obtain ⟨-, f, hf, -, hv⟩ := Formalism.L2.Pj.crude_val C.ch.B C.ch.h C.ch.gauge H.w0 k C.ch.uvec
    (Formalism.L2.Pj.satDir_of Formalism.L2.Pj.chart_saturated C) a n hdom hcard
  rw [hmap]
  refine le_trans (iInf_le_of_le f (iInf_le_of_le hf (le_of_eq (congrArg (Formalism.L2.Pj.nval T.V e) hv)))) ?_
  set N := Formalism.L2.Pj.fact1 Dw a hcard with hN
  have hN0 : N ≠ 0 := by
    rw [hN]; unfold Formalism.L2.Pj.fact1
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hu : IsUnit ((N : ℕ) : T.V) := by
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_
    rw [map_natCast]
    exact Nat.cast_ne_zero.2 hN0
  have hne : ((N : ℕ) : T.Fr) ≠ 0 := by
    rw [← map_natCast (algebraMap T.V T.Fr)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hu.ne_zero
  have hv0 : Formalism.L2.Pj.vV T.V ((N : ℕ) : T.Fr) = 0 := by
    rw [← map_natCast (algebraMap T.V T.Fr)]
    exact GlobalTheory.RefSum.GlobalPoly.vV_of_isUnit T hu
  rw [Formalism.L2.Pj.nval_of_ne hne, hv0]
  simp

end GlobalTheory.ResZeroDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentImaginaryQuadraticEigenCrystal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.UPel.HT


open Polynomial in
theorem exists_idem_crys : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] (ρ : D.O →+* Module.End C H) (φ : LinearMap.BilinForm C H), (∀ (c : D.O) x y, φ (ρ c x) y = φ x (ρ (D.star c).unop y)) → ∃ e : Module.End C H, e * e = e ∧ (∀ c, ρ c * e = e * ρ c) ∧ (∀ x y, φ (e x) y = φ x (y - e y)) ∧ (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) ∧ (∃ v : C, IsUnit v ∧ ∀ x, e x = 0 → ρ (algebraMap (𝓞 D.F) D.O D.ω) x - tR b.ρ • x = v • x) ∧ ∀ N : Submodule C H, (∀ (c : D.O), ∀ x ∈ N, ρ c x ∈ N) → ∀ x ∈ N, e x ∈ N := by
  intro p _ D R _ b C _ tR H _ _ ρ φ hφ

  have hroot : tR b.ρ ^ 2 - (D.tr : C) * tR b.ρ + (D.nm : C) = 0 := by
    have := congrArg tR b.ρ_root
    simpa only [map_sub, map_add (f := _), map_mul, map_pow, map_intCast, map_zero] using this
  have hu2 : (tR b.ρ - ((D.tr : C) - tR b.ρ)) ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : C) := by
    push_cast; linear_combination 4 * hroot
  have hunit : IsUnit (tR b.ρ - ((D.tr : C) - tR b.ρ)) := by
    have hk : (D.tr ^ 2 - 4 * D.nm : ℤ) = -((D.tr ^ 2 - 4 * D.nm).natAbs : ℤ) := by
      rw [Int.ofNat_natAbs_of_nonpos (le_of_lt D.disc_neg)]; ring
    have hcop : (D.tr ^ 2 - 4 * D.nm).natAbs.Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
      intro h; apply D.disc_p; exact Int.natCast_dvd.mpr h
    have h1 := (b.unit _ hcop).map tR
    have : IsUnit ((tR b.ρ - ((D.tr : C) - tR b.ρ)) ^ 2) := by
      rw [hu2, hk]; push_cast; simpa using h1.neg
    exact (isUnit_pow_iff two_ne_zero).mp this
  obtain ⟨uu, huu⟩ := hunit
  have hui : (↑uu⁻¹ : C) * (tR b.ρ - ((D.tr : C) - tR b.ρ)) = 1 := by rw [← huu]; exact uu.inv_mul

  set ui : C := (↑uu⁻¹ : C) with hui_def
  set r : C := tR b.ρ with hr_def
  set W : Module.End C H := ρ (algebraMap (𝓞 D.F) D.O D.ω) with hW_def

  have hωF : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    linear_combination D.ω * D.tr_eq - D.nm_eq
  have hWrel : W * W - (D.tr : Module.End C H) * W + (D.nm : Module.End C H) = 0 := by
    have := congrArg (fun z => ρ (algebraMap (𝓞 D.F) D.O z)) hωF
    simpa only [map_sub, map_add (f := _), map_mul, map_intCast, map_zero] using this
  have hWx : ∀ x, W (W x) = (D.tr : C) • W x - (D.nm : C) • x := by
    intro x
    have := congrArg (fun f : Module.End C H => f x) hWrel
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, Module.End.intCast_apply,
      LinearMap.zero_apply] at this
    rw [← Int.cast_smul_eq_zsmul C, ← Int.cast_smul_eq_zsmul C] at this
    rw [← sub_eq_zero, ← this]; abel

  have hcomm : ∀ c : D.O, ∀ x, ρ c (W x) = W (ρ c x) := by
    intro c x
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Algebra.commutes]
  have hbar : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω := by rw [← D.tr_eq]; ring
  have hWadj : ∀ x y, φ (W x) y = φ x ((D.tr : C) • y - W y) := by
    intro x y
    rw [hW_def, hφ, D.star_F, MulOpposite.unop_op, hbar, map_sub, map_intCast, map_sub, map_intCast,
      LinearMap.sub_apply, Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul C]
  refine ⟨ui • (W - ((D.tr : C) - r) • 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul,
      map_sub, hWx]
    match_scalars
    all_goals first | linear_combination ui * hui | linear_combination (-ui * ((D.tr:C) - r)) * hui - ui ^ 2 * hroot | linear_combination (ui * ((D.tr:C) - r)) * hui + ui ^ 2 * hroot | linear_combination (-ui * ((D.tr:C) - r)) * hui + ui ^ 2 * hroot | linear_combination (ui * ((D.tr:C) - r)) * hui - ui ^ 2 * hroot
  · intro c; ext x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul,
      map_sub, hcomm]
  · intro x y
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_sub,
      LinearMap.smul_apply, LinearMap.sub_apply, hWadj, smul_eq_mul]
    linear_combination (φ x y) * hui
  · intro x
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_sub, hWx]
    match_scalars
    all_goals first | linear_combination (0:C) | linear_combination ui * hroot | linear_combination -ui * hroot
  · refine ⟨-(r - ((D.tr : C) - r)), by rw [← huu]; exact (Units.isUnit uu).neg, ?_⟩
    intro x hx
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply] at hx
    have h2 : W x - ((D.tr : C) - r) • x = 0 := by
      have := congrArg (fun z => (↑uu : C) • z) hx
      simpa [smul_smul, hui_def] using this
    rw [sub_eq_zero] at h2
    rw [h2]
    match_scalars
    ring
  · intro N hN x hx
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
    exact N.smul_mem _ (N.sub_mem (hN _ x hx) (N.smul_mem _ hx))

end GlobalTheory.UPel.HT
end

