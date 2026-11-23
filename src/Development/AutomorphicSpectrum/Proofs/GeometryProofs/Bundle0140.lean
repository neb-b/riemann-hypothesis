module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceFamilyOverlap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationModel
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0048
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenCover
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderFlatBaseChange
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0012
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAfterFiniteExtension
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CiEigVal
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0133
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRank

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeBound
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem chartPack_lift_overlap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c₁ c₂ : ∀ k, J k), mseg y c₁ ≠ 0 → mseg y c₂ ≠ 0 → ∀ (P₁ : ChartPack G O c₁) (P₂ : ChartPack G O c₂) (x : Fin (D.p + D.q) → 𝓞 E), ∃ n : ℕ, ∃ u ∈ P₂.Dh.om, (mseg y c₁ / mseg y c₂) ^ n • (P₁.Dh.h x - P₂.Dh.h x) = (p ^ 𝔐.R p) • u :=
  PositivityTheory.Xgn.sequence_family_overlap

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLieModelExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

theorem frame_lieModel_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (u : Fin n → ℂ), ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left) :=
  @PositivityTheory.Xgn.quotient_uniformization_model

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenImmersion
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem btEmb_localData (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)))
    (hj : Γ.IsEmb (Γ.btOrder ⊤) j) (R' : Type) [CommRing R'] [IsDomain R'] [HenselianLocalRing R'] [Algebra R R']
    [IsIntegrallyClosed R'] (hflat : Module.Flat R R') :
    ∃ (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left) (j' : Γ'.G.left ⟶ Spec (CommRingCat.of (Γ'.btOrder ⊤)))
      (ψ : Γ.btOrder ⊤ →+* Γ'.btOrder ⊤) (U : Γ'.G.left.Opens),
      (∀ (a : Γ.btOrder ⊤) (t : T), (ψ a).1 t = algebraMap R R' (a.1 t)) ∧
      IsPullback (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
      IsPullback F j' j (Spec.map (CommRingCat.ofHom ψ)) ∧
      IsOpenImmersion (U.ι ≫ j') ∧ Γ'.TranslatesCover (Γ'.btOrder ⊤) j' U ∧
      ∀ x : Γ'.G.left, Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))) (j' x) =
        IsLocalRing.closedPoint R' → x ∈ U := by
  have hA := _root_.PositivityTheory.UnitarySelfGeneration.bt_hopf R T Γ
  have hinj : Function.Injective (algebraMap R R') := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hreg : IsSMulRegular R' r :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R') (mem_nonZeroDivisors_of_ne_zero hr0)
    have : r • (1 : R') = r • (0 : R') := by
      simp [Algebra.smul_def, hr]
    exact one_ne_zero (hreg this)
  obtain ⟨Γ', F, hbc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_isBaseChange_of_injective R T Γ R' (algebraMap R R') hinj
  haveI := Γ'.quasiFinite
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  haveI := Γ'.finPres
  obtain ⟨U, hUfin, hUcl⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.exists_isFinite_open_of_henselian R' Γ'.G.left Γ'.G.hom
  have hU : Γ'.IsFinOpenSub U := _root_.GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre R' T Γ' U hUfin hUcl
  obtain ⟨j', hj'⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.BT.exists_unique_emb_btOrder_top R' T Γ').exists
  have hbt := _root_.GlobalTheory.CompanionTheory.Ar.BT.FlatBC.btOrder_flat_baseChange R T Γ R' Γ' F hbc hflat
  have hfull : ∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ := by
    obtain ⟨d, hd, hf⟩ := hA.full
    exact ⟨d, fun h => hd (hinj (by simpa using h)), hf⟩
  have hext := (_root_.GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change R T R' (Γ.btOrder ⊤) hA hfull).2
  have hext' : ∃ e : R' ⊗[R] (Γ.btOrder ⊤) ≃ₐ[R'] Γ'.btOrder ⊤,
      ∀ (a : Γ.btOrder ⊤) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) := by
    rw [hbt]; exact hext
  obtain ⟨e, he⟩ := hext'
  let iL : R' →+* R' ⊗[R] (Γ.btOrder ⊤) := Algebra.TensorProduct.includeLeftRingHom
  let iR : (Γ.btOrder ⊤) →+* R' ⊗[R] (Γ.btOrder ⊤) :=
    (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := Γ.btOrder ⊤)).toRingHom
  let ψ : Γ.btOrder ⊤ →+* Γ'.btOrder ⊤ := (e : R' ⊗[R] (Γ.btOrder ⊤) →+* Γ'.btOrder ⊤).comp iR
  have hψ : ∀ (a : Γ.btOrder ⊤) (t : T), (ψ a).1 t = algebraMap R R' (a.1 t) := fun a t => he a t
  have sq : IsPullback (Spec.map (CommRingCat.ofHom iL)) (Spec.map (CommRingCat.ofHom iR))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R R' (Γ.btOrder ⊤))
  let eH : CommRingCat.of (R' ⊗[R] (Γ.btOrder ⊤)) ⟶ CommRingCat.of (Γ'.btOrder ⊤) :=
    CommRingCat.ofHom (e : R' ⊗[R] (Γ.btOrder ⊤) →+* Γ'.btOrder ⊤)
  haveI : IsIso eH := (e.toRingEquiv.toCommRingCatIso).isIso_hom
  have hb : Spec.map (CommRingCat.ofHom ψ) = Spec.map eH ≫ Spec.map (CommRingCat.ofHom iR) := by
    rw [← Spec.map_comp]; rfl
  have hq : Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))) =
      Spec.map eH ≫ Spec.map (CommRingCat.ofHom iL) := by
    rw [← Spec.map_comp]
    congr 2
    ext r t
    exact congrArg (fun y : Γ'.btOrder ⊤ => y.1 t) (e.commutes r).symm
  have hsq : IsPullback (Spec.map (CommRingCat.ofHom ψ))
      (Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    refine IsPullback.of_iso sq.flip (asIso (Spec.map eH)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hb]
    · simp [hq]
    · simp
    · simp
  have hw : F ≫ j = j' ≫ Spec.map (CommRingCat.ofHom ψ) :=
    _root_.GlobalTheory.CompanionTheory.Ar.BT.isEmb_baseChange_square R T Γ R' Γ' F hbc _ _ ψ hψ j j' hj hj'
  have hsq2 : IsPullback F j' j (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_bot ?_ hw hsq
    rw [hj'.isOver, hj.isOver]
    exact hbc.cart
  obtain ⟨ho, hTC⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.EmbSub.openImmersion_translatesCover R' T Γ' U hU j' hj'
  refine ⟨Γ', F, j', ψ, U, hψ, hsq, hsq2, ho, hTC, fun x hx => hUcl x ?_⟩
  rw [← hj'.isOver]
  simpa using hx

theorem btEmb_specMap_asIdeal {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (x : Spec (CommRingCat.of B)) :
    (Spec.map (CommRingCat.ofHom φ) x).asIdeal = Ideal.comap φ x.asIdeal := rfl

theorem isOpenImmersion_emb_and_translatesCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsOpenImmersion j ∧ Γ.TranslatesCover (Γ.btOrder ⊤) j ⊤ := by
  intro R _ _ _ _ T _ _ Γ j hj
  have hA := _root_.PositivityTheory.UnitarySelfGeneration.bt_hopf R T Γ
  refine ⟨?_, ?_⟩
  · haveI := hA.finite
    haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    haveI : LocallyOfFinitePresentation (j ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) := by
      rw [hj.isOver]; exact Γ.finPres
    haveI := GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp j
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))))
    refine _root_.PositivityTheory.HtPt.Mi.open_crit R Γ.G.left _ j (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) ?_
    intro P _
    obtain ⟨R', _, _, _, _, hic, hflat, hcomap⟩ := _root_.GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime R P
    obtain ⟨Γ', F, j', ψ, U, -, hsq, hsq2, ho, -, hcl⟩ := btEmb_localData R T Γ j hj R' hflat
    exact ⟨R', inferInstance, inferInstance, inferInstance, Γ'.G.left, _, j', _, F, _, U, hflat, hcomap, hsq, hsq2, ho, hcl⟩
  · intro P
    let p : Ideal R := P.asIdeal.comap (algebraMap R (Γ.btOrder ⊤))
    haveI : p.IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨R', _, _, _, _, hic, hflat, hcomap⟩ := _root_.GlobalTheory.CompanionTheory.CommAlg.exists_flat_henselian_normal_over_prime R p
    obtain ⟨Γ', F, j', ψ, U, hψ, hsq, hsq2, -, hTC, -⟩ := btEmb_localData R T Γ j hj R' hflat
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))))
      (g := Spec.map (CommRingCat.ofHom (algebraMap R R'))) P (IsLocalRing.closedPoint R')
      (PrimeSpectrum.ext hcomap.symm)
    let Q := hsq.isoPullback.inv z
    have hQ : Spec.map (CommRingCat.ofHom ψ) Q = P := by
      rw [← hz1]
      change (hsq.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom ψ)) z = _
      rw [hsq.isoPullback_inv_fst]
    obtain ⟨t, g', -, H⟩ := hTC Q
    refine ⟨t, F g', trivial, fun f f' hff => ?_⟩
    have h1 := H (ψ f) (ψ f') (fun h => by rw [hψ, hψ, hff])
    have hg : (j (F g')).asIdeal = Ideal.comap ψ (j' g').asIdeal := by
      rw [← btEmb_specMap_asIdeal]
      change ((F ≫ j) g').asIdeal = ((j' ≫ Spec.map (CommRingCat.ofHom ψ)) g').asIdeal
      rw [hsq2.w]
    rw [hg, ← hQ, btEmb_specMap_asIdeal]
    exact h1

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAfterFiniteExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_after_finite_extension : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] [CharZero Ω] (i : Ω₁ →+* Ω) (y : (Σ k, J k) → Ω₁) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω₁) ⟶ X), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (M : PModel ℤ (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩)) (h : M.X ⟶ X), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = i (y ⟨k, a⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates M.ξ ξ h i ∧ Flat.NormalCpt M.ξ ∧ SmoothGenericFibreM y' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChangeModel.exists_normal_model | exact GlobalTheory.CompanionTheory.Ar.ChangeModel.exists_normal_model | (intros; apply GlobalTheory.CompanionTheory.Ar.ChangeModel.exists_normal_model <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieEigenDecomposition
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.EigVal

theorem values_eigen_sheaves : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (k K : Type) [Field k] [Field K] [Algebra k K] (z : Spec (CommRingCat.of K) ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (O S : Type) [CommRing O] [Fintype S] (act : O → (G ⟶ G)) (r : O →+* Module.End Ω V) (rz : O →+* Module.End K Vz) (σ : S → (O →+* Ω)) (χ : S → (O →+* k)), IsCptGen ξ → Smooth G.hom → (∀ a, IsMonHom (act a)) → M.IsActOf act r → Mz.IsActOf act rz → IsSplit χ → (∀ s a, ValAt ξ z (σ s a) (algebraMap k K (χ s a))) → M.lat ⟨centre z, h₀⟩ = ⨆ s, M.eigLat r (σ s) ⟨centre z, h₀⟩ → ∀ s, Submodule.span K {v | ∃ e ∈ M.eigLat r (σ s) ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} = eigSp rz ((algebraMap k K).comp (χ s)) :=
  @PositivityTheory.HtPt.Ci.eig_val

end GlobalTheory.CompanionTheory.Ar.EigVal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.EigBase

section Linear

variable {O F F' V T : Type} [CommRing O] [Field F] [Field F'] [Algebra F F'] [AddCommGroup V] [Module F V]
  [AddCommGroup T] [Module F' T] [Module F T] [IsScalarTower F F' T]

theorem mem_eigSp {R E : Type} [CommRing R] [AddCommGroup E] [Module R E] (ρ : O →+* Module.End R E) (σ : O →+* R)
    (u : E) : u ∈ eigSp ρ σ ↔ ∀ a, ρ a u = σ a • u := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem linearIndependent_base {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {n : ℕ} {u : Fin n → V}
    (hu : LinearIndependent F u) : LinearIndependent F' fun i => j (u i) := by
  have hs : LinearIndepOn F id (Set.range u) := hu.linearIndepOn_id
  let b := Module.Basis.extend hs
  let g : Fin n → (hs.extend (Set.subset_univ _)) := fun i => ⟨u i, hs.subset_extend _ ⟨i, rfl⟩⟩
  have hg : Function.Injective g := fun a c e => hu.injective (congrArg Subtype.val e)
  have e : (fun i => j (u i)) = (hj.basis b) ∘ g := by
    funext i
    simp [IsBaseChange.basis_apply, b, g]
  rw [e]
  exact (hj.basis b).linearIndependent.comp g hg

theorem equiv_baseChange {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {ρ : O →+* Module.End F V}
    {ρ' : O →+* Module.End F' T} (σ : O →+* F) (hact : ∀ a e, ρ' a (j e) = j (ρ a e)) (a : O) (y : F' ⊗[F] V) :
    hj.equiv (LinearMap.baseChange F' (ρ a - σ a • LinearMap.id) y) =
      ρ' a (hj.equiv y) - algebraMap F F' (σ a) • hj.equiv y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c w =>
    rw [LinearMap.baseChange_tmul, hj.equiv_tmul, hj.equiv_tmul, map_smul, hact, smul_comm (algebraMap F F' (σ a)) c,
      ← smul_sub]
    congr 1
    simp [algebraMap_smul]
  | add y z hy hz =>
    simp only [map_add (f := _), hy, hz, smul_add]
    abel

theorem exists_sum_of_mem_eigSp {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {ρ : O →+* Module.End F V}
    {ρ' : O →+* Module.End F' T} (σ : O →+* F) (hact : ∀ a e, ρ' a (j e) = j (ρ a e)) {t : T}
    (ht : t ∈ eigSp ρ' ((algebraMap F F').comp σ)) :
    ∃ (J : Type) (B : J → F') (b : J →₀ V), (∀ k, b k ∈ eigSp ρ σ) ∧ t = b.sum fun k w => B k • j w := by
  classical
  let B := Module.Basis.ofVectorSpace F F'
  obtain ⟨b, hb⟩ := TensorProduct.eq_repr_basis_left B (hj.equiv.symm t)
  refine ⟨_, B, b, fun k => (mem_eigSp ρ σ _).2 fun a => ?_, ?_⟩
  · obtain ⟨A, hA⟩ : ∃ A : V →ₗ[F] V, A = ρ a - σ a • LinearMap.id := ⟨_, rfl⟩
    have h0 : LinearMap.baseChange F' A (hj.equiv.symm t) = 0 := by
      apply hj.equiv.injective
      rw [hA, equiv_baseChange hj σ hact, LinearEquiv.apply_symm_apply, map_zero]
      exact sub_eq_zero.2 ((mem_eigSp ρ' _ t).1 ht a)
    rw [← hb, map_finsuppSum] at h0
    simp only [LinearMap.baseChange_tmul] at h0
    have h1 : (b.mapRange A (map_zero A)).sum (fun i n => B i ⊗ₜ[F] n) = 0 := by
      rw [Finsupp.sum_mapRange_index (by simp)]
      exact h0
    have h2 := TensorProduct.sum_tmul_basis_left_eq_zero B _ h1
    have h3 := DFunLike.congr_fun h2 k
    simpa [hA, sub_eq_zero] using h3
  · rw [← hj.equiv.apply_symm_apply t, ← hb, map_finsuppSum]
    simp [hj.equiv_tmul]

theorem frame_base {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {ρ : O →+* Module.End F V}
    {ρ' : O →+* Module.End F' T} (σ : O →+* F) (hact : ∀ a e, ρ' a (j e) = j (ρ a e)) {n : ℕ} {u : Fin n → V}
    (hu : LinearIndependent F u) (hs : Submodule.span F (Set.range u) = eigSp ρ σ) :
    LinearIndependent F' (fun i => j (u i)) ∧
      Submodule.span F' (Set.range fun i => j (u i)) = eigSp ρ' ((algebraMap F F').comp σ) := by
  refine ⟨linearIndependent_base hj hu, le_antisymm (Submodule.span_le.2 ?_) fun t ht => ?_⟩
  · rintro _ ⟨i, rfl⟩
    have hi : u i ∈ eigSp ρ σ := hs ▸ Submodule.subset_span ⟨i, rfl⟩
    refine (mem_eigSp ρ' _ _).2 fun a => ?_
    rw [hact, (mem_eigSp ρ σ _).1 hi a, map_smul]
    simp [algebraMap_smul]
  · obtain ⟨J, B, b, hb, rfl⟩ := exists_sum_of_mem_eigSp hj σ hact ht
    have key : ∀ w ∈ Submodule.span F (Set.range u),
        j w ∈ Submodule.span F' (Set.range fun i => j (u i)) := fun w hw => by
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨i, rfl⟩ := hw
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add w z _ _ hw hz =>
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hw hz
      | smul c w _ hw =>
        rw [map_smul, ← algebraMap_smul F' c]
        exact Submodule.smul_mem _ _ hw
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (key _ (hs ▸ hb k))

end Linear

theorem eigFrame_base {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {F F' : Type} [Field F]
    [Field F'] [Algebra F F'] (x : Sp F ⟶ S) {P : Type} [CommRing P] (act : OAct P G) (σ : P →+* F) {n : ℕ}
    (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt (spMap (algebraMap F F') ≫ x) ⟶ G))
    (hv : ∀ i, (v' i).left = spMap (dualMap (algebraMap F F')) ≫ (v i).left) (h : IsEigFrame act x σ v) :
    IsEigFrame act (spMap (algebraMap F F') ≫ x) ((algebraMap F F').comp σ) v' := by
  obtain ⟨V, _, _, ⟨M⟩⟩ := lieModel_exists S G F x
  obtain ⟨T, _, _, _, _, M', j, hl, hj⟩ := _root_.GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange S G F F' x V M
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act S G F x V M P act.act act.hom act.one act.mul act.add
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act S G F' _ T M' P act.act act.hom act.one act.mul act.add
  have hl' : ∀ e, (M'.pt (j e)).left = spMap (dualMap (algebraMap F F')) ≫ (M.pt e).left := fun e => by
    have := hl e
    simpa using this
  have hact : ∀ a e, ρ' a (j e) = j (ρ a e) := fun a e => M'.inj (Over.OverMorphism.ext (by
    rw [hρ' a (j e), Over.comp_left, hl', hl', hρ a e, Over.comp_left, Category.assoc]))
  choose u hu using fun i => M.onto (v i) (h.1 i).1
  obtain rfl : (fun k => M.pt (u k)) = v := funext hu
  obtain ⟨-, hf⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame S F G x V M
  obtain ⟨hli, hsp⟩ := ((hf P act ρ σ hρ).2 n u).1 h
  have hvv : v' = fun k => M'.pt (j (u k)) := funext fun k => Over.OverMorphism.ext (by rw [hv k, hl'])
  rw [hvv]
  exact (((_root_.GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame S F' G _ T M').2 P act ρ' _ hρ').2 n _).2 (frame_base hj σ hact hli hsp)

theorem isEigFrame_base : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) [Smooth G.hom] (P : Type) [CommRing P] (act : OAct P G) (σ : P →+* F) (F' : Type) [Field F'] (f : F →+* F') (x' : Sp F' ⟶ S), spMap f ≫ x = x' → ∀ (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt x' ⟶ G)), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → IsEigFrame act x σ v → IsEigFrame act x' (f.comp σ) v' := by
  intro S G _ _ F _ x _ P _ act σ F' _ f x' hx n v v' hv h
  letI := f.toAlgebra
  subst hx
  exact eigFrame_base x act σ v v' hv h

end GlobalTheory.CompanionTheory.Ar.EigBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsActionComplexPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

private theorem exists_isActOf_lemma {S : Scheme} {R : Type} [CommRing R]
    {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {V : Type} [AddCommGroup V]
    [Module R V] (M : GlobalTheory.CompanionTheory.Ar.LieModel G x V) {O : Type} [CommRing O]
    (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) :
    ∃ ρ : O →+* Module.End R V, M.IsActOf act.act ρ := by
  have hpt0 : M.pt 0 = 1 := by
    have h : M.pt 0 * 1 = M.pt 0 * M.pt 0 := by
      rw [_root_.mul_one, ← M.add, add_zero]
    exact (mul_left_cancel h).symm
  have hact0 : act.act 0 = 1 := by
    have h : act.act 0 * 1 = act.act 0 * act.act 0 := by
      rw [_root_.mul_one, ← act.add, add_zero]
    exact (mul_left_cancel h).symm
  have htan : ∀ (a : O) (e : V), GlobalTheory.CompanionTheory.Ar.IsTanAt G x (M.pt e ≫ act.act a) := by
    intro a e
    haveI := act.hom a
    have h1 := M.tan e
    unfold GlobalTheory.CompanionTheory.Ar.IsTanAt at h1 ⊢
    rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, MonObj.one_comp]
  choose f hf using fun (a : O) (e : V) => M.onto _ (htan a e)
  have hadd : ∀ (a : O) (e e' : V), f a (e + e') = f a e + f a e' := by
    intro a e e'
    haveI := act.hom a
    apply M.inj
    rw [hf, M.add, M.add, hf, hf, MonObj.mul_comp]
  have hsmul : ∀ (a : O) (r : R) (e : V), f a (r • e) = r • f a e := by
    intro a r e
    apply M.inj
    apply Over.OverMorphism.ext
    rw [hf, M.smul, hf, Over.comp_left, Over.comp_left, M.smul, Category.assoc]
  refine ⟨{
      toFun := fun a => { toFun := f a, map_add' := hadd a, map_smul' := hsmul a }
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_ }, ?_⟩
  · ext e
    show f 1 e = e
    apply M.inj
    rw [hf, act.one, Category.comp_id]
  · intro a b
    ext e
    show f (a * b) e = f a (f b e)
    apply M.inj
    rw [hf, hf, hf, mul_comm a b, act.mul, Category.assoc]
  · ext e
    show f 0 e = 0
    apply M.inj
    rw [hf, hact0, MonObj.comp_one, hpt0]
  · intro a b
    ext e
    show f (a + b) e = f a e + f b e
    apply M.inj
    rw [hf, M.add, hf, hf, act.add, MonObj.comp_mul]
  · unfold GlobalTheory.CompanionTheory.Ar.LieModel.IsActOf GlobalTheory.CompanionTheory.Ar.LieModel.IsDiffOf
    intro a e
    exact hf a e

theorem exists_lieModel_tied_isEigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (y : Sp ℂ ⟶ Xo.XF c), ∃ (EC : Type) (_ : AddCommGroup EC) (_ : Module ℂ EC) (N : LieModel Y.t.G (y ≫ Y.j) EC) (ρ : 𝓞 E →+* Module.End ℂ EC), N.IsActOf Y.t.act.act ρ ∧ ∀ (ch : 𝓞 E →+* ℂ) (n : ℕ) (v : Vecs y n) (w : Fin n → EC), LieMult Xo.univ.t.act (under y) ch n → (∀ i, SameVec Y y (v i) (N.pt (w i))) → LinearIndependent ℂ w → (∀ i, w i ∈ eigSp ρ ch) → IsEigFrame Xo.univ.t.act (under y) ch v := by
  intro E _ _ _ H D l Xo c O _ β Y y
  haveI := Xo.univ.t.comm
  obtain ⟨V, i1, i2, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Xo.univ.t.G ℂ (under y)
  obtain ⟨ρ, hρ⟩ := exists_isActOf_lemma M₀ Xo.univ.t.act
  obtain ⟨M', hM'⟩ :=
    (GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback _ _ _ _ _ _ Y.m0.toSABMap.cart ℂ y V).1 M₀
  obtain ⟨N, hN⟩ := (GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback _ _ _ _ _ _ Y.m.cart ℂ y V).2 M'
  have hsame : ∀ e, SameVec Y y (M₀.pt e) (N.pt e) := by
    intro e
    unfold GlobalTheory.CompanionTheory.Ar.Flat.SameVec
    exact ⟨(M'.pt e).left, Over.w (M'.pt e), hM' e, hN e⟩
  have hK : ∀ (a : 𝓞 E) (e : V),
      (M'.pt (ρ a e)).left = (M'.pt e).left ≫ (Y.oF.t.act.act a).left := by
    intro a e
    refine Y.m0.toSABMap.cart.1.hom_ext ?_ ?_
    · rw [hM', Category.assoc, Y.m0.toSABMap.act a, ← Category.assoc, hM', ← Over.comp_left,
        ← hρ a e]
    · rw [Over.w, Category.assoc, Over.w, Over.w]
  have hNact : N.IsActOf Y.t.act.act ρ := by
    unfold GlobalTheory.CompanionTheory.Ar.LieModel.IsActOf GlobalTheory.CompanionTheory.Ar.LieModel.IsDiffOf
    intro a e
    apply Over.OverMorphism.ext
    rw [← hN, hK, Over.comp_left, ← hN, Category.assoc, Category.assoc, Y.m.act a]
  refine ⟨V, i1, i2, N, ρ, hNact, ?_⟩
  intro ch n v w hmult hsv hli hmem
  have hv : v = fun k => M₀.pt (w k) := by
    funext k
    exact SameVec.unique_left (hsv k) (hsame (w k))
  obtain ⟨v₀, hv₀⟩ := hmult
  have hfr₀ : IsEigFrame Xo.univ.t.act (under y) ch v₀ := hv₀
  have htan₀ : ∀ k, IsTanAt Xo.univ.t.G (under y) (v₀ k) := fun k => (hfr₀.1 k).1
  choose u hu using fun k => M₀.onto (v₀ k) (htan₀ k)
  have hI := (_root_.GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame _ ℂ Xo.univ.t.G (under y) V M₀).2 _ Xo.univ.t.act ρ ch hρ
  have hv₀' : v₀ = fun k => M₀.pt (u k) := funext fun k => (hu k).symm
  rw [hv₀'] at hfr₀
  obtain ⟨hu_li, hu_span⟩ := (hI.2 n u).1 hfr₀
  haveI : FiniteDimensional ℂ (eigSp ρ ch) := by
    rw [← hu_span]
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  have hspan : Submodule.span ℂ (Set.range w) = eigSp ρ ch := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hmem k
    · rw [finrank_span_eq_card hli, ← hu_span, finrank_span_eq_card hu_li]
  rw [hv]
  exact (hI.2 n w).2 ⟨hli, hspan⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

