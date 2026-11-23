module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesInjectiveLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldsCommuteOfCommGroupScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationFibreProductAffineCompatible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FibreDer

theorem exists_der_fibre : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (D' : Derivation ℤ Γ(X', U'.1) Γ(X', U'.1)), (∀ r, D' ((g.appLE U.1 U'.1 hU).hom r) = (g.appLE U.1 U'.1 hU).hom (D r)) → ∀ (O : Z.affineOpens) (hO : O.1 ≤ p ⁻¹ᵁ U.1) (δ : Derivation ℤ Γ(Z, O.1) Γ(Z, O.1)), (∀ r, δ ((p.appLE U.1 O.1 hO).hom r) = (p.appLE U.1 O.1 hO).hom (D r)) → ∃ δ' : Derivation ℤ Γ(Z', φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) Γ(Z', φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1), (∀ r, δ' ((p'.appLE U'.1 _ inf_le_right).hom r) = (p'.appLE U'.1 _ inf_le_right).hom (D' r)) ∧ ∀ f, δ' ((φ.appLE O.1 _ inf_le_left).hom f) = (φ.appLE O.1 _ inf_le_left).hom (δ f) := by
  intro Z Z' X X' p p' φ g H U U' hU D D' hD' O hO δ hδ
  have P := (isIso_pushoutSection_iff H (US := U.1) (UT := U'.1) (UX := O.1)
    (UY := φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) hU hO rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H hU hO rfl U.2 U'.2 O.2)
  set α := φ.appLE O.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_left with hα
  set β := p'.appLE U'.1 (φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_right with hβ
  let a : Γ(Z, O.1) →+* DualNumber Γ(Z', φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) :=
    { toFun := fun f => TrivSqZeroExt.inl (α.hom f) + TrivSqZeroExt.inr (α.hom (δ f))
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp <;> ring
      map_mul' := fun x y => by ext <;> simp [Derivation.leibniz] <;> ring }
  let b : Γ(X', U'.1) →+* DualNumber Γ(Z', φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) :=
    { toFun := fun r => TrivSqZeroExt.inl (β.hom r) + TrivSqZeroExt.inr (β.hom (D' r))
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp <;> ring
      map_mul' := fun x y => by ext <;> simp [Derivation.leibniz] <;> ring }
  have hw0 : ∀ s, α.hom ((p.appLE U.1 O.1 hO).hom s) = β.hom ((g.appLE U.1 U'.1 hU).hom s) :=
    fun s => congr($(P.w).hom s)
  have hw : p.appLE U.1 O.1 hO ≫ CommRingCat.ofHom a = g.appLE U.1 U'.1 hU ≫ CommRingCat.ofHom b := by
    ext s
    · simp [a, b, hw0]
    · simp [a, b, hδ, hD', hw0]
  let σ := P.desc (CommRingCat.ofHom a) (CommRingCat.ofHom b) hw
  have hσl : ∀ f, σ.hom (α.hom f) = a f := fun f => congr($(P.inl_desc _ _ hw).hom f)
  have hσr : ∀ r, σ.hom (β.hom r) = b r := fun r => congr($(P.inr_desc _ _ hw).hom r)
  have hfst0 : σ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom ℤ _ _).toRingHom = 𝟙 _ := by
    refine P.hom_ext ?_ ?_
    · ext f
      simp [hσl, a]
    · ext r
      simp [hσr, b]
  have hfst : ∀ x, (σ.hom x).fst = x := fun x => congr($(hfst0).hom x)
  refine ⟨Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := fun x => (σ.hom x).snd, map_zero' := by simp, map_add' := fun x y => by rw [map_add (f := _)]; rfl })
    fun x y => ?_, fun r => ?_, fun f => ?_⟩
  · change (σ.hom (x * y)).snd = x • (σ.hom y).snd + y • (σ.hom x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [smul_eq_mul, mul_comm]
  · change (σ.hom (β.hom r)).snd = _
    rw [hσr]
    simp [b]
  · change (σ.hom (α.hom f)).snd = _
    rw [hσl]
    simp [a]

end GlobalTheory.FibreDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationLiftRaynaudPreimageAffine
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LiftDer

theorem exists_lift_of_smooth (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Smooth f]
    (U : X.Opens) (hU : IsAffineOpen U) (D : Derivation ℤ R R) :
    ∃ δ : Γ(X, U) → Γ(X, U), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧
      ∀ r, δ (constFn f U r) = constFn f U (D r) := by
  let g : R →+* Γ(X, U) :=
    (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hg : g.Smooth := by
    refine RingHom.Smooth.comp (RingHom.Smooth.of_bijective ?_) ?_
    · exact ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm).bijective
    · exact HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  letI : Algebra R Γ(X, U) := g.toAlgebra
  haveI : Algebra.FormallySmooth R Γ(X, U) := hg.formallySmooth
  obtain ⟨d, hadd, hmul, hc⟩ := GlobalTheory.KS.exists_derivation_extend_of_formallySmooth R Γ(X, U) Γ(X, U)
    (RingHom.id _) (fun r => g (D r)) (fun a b => by simp) (fun a b => by
      simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, RingHom.id_apply]
      rw [RingHom.algebraMap_toAlgebra])
  exact ⟨d, hadd, hmul, fun r => hc r⟩

theorem isAffineHom_q {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) : IsAffineHom Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have hc : IsAffineHom c.q.left := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst Q.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

theorem smooth_H {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) : Smooth Y.H.hom := by
  have h1 : Smooth Y.q.left := Y.smooth_q
  have := Q.P.smoothDim
  have h2 : Smooth Q.P.A.hom := SmoothOfRelativeDimension.smooth Q.P.g _
  rw [← Over.w Y.q]
  infer_instance

theorem exists_lift_preimage : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ ∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r) := by
  intro R _ _ Q O _ _ _ oa Y V D
  have := isAffineHom_q Y
  have := smooth_H Y
  exact exists_lift_of_smooth R Y.H.left Y.H.hom _ (V.2.preimage Y.q.left) D

end GlobalTheory.LiftDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalPointOriginSmoothCommGroupScheme
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalOrigin

theorem exists_formalPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsIntegral G.left → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : R → R) (W : G.left.Opens) (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ (Ω : Type) (_ : CommRing Ω) (_ : IsDomain Ω) (_ : IsLocalRing Ω) (φ : R →+* Ω) (x : Sp Ω ⟶ G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dΩ : Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω ∧ x ≫ G.hom = spMap φ ∧ ⊤ ≤ x ⁻¹ᵁ W ∧ (∀ r, dΩ (φ r) = φ (D r)) ∧ (∀ a r, δ a (φ r) = 0) ∧ (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) ∧ (∀ O f, O ≤ W → ⊤ ≤ x ⁻¹ᵁ O → valR x O (d O f) = dΩ (valR x O f)) ∧ ∀ O (f : Γ(G.left, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0 := by
  intro R _ _ _ _ _ _ G _ _ hsm hint n v dd hdd D W d hd hW
  have hx0W : origin G ∈ W := hW (show IsLocalRing.closedPoint R ∈ (⊤ : (Sp R).Opens) from trivial)
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨D', hD'⟩ := _root_.GlobalTheory.Heat.liftDer_isDerivation R G D W d hd hW
  choose δ hδ using fun a => _root_.GlobalTheory.StalkDerField.exists_stalk_derivation G.left ⊤ (dd a) (hdd a).1 (origin G) trivial
  obtain ⟨dA, hdA⟩ := _root_.GlobalTheory.StalkDerField.exists_stalk_derivation G.left W d hd.1 (origin G) hx0W
  have hcomm : ∀ a b s, δ a (δ b s) = δ b (δ a s) := by
    intro a b s
    obtain ⟨O, hO, f, rfl⟩ := TopCat.Presheaf.germ_exist G.left.presheaf s
    rw [hδ b O hO le_top, hδ a O hO le_top, hδ a O hO le_top, hδ b O hO le_top,
      _root_.GlobalTheory.InvFieldComm.invField_comm R G (v a) (v b) (dd a) (dd b) (hdd a) (hdd b)]
  have hconst : ∀ a r, δ a (constO G r) = 0 := by
    intro a r
    rw [← _root_.GlobalTheory.GermConst.germ_constFn_origin R G ⊤ trivial r, hδ a ⊤ trivial le_top, GlobalTheory.T.invariantVectorField_apply_constant_eq_zero R G (v a) (dd a) (hdd a), map_zero]
  have hdc : ∀ r, dA (constO G r) = constO G (D' r) := by
    intro r
    rw [← _root_.GlobalTheory.GermConst.germ_constFn_origin R G W hx0W r, hdA W hx0W le_rfl, hd.2 W le_rfl, ← hD', _root_.GlobalTheory.GermConst.germ_constFn_origin]
  obtain ⟨z, hz0, hz1, hm⟩ := _root_.GlobalTheory.CoordsOrigin.coords_at_origin R G hsm n v dd hdd δ (fun a O hO f => hδ a O hO le_top f)
  obtain ⟨T, hT⟩ := _root_.GlobalTheory.FormalOrigin.taylor_isRingHom _ R n (evO G) δ
  have hTC : ∀ r, T (constO G r) = MvPowerSeries.C r := by
    intro r
    rw [hT, _root_.GlobalTheory.FormalOrigin.taylor_const _ R n (evO G) δ _ (fun i => hconst i r), _root_.GlobalTheory.FormalOrigin.evO_constO]
  have hT0 : ∀ s, MvPowerSeries.constantCoeff (T s) = evO G s := by
    intro s
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hT]
    show (∏ i, (((0 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • evO G (iterOp _ 0 s) = _
    rw [iterOp_zero]
    simp
  haveI : IsLocalHom (evO G) := Scheme.isLocalHom_stalkClosedPointTo (R := CommRingCat.of R) (η[G]).left
  have : IsLocalHom T := ⟨fun s hs => by
    have h1 : IsUnit (evO G s) := by rw [← hT0]; exact (MvPowerSeries.isUnit_iff_constantCoeff).1 hs
    exact (isUnit_map_iff (evO G) s).1 h1⟩
  obtain ⟨dΩ, hdΩC, hdΩ⟩ := _root_.GlobalTheory.FormalOrigin.Extend.derivation_extends R _ (constO G) (evO G) (_root_.GlobalTheory.FormalOrigin.evO_constO R G) n δ z hz0 hz1 hm hconst dA D' hdc
  have hval : ∀ (O : G.left.Opens) (hO : origin G ∈ O) (f : Γ(G.left, O)),
      valR (spMap T ≫ G.left.fromSpecStalk (origin G)) O f = T ((G.left.presheaf.germ O (origin G) hO).hom f) :=
    fun O hO f => GlobalTheory.FlagBundle.valR_spMap_fromSpecStalk T hO f
  have htop : ∀ O : G.left.Opens, ⊤ ≤ (spMap T ≫ G.left.fromSpecStalk (origin G)) ⁻¹ᵁ O → origin G ∈ O :=
    fun O h => (_root_.GlobalTheory.spMap_fromSpecStalk_top_le_iff G.left (origin G) _ T inferInstance O).1 h
  refine ⟨MvPowerSeries (Fin n) R, inferInstance, NoZeroDivisors.to_isDomain _, inferInstance, MvPowerSeries.C,
    spMap T ≫ G.left.fromSpecStalk (origin G), fun a => intDer (MvPowerSeries.pderiv (R := R) a), intDer dΩ,
    _root_.GlobalTheory.PowerSeriesComplete.isAdicComplete_map_C R _ ‹_› n, ?_, (_root_.GlobalTheory.spMap_fromSpecStalk_top_le_iff G.left (origin G) _ T inferInstance W).2 hx0W, fun r => ?_, fun a r => ?_,
    fun a O f hO => ?_, fun O f hOW hO => ?_, fun O f hO hf => ?_⟩
  · rw [Category.assoc, _root_.GlobalTheory.FormalOrigin.spMap_fromSpecStalk_origin_hom R G _ T]
    congr 1
    exact RingHom.ext hTC
  · rw [← hD']; exact hdΩC r
  · exact MvPowerSeries.pderiv_C
  · have h := htop O hO
    rw [hval O h, hval O h, ← hδ a O h le_top, hT, hT, GlobalTheory.T.derivationTaylorPowerSeries_derivation_eq_pderiv _ R n (evO G) δ hcomm]
    rfl
  · have h := htop O hO
    rw [hval O h, hval O h, ← hdA O h hOW, hT, hT]
    exact (hdΩ _).symm
  · have h := htop O hO
    rw [hval O h, hT] at hf
    have h0 := _root_.GlobalTheory.TaylorInj.taylor_injective R _ (constO G) (evO G) (_root_.GlobalTheory.FormalOrigin.evO_constO R G) n δ z hz0 hz1 hm _ hf
    exact germ_injective_of_isIntegral G.left (origin G) h (h0.trans (map_zero _).symm)

end GlobalTheory.FormalOrigin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Glue

open GlobalTheory.KS

variable {X Y : Scheme.{0}}

theorem map_eq_rsT {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) :
    (Y.presheaf.map (homOfLE h).op).hom s = rsT s O := (rsT_of_le h s).symm

theorem rsT_pow' {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) (k : ℕ) : rsT (s ^ k) O = rsT s O ^ k := by
  rw [rsT_of_le h, rsT_of_le h, map_pow]

theorem le_wchart {m : Y ⟶ X} {L : LB X} (c : Fin 1 → L.ι) {O : Y.Opens} (h : O ≤ m ⁻¹ᵁ L.U (c 0)) :
    O ≤ LB.wchart L (fun _ : Fin 1 => m) c := fun y hy =>
  Set.mem_iInter.2 fun x => by rw [Subsingleton.elim x 0]; exact h hy

theorem pullbackBundleChart_le_preimage {m : Y ⟶ X} {L : LB X} (c : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => m) c ≤ m ⁻¹ᵁ L.U (c 0) := LB.wchart_le L _ c 0

theorem pbT_cocycle {L : LB X} (hL : L.IsLB) (m : Y ⟶ X) (a b c : L.ι) {O : Y.Opens}
    (h : O ≤ m ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c)) :
    pbT m (L.g a b).val O * pbT m (L.g b c).val O = pbT m (L.g a c).val O := by
  have e := congrArg (fun u => pbT m u.val O) (hL.cocycle a b c)
  simp only [Units.val_mul, GlobalTheory.KS.AdjDlog.val_res, pbT_mul] at e
  rwa [pbT_rsT m inf_le_left h, pbT_rsT m (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h,
    pbT_rsT m (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h] at e

theorem linComb_g {L : LB X} (m : Y ⟶ X) (k : ℕ) (c c' : Fin 1 → L.ι) {O : Y.Opens}
    (h : O ≤ LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c') :
    rsT ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).g c c').val O =
      pbT m (L.g (c 0) (c' 0)).val O ^ k := by
  have hle : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ≤ m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (c' 0)) :=
    fun y hy => ⟨pullbackBundleChart_le_preimage c hy.1, pullbackBundleChart_le_preimage c' hy.2⟩
  simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
  rw [rsT_pow' h]
  exact congrArg (· ^ k) ((congrArg (fun s => rsT s O) (GlobalTheory.KS.AdjDlog.val_res_pullU m hle (L.g (c 0) (c' 0)))).trans
    (rsT_pbT m hle h _))

theorem sec_rel {L : LB X} (m : Y ⟶ X) (k : ℕ) (τ : SecM m L k) (c c' : Fin 1 → L.ι) {O : Y.Opens}
    (h : O ≤ LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c') :
    rsT (τ.f c) O = pbT m (L.g (c 0) (c' 0)).val O ^ k * rsT (τ.f c') O := by
  have e := congrArg (fun s => rsT s O) (τ.compat c c')
  simp only [map_eq_rsT] at e
  have h' : O ≤ (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
      (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' := h
  rwa [rsT_rsT inf_le_left h', rsT_mul, linComb_g m k c c' h, rsT_rsT inf_le_right h'] at e

theorem exists_acts : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m : G.left ⟶ X) (L : LB X), L.IsLB → ∀ (dd : Fin n → Fld G.left), (∀ a, IsField ⊤ (dd a)) →
    ∀ (D : R → R) (h : Heat G m L dd D) (k : ℕ) (τ : SecM m L k), ∃ τ' : SecM m L k, h.Acts k τ τ' := by
  intro R _ G _ _ n X m L hL dd hdd D h k τ

  have loc : ∀ i O (hO : O ≤ h.W i) (f : Γ(G.left, h.W i)),
      rsT (op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) O =
        op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k O (rsT f O) := by
    intro i O hO f
    have hd : ∀ g, resG G.left hO (h.d i (h.W i) g) = h.d i O (resG G.left hO g) :=
      fun g => ((h.lift i).1.2.2 (h.W i) O hO le_rfl g).symm
    have hdd' : ∀ a g, resG G.left hO (dd a (h.W i) g) = dd a O (resG G.left hO g) :=
      fun a g => ((hdd a).2.2 (h.W i) O hO le_top g).symm
    have hc : ∀ r, resG G.left hO (constFn G.hom (h.W i) r) = constFn G.hom O r :=
      fun r => (rsT_of_le hO _).symm.trans (rsT_constFn G.hom hO r)
    have hp : ∀ q : Γ(G.left, h.W i), resG G.left hO (rsT q (h.W i)) = rsT q O := fun q => by
      rw [← rsT_of_le hO, rsT_rsT le_rfl hO]
    rw [rsT_of_le hO, rsT_of_le hO]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [op, map_add (f := _), map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd', hc, hp]
  obtain ⟨F, hF⟩ : ∃ F : ∀ i, Γ(G.left, h.W i), ∀ i,
      F i = op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) (rsT (τ.f fun _ => h.j i) (h.W i)) :=
    ⟨_, fun _ => rfl⟩
  have hWc : ∀ i, h.W i ≤ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) := fun i => le_wchart _ (h.le i)

  have Fc : ∀ i i', rsT (F i) (h.W i ⊓ h.W i') =
      pbT m (L.g (h.j i) (h.j i')).val (h.W i ⊓ h.W i') ^ k * rsT (F i') (h.W i ⊓ h.W i') := by
    intro i i'
    have hWc' : ∀ i, h.W i ≤ (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U (fun _ => h.j i) := hWc
    rw [hF, hF, loc i _ inf_le_left, loc i' _ inf_le_right, rsT_rsT (hWc' i) inf_le_left,
      rsT_rsT (hWc' i') inf_le_right,
      sec_rel m k τ (fun _ => h.j i) (fun _ => h.j i') (inf_le_inf (hWc i) (hWc i'))]
    exact h.glue k i i' _ le_rfl _
  have cov : ∀ V : G.left.Opens, V ≤ ⨆ i, V ⊓ h.W i := by
    intro V y hy
    have : y ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, hi⟩

  have glue : ∀ c : Fin 1 → L.ι, ∃ t : Γ(G.left, LB.wchart L (fun _ : Fin 1 => m) c), ∀ i,
      rsT t (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) =
        pbT m (L.g (c 0) (h.j i)).val (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ^ k *
          rsT (F i) (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) := by
    intro c
    refine exists_rsT_eq (fun i => LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) (fun i => inf_le_left) (cov _) _
      fun i i' => ?_
    have hN1 : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i := inf_le_left
    have hN2 : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i' := inf_le_right
    have hNW : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        h.W i ⊓ h.W i' := fun y hy => ⟨hy.1.2, hy.2.2⟩
    have hV : ∀ i, LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i ≤ m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (h.j i)) :=
      fun i y hy => ⟨pullbackBundleChart_le_preimage c hy.1, h.le i hy.2⟩
    have h3 : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (h.j i) ⊓ L.U (h.j i')) :=
      fun y hy => ⟨⟨pullbackBundleChart_le_preimage c hy.1.1, h.le i hy.1.2⟩, h.le i' hy.2.2⟩
    rw [rsT_mul, rsT_mul, rsT_pow' hN1, rsT_pow' hN2, rsT_pbT m (hV i) hN1, rsT_pbT m (hV i') hN2,
      rsT_rsT inf_le_right hN1, rsT_rsT inf_le_right hN2, ← rsT_rsT inf_le_left hNW (F i), Fc, rsT_mul,
      rsT_pow' hNW, rsT_pbT m (show h.W i ⊓ h.W i' ≤ m ⁻¹ᵁ (L.U (h.j i) ⊓ L.U (h.j i')) from fun y hy => ⟨h.le i hy.1, h.le i' hy.2⟩) hNW, rsT_rsT inf_le_right hNW,
      ← _root_.mul_assoc, ← _root_.mul_pow, pbT_cocycle hL m _ _ _ h3]
  choose t ht using glue

  refine ⟨⟨t, fun c c' => ?_⟩, fun i => ?_⟩
  · have goal : rsT (t c) ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
          (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c') =
        ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).g c c').val *
          rsT (t c') ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
            (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c') := ?_
    · exact (rsT_of_le inf_le_left (t c)).symm.trans (goal.trans (congrArg _ (rsT_of_le inf_le_right (t c'))))
    refine eq_of_rsT_eq (fun i => LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i)
      (fun i => inf_le_left) (cov _) _ _ fun i => ?_
    have a1 : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i := fun y hy => ⟨hy.1.1, hy.2⟩
    have a2 : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i := fun y hy => ⟨hy.1.2, hy.2⟩
    have hV : ∀ c : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i ≤ m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (h.j i)) :=
      fun c y hy => ⟨pullbackBundleChart_le_preimage c hy.1, h.le i hy.2⟩
    have h3 : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (c' 0) ⊓ L.U (h.j i)) :=
      fun y hy => ⟨⟨pullbackBundleChart_le_preimage c hy.1.1, pullbackBundleChart_le_preimage c' hy.1.2⟩, h.le i hy.2⟩
    have e' : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
          (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' := inf_le_left
    have eL : (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
        (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' ≤ LB.wchart L (fun _ : Fin 1 => m) c := inf_le_left
    have eR : (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
        (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' ≤ LB.wchart L (fun _ : Fin 1 => m) c' := inf_le_right
    erw [rsT_rsT eL e', rsT_mul, rsT_rsT eR e', linComb_g m k c c' e',
      ← rsT_rsT inf_le_left a1 (t c), ← rsT_rsT inf_le_left a2 (t c'), ht, ht, rsT_mul, rsT_mul,
      rsT_pow' a1, rsT_pow' a2, rsT_pbT m (hV c) a1, rsT_pbT m (hV c') a2, rsT_rsT inf_le_right a1,
      rsT_rsT inf_le_right a2, ← _root_.mul_assoc, ← _root_.mul_pow, pbT_cocycle hL m _ _ _ h3]
  ·
    change rsT (t fun _ => h.j i) (h.W i) = _
    have a : h.W i ≤ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) ⊓ h.W i := le_inf (hWc i) le_rfl
    rw [← rsT_rsT inf_le_left a, ht, rsT_mul, rsT_pow' a,
      rsT_pbT m (show LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) ⊓ h.W i ≤ m ⁻¹ᵁ (L.U (h.j i) ⊓ L.U (h.j i))
        from fun y hy => ⟨pullbackBundleChart_le_preimage _ hy.1, h.le i hy.2⟩) a, rsT_rsT inf_le_right a, rsT_self,
      GlobalTheory.KS.AdjDlog.pbT_g_self hL m (h.j i) (h.le i), one_pow, _root_.one_mul, hF]

end GlobalTheory.Heat.Glue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTwistedSumSignEveryMember
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

theorem GlobalTheory.Poinc.Sep.twistAtEach_exists : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg ∧ (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv
  obtain ⟨sg, hsg⟩ := GlobalTheory.Poinc.Sep.torusChar_eq_weil g n F W Z i X₁ z₁ act
  refine ⟨sg, ?_, hsg⟩
  intro V _ _ _ ev X _ m t δ 𝔪 C lab hlab T hT c τ hτ
  obtain ⟨χ, hχN, hχo⟩ := GlobalTheory.T.exists_torusTorsionPoint_of_label_orthogonal g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 τ hτ
  obtain ⟨e, he⟩ := GlobalTheory.T.twisted_sum_terms_eq_theta_constant_translate g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ C lab hlab T hT c τ hτ χ hχN hχo
  exact ⟨e, GlobalTheory.Poinc.TwistSum₂.twistSum_of_sumF g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ C lab T sg c τ χ e
    (GlobalTheory.Poinc.Sep.UMem.yK_th_ne_zero g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv)
    (GlobalTheory.Poinc.Sep.UMem.exists_yy g n F W Z i X₁ z₁ act V ev X m t δ 𝔪) (hsg V ev X m t δ 𝔪 τ χ hχN hχo) he⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisation
section
namespace GlobalTheory

theorem formalAlgebraisation : GlobalTheory.Published.FormalAlgebraisation :=
  ⟨_root_.GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms, _root_.GlobalTheory.FormalAlg.formalAlgebraisation_schemes⟩

end GlobalTheory
end

