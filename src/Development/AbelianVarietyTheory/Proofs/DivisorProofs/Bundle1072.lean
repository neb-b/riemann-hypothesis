module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContinuousCrystallineMatrixRepOfIntertwinesDet
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WachPlace

theorem matGood_of_tw {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (f n : ℕ)
    (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r r' : ↥(GK K) →* GL (Fin n) ↥(OL LL))
    (U : ZMod f → Multiset ℤ) (a : Mx ↥(OL LL) n n) :
    MatGood P emb r U → Tw r' r a → a.det ≠ 0 → MatGood P emb r' U := by
  rintro ⟨hc, hcr, hj⟩ ht hdet
  set φ := algebraMap ↥(OL LL) ↥LL.1 with hφ
  have hinj : Function.Injective φ := fun x y h => Subtype.ext h
  set aL : Mx ↥LL.1 n n := a.map φ with haL
  have hdL : IsUnit aL.det := by
    have hd : aL.det = φ a.det := (RingHom.map_det φ a).symm
    rw [hd]
    exact isUnit_iff_ne_zero.mpr (fun h => hdet (hinj (by rw [h, map_zero])))
  have htL : ∀ g, aL * (r' g : Mx ↥(OL LL) n n).map φ = (r g : Mx ↥(OL LL) n n).map φ * aL := fun g => by
    rw [haL, ← Matrix.map_mul, ← Matrix.map_mul, ht g]
  have hconj : ∀ g, (r' g : Mx ↥(OL LL) n n).map φ = aL⁻¹ * ((r g : Mx ↥(OL LL) n n).map φ * aL) := fun g => by
    rw [← htL g, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdL, Matrix.one_mul]
  let e : (Fin n → ↥LL.1) ≃ₗ[↥LL.1] (Fin n → ↥LL.1) :=
    LinearEquiv.ofLinear (Matrix.toLin' aL) (Matrix.toLin' aL⁻¹)
      (by rw [← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _ hdL, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul _ hdL, Matrix.toLin'_one])
  have he : ∀ g v, e (repOf r' g v) = repOf r g (e v) := fun g v => by
    show aL.mulVec (repOf r' g v) = repOf r g (aL.mulVec v)
    rw [repOf_apply, repOf_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, htL g]
  refine ⟨fun i j => ?_, GlobalTheory.HTW.Rec.isCrys_of_equiv _ e he hcr, fun i τ hτ u => ?_⟩
  · have hform : (fun g => (((r' g : Mx ↥(OL LL) n n) i j : ↥(OL LL)) : ↥LL.1)) =
        fun g => ∑ k, aL⁻¹ i k * ∑ m, (((r g : Mx ↥(OL LL) n n) k m : ↥(OL LL)) : ↥LL.1) * aL m j := by
      funext g
      have := congrFun (congrFun (hconj g) i) j
      simp only [Matrix.map_apply, Matrix.mul_apply] at this
      exact this
    rw [hform]
    refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
    exact continuous_finsetSum _ fun m _ => (hc k m).mul continuous_const
  · rw [GlobalTheory.HTW.Rec.multV_eq_of_equiv _ e he]
    exact hj i τ hτ u

end GlobalTheory.WachPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenBaseChangePreimage
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LogPair

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)

theorem isEtCoord_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (U : X.Opens) (d : ℕ) (t : Fin d → Γ(X, U)), IsPullback π f' f (spMap φ) → IsAffineOpen U → IsEtCoord f U t → IsAffineOpen (π ⁻¹ᵁ U) ∧ IsEtCoord f' (π ⁻¹ᵁ U) (fun a => (π.app U).hom (t a)) := by
  intro R R' _ _ φ X X' f f' π U d t H hU ht
  refine ⟨GlobalTheory.TopForm.isAffineOpen_preimage_of_isPullback H hU, ?_⟩
  letI := φ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (R := R) (S := R') (σ := Fin d)
  have h₁ := (CommRingCat.isPushout_of_isPushout R R' (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R')).flip
  have hx : (MvPolynomial.eval₂Hom (algX f U) t).Etale := ht
  have key : ∀ (W : X'.Opens) (hle : W ≤ π ⁻¹ᵁ U),
      IsPushout (CommRingCat.ofHom (algX f U)) (CommRingCat.ofHom (algebraMap R R'))
        (π.appLE U W hle) (CommRingCat.ofHom (algX f' W)) →
      (MvPolynomial.eval₂Hom (algX f' W) fun a => (π.appLE U W hle).hom (t a)).Etale := by
    intro W hle h₂
    have e₁ : CommRingCat.ofHom (algX f U) = CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin d) R)) ≫
        CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX f U) t) := by
      ext a
      exact (MvPolynomial.eval₂Hom_C _ _ a).symm
    have e₂ : CommRingCat.ofHom (algX f' W) =
        CommRingCat.ofHom (algebraMap R' (MvPolynomial (Fin d) R')) ≫
        CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX f' W) fun a => (π.appLE U W hle).hom (t a)) := by
      ext a
      exact (MvPolynomial.eval₂Hom_C _ _ a).symm
    have hw := h₂.w
    rw [e₁, e₂] at h₂
    have h₃ := h₂.of_left (CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_)) h₁
    · have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
      exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.Etale) h₃.flip hx
    · change (π.appLE U W hle).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.map φ (MvPolynomial.C a))
      rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      exact congrArg (fun g => (CommRingCat.Hom.hom g) a) hw
    · change (π.appLE U W hle).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X a)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.map φ (MvPolynomial.X a))
      rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  have h₄ := key _ inf_le_left (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.isPushout_sections f f' π H U hU)
  have tr : ∀ (W : X'.Opens) (hle : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U →
      (MvPolynomial.eval₂Hom (algX f' W) fun a => (π.appLE U W hle).hom (t a)).Etale →
      IsEtCoord f' (π ⁻¹ᵁ U) (fun a => (π.app U).hom (t a)) := by
    rintro W hle rfl h
    rw [Scheme.Hom.app_eq_appLE]
    exact h
  exact tr _ _ (inf_top_eq _) h₄

end GlobalTheory.LogPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenPullOpenImmersion
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPair

theorem isEtCoord_openImmersion (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R) (e : Y ⟶ X)
    [IsOpenImmersion e] (U : X.Opens) (W : Y.Opens) (h : W ≤ e ⁻¹ᵁ U) (d : ℕ) (t : Fin d → Γ(X, U)) :
    IsAffineOpen U → IsAffineOpen W → IsEtCoord f U t →
      IsEtCoord (e ≫ f) W (fun a => (e.appLE U W h).hom (t a)) := by
  intro hU hW ht
  have hφ : (e.appLE U W h).hom.Etale := e.etale_appLE hU hW h
  have hc : (e.appLE U W h).hom.comp (cstOn f U) = cstOn (e ≫ f) W := by
    have e₁ : f.appLE ⊤ U le_top ≫ e.appLE U W h = (e ≫ f).appLE ⊤ W le_top :=
      Scheme.Hom.appLE_comp_appLE e f ⊤ U W le_top h
    have e₂ : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top) ≫ e.appLE U W h =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (e ≫ f).appLE ⊤ W le_top := by
      rw [Category.assoc, e₁]
    exact congrArg CommRingCat.Hom.hom e₂
  unfold IsEtCoord
  rw [← hc, ← MvPolynomial.comp_eval₂Hom]
  exact RingHom.Etale.stableUnderComposition _ _ ht hφ

end GlobalTheory.LogPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenRestrictAffineOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem isEtCoord_res : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (U W : X.Opens) (h : W ≤ U) (d : ℕ) (t : Fin d → Γ(X, U)), IsAffineOpen U → IsAffineOpen W → IsEtCoord f U t → IsEtCoord f W (fun a => resG X h (t a)) := by
  intro R _ X f U W h d t hU hW ht
  have h1 : (resG X h).Etale := GlobalTheory.TopForm.etale_resG hU hW h
  have h2 : ((resG X h).comp (MvPolynomial.eval₂Hom (cstOn f U) t)).Etale :=
    RingHom.Etale.stableUnderComposition _ _ ht h1
  have h3 : MvPolynomial.eval₂Hom (cstOn f W) (fun a => resG X h (t a)) =
      (resG X h).comp (MvPolynomial.eval₂Hom (cstOn f U) t) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have hc : cstOn f W = (resG X h).comp (cstOn f U) := by
        unfold cstOn resG
        rw [← CommRingCat.hom_comp]
        have e := Scheme.Hom.appLE_map f (U := ⊤) (V := U) (by simp) (homOfLE h).op
        exact congrArg (fun g => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g).hom) e.symm
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, hc]
    · intro i
      simp
  unfold IsEtCoord
  rw [h3]
  exact h2

end GlobalTheory.LogPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodGlRepPiTensorActionAtFactorAndCommute
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.FactorAct

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

omit [Fintype T] in
theorem atPl_tprod' (w : T) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

omit [Fintype T] in
theorem atPl_mul' (w : T) (L L' : Module.End ℂ (V w)) : atPl w (L * L') = atPl w L * atPl w L' := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
  simp [atPl_tprod']

omit [Fintype T] in
theorem atPl_comm' {w w' : T} (h : w ≠ w') (L : Module.End ℂ (V w)) (L' : Module.End ℂ (V w')) (x : ⨂[ℂ] i, V i) :
    atPl w L (atPl w' L' x) = atPl w' L' (atPl w L x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, atPl_tprod', Function.update_of_ne h, Function.update_of_ne h.symm]
    rw [Function.update_comm h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def intersection_update_fsHerm_neg_one (f : ∀ i, V i) (w : T) : V w →ₗ[ℂ] ⨂[ℂ] i, V i := (PiTensorProduct.tprod ℂ (s := V)).toLinearMap f w

omit [Fintype T] in
theorem position_apply (f : ∀ i, V i) (w : T) (v : V w) : intersection_update_fsHerm_neg_one f w v = PiTensorProduct.tprod ℂ (Function.update f w v) := rfl

omit [Fintype T] in
theorem position_self (f : ∀ i, V i) (w : T) : intersection_update_fsHerm_neg_one f w (f w) = PiTensorProduct.tprod ℂ f := by
  rw [position_apply, Function.update_eq_self]

omit [Fintype T] in
theorem atPl_tprod_update (f : ∀ i, V i) (w : T) (L : Module.End ℂ (V w)) (v : V w) :
    atPl w L (intersection_update_fsHerm_neg_one f w v) = intersection_update_fsHerm_neg_one f w (L v) := by
  simp [position_apply, atPl_tprod']

variable {p q : ℕ}

omit [Fintype T] in
theorem atPl_sub' (w : T) (A B : Module.End ℂ (V w)) : atPl w (A - B) = atPl w A - atPl w B :=
  map_sub ((PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w) A B

theorem actAt_lie (w : T) {a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)} (h : IsLieAct a) : IsLieAct (actAt w a) := by
  intro X Y
  rw [actAt_apply, actAt_apply, actAt_apply, h X Y, atPl_sub', atPl_mul', atPl_mul']

theorem actAt_wts (w : T) {a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)} (h : ∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ)
    (x : ⨂[ℂ] i, V i) : x ∈ ⨆ μ : Ix p q → ℚ, wtSub (actAt w a) μ := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine Submodule.smul_mem _ _ ?_
    rw [← position_self f w]
    refine Submodule.iSup_induction _ (motive := fun v => intersection_update_fsHerm_neg_one f w v ∈ ⨆ μ : Ix p q → ℚ, wtSub (actAt w a) μ) (h (f w))
      ?_ (by simp) ?_
    · intro μ y hy
      refine Submodule.mem_iSup_of_mem μ ?_
      simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
      intro c
      rw [actAt_apply, atPl_tprod_update, ← map_smul, ← map_sub, hy c, map_zero]
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem actAt_locU (w : T) {a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)} (h : LocU (fun c : Ix p q => c.isLeft) (units a)) :
    LocU (fun c : Ix p q => c.isLeft) (units (actAt w a)) := by
  refine _root_.GlobalTheory.HoweR.locU_of_iSup_range_eq_top (Ix p q) (V w) (fun c : Ix p q => c.isLeft) (units a) (⨂[ℂ] i, V i) (units (actAt w a))
    {g | ∃ f : ∀ i, V i, g = intersection_update_fsHerm_neg_one f w} ?_ ?_ h
  · rintro g ⟨f, rfl⟩ c d _ x
    simp only [units, actAt_apply, atPl_tprod_update]
  · refine eq_top_iff.2 ?_
    rw [← PiTensorProduct.span_tprod_eq_top]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    refine (le_iSup₂ (f := fun (g : V w →ₗ[ℂ] ⨂[ℂ] i, V i) (_ : g ∈ {g | ∃ f : ∀ i, V i, g = intersection_update_fsHerm_neg_one f w}) =>
      LinearMap.range g) (intersection_update_fsHerm_neg_one f w) ⟨f, rfl⟩ : _) ⟨f w, position_self f w⟩

end GlobalTheory.HoweR.FactorAct

namespace GlobalTheory.HoweR

theorem actAt_good_comm : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)), (∀ w, Good (a w)) →
    (∀ w, Good (actAt w (a w))) ∧ ∀ w w', w ≠ w' → ∀ Z Z' v,
      actAt w (a w) Z (actAt w' (a w') Z' v) = actAt w' (a w') Z' (actAt w (a w) Z v) := by
  intro T _ _ V _ _ R S a ha
  refine ⟨fun w => ⟨FactorAct.actAt_lie w (ha w).1, FactorAct.actAt_wts w (ha w).2.1, FactorAct.actAt_locU w (ha w).2.2⟩,
    fun w w' hw Z Z' v => ?_⟩
  exact FactorAct.atPl_comm' hw _ _ v

end GlobalTheory.HoweR

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIntegralMatrixCharpolyRoot
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwLat

theorem isIntegral_of_charpoly_intGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (u : B.A) (Q : (w.adicCompletion E)[X]), Q.Monic → aeval u (Q.map e.symm.toRingHom) = 0 → ∀ y : GLw m w, y ∈ GlobalTheory.LFun.KGL w (n := m) → y.val.charpoly = Q → IsIntegral K.O u := by
  intro E _ _ _ _ w _ K e _ hint _ B m b u Q hQ hu y hy hcp
  obtain ⟨z, rfl⟩ := hy
  have hcoef : ∀ i, Valued.v (Q.coeff i) ≤ 1 := by
    intro i
    rw [← hcp]
    have hm : ((bc (n := Fin m) (Ov E w).subtype z : GL (Fin m) (w.adicCompletion E)) :
        Matrix (Fin m) (Fin m) (w.adicCompletion E)) =
        (RingHom.mapMatrix (Ov E w).subtype) (z : Matrix (Fin m) (Fin m) (Ov E w)) := rfl
    rw [hm, RingHom.mapMatrix_apply, Matrix.charpoly_map, Polynomial.coeff_map]
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (z.val.charpoly.coeff i).2
  have hlift : Q.map e.symm.toRingHom ∈ Polynomial.lifts (algebraMap K.O K.E) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_map]
    have := (hint (e.symm (Q.coeff i))).2 (by simpa using hcoef i)
    simpa using this
  obtain ⟨P, hPm, -, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift (hQ.map _)
  refine ⟨P, hPmon, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K.E, hPm]
  exact hu

end GlobalTheory.TwLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfPreservesFullLattice
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.UnitLemma

theorem aeval_restrict_coe_of_stable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (f : Module.End R M) {N : Submodule R M} (h : ∀ x ∈ N, f x ∈ N) (q : R[X]) (x : N) :
    ((aeval (f.restrict h) q x : N) : M) = aeval f q x := by
  induction q using Polynomial.induction_on' with
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, Submodule.coe_add, ha, hb]
  | monomial n a =>
    have hpow : ∀ (k : ℕ) (y : N), ((((f.restrict h) ^ k) y : N) : M) = (f ^ k) y := by
      intro k
      induction k with
      | zero => intro y; rfl
      | succ k ih =>
        intro y
        rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, pow_succ', Module.End.mul_apply]
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul, hpow]

theorem isIntegral_of_lat_stable : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (u : B.A)
    (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → (∀ z ∈ L, u * z ∈ L) → IsIntegral K.O u := by
  intro K B u L hL hu
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hL.1
  let f : Module.End K.O B.A := LinearMap.mulLeft K.O u
  have hf : ∀ x ∈ L, f x ∈ L := hu
  obtain ⟨p, hpm, hp⟩ := LinearMap.exists_monic_and_aeval_eq_zero K.O (f.restrict hf)
  refine ⟨p, hpm, ?_⟩
  have hlmul : aeval f p = LinearMap.mulLeft K.O (aeval u p) := by
    have : f = Algebra.lmul K.O B.A u := rfl
    rw [this, Polynomial.aeval_algHom_apply]
    rfl
  have key : ∀ x ∈ L, aeval u p * x = 0 := by
    intro x hx
    have h1 := aeval_restrict_coe_of_stable f hf p ⟨x, hx⟩
    rw [hp, hlmul] at h1
    simpa using h1.symm
  have hall : ∀ a : B.A, aeval u p * a = 0 := by
    intro a
    have ha : a ∈ Submodule.span K.E (L : Set B.A) := hL.2 ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx => exact key x hx
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul c x _ hx => rw [mul_smul_comm, hx, smul_zero]
  have := hall 1
  rw [mul_one] at this
  exact this

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def kernSum (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) : ℂ :=
  (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ *
    ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n))),
      ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU (E := E) (n := n))) :
        ℂ))⁻¹ *
      ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q) * chW lam γ.1.val.charpoly

def clsSum (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (γ : UE E n) : ℂ :=
  (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ *
    ∑ᶠ q : DoubleCoset.Quotient ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt γ) : Subgroup (finU (E := E) (n := n))) : Set (finU (E := E) (n := n)))
        (globLev S K' : Set (finU (E := E) (n := n))),
      ((Nat.card ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt γ)) ⊓
          (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU (E := E) (n := n))) : ℂ))⁻¹ *
        globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q)

end GlobalTheory.BCT
end
end

