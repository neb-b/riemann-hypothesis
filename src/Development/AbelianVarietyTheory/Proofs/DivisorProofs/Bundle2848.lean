module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0569
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqExpRiemannFormAppellHumbertFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2835
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2836
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianCechH1BasisCocycles
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
open GlobalTheory.CechDR (HO1)

namespace GlobalTheory.CechFree

theorem cech_free : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (I : Type) [Finite I] (U : I → B.left.Opens), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ⨆ i, U i = ⊤ → (∀ i, IsAffineOpen (U i)) → ∃ b : Fin g → C1 U, (∀ a, IsCoc U (b a)) ∧ ∀ c : C1 U, IsCoc U c → ∃! cc : Fin g → A, IsCob U (fun i j => c i j - ∑ a, constFn B.hom _ (cc a) * b a i j) := by
  intro A _ _ _ B _ _ g I _ U hA hg hcov hU
  classical
  have hinf : ∀ V W : B.left.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W) := by
    haveI := hA.proper
    have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
    exact fun V W hV hW => hV.inf hW
  obtain ⟨hfin, hproj, hrk⟩ := (_root_.GlobalTheory.AbCohRing.oStr_noetherian A B g hA hg).1
  haveI := hfin
  haveI := hproj
  haveI : Module.Free A (HO1 B.hom) := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank A (HO1 B.hom) = g := by
    rw [← hrk (IsLocalRing.closedPoint A), Module.rankAtStalk_eq_finrank_tensorProduct, Module.finrank_baseChange]
  let bH := Module.finBasisOfFinrankEq A (HO1 B.hom) hr
  let F := GlobalTheory.CechCmp.capF B.hom U hU hinf
  let e : HO1 B.hom ≃ₗ[A] CatCoh.H1 F :=
    LinearEquiv.ofBijective (CatCoh.CoefMap.restrict (GlobalTheory.CechDR.OAff B.hom)
      (GlobalTheory.CechCmp.capAff_mono U hU hinf).functor.op).pull1 (GlobalTheory.CechCmp.restrict_capF_bijective B.hom U hU hinf hcov)
  let bP := bH.map e
  choose f hf using fun a => CatCoh.H1.mk_surjective F (bP a)
  let b : Fin g → C1 U := fun a => GlobalTheory.CechCmp.toCech B.hom U hU hinf (f a).1
  have hb : ∀ a, IsCoc U (b a) := fun a => _root_.GlobalTheory.CechCmp.isCoc_toCech I B.left A B.hom U hU hinf _ (f a).2
  have hbP : ∀ a, CatCoh.H1.mk F ⟨GlobalTheory.CechCmp.toPos B.hom U hU hinf (b a),
      _root_.GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles I B.left A B.hom U hU hinf _ (hb a)⟩ = bP a := by
    intro a
    rw [← hf a, CatCoh.H1.mk_eq_mk]
    exact _root_.GlobalTheory.CechCmp.cechToPoset_posetToCech_sub_coboundary I B.left A B.hom U hU hinf _ (f a).2
  have hbb : ∀ a, GlobalTheory.CechCmp.toCech B.hom U hU hinf (GlobalTheory.CechCmp.toPos B.hom U hU hinf (b a)) = b a :=
    fun a => _root_.GlobalTheory.CechCmp.toCech_toPos I B.left A B.hom U hU hinf _ (hb a)

  have hlc : ∀ (cc : Fin g → A) (hm : GlobalTheory.CechCmp.toPos B.hom U hU hinf
      (fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (cc a) * b a i j) ∈ CatCoh.Z1 F),
      CatCoh.H1.mk F ⟨_, hm⟩ = ∑ a, cc a • bP a := by
    intro cc hm
    have : (⟨_, hm⟩ : CatCoh.Z1 F) = ∑ a, cc a • ⟨GlobalTheory.CechCmp.toPos B.hom U hU hinf (b a),
        _root_.GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles I B.left A B.hom U hU hinf _ (hb a)⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact GlobalTheory.CechCmp.toPos_lc B.hom U hU hinf cc b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hbP]
  have hmem : ∀ cc : Fin g → A, GlobalTheory.CechCmp.toPos B.hom U hU hinf
      (fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (cc a) * b a i j) ∈ CatCoh.Z1 F := by
    intro cc
    rw [GlobalTheory.CechCmp.toPos_lc]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (_root_.GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles I B.left A B.hom U hU hinf _ (hb a))
  refine ⟨b, hb, fun c hc => ?_⟩
  have hcm := _root_.GlobalTheory.CechCmp.cechOneCochainToPosetCochain_mem_cocycles I B.left A B.hom U hU hinf c hc
  let x := CatCoh.H1.mk F ⟨_, hcm⟩
  have hex : IsCob U (fun i j => c i j - ∑ a, constFn B.hom (U i ⊓ U j) (bP.repr x a) * b a i j) := by
    let l : C1 U := fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (bP.repr x a) * b a i j
    have hl : GlobalTheory.CechCmp.toCech B.hom U hU hinf (GlobalTheory.CechCmp.toPos B.hom U hU hinf l) = l := by
      rw [GlobalTheory.CechCmp.toPos_lc, GlobalTheory.CechCmp.toCech_lc]
      simp only [hbb, l]
    have h0 : CatCoh.H1.mk F ⟨_, hcm⟩ = CatCoh.H1.mk F ⟨_, hmem (bP.repr x)⟩ := by
      rw [hlc _ (hmem _)]
      exact (bP.sum_repr x).symm
    obtain ⟨g0, hg0⟩ := CatCoh.H1.mk_eq_mk.1 h0
    have key : (fun i j => c i j - l i j) = GlobalTheory.CechCmp.toCech B.hom U hU hinf (CatCoh.d0 F g0) := by
      rw [hg0, GlobalTheory.CechCmp.toCech_sub, _root_.GlobalTheory.CechCmp.toCech_toPos I B.left A B.hom U hU hinf c hc, hl]
      rfl
    show IsCob U (fun i j => c i j - l i j)
    rw [key]
    exact _root_.GlobalTheory.CechCmp.posetOneCochainToCechCochain_coboundary I B.left A B.hom U hU hinf g0
  refine ⟨bP.repr x, hex, fun cc hcc => ?_⟩
  have hcs : ∀ (O : B.left.Opens) (y z : A), constFn B.hom O (y - z) = constFn B.hom O y - constFn B.hom O z :=
    fun O y z => by simp only [constFn, map_sub]
  let δ : Fin g → A := fun a => bP.repr x a - cc a
  have hcob : IsCob U (fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (δ a) * b a i j) := by
    obtain ⟨β₁, h₁⟩ := hcc
    obtain ⟨β₂, h₂⟩ := hex
    refine ⟨fun i => β₁ i - β₂ i, fun i j => ?_⟩
    have e₁ := h₁ i j
    have e₂ := h₂ i j
    simp only [δ, hcs, sub_mul, Finset.sum_sub_distrib, GlobalTheory.KS.rsT_sub] at e₁ e₂ ⊢
    linear_combination e₁ - e₂
  obtain ⟨g1, hg1⟩ := _root_.GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists I B.left A B.hom U hU hinf _ hcob
  have hz : ∑ a, δ a • bP a = 0 := by
    rw [← hlc δ (hmem δ)]
    exact CatCoh.H1.mk_eq_zero.2 ⟨g1, hg1⟩
  have hδ := Fintype.linearIndependent_iff.1 bP.linearIndependent δ hz
  funext a
  exact (sub_eq_zero.1 (hδ a)).symm

end GlobalTheory.CechFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDualNumberEndoEqTranslation
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

namespace GlobalTheory.RigidEndo

theorem exists_factor_of_range_subset {X Y S : Scheme.{0}} [IsAffine S] (p : X ⟶ S) [IsIso p.appTop]
    (f : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U) (hf : Set.range f ⊆ U) :
    ∃ h : S ⟶ Y, f = p ≫ h := by
  have : IsAffine U := hU
  have hr : Set.range f ⊆ Set.range U.ι := by simpa using hf
  let g : X ⟶ U := IsOpenImmersion.lift U.ι f hr
  have hg : g ≫ U.ι = f := IsOpenImmersion.lift_fac _ _ _
  refine ⟨S.isoSpec.hom ≫ inv (Spec.map p.appTop) ≫ Spec.map g.appTop ≫ (U : Scheme).isoSpec.inv ≫ U.ι, ?_⟩
  have e1 : g = X.toSpecΓ ≫ Spec.map g.appTop ≫ (U : Scheme).isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  have e2 : X.toSpecΓ = p ≫ S.isoSpec.hom ≫ inv (Spec.map p.appTop) := by
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality_assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← hg]
  nth_rw 1 [e1]
  rw [e2]
  simp only [Category.assoc]

theorem isIso_appTop (k : Type) [Field k] (B : Over (Sp (DualNumber k))) [GrpObj B]
    (hB : IsAbelianScheme B) : IsIso B.hom.appTop := by
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  haveI : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom ‹_› ‹_›
  exact GlobalTheory.GlobalFunctions.isIso_app GlobalTheory.FlatFibreInjective.injective_baseChange
    GlobalTheory.exists_noetherian_model_of_smooth B.hom ⊤

theorem eq_translate : ∀ (k : Type) [Field k] (B : Over (Sp (DualNumber k))) [GrpObj B], IsAbelianScheme B →
    ∀ (α : B ⟶ B), (∀ (Z : Scheme.{0}) (z : Z ⟶ B.left) (y : Z ⟶ Sp k),
      z ≫ B.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → z ≫ α.left = z) →
    α = lift (toUnit B ≫ η[B] ≫ α) (𝟙 B) ≫ μ[B] := by
  intro k _ B _ hB α hα
  set β : B ⟶ B := α * (𝟙 B)⁻¹ with hβ

  have h1 : ∀ (Z : Scheme.{0}) (z : Z ⟶ B.left) (y : Z ⟶ Sp k),
      z ≫ B.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom →
      z ≫ β.left = z ≫ B.hom ≫ η[B].left := by
    intro Z z y hz
    let zo : Over.mk (z ≫ B.hom) ⟶ B := Over.homMk z
    have ha : zo ≫ α = zo := by
      ext; exact hα Z z y hz
    have hb : zo ≫ β = toUnit _ ≫ η[B] := by
      rw [hβ, comp_mul, GrpObj.comp_inv, ha, Category.comp_id, mul_inv_cancel, Hom.one_def]
    have := congrArg CommaMorphism.left hb
    simpa [zo] using this

  let q : Sp k := Classical.arbitrary _
  let e0 : B.left := η[B].left (spMap (TrivSqZeroExt.fstHom k k k).toRingHom q)
  have hsurj : Surjective (pullback.fst B.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) := by
    have := GlobalTheory.ConstThickening.surjective_spMap_fst (K := k)
    infer_instance
  have h2 : ∀ x : B.left, β.left x = e0 := by
    intro x
    obtain ⟨w, rfl⟩ := hsurj.surj x
    have := h1 _ _ _ (pullback.condition (f := B.hom) (g := spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
    rw [← Scheme.Hom.comp_apply, this, pullback.condition_assoc]
    simp only [Scheme.Hom.comp_apply, e0]
    congr 2
    exact Subsingleton.elim _ _

  obtain ⟨U, hU, heU, -⟩ := exists_isAffineOpen_mem_and_subset (X := B.left) (x := e0) (U := ⊤) trivial
  have := isIso_appTop k B hB
  obtain ⟨h, hh⟩ := exists_factor_of_range_subset B.hom β.left U hU (by
    rintro _ ⟨x, rfl⟩; rw [h2 x]; exact heU)
  have hη : η[B].left ≫ B.hom = 𝟙 _ := by simpa using Over.w η[B]
  have h3 : β.left = B.hom ≫ η[B].left ≫ β.left := by
    rw [hh, reassoc_of% hη]

  have h4 : β = toUnit B ≫ η[B] ≫ β := by
    ext; simpa using h3
  have h5 : η[B] ≫ β = η[B] ≫ α := by
    have e : η[B] = (1 : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B) := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have e' : η[B]⁻¹ = (1 : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B) := by rw [e, inv_one]
    rw [hβ, comp_mul, GrpObj.comp_inv, Category.comp_id, e', _root_.mul_one]
  calc α = β * 𝟙 B := by rw [hβ, inv_mul_cancel_right]
    _ = _ := by rw [Hom.mul_def, h4, h5]

end GlobalTheory.RigidEndo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfDeRhamCohomology
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem abelianSchemeLifts_of_abelianHodgeDeRham : AbelianHodgeDeRham → AbelianSchemeLifts :=
  abelianSchemeLifts_of_hodgeDeRham
    GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations

end GlobalTheory.LiftSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointLocallyConstantGeomPoin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TorsLocConst

theorem push_injective {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (x : S' ⟶ S) (T : Over S') :
    Function.Injective (pushHom (isGrpPullback_pullback A x) T) := by
  intro a b h
  have h' := congrArg CommaMorphism.left h
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h'
  · exact (Over.w a).trans (Over.w b).symm

theorem locally_const_torsion :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k] [IsAlgClosed k]
      (x : Sp k ⟶ S) (n : ℕ), (n : k) ≠ 0 → ∀ (Z : Over S) (t : Z ⟶ Over.mk x) (z : Z ⟶ A), z ^ n = 1 →
      ∀ w : Z.left, ∃ (V : Over S) (i : V ⟶ Z) (y : Over.mk x ⟶ A) (w' : V.left),
        IsOpenImmersion i.left ∧ i.left w' = w ∧ y ^ n = 1 ∧ i ≫ z = i ≫ t ≫ y := by
  intro S A _ hA k _ _ x n hn Z t z hz w
  have hB : IsAbelianScheme ((Over.pullback x).obj A) := Out.TLinPf.isAb_pullback x A hA
  have hg := isGrpPullback_pullback A x
  have htx : t.left ≫ x = Z.hom := Over.w t
  let Z' : Over (Sp k) := Over.mk t.left
  let z' : Z' ⟶ (Over.pullback x).obj A :=
    Over.homMk (pullback.lift z.left t.left ((Over.w z).trans htx.symm)) (pullback.lift_snd _ _ _)
  let e : Z ⟶ Over.mk (Z'.hom ≫ x) := Over.homMk (𝟙 Z.left) (by
    show 𝟙 _ ≫ t.left ≫ x = Z.hom
    rw [Category.id_comp, htx])
  let e' : Over.mk (Z'.hom ≫ x) ⟶ Z := Over.homMk (𝟙 Z.left) (by
    show 𝟙 _ ≫ Z.hom = t.left ≫ x
    rw [Category.id_comp, htx])
  have hee : e' ≫ e = 𝟙 _ := Over.OverMorphism.ext (by show 𝟙 Z.left ≫ 𝟙 Z.left = 𝟙 Z.left; exact Category.id_comp _)
  have hez : e ≫ pushHom hg Z' z' = z := Over.OverMorphism.ext (by
    show 𝟙 _ ≫ (pullback.lift _ _ _ ≫ pullback.fst _ _) = z.left
    rw [Category.id_comp, pullback.lift_fst])
  have hz' : z' ^ n = 1 := by
    apply push_injective A x Z'
    rw [map_pow, map_one]
    calc (pushHom hg Z' z') ^ n = e' ≫ e ≫ (pushHom hg Z' z') ^ n := by
          rw [← Category.assoc, hee, Category.id_comp]
      _ = e' ≫ (e ≫ pushHom hg Z' z') ^ n := by rw [MonObj.comp_pow]
      _ = 1 := by rw [hez, hz, MonObj.comp_one]
  have hK := GlobalTheory.KerConst.isPullback_const_ker k ((Over.pullback x).obj A) hB n hn
  have hcond : z' ≫ 𝟙 _ ^ n = toUnit Z' ≫ η[(Over.pullback x).obj A] := by
    rw [MonObj.comp_pow, Category.comp_id, hz', Hom.one_def]
  let g := hK.lift z' (toUnit Z') hcond
  have hgz : g ≫ Sigma.desc (fun c => c.1) = z' := hK.lift_fst _ _ _
  let P := {c : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback x).obj A // c ^ n = 1}
  let D : (∐ fun _ : P => 𝟙_ (Over (Sp k))) ⟶ GlobalTheory.PointQuot.constObj (Sp k) P :=
    Sigma.desc fun c => GlobalTheory.PointQuot.constPt (Sp k) c
  have hDE : D ≫ GlobalTheory.PointQuot.constDesc (fun c : P => c.1) = Sigma.desc (fun c : P => c.1) :=
    Sigma.hom_ext _ _ fun c => by
      rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc, GlobalTheory.PointQuot.constPt_desc]
  obtain ⟨U, hwU, c, hc⟩ := GlobalTheory.PointQuot.locally_const_desc (fun c : P => c.1) (g ≫ D) w
  have hU : GlobalTheory.PointQuot.openι Z' U ≫ z' = toUnit _ ≫ c.1 := by
    rw [← hc, ← hgz, ← hDE]
    simp only [Category.assoc]
  let y : Over.mk x ⟶ A := Over.homMk (c.1.left ≫ pullback.fst A.hom x) (by
    show (c.1.left ≫ pullback.fst A.hom x) ≫ A.hom = x
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hc1 : c.1.left ≫ pullback.snd A.hom x = 𝟙 _ := Over.w c.1
    rw [hc1, Category.id_comp])
  let e'' : Over.mk x ⟶ Over.mk ((𝟙_ (Over (Sp k))).hom ≫ x) := Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ 𝟙 _ ≫ x = x
    rw [Category.id_comp, Category.id_comp])
  have hy : y = e'' ≫ pushHom hg _ c.1 := Over.OverMorphism.ext (by
    show c.1.left ≫ pullback.fst A.hom x = 𝟙 _ ≫ (c.1.left ≫ pullback.fst A.hom x)
    rw [Category.id_comp])
  refine ⟨GlobalTheory.PointQuot.openObj Z U, GlobalTheory.PointQuot.openι Z U, y, ⟨w, hwU⟩, ?_, rfl, ?_, ?_⟩
  · show IsOpenImmersion U.ι
    infer_instance
  · rw [hy, ← MonObj.comp_pow, ← map_pow, c.2, map_one, MonObj.comp_one]
  · apply Over.OverMorphism.ext
    have h1 := congrArg CommaMorphism.left hU
    have h2 : (toUnit (GlobalTheory.PointQuot.openObj Z' U)).left = U.ι ≫ t.left :=
      (Category.comp_id _).symm.trans (Over.w (toUnit (GlobalTheory.PointQuot.openObj Z' U)))
    show U.ι ≫ z.left = U.ι ≫ t.left ≫ c.1.left ≫ pullback.fst A.hom x
    have h3 : z.left = z'.left ≫ pullback.fst A.hom x := (pullback.lift_fst _ _ _).symm
    simp only [Over.comp_left] at h1
    rw [h3, ← Category.assoc]
    erw [h1, h2]
    exact Category.assoc _ _ _

end GlobalTheory.TorsLocConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedSquareZeroAffine
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UnobTop.abelianUnobstructed : GlobalTheory.Published.AbelianUnobstructed :=
  GlobalTheory.T.abelianScheme_unobstructed_of_cohomology_structure _root_.GlobalTheory.AbCoh.oStr fun R _ A _ g hA hg =>
    ⟨(_root_.GlobalTheory.AbCoh.hasFrame_and_primF_of_isAbelianScheme R A g hA hg).1, _root_.GlobalTheory.AbCoh.uConst_of_isAbelianScheme R A hA, (_root_.GlobalTheory.AbCoh.hasFrame_and_primF_of_isAbelianScheme R A g hA hg).2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointAppellHumbertFormOfMumfordBundleLbIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.AdjFwd

theorem adjoint_hermForm_of_lbIso : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (N : LB A.left), N.IsLB → Out.RelAmple A N → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (f f' : A ⟶ A) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → LBIso (cubeLB A ![fst A A ≫ f, snd A A] M) (cubeLB A ![fst A A, snd A A ≫ f'] M) → ∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w) := by
  intro A _ _ g hA _ N _ _ M u Hm χ hM hF f f' F F' hf hf' e e' hiso
  haveI := hf
  haveI := hf'
  obtain ⟨Mr, hMr, ⟨c⟩⟩ := GlobalTheory.AHWeilAny.exists_cubical A hA M hM
  subst hMr
  have hR := GlobalTheory.AdjPolLocal.rosatiAdj_of_lbIso _ A Mr.L f f' hM hiso
  have hFl : ∀ a : u.Λ, F a ∈ u.Λ := fun a => by rw [← u.ker, e, (u.ker _).2 a.2, MonObj.one_comp]
  have hF'l : ∀ a : u.Λ, F' a ∈ u.Λ := fun a => by rw [← u.ker, e', (u.ker _).2 a.2, MonObj.one_comp]
  refine GlobalTheory.HermAdjoint.adjoint_of_im Hm F F' _ u.full fun a ha b hb => ?_
  obtain ⟨E₁, hE₁⟩ := GlobalTheory.AHWeilFactor.im_hermForm_int hM u hF ⟨_, hFl ⟨a, ha⟩⟩ ⟨b, hb⟩
  obtain ⟨E₂, hE₂⟩ := GlobalTheory.AHWeilFactor.im_hermForm_int hM u hF ⟨a, ha⟩ ⟨_, hF'l ⟨b, hb⟩⟩
  have hE : E₁ = E₂ := GlobalTheory.HermAdjoint.int_eq_of_exp fun n hn => by
    have hx := GlobalTheory.HermAdjoint.ex_period_pow u hn ⟨a, ha⟩
    have hy := GlobalTheory.HermAdjoint.ex_period_pow u hn ⟨b, hb⟩
    have hy' : (u.ex ((n : ℂ)⁻¹ • b) ≫ f') ^ n = 1 := by
      rw [← MonObj.pow_comp]
      exact (congrArg (· ≫ f') hy).trans (MonObj.one_comp _)
    let c₁ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (E₁ : ℂ) / n))
    let c₂ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (E₂ : ℂ) / n))
    have v₁ : Out.WeilIs A Mr.L n (u.ex ((n : ℂ)⁻¹ • a) ≫ f) (u.ex ((n : ℂ)⁻¹ • b)) (unitOn c₁) := by
      rw [← e, map_smul]
      refine GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm A hA Mr.L hM g u Hm χ hF n (F a) b c₁ hn
        (hFl ⟨a, ha⟩) hb ?_
      show Complex.exp _ = _
      rw [← hE₁, Complex.ofReal_intCast]
    have v₂ : Out.WeilIs A Mr.L n (u.ex ((n : ℂ)⁻¹ • a)) (u.ex ((n : ℂ)⁻¹ • b) ≫ f') (unitOn c₂) := by
      rw [← e', map_smul]
      refine GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm A hA Mr.L hM g u Hm χ hF n a (F' b) c₂ hn
        ha (hF'l ⟨b, hb⟩) ?_
      show Complex.exp _ = _
      rw [← hE₂, Complex.ofReal_intCast]
    have v₁' := (GlobalTheory.WeilCube.weilIs_rosati c GlobalTheory.globalFns_holds hA f f' hR hx hy _).1 v₁
    obtain ⟨e₀, he₀⟩ := GlobalTheory.WeilCube.exists_isRatio c n _ _ hx hy'
    have h₁ := (GlobalTheory.WeilCube.weilIs_iff c GlobalTheory.globalFns_holds hA hx hy' he₀ _).1 v₁'
    have h₂ := (GlobalTheory.WeilCube.weilIs_iff c GlobalTheory.globalFns_holds hA hx hy' he₀ _).1 v₂
    exact congrArg Units.val (GlobalTheory.HermAdjoint.unitOn_injective (h₁.trans h₂.symm))
  show (F a ⬝ᵥ Hm *ᵥ star b).im = (a ⬝ᵥ Hm *ᵥ star (F' b)).im
  rw [← hE₁, ← hE₂, hE]

end GlobalTheory.AdjFwd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistBaseTupleStatement
section
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomPairs_exist_baseTuple : (∀ D, GlobalTheory.NormSum.Inp D) → BotEx := by
  first | exact @GlobalTheory.SqTop.botEx_holds | exact GlobalTheory.SqTop.botEx_holds | (intros; apply GlobalTheory.SqTop.botEx_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistEveryTupleOfCmThetaHypothesesStatement
section
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomPairsExistEveryTuple_of_cmThetaHypotheses : (∀ D, GlobalTheory.NormSum.Inp D) → BotExT := by
  first | exact @GlobalTheory.SqTop.botExT_holds | exact GlobalTheory.SqTop.botExT_holds | (intros; apply GlobalTheory.SqTop.botExT_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentSumEqZeroOfOrbitalIntegralEqZeroStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centSum_eq_zero_of_orbitalIntegral_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
    ∀ (B : GlobalTheory.LKDef.DForm G) (y : GlobalTheory.LKCx.grp G B.β),
      orbK (MonoidHom.id _) (L.K.toSubgroup.prod K') (B.emb y) (fun h => f h.1 * f' h.2) = 0 →
      centSum (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec)
        (GlobalTheory.LKCx.toP1 G B.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' y = 0 := by
  first | (exact @GlobalTheory.LKDef.DForm.centSum_eq_zero_of_orbK) | (exact GlobalTheory.LKDef.DForm.centSum_eq_zero_of_orbK) | (intros; apply GlobalTheory.LKDef.DForm.centSum_eq_zero_of_orbK <;> assumption)
end

