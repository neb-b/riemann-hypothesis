module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDegenerationDataAlgebraicPointModel
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DatAtPoint

theorem exists_ext_containing (T : CDVR) (hT : T.FinRes) {C : Type} [Field C] [CharZero C] (e : T.Fr →+* C)
    {F : Type} [Field F] [CharZero F] [FiniteDimensional ℚ F] (f : F →+* C) :
    ∃ (T₁ : CDVR) (φ : T.V →+* T₁.V) (e₁ : T₁.Fr →+* C) (f₁ : F →+* T₁.Fr), Function.Injective φ ∧ φ.Finite ∧ T₁.FinRes ∧
      e₁.comp f₁ = f ∧ ∀ a, e₁ (algebraMap T₁.V T₁.Fr (φ a)) = e (algebraMap T.V T.Fr a) := by
  have : Finite (ResidueField T.V) := hT
  have : CharZero T.Fr := IsFractionRing.charZero_of_isFractionRing T.V
  letI : Algebra T.Fr C := e.toAlgebra
  let b := Module.finBasis ℚ F
  let L : IntermediateField T.Fr C := IntermediateField.adjoin T.Fr (Set.range fun i => f (b i))
  have hfin : FiniteDimensional T.Fr L := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨i, rfl⟩
    have h₁ : IsIntegral ℚ (f (b i)) := (Algebra.IsIntegral.isIntegral (R := ℚ) (b i)).map f.toRatAlgHom
    exact h₁.tower_top
  have hmem : ∀ x, f x ∈ L := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem L _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  letI : Algebra T.V L := ((algebraMap T.Fr L).comp (algebraMap T.V T.Fr)).toAlgebra
  have : IsScalarTower T.V T.Fr L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hB : Module.Finite T.V (integralClosure T.V L) := IsIntegralClosure.finite T.V T.Fr L _
  have hBd : IsDiscreteValuationRing (integralClosure T.V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr T.V T.Fr L
  have hfr : IsFractionRing (integralClosure T.V L) L := integralClosure.isFractionRing_of_finite_extension T.Fr L
  have hinj : Function.Injective (algebraMap T.V (integralClosure T.V L)) := fun a a' h =>
    IsFractionRing.injective T.V T.Fr ((algebraMap T.Fr L).injective (congrArg Subtype.val h))
  have : FaithfulSMul T.V (integralClosure T.V L) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hz : CharZero (integralClosure T.V L) := charZero_of_injective_ringHom hinj
  have hc := GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local T.V (integralClosure T.V L)
  have hr : Finite (ResidueField (integralClosure T.V L)) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact Module.finite_of_finite (ResidueField T.V)
  let q : FractionRing (integralClosure T.V L) ≃ₐ[integralClosure T.V L] L := FractionRing.algEquiv _ L
  refine ⟨{ V := integralClosure T.V L }, algebraMap _ _, (algebraMap L C).comp q.toRingEquiv.toRingHom,
    q.symm.toRingEquiv.toRingHom.comp (f.codRestrict L hmem), hinj, RingHom.finite_algebraMap.2 hB, hr,
    RingHom.ext fun x => ?_, fun a => ?_⟩
  · exact congrArg Subtype.val (q.apply_symm_apply ⟨f x, hmem x⟩)
  · exact congrArg Subtype.val (q.commutes _)

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem eq_of_field_ext {K C O : Type} [Field K] [Field C] [CommRing O] (e : K →+* C) (u v : Sp K ⟶ Sp O)
    (h : spMap e ≫ u = spMap e ≫ v) : u = v := by
  obtain ⟨u, rfl⟩ := Spec.map_surjective u
  obtain ⟨v, rfl⟩ := Spec.map_surjective v
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext a
  exact e.injective (congrArg (fun w => w.hom a) h')

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_lift_to_open (Y : Model Xo c β) {K C : Type} [Field K] [Field C] (e : K →+* C) (f : c.F →+* K)
    (x : Sp K ⟶ Y.X) (y : Sp C ⟶ Xo.XF c) (hy : y ≫ pullback.snd _ _ = spMap (e.comp f))
    (h : spMap e ≫ x = y ≫ Y.j) : ∃ z : Sp K ⟶ Xo.XF c, z ≫ Y.j = x := by
  have hj : Y.j = Y.jQ ≫ pullback.fst _ _ := rfl
  have hc : x ≫ Y.s = spMap f ≫ spMap β := by
    refine eq_of_field_ext e _ _ ?_
    rw [← Category.assoc, h, hj, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
      ← Category.assoc, hy, ← Category.assoc, spMap_spMap f]
  let w : Sp K ⟶ pullback Y.s (spMap β) := pullback.lift x (spMap f) hc
  have hw : spMap e ≫ w = y ≫ Y.jQ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, h, hj, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, Y.jQ_over, hy, spMap_spMap]
  have := Y.jQ_open
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    let q' : Sp C := (default : PrimeSpectrum C)
    have hq : spMap e q' = q := Subsingleton.elim (α := PrimeSpectrum K) _ _
    refine ⟨y q', ?_⟩
    rw [← hq, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hw]
  refine ⟨IsOpenImmersion.lift Y.jQ w hr, ?_⟩
  rw [hj, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

theorem exists_datAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ) (C : SCF p) (P : PointsOfFlagModel.PtC Y C), p.Prime → ∀ (T : CDVR) (g : T.V →+* intO ↥C.S) (ιT : Sp T.V ⟶ Y.X), T.FinRes → Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → spMap g ≫ ιT = P.yt → ∃ A : DatAt Y P, (∃ _ : IsDiscreteValuationRing A.R, Finite (ResidueField A.R)) ∧ Function.Injective A.f ∧ ∃ φ : T.V →+* A.R, A.f.comp φ = g ∧ A.ι = spMap φ ≫ ιT ∧ φ.Finite := by
  intro E _ _ _ H Dw l Xo c O _ β Y p C P _ T g ιT hT hg hloc hfac
  have hinj : Function.Injective ((intO ↥C.S).subtype.comp g) := Subtype.val_injective.comp hg
  let eF : T.Fr →+* ↥C.S := IsFractionRing.lift hinj
  have heF : ∀ a, eF (algebraMap T.V T.Fr a) = ((g a : intO ↥C.S) : ↥C.S) := fun a =>
    IsFractionRing.lift_algebraMap hinj a
  clear_value eF
  have := c.fin
  obtain ⟨T₁, φ₁, e₁, f₁, hi₁, hf₁, hT₁, hef, he₁⟩ := exists_ext_containing T hT eF P.fK
  have hring : (e₁.comp (algebraMap T₁.V T₁.Fr)).comp φ₁ = (intO ↥C.S).subtype.comp g :=
    RingHom.ext fun a => (he₁ a).trans (heF a)
  obtain ⟨z, hz⟩ := exists_lift_to_open Y e₁ f₁ (spMap (algebraMap T₁.V T₁.Fr) ≫ spMap φ₁ ≫ ιT) P.y
    (by rw [hef, P.y_over]) (by
      rw [← P.ext, ← hfac, ← Category.assoc, spMap_spMap, ← Category.assoc, spMap_spMap, hring, ← Category.assoc,
        spMap_spMap])
  obtain ⟨t, m⟩ : ∃ t : SAB H (Sp T₁.V), Nonempty (SABMap t Y.t (spMap φ₁ ≫ ιT)) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap φ₁ ≫ ιT) Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m⟩ := m
  obtain ⟨tK, mK⟩ : ∃ tK : SAB H (Sp T₁.Fr), Nonempty (SABMap tK t (spMap (algebraMap T₁.V T₁.Fr))) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ :=
      sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap (algebraMap T₁.V T₁.Fr)) t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨mK⟩ := mK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t t _ _ _ m mK
  have cancel : ∀ (q : Sp T₁.Fr ⟶ Y.X) (_ : q = z ≫ Y.j) (_ : SABMap tK Y.t q), Nonempty (SABMap tK Y.oF.t z) := by
    intro q hq n; subst hq
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m'⟩ := cancel _ hz.symm n
  obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t _ (pullback.fst _ _) z Y.m0.toSABMap m'
  obtain ⟨T', φ', t', m₂, hi', hf', hT', -, U, hU, hTor⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T₁ t tK mK _ mx hT₁
  have hφ : (φ'.comp φ₁).Finite := hf'.comp hf₁
  obtain ⟨-, -, -, -, -, hext⟩ :=
    GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' (φ'.comp φ₁) (hi'.comp hi₁) hφ
  obtain ⟨f, hfi, hfg, hfl⟩ := hext p C eF (fun a => by rw [heF]; exact (g a).2) (fun a ha => by rw [heF]; exact hloc a ha)
  have hcomp : f.comp (φ'.comp φ₁) = g := RingHom.ext fun a => Subtype.ext ((hfg a).trans (heF a))
  obtain ⟨n₂, -⟩ := sabComp pullCubComp E H _ _ _ Y.t t t' _ _ m m₂
  have hι : spMap φ' ≫ spMap φ₁ ≫ ιT = spMap (φ'.comp φ₁) ≫ ιT := by rw [← Category.assoc, spMap_spMap]
  have hab : (spMap φ' ≫ spMap φ₁ ≫ ιT) ⁻¹' abLocus Y.t.G = abLocus t'.G :=
    Set.ext fun q => abLocus_pullback abLocusOne Y.t.semi n₂.cart.1 q
  refine ⟨
    { R := T'.V
      noeth := inferInstance
      normal := inferInstance
      complete := inferInstance
      «ι» := spMap φ' ≫ spMap φ₁ ≫ ιT
      f := f
      f_loc := hfl
      fac := by rw [hι, ← Category.assoc, spMap_spMap, hcomp, hfac]
      t := t'
      m := n₂
      U := U
      unitOn := fun χ => by rw [hab]; exact hU χ
      tors := hTor }, ⟨T'.dvr, hT'⟩, hfi, φ'.comp φ₁, hcomp, hι, hφ⟩

end GlobalTheory.DatAtPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PermutesPeriodSpacesIdOfFixesCmCurveTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem isHolTo_subst {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {B : Set W} {y : W → (Sp ℂ ⟶ X)} (hy : IsHolTo B y) {φ : V → W}
    (hφ : Differentiable ℂ φ) (hB : ∀ z, φ z ∈ B) : IsHolTo Set.univ (fun z => y (φ z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := hy U f
  have e : {b ∈ (Set.univ : Set V) | ⊤ ≤ y (φ b) ⁻¹ᵁ U} = φ ⁻¹' {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} :=
    Set.ext fun z => ⟨fun h => ⟨hB z, h.2⟩, fun h => ⟨trivial, h.2⟩⟩
  refine ⟨?_, ?_⟩
  · beta_reduce
    rw [e]
    exact h1.preimage hφ.continuous
  · beta_reduce
    rw [e]
    exact DifferentiableOn.comp (g := fun b => valAt' (y b) U f) (f := φ) h2 hφ.differentiableOn fun z hz => hz

theorem isHolTo_ex_at_period {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) :
    IsHolTo Set.univ (fun z => (F.ex i P z).left) :=
  isHolTo_subst (φ := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z))
    (F.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
    (by fun_prop) fun _ => ⟨trivial, trivial⟩

theorem conj_point_eq_of_isSplit {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (hD : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0) (hty : IsTypeFn H D.p D.q ty) (hA : l.A = 1) (τ : ℂ ≃+* ℂ)
    (hτ : τ H.rt0 = H.rt0) (hfix : FixesCurve H τ l.M) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (hs : IsSplit hP) : spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i P := by
  obtain ⟨C, io, hC⟩ := hfix
  have hτσ : (τ : ℂ →+* ℂ).comp σ = σ := GlobalTheory.ConjPermutes.ringHom_ext hA (by
    show τ (σ _) = σ _
    rw [hσ, hτ])
  obtain ⟨i', P', hP', hu⟩ := F.onto (spMap (τ : ℂ →+* ℂ) ≫ F.u i P)
    (by rw [Category.assoc, F.over_σ i P hP, GlobalTheory.ConjPermutes.spMap_comp, hτσ])
  obtain ⟨Φ, hE, hp, hm, hlev⟩ := marking_conj E H D l Xo σ g ty F hD hσ hty hA τ hτ C io hC.1 i P hP i' P' hP' hs
    hu.symm (1, 0) hC
  obtain ⟨L, hL⟩ := exists_complex_linear_of_pure_types E H _ _ g ty P P' hP hP' Φ hs (fun a ha => (hp a).2 ha)
    (fun a ha => (hm a).2 ha)
  have hw : wE H (1, 0) = 1 := by simp [wE]
  have hA' : ∀ a, ∃ x, Φ (F.t i a) = F.t i' a + l.A • x := fun a =>
    ⟨Φ (F.t i a) - F.t i' a, by rw [hA, one_smul, add_sub_cancel]⟩
  refine hu.symm.trans ((GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
      E H D l Xo σ g ty hD hσ hty (F.Di i) (F.Di i')
      (F.t i) (F.t i') P P' (F.u i P) (F.u i' P') (F.ex i P) (F.ex i' P')
      ⟨F.over_σ i P hP, hP, ⟨F.ex_add i P hP, F.ex_onto i P hP, isHolTo_ex_at_period F i P hP,
        (F.ex_diff i P hP).1, (F.ex_diff i P hP).2⟩, F.ex_ker i P hP, F.ex_lin i P hP, F.ex_weil i P hP,
        F.ex_eta i P hP, F.ex_etaA i P hP⟩
      ⟨F.over_σ i' P' hP', hP', ⟨F.ex_add i' P' hP', F.ex_onto i' P' hP', isHolTo_ex_at_period F i' P' hP',
        (F.ex_diff i' P' hP').1, (F.ex_diff i' P' hP').2⟩, F.ex_ker i' P' hP', F.ex_lin i' P' hP',
        F.ex_weil i' P' hP', F.ex_eta i' P' hP', F.ex_etaA i' P' hP'⟩).2 ⟨Φ, L, hE, fun v hv => ?_, hA', hL⟩).symm
  have hmem : F.t i v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0) := by
    rw [show lat hP H.rt0 ⊔ lat hP (-H.rt0) = ⊤ from hs]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨e, he⟩ := hlev v hv a ha b hb hab.symm
  rw [hw, map_one, one_smul, one_smul, hab] at he
  exact ⟨-e, by rw [he, smul_neg, add_neg_cancel_right]⟩

theorem permutes_id_of_fixesCurve : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → FixesCurve H τ l.M → ConjugationPermutesPeriods F τ id := by
  intro E _ _ _ H D l Xo σ g ty F hpq hσ hty hA hsig τ hτ hC
  obtain ⟨π, hπ⟩ := GlobalTheory.ConjPermutes.exists_perm E H D l Xo σ g ty F hpq hσ hty hA τ hτ
  have hid : ∀ i, π i = i := by
    intro i
    obtain ⟨P, hP, hs⟩ := exists_isSplit_period E H D l Xo σ g ty F hpq hσ hty hA hsig i
    have h1 := conj_point_eq_of_isSplit F hpq hσ hty hA τ hτ hC i P hP hs
    obtain ⟨P', hP', h2⟩ := hπ i P hP
    exact (F.disj i (π i) P P' hP hP' (h1.symm.trans h2)).symm
  have : (π : Fin F.n → Fin F.n) = id := funext hid
  rwa [this] at hπ

end GlobalTheory.CompRat
end

