module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.FixedConst

open Polynomial

theorem exists_section_of_isIntegral {Y : Scheme.{0}} [GlobalTheory.IsNormalScheme Y] [IsIntegral Y] (p : Γ(Y, ⊤)[X])
    (hp : p.Monic) (r : Y.residueField (genericPoint Y))
    (hr : p.eval₂ (Y.evaluation ⊤ (genericPoint Y) trivial).hom r = 0) :
    ∃ s : Γ(Y, ⊤), (Y.evaluation ⊤ (genericPoint Y) trivial).hom s = r ∧ p.eval s = 0 := by
  haveI : Nonempty (⊤ : Y.Opens) := ⟨Nonempty.some inferInstance, trivial⟩
  obtain ⟨t, rfl⟩ := Y.residue_surjective (genericPoint Y) r
  let ρ : Y.functionField →+* Y.residueField (genericPoint Y) := (Y.residue (genericPoint Y)).hom
  have e : (Y.evaluation ⊤ (genericPoint Y) trivial).hom = ρ.comp (algebraMap Γ(Y, ⊤) Y.functionField) := rfl
  have ht : p.eval₂ (algebraMap Γ(Y, ⊤) Y.functionField) t = 0 := by
    apply ρ.injective
    rw [hom_eval₂, ← e, map_zero]
    exact hr
  obtain ⟨s, hs⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral (R := Γ(Y, ⊤)) (A := Y.functionField)
    (x := t) ⟨p, hp, ht⟩
  refine ⟨s, by rw [e, RingHom.comp_apply, hs], ?_⟩
  apply Y.germToFunctionField_injective ⊤
  rw [← hs, eval₂_at_apply] at ht
  exact ht.trans (map_zero _).symm

theorem exists_extension_zero {Y : Scheme.{0}} (V W : Y.Opens) (hU : V ⊔ W = ⊤) (hVW : Disjoint V W) (s : Γ(Y, V)) :
    ∃ f : Γ(Y, ⊤), Y.presheaf.map (homOfLE le_top).op f = s ∧
      Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op f = 0 := by
  have hs : ∀ T : Y.Opens, T = ⊥ → Subsingleton Γ(Y, T) := fun T hT ↦
    CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty hT)
  obtain ⟨e, he, -⟩ := Y.sheaf.existsUnique_gluing' (fun b : Bool ↦ cond b V W) ⊤
    (fun b ↦ homOfLE le_top)
    (by rw [iSup_bool_eq]; exact hU.ge)
    (fun b ↦ match b with | true => s | false => (0 : Γ(Y, W))) (by
      rintro (_ | _) (_ | _)
      · rfl
      · exact (hs _ (hVW.symm.eq_bot)).elim _ _
      · exact (hs _ (hVW.eq_bot)).elim _ _
      · rfl)
  exact ⟨e, he true, he false⟩

theorem exists_section {Y : Scheme.{0}} [GlobalTheory.IsNormalScheme Y] [IsLocallyNoetherian Y] (Z : irreducibleComponents Y)
    (ξ : Y) (hξ : IsGenericPoint ξ Z.1) (p : Γ(Y, ⊤)[X]) (hp : p.Monic) (r : Y.residueField ξ)
    (hr : p.eval₂ (Y.evaluation ⊤ ξ trivial).hom r = 0) :
    ∃ f : Γ(Y, ⊤), (Y.evaluation ⊤ ξ trivial).hom f = r ∧ f * p.eval f = 0 := by
  let V : Y.Opens := IsNormalScheme.component Z
  let W : Y.Opens := ⟨Z.1ᶜ, (IsNormalScheme.isClosed_component Z).isOpen_compl⟩
  have hU : V ⊔ W = ⊤ := by
    refine le_antisymm le_top fun x _ ↦ ?_
    by_cases h : x ∈ Z.1
    exacts [Or.inl h, Or.inr h]
  have hVW : Disjoint V W := by
    rw [← TopologicalSpace.Opens.coe_disjoint]
    exact Set.disjoint_left.mpr fun x hx hx' ↦ hx' hx
  obtain rfl : V.ι (genericPoint V.toScheme) = ξ := by
    refine IsGenericPoint.eq ?_ hξ
    have h := (genericPoint_spec V.toScheme).image V.ι.continuous
    rwa [Set.image_univ, Scheme.Opens.range_ι, (IsNormalScheme.isClosed_component Z).closure_eq] at h
  let φ := (V.ι.residueFieldMap (genericPoint V.toScheme)).hom
  have e : ∀ f : Γ(Y, ⊤), φ ((Y.evaluation ⊤ (V.ι (genericPoint V.toScheme)) trivial).hom f) =
      (V.toScheme.evaluation ⊤ (genericPoint V.toScheme) trivial).hom (V.ι.appTop.hom f) := fun f =>
    Scheme.evaluation_naturality_apply V.ι (genericPoint V.toScheme) (V := ⊤) trivial f
  obtain ⟨s, hs, hps⟩ := exists_section_of_isIntegral (p.map V.ι.appTop.hom) (hp.map _) (φ r) (by
    have e' : φ.comp (Y.evaluation ⊤ (V.ι (genericPoint V.toScheme)) trivial).hom =
        (V.toScheme.evaluation ⊤ (genericPoint V.toScheme) trivial).hom.comp V.ι.appTop.hom := RingHom.ext e
    rw [eval₂_map, ← e', ← hom_eval₂, hr, map_zero])
  obtain ⟨f, h1, h0⟩ := exists_extension_zero V W hU hVW (V.topIso.hom.hom s)
  have e2 : V.ι.appTop ≫ V.topIso.hom = Y.presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
    exact (Y.presheaf.map_comp _ _).symm
  have hf : V.ι.appTop.hom f = s := by
    apply V.topIso.commRingCatIsoToRingEquiv.injective
    exact (congrArg (fun g => g.hom f) e2).trans h1
  refine ⟨f, φ.injective (by rw [e, hf, hs]), ?_⟩
  refine Y.sheaf.eq_of_locally_eq₂ (homOfLE (le_top : V ≤ ⊤)) (homOfLE (le_top : W ≤ ⊤)) hU.ge _ _ ?_ ?_
  · change Y.presheaf.map (homOfLE le_top).op (f * p.eval f) = Y.presheaf.map (homOfLE le_top).op 0
    rw [← e2]
    change V.topIso.hom.hom (V.ι.appTop.hom _) = V.topIso.hom.hom (V.ι.appTop.hom _)
    rw [map_mul, ← eval₂_at_apply, hf, ← Polynomial.eval_map, hps, mul_zero, map_zero V.ι.appTop.hom]
  · change Y.presheaf.map (homOfLE le_top).op (f * p.eval f) = Y.presheaf.map (homOfLE le_top).op 0
    rw [map_mul, h0, zero_mul, map_zero]

theorem mem_range_of_fixed {K L : Type} [Field K] [Field L] [Countable L] [Algebra K L] [Algebra K ℂ] [CharZero K]
    (φ : L →ₐ[K] ℂ) {r : L} (hr : IsIntegral K r)
    (h : ∀ τ : ℂ ≃+* ℂ, (∀ x : K, τ (algebraMap K ℂ x) = algebraMap K ℂ x) → τ (φ r) = φ r) :
    r ∈ (algebraMap K L).range := by
  let M := IntermediateField.adjoin K {r}
  haveI : FiniteDimensional K M := IntermediateField.adjoin.finiteDimensional hr
  have key : ∀ ψ : M →ₐ[K] ℂ, ψ = φ.comp M.val := by
    intro ψ
    obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq M (φ.comp M.val).toRingHom ψ.toRingHom
    refine IntermediateField.algHom_ext_of_eq_adjoin K (S := M) rfl fun x hx => ?_
    obtain rfl : x = r := hx
    refine (hτ _).symm.trans (h τ fun y => ?_)
    have := hτ (algebraMap K M y)
    simpa using this
  have hc : Module.finrank K M ≤ 1 := by
    rw [← AlgHom.card K M ℂ]
    exact Fintype.card_le_one_iff.2 fun a b => (key a).trans (key b).symm
  have h1 : Module.finrank K M = 1 := le_antisymm hc Module.finrank_pos
  exact IntermediateField.mem_bot.1 (IntermediateField.finrank_adjoin_simple_eq_one_iff.1 h1)

noncomputable def ev {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) : Γ(Y, ⊤) →+* ℂ :=
  (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom

theorem valAt'_top {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (f : Γ(Y, ⊤)) : valAt' x ⊤ f = ev x f := by
  have h : ⊤ ≤ x ⁻¹ᵁ ⊤ := le_rfl
  rw [valAt', dite_eq_left h, valAt, ev]
  exact congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (g.hom f)) (x.appLE_eq_app (U := ⊤))

theorem ev_comp {Y Y' : Scheme.{0}} (x : Sp ℂ ⟶ Y) (g : Y ⟶ Y') (f : Γ(Y', ⊤)) :
    ev (x ≫ g) f = ev x (g.appTop.hom f) := by
  rw [ev, ev, Scheme.Hom.comp_appTop]; rfl

theorem ev_spec {R : CommRingCat.{0}} (j : R ⟶ CommRingCat.of ℂ) (a : Γ(Spec R, ⊤)) :
    ev (Spec.map j) a = j.hom ((Scheme.ΓSpecIso R).hom.hom a) := by
  rw [ev, Scheme.ΓSpecIso_naturality]; rfl

theorem ev_conj {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (τ : ℂ →+* ℂ) (f : Γ(Y, ⊤)) : ev (spMap τ ≫ x) f = τ (ev x f) := by
  rw [ev_comp, ev_spec]; rfl

theorem ΓSpecIso_fromSpecResidueField {Y : Scheme.{0}} (ξ : Y) :
    (Y.fromSpecResidueField ξ).appTop ≫ (Scheme.ΓSpecIso _).hom = Y.evaluation ⊤ ξ trivial := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    Scheme.fromSpecStalk_appTop]
  simp [Scheme.evaluation]

theorem ev_residue {Y : Scheme.{0}} (ξ : Y) (φ : Y.residueField ξ →+* ℂ) (f : Γ(Y, ⊤)) :
    ev (Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecResidueField ξ) f = φ ((Y.evaluation ⊤ ξ trivial).hom f) := by
  rw [ev_comp, ev_spec, ← ΓSpecIso_fromSpecResidueField]; rfl

theorem emb_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) (σ : KA l →+* ℂ)
    (hσ : σ (baseKA l).ρ = H.rt0) (hA : l.A = 1) : σ = algebraMap (KA l) ℂ := by
  have h : σ.toRatAlgHom = (KA l).val := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := KA l) rfl fun x hx => ?_
    rcases hx with rfl | rfl
    · exact hσ
    · have e : zeta l.A = 1 := by simp [zeta, hA]
      have e' : ∀ h, (⟨zeta l.A, h⟩ : KA l) = 1 := fun _ => Subtype.ext e
      exact (congrArg _ (e' _)).trans ((map_one _).trans e.symm)
  exact RingHom.ext fun x => DFunLike.congr_fun h x

theorem fnAlgClosed_of_permutes_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ c : Coeff l, (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ConjugationPermutesPeriods F τ id) → FnAlgClosed (Xo := Xo) (c := c) := by
  intro E _ _ _ H D l Xo σ g ty F h1 hσ hty hA c hperm Z a ha
  obtain ⟨r, rfl⟩ := GlobalTheory.GeomIrr.mem_range_of_isAlgebraic_ratFun a (ha.tower_top (kap Z))
  have hr : IsIntegral c.F r := (isIntegral_algebraMap_iff ).1 ha.isIntegral
  suffices h : r ∈ (algebraMap c.F (kap Z)).range by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← hk, ← IsScalarTower.algebraMap_apply]⟩
  have hfin : FiniteDimensional ℚ c.F := c.fin
  have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
  have hk : Countable (kap Z) :=
    GlobalTheory.GenericReading.countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H D l Xo c).1 Z)
  obtain ⟨φ⟩ : Nonempty (kap Z →ₐ[c.F] ℂ) := GlobalTheory.nonempty_algHom_complex_of_countable c.F (kap Z)
  refine mem_range_of_fixed φ hr fun τ hτ => ?_
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have : GlobalTheory.IsNormalScheme (Xo.XF c) := (GlobalTheory.isNormalScheme_iff _).2
    (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (strK (Xo := Xo) (c := c))
      ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))
  let κ : c.F →+* Γ(Xo.XF c, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫ (strK (Xo := Xo) (c := c)).appTop).hom
  let j : c.F →+* ℂ := algebraMap c.F ℂ
  have hκ : ∀ (x : Sp ℂ ⟶ Xo.XF c) (i : c.F →+* ℂ), x ≫ strK = spMap i → (ev x).comp κ = i := by
    intro x i hx
    ext k
    change ev x ((strK (Xo := Xo) (c := c)).appTop.hom _) = _
    rw [← ev_comp, hx, ev_spec]
    exact congrArg i ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv_hom_id_apply k)
  let x : Sp ℂ ⟶ Xo.XF c := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ genSp Z
  have hx : x ≫ strK = spMap j := by
    rw [Category.assoc, ← Spec.map_preimage (genSp Z ≫ strK), ← Spec.map_comp]
    congr 1
    ext k
    exact φ.commutes k
  have hev : ∀ f, ev x f = φ (((Xo.XF c).evaluation ⊤ (genPt Z) trivial).hom f) := ev_residue _ φ.toRingHom
  have hm := minpoly.monic hr
  obtain ⟨f, hf, hf0⟩ := exists_section Z (genPt Z)
    ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.2)) ((minpoly c.F r).map κ) (hm.map _) r (by
    apply φ.toRingHom.injective
    rw [hom_eval₂, ← (RingHom.ext hev : ev x = φ.toRingHom.comp _), eval₂_map, hκ x j hx, map_zero]
    exact (aeval_algHom_apply φ r _).trans (by rw [minpoly.aeval, map_zero]))
  have hS : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap j →
      valAt' y ⊤ f ∈ insert 0 ((minpoly c.F r).rootSet ℂ) := by
    intro y hy
    have h := congrArg (ev y) hf0
    rw [map_mul, ← eval₂_at_apply, eval₂_map, hκ y j hy, map_zero, mul_eq_zero] at h
    rw [valAt'_top]
    exact h.imp id fun h => mem_rootSet.2 ⟨hm.ne_zero, h⟩
  obtain ⟨i, P, hP, hu⟩ := F.onto (x ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, emb_eq l σ hσ hA, ← Spec.map_comp]
    rfl)
  obtain ⟨P', hP', hu'⟩ := hperm τ (fun z hz => hτ ⟨z, hz⟩) i P hP
  have key := _root_.GlobalTheory.CompRat.valAt_eq_of_finite_values E H D l Xo σ g ty F h1 hσ hty hA c j f _ ((rootSet_finite _ _).insert 0) hS i P' P hP' hP
    (spMap (τ : ℂ →+* ℂ) ≫ x) x (by rw [Category.assoc, ← hu]; exact hu') (by
      rw [Category.assoc, hx, ← Spec.map_comp]
      congr 1
      ext k
      exact hτ k) hu.symm hx
  rwa [valAt'_top, valAt'_top, ev_conj, hev, hf] at key

end GlobalTheory.CompRat.FixedConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffFieldIdempotentsPeriodSpacesAnyLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompRat

open GlobalTheory.CompIdem ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem exists_coeff_idempotents_any_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ c₀ : Coeff l, ∃ c : Coeff l, c₀.F ≤ c.F ∧ ∀ i : Fin F.n, ∃ e : Γ(Xo.XF c, ⊤), e * e = e ∧ ∀ i' P, IsPeriod (F.Di i') ty P → ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i' P → x ≫ pullback.snd _ _ = spMap c.F.val.toRingHom → valAt' x ⊤ e = if i' = i then 1 else 0 := by
  intro E _ _ _ H D l Xo σ₀ g ty F _ _ _ hA c
  obtain rfl : σ₀ = (KA l).val.toRingHom := RingHom.ext hA
  classical
  have := CompFin.quasiCompact_alt Xo
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨S, hS, hrat⟩ := exists_rational_components (c.le.trans (coeff_le_algebraicClosure c)) Xo.s
  have := c.fin
  let b := Module.finBasis ℚ c.F
  obtain ⟨c', hc'⟩ := exists_coeff_containing E H l (S ∪ Finset.univ.image fun j => (b j : ℂ)) (by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact mem_algebraicClosure_iff.1 (hS z h)
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 h
      exact mem_algebraicClosure_iff.1 (coeff_le_algebraicClosure c (b j).2))
  refine ⟨c', fun z hz => ?_, fun i => ?_⟩
  · have e := congrArg c.F.val (b.sum_repr ⟨z, hz⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e
    have e' : z = _ := e.symm
    rw [e']
    refine sum_mem fun j _ => ?_
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _
      (hc' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  have hr := hrat c'.F c'.le (coeff_le_algebraicClosure c') fun z hz => hc' z (Finset.mem_union_left _ hz)
  obtain ⟨t, ht, hcont⟩ := exists_index F
  have := CompFin.isNoetherian_XF Xo c'
  let σ : c'.F →+* ℂ := c'.F.val.toRingHom
  let s : Xo.XF c' ⟶ Sp c'.F := pullback.snd _ _
  let pr : Xo.XF c' ⟶ Xo.X := pullback.fst _ _
  have hover : ∀ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → (p ≫ pr) ≫ Xo.s = spMap (KA l).val.toRingHom := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, GlobalTheory.CompIdem.spMap_comp]
    rfl
  have hconst : ∀ p q : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → q ≫ s = spMap σ →
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q (IsLocalRing.closedPoint ℂ)) →
      t (p ≫ pr) = t (q ≫ pr) := by
    intro p q hp hq hpq
    obtain ⟨r, hr1, hr2⟩ := hr (q (IsLocalRing.closedPoint ℂ))
    exact const_on_component σ s r hr1 (fun x => t (x ≫ pr))
      (fun m B y hB hy hh => hcont m B _ hB (fun b hb => hover _ (hy b hb)) (GlobalTheory.LocLift.isHolTo_comp_hom hh _))
      p q hp hq ((connectedComponent_eq hr2) ▸ hpq) hr2
  let U : Set (Xo.XF c') := {z | ∃ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ ∧
    p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z ∧ t (p ≫ pr) = i}
  have hUc : ∀ z w, w ∈ connectedComponent z → (w ∈ U ↔ z ∈ U) := by
    intro z w h
    simp only [U, Set.mem_setOf_eq, connectedComponent_eq h]
  have hU : IsClopen U := by
    refine ⟨⟨isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩, isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩
    · exact ⟨connectedComponent z, fun w hw h => hz ((hUc z w hw).1 h),
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
    · exact ⟨connectedComponent z, fun w hw => (hUc z w hw).2 hz,
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
  obtain ⟨e, h1, h2⟩ := exists_indicator_function U hU
  refine ⟨e, h1, fun i' P hP p hp1 hp => ?_⟩
  have hp' : t (p ≫ pr) = i' := by
    have : p ≫ pr = F.u i' P := hp1
    rw [this]
    exact ht i' P hP
  split_ifs with h
  · subst h
    exact (h2 p).1 ⟨p, hp, mem_connectedComponent, hp'⟩
  · refine (h2 p).2 ?_
    rintro ⟨q, hq, hqp, hqi⟩
    exact h (Fin.ext (hp'.symm.trans ((hconst q p hq hp hqp).symm.trans hqi)))

end GlobalTheory.CompRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDictionaryByMarkingRule
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem GlobalTheory.Member.Ctx.exists_isDict : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∃ dict, C.IsDict dict := by
  intro D H Dw l Xo c σ V r C hC
  classical
  choose k₀ γ₀ h₀ using _root_.GlobalTheory.Member.exists_mark D H Dw l Xo c σ V r C hC
  refine ⟨fun h => if hk : ∃ k, C.Mark h k 1 then ⟨hk.choose, C.fr h hk.choose⟩
    else ⟨k₀ h, C.fr (γ₀ h * h) (k₀ h)⟩, ?_, ?_⟩
  · intro h
    by_cases hk : ∃ k, C.Mark h k 1
    · refine ⟨1, ?_⟩
      beta_reduce
      rw [dite_eq_left hk]
      exact ⟨hk.choose_spec, by rw [one_mul]⟩
    · refine ⟨γ₀ h, ?_⟩
      beta_reduce
      rw [dite_eq_right hk]
      exact ⟨h₀ h, rfl⟩
  · intro k
    obtain ⟨h, hf, hm⟩ := _root_.GlobalTheory.Member.exists_finite_mark D H Dw l Xo c σ V r C hC k
    have hk : ∃ k, C.Mark h k 1 := ⟨k, hm⟩
    refine ⟨h, ?_⟩
    beta_reduce
    rw [dite_eq_left hk]
    have e : hk.choose = k :=
      (_root_.GlobalTheory.MarkUniq.mark_unique D H Dw l Xo c σ V r C hC h).1 _ _ _ _ hk.choose_spec hm
    rw [e]
    have := (_root_.GlobalTheory.Member.fr_orthonormal_unit D H Dw l Xo c σ V r C hC 1 k).2.2.2.2.1 h hf
    rw [one_mul] at this
    rw [this]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem exists_framesOK : Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∃ un, FramesOK e F M un := by
  intro hB hT E _ _ _ H Dw l Xo c σ g e F r M hσ hM hξ
  have T : ∀ k, ThetaData e F M k := fun k =>
    (_root_.GlobalTheory.FrameUnif.nonempty_thetaData E H Dw l Xo c σ g e F r M hσ hM hξ k).some
  choose un hun using fun k => _root_.GlobalTheory.FrameUnif.exists_isNormUn hT E H Dw l Xo c σ g e F r M k (T k)
  exact ⟨un,
    fun k => _root_.GlobalTheory.NormFrame.frameOK_of_isNormUn hT E H Dw l Xo c σ g e F r M k (T k) (un k) hσ hM hξ (hun k),
    fun k => _root_.GlobalTheory.NormUnBor.normUn_bor hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
    fun k => _root_.GlobalTheory.FrameUnif.normUn_gamma hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
    fun a n han f hf k => _root_.GlobalTheory.FrameUnif.NormUnHol.differentiableOn_rdU hB hT E H Dw l Xo c σ g e F r M un k (T k) (hun k) a n han f hf⟩

end GlobalTheory.FrameUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitPureTypePeriodOfSignatureSplitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPureTypePeriod_of_signatureSplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → SplitLat D → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P), IsSplit hP := by
  first | exact @GlobalTheory.CompRat.exists_isSplit_of_splitLat | exact GlobalTheory.CompRat.exists_isSplit_of_splitLat | (intros; apply GlobalTheory.CompRat.exists_isSplit_of_splitLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationWithComponentAtEveryEmbeddin
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory

theorem exists_unf_nonempty_comp_all : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → ∀ j (σ : Q.c.F →+* ℂ), ∃ U : Unf (Q.Xo j) Q.c σ D.R.r, Nonempty U.Comp := by
  intro D Q _ h j σ
  obtain ⟨X⟩ := DefiniteData.nonempty_data D.host.E D.R.r
  obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws
    GlobalTheory.firstFiveLaws.2.1.secTwist _ _ _ _ (Q.Xo j) Q.c (h j) σ
  exact ⟨{ Comp := Unit, X := fun _ => X, un := fun _ _ => y }, ⟨()⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelMoveModuliUniqueUniversalTripleStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelMove_moduli_unique_universalTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (ρ ρ' : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ν' : SABMap Xo.univ.t Xo.univ.t ρ') (gM gM' gA gA' : Dw.La →ₗ[𝓞 E] Dw.La), 1 ≤ Dw.p + Dw.q → (∀ a, gM a - gM' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA a - gA' a)) → IsIso ρ → IsIso ρ' → IsLevMove ρ ν gM gA → IsLevMove ρ' ν' gM' gA' → (∃ g : Sim Dw, (∀ a, g.f l.M a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ a, Dw.ModN l.A (g.f l.A a - gA a)) ∧ (l.A : ℤ) ∣ g.ν l.A - 1) → ρ = ρ' ∧ ν.φ = ν'.φ := by
  first | exact @GlobalTheory.levMove_unique | exact GlobalTheory.levMove_unique | (intros; apply GlobalTheory.levMove_unique <;> assumption)
end

