module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
public import ReciprocityTheory.GroupCohomology.ImportsAlt
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocD

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmHom
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

noncomputable section

namespace UpperTheory.V.Loc

section Generic

variable {G : Type} [Group G] {Q V V' W : Type} [Field Q] [AddCommGroup V] [Module Q V] [AddCommGroup V']
  [Module Q V'] [AddCommGroup W] [Module Q W] [FiniteDimensional Q V]

private theorem exists_inj_dual_tprod (ρ : Representation Q G V) (ρ' : Representation Q G V')
    (π : Representation Q G W) (b : W →ₗ[Q] V →ₗ[Q] V') (hb : ∀ g w x, b (π g w) (ρ g x) = ρ' g (b w x))
    (hi : Function.Injective b) :
    ∃ f : W →ₗ[Q] Module.Dual Q V ⊗[Q] V', (∀ g w, f (π g w) = (ρ.dual.tprod ρ') g (f w)) ∧
      Function.Injective f := by
  let e := dualTensorHomEquiv Q V V'
  refine ⟨e.symm.toLinearMap ∘ₗ b, fun g w => ?_, e.symm.injective.comp hi⟩
  have key : ∀ (t : Module.Dual Q V ⊗[Q] V') (x : V),
      e ((ρ.dual.tprod ρ') g t) (ρ g x) = ρ' g (e t x) := by
    intro t x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [map_add (f := _), LinearMap.add_apply, hs, ht]
    | tmul f y => simp [e, Module.Dual.transpose_apply]
  apply e.injective
  ext x
  obtain ⟨x, rfl⟩ : ∃ y, ρ g y = x := ⟨ρ g⁻¹ x, by simp⟩
  rw [key]
  simp [hb]

end Generic

section Transport

variable {l : ℕ} [Fact l.Prime] {G H A V : Type} [Group G] [Group H] [CommRing A] [Algebra ℚ_[l] A]
  [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]

private theorem admissible_transport_equiv (ψ : H →* GQ l) (e : G ≃* H) (ρ : Representation A G V) :
    (IsCr (ψ.comp e.toMonoidHom) ρ ↔ IsCr ψ (ρ.comp e.symm.toMonoidHom : Representation A H V)) ∧
    (IsDr (ψ.comp e.toMonoidHom) ρ ↔ IsDr ψ (ρ.comp e.symm.toMonoidHom : Representation A H V)) := by
  have hr : (ψ.comp e.toMonoidHom).range = ψ.range := by
    ext x
    exact ⟨fun ⟨g, hg⟩ => ⟨e g, hg⟩, fun ⟨h, hh⟩ => ⟨e.symm h, by simpa using hh⟩⟩
  have h1 : Dcr (ψ.comp e.toMonoidHom) (resCoef ℚ_[l] ρ) =
      Dcr ψ (resCoef ℚ_[l] (ρ.comp e.symm.toMonoidHom : Representation A H V)) := by
    unfold Dcr
    refine e.toEquiv.iInf_congr fun g => ?_
    simp [actC, resCoef]
  have h2 : Ddr (ψ.comp e.toMonoidHom) (resCoef ℚ_[l] ρ) =
      Ddr ψ (resCoef ℚ_[l] (ρ.comp e.symm.toMonoidHom : Representation A H V)) := by
    unfold Ddr
    refine e.toEquiv.iInf_congr fun g => ?_
    simp [actD, resCoef]
  unfold IsCr IsDr
  rw [hr, h1, h2]
  exact ⟨Iff.rfl, Iff.rfl⟩

end Transport

section Field

variable {l : ℕ} [Fact l.Prime] (K : FinExt l) {V V' W : Type} [AddCommGroup V] [Module ℚ_[l] V]
  [AddCommGroup V'] [Module ℚ_[l] V'] [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] V]
  [FiniteDimensional ℚ_[l] V'] [FiniteDimensional ℚ_[l] W]
  (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V')
  (π : Representation ℚ_[l] ↥(GK K) W) (f : W →ₗ[ℚ_[l]] Module.Dual ℚ_[l] V ⊗[ℚ_[l]] V')
  (hf : ∀ g w, f (π g w) = (ρ.dual.tprod ρ') g (f w)) (hi : Function.Injective f)
include hf hi

private theorem crys_hom (h : IsCrys ((PP l).PD K) ρ) (h' : IsCrys ((PP l).PD K) ρ') :
    IsCrys ((PP l).PD K) π := by
  obtain ⟨T⟩ := tiedP l
  obtain ⟨C, hfit⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l _ _ T
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  have h1 := GlobalTheory.RegularRing.fracInv hfit (_root_.GlobalTheory.MemLoc.TensorInj.tensorInj l C) K
  have h2 := GlobalTheory.RegularRing.lineUnit hfit (_root_.GlobalTheory.MemLoc.regular_of_tensorInj l C (_root_.GlobalTheory.MemLoc.TensorInj.tensorInj l C)) K
  exact GlobalTheory.RegularRing.subCrys _ ℚ_[l] h1 _ _ _ π f hf hi
    (GlobalTheory.RegularRing.tensorCrys _ ℚ_[l] h1 h2 _ _ _ _
      (GlobalTheory.RegularRing.dualCrys _ ℚ_[l] h1 h2 _ ρ h) h')

private theorem dR_hom (h : IsDR ((PP l).PD K) ρ) (h' : IsDR ((PP l).PD K) ρ') :
    IsDR ((PP l).PD K) π := by
  obtain ⟨T⟩ := tiedP l
  have := K.2
  have hF := GlobalTheory.DRFil.isField_dR T
  have s : GlobalTheory.DRFil.Spans ((PP l).PD K) ρ := GlobalTheory.Per.DeRhamSpan.span_of_isField _ ρ hF h
  have s' : GlobalTheory.DRFil.Spans ((PP l).PD K) ρ' := GlobalTheory.Per.DeRhamSpan.span_of_isField _ ρ' hF h'
  have sd : GlobalTheory.DRFil.Spans ((PP l).PD K) ρ.dual :=
    GlobalTheory.DRFil.spans_dual_of_spans _ ρ ρ.dual (Module.Dual.eval ℚ_[l] V) hF
      (fun g x y => by simp [Module.Dual.transpose_apply]) Function.bijective_id s
  have st : GlobalTheory.DRFil.Spans ((PP l).PD K) (ρ.dual.tprod ρ') :=
    GlobalTheory.DRFil.Spans.tensor _ (LinearEquiv.refl _ _) (fun g x y => by simp) sd s'
  have sw := GlobalTheory.DRSubQuot.spans_of_injective _ π _ f hf hF hi st
  obtain ⟨h1, h2⟩ := GlobalTheory.Per.FontaineBound.ddR_finite_le ((PP l).PD K) hF π
  exact le_antisymm h2 (GlobalTheory.DRFil.finrank_mul_le_finrank_DdR_of_spans _ π h1 sw)

end Field

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.isCrys_isDR_internalHom :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A V'] {W : Type} [AddCommGroup W] [Module A W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] A W] [FiniteDimensional ℚ_[l] W] [TopologicalSpace W] [IsModuleTopology ℚ_[l] W] [IsTopologicalAddGroup W] [ContinuousConstSMul A W] (ρ : Representation A G V) (ρ' : Representation A G V') (π : Representation A G W), ContAction ρ → ContAction ρ' → ContAction π → ∀ b : W →ₗ[ℚ_[l]] V →ₗ[ℚ_[l]] V', (∀ g w x, b (π g w) (ρ g x) = ρ' g (b w x)) → Function.Injective b → (IsCr φ ρ → IsCr φ ρ' → IsCr φ π) ∧ (IsDr φ ρ → IsDr φ ρ' → IsDr φ π) := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ _ ρ ρ' π _ _ _ b hb hi
  obtain ⟨K, e, -, -, rfl, -⟩ := openField φ hφ
  obtain ⟨f, hf, hfi⟩ := exists_inj_dual_tprod
    (resCoef ℚ_[l] (ρ.comp e.symm.toMonoidHom : Representation A ↥(GK K) V))
    (resCoef ℚ_[l] (ρ'.comp e.symm.toMonoidHom : Representation A ↥(GK K) V'))
    (resCoef ℚ_[l] (π.comp e.symm.toMonoidHom : Representation A ↥(GK K) W)) b
    (fun g w x => hb (e.symm g) w x) hi
  rw [(admissible_transport_equiv _ e ρ).1, (admissible_transport_equiv _ e ρ').1, (admissible_transport_equiv _ e π).1, (admissible_transport_equiv _ e ρ).2,
    (admissible_transport_equiv _ e ρ').2, (admissible_transport_equiv _ e π).2, (isCrIff K _).1, (isCrIff K _).1, (isCrIff K _).1,
    (isCrIff K _).2, (isCrIff K _).2, (isCrIff K _).2]
  exact ⟨crys_hom K _ _ _ f hf hfi, dR_hom K _ _ _ f hf hfi⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc.AdmRes

variable {l : ℕ} [Fact l.Prime]

section Transport

variable {G G' A A' V : Type} [Group G] [Group G'] [CommRing A] [Algebra ℚ_[l] A] [CommRing A'] [Algebra ℚ_[l] A']
  [AddCommGroup V] [Module A V] [Module A' V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [IsScalarTower ℚ_[l] A' V]
  {φ : G →* GQ l} {ρ : Representation A G V} {φ' : G' →* GQ l} {ρ' : Representation A' G' V}

private theorem transport (e : G → G') (he : Function.Surjective e) (h1 : ∀ g, φ' (e g) = φ g)
    (h2 : ∀ g x, ρ' (e g) x = ρ g x) : (IsCr φ ρ ↔ IsCr φ' ρ') ∧ (IsDr φ ρ ↔ IsDr φ' ρ') := by
  have hr : φ.range = φ'.range := by
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e g, h1 g⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨g, rfl⟩ := he g
      exact ⟨g, (h1 g).symm⟩
  have hρ : ∀ g, resCoef ℚ_[l] ρ' (e g) = resCoef ℚ_[l] ρ g := fun g => LinearMap.ext fun x => h2 g x
  have hc : Dcr φ (resCoef ℚ_[l] ρ) = Dcr φ' (resCoef ℚ_[l] ρ') := by
    unfold Dcr
    rw [he.iInf_comp (fun g => LinearMap.ker (actC φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]
    refine iInf_congr fun g => ?_
    unfold actC
    rw [hρ, h1]
  have hd : Ddr φ (resCoef ℚ_[l] ρ) = Ddr φ' (resCoef ℚ_[l] ρ') := by
    unfold Ddr
    rw [he.iInf_comp (fun g => LinearMap.ker (actD φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]
    refine iInf_congr fun g => ?_
    unfold actD
    rw [hρ, h1]
  unfold IsCr IsDr
  rw [hr, hc, hd]
  exact ⟨Iff.rfl, Iff.rfl⟩

end Transport

private theorem field_case (K K' LL : FinExt l) (h : K.1 ≤ K'.1) {V : Type} [AddCommGroup V] [Module ↥LL.1 V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V) :
    (IsCr (GK K).subtype ρ → IsDr (GK K).subtype ρ) ∧
      (IsCr (GK K).subtype ρ → IsCr (GK K').subtype (ρ.comp (incl h) : Representation ↥LL.1 ↥(GK K') V)) ∧
      (IsDr (GK K).subtype ρ ↔ IsDr (GK K').subtype (ρ.comp (incl h) : Representation ↥LL.1 ↥(GK K') V)) := by
  have := LL.2
  have : FiniteDimensional ↥LL.1 V := Module.Finite.of_restrictScalars_finite ℚ_[l] ↥LL.1 V
  obtain ⟨T⟩ := tiedP l
  have hres := GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (PP l) (AIP l) T K K' LL h V ρ
  rw [(isCrIff K ρ).1, (isCrIff K ρ).2, (isCrIff K' _).1, (isCrIff K' _).2, (isCrField K ρ).1, (isCrField K ρ).2.1,
    (isCrField K' _).1, (isCrField K' _).2.1]
  exact ⟨fun hc => (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (PP l) (AIP l) T K LL V ρ hc).1, hres.1, hres.2⟩

private theorem gal_case (K K' : FinExt l) (h : K.1 ≤ K'.1) {A V : Type} [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    (ρ : Representation A ↥(GK K) V) :
    (IsCr (GK K).subtype ρ → IsDr (GK K).subtype ρ) ∧
      (IsCr (GK K).subtype ρ → IsCr (GK K').subtype (ρ.comp (incl h) : Representation A ↥(GK K') V)) ∧
      (IsDr (GK K).subtype ρ ↔ IsDr (GK K').subtype (ρ.comp (incl h) : Representation A ↥(GK K') V)) := by
  let β : ↥(botExt l).1 ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI : Module ↥(botExt l).1 V := Module.compHom V (β : ↥(botExt l).1 →+* ℚ_[l])
  have hs : ∀ (c : ↥(botExt l).1) (x : V), c • x = β c • x := fun _ _ => rfl
  haveI : IsScalarTower ℚ_[l] ↥(botExt l).1 V := ⟨fun a c x => by
    rw [hs, hs, Algebra.smul_def, map_mul, β.commutes, mul_smul]; rfl⟩
  haveI : ContinuousConstSMul ↥(botExt l).1 V := ⟨fun c => continuous_const_smul (β c)⟩
  let ρ' : Representation ↥(botExt l).1 ↥(GK K) V :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := map_add _
          map_smul' := fun c x => by
            rw [RingHom.id_apply, hs, hs]
            exact LinearMap.map_smul_of_tower _ _ _ }
      map_one' := by ext x; simp
      map_mul' := fun g g' => by ext x; simp }
  have t1 := transport (φ := (GK K).subtype) (ρ := ρ) (φ' := (GK K).subtype) (ρ' := ρ') id
    Function.surjective_id (fun _ => rfl) (fun _ _ => rfl)
  have t2 := transport (φ := (GK K').subtype) (ρ := (ρ.comp (incl h) : Representation A ↥(GK K') V))
    (φ' := (GK K').subtype) (ρ' := (ρ'.comp (incl h) : Representation ↥(botExt l).1 ↥(GK K') V)) id
    Function.surjective_id (fun _ => rfl) (fun _ _ => rfl)
  rw [t1.1, t1.2, t2.1, t2.2]
  exact field_case K K' (botExt l) h ρ'

end UpperTheory.V.Loc.AdmRes

open UpperTheory.V.Loc.AdmRes in
theorem UpperTheory.V.Loc.isCrys_isDR_restrict_openSubgroup :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → (IsCr φ ρ → IsDr φ ρ) ∧ ∀ H : Subgroup G, IsOpen (H : Set G) → (IsCr φ ρ → CrOn φ ρ H) ∧ (IsDr φ ρ ↔ IsDr (φ.comp H.subtype) (ρ.comp H.subtype : Representation A H V)) := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ ρ _
  obtain ⟨K, e, -, -, he, hK, -, -⟩ := openField φ hφ
  have he' : ∀ g, ((e g : ↥(GK K)) : GQ l) = φ g := fun g => DFunLike.congr_fun he g
  let ρK : Representation A ↥(GK K) V := ρ.comp e.symm.toMonoidHom
  have t1 := transport (φ := φ) (ρ := ρ) (φ' := (GK K).subtype) (ρ' := ρK) e e.surjective he'
    (fun g x => by simp [ρK])
  refine ⟨?_, fun H hH => ?_⟩
  · rw [t1.1, t1.2]
    exact (gal_case K K le_rfl ρK).1
  have hφH : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  obtain ⟨K', e', -, -, hf, hK', -, -⟩ := openField (φ.comp H.subtype) hφH
  have hf' : ∀ g, ((e' g : ↥(GK K')) : GQ l) = φ g := fun g => DFunLike.congr_fun hf g
  have hle : GK K' ≤ GK K := by
    rw [← hK, ← hK']
    rintro _ ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have h : K.1 ≤ K'.1 := by
    have : IsGalois ℚ_[l] (Om l) := inferInstance
    rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, ← InfiniteGalois.fixedField_fixingSubgroup K'.1]
    exact IntermediateField.fixedField_le hle
  have t2 := transport (φ := φ.comp H.subtype) (ρ := (ρ.comp H.subtype : Representation A H V))
    (φ' := (GK K').subtype) (ρ' := (ρK.comp (incl h) : Representation A ↥(GK K') V)) e' e'.surjective hf'
    (fun g x => by
      have : incl h (e' g) = e g := Subtype.ext ((hf' g).trans (he' g).symm)
      simp [ρK, this])
  unfold CrOn
  rw [t1.1, t1.2, t2.1, t2.2]
  exact (gal_case K K' h ρK).2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

section Generic

variable {G Q B : Type} [Group G] [Field Q] [AddCommGroup B] [Module Q B] (a : G → B →ₗ[Q] B)

private noncomputable def invT {V : Type} [AddCommGroup V] [Module Q V] (ρ : Representation Q G V) :
    Submodule Q (V ⊗[Q] B) :=
  ⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g) (a g) - LinearMap.id)

private theorem mem_invT {V : Type} [AddCommGroup V] [Module Q V] (ρ : Representation Q G V) (x : V ⊗[Q] B) :
    x ∈ invT a ρ ↔ ∀ g, AlgebraTensorModule.map (ρ g) (a g) x = x := by
  simp only [invT, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

private theorem rT_comm {V V' : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
    {ρ : Representation Q G V} {ρ' : Representation Q G V'} {f : V →ₗ[Q] V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : G) (y : V ⊗[Q] B) :
    f.rTensor B (AlgebraTensorModule.map (ρ g) (a g) y) =
      AlgebraTensorModule.map (ρ' g) (a g) (f.rTensor B y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [hf g]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private noncomputable def invMap {V V' : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
    {ρ : Representation Q G V} {ρ' : Representation Q G V'} {f : V →ₗ[Q] V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) : invT a ρ →ₗ[Q] invT a ρ' :=
  (f.rTensor B).restrict fun x hx => (mem_invT a ρ' _).2 fun g => by
    rw [← rT_comm a hf, (mem_invT a ρ _).1 hx]

private theorem of_exact {V₀ V V' : Type} [AddCommGroup V₀] [Module Q V₀] [AddCommGroup V] [Module Q V]
    [AddCommGroup V'] [Module Q V'] [FiniteDimensional Q V]
    {ρ₀ : Representation Q G V₀} {ρ : Representation Q G V} {ρ' : Representation Q G V'}
    {i : V₀ →ₗ[Q] V} {p : V →ₗ[Q] V'}
    (hi : ∀ g x, i (ρ₀ g x) = ρ g (i x)) (hp : ∀ g x, p (ρ g x) = ρ' g (p x))
    (h1 : Function.Injective i) (h2 : Function.Exact i p) (h3 : Function.Surjective p) (n : ℕ)
    [Module.Finite Q (invT a ρ)] [Module.Finite Q (invT a ρ')]
    (c₀ : finrank Q (invT a ρ₀) ≤ n * finrank Q V₀) (c' : finrank Q (invT a ρ') ≤ n * finrank Q V')
    (h : finrank Q (invT a ρ) = n * finrank Q V) :
    finrank Q (invT a ρ₀) = n * finrank Q V₀ ∧ finrank Q (invT a ρ') = n * finrank Q V' := by
  have hex : Function.Exact (i.rTensor B) (p.rTensor B) := rTensor_exact B h2 h3
  have hinj : Function.Injective (i.rTensor B) := Module.Flat.rTensor_preserves_injective_linearMap _ h1
  have e1 : Function.Injective (invMap a hi) := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  have e2 : Function.Exact (invMap a hi) (invMap a hp) := by
    refine fun x => ⟨fun h => ?_, ?_⟩
    · obtain ⟨y, hy⟩ := (hex x).1 (congrArg Subtype.val h)
      refine ⟨⟨y, (mem_invT a ρ₀ y).2 fun g => hinj ?_⟩, Subtype.ext hy⟩
      rw [rT_comm a hi, hy]
      exact (mem_invT a ρ _).1 x.2 g
    · rintro ⟨y, rfl⟩
      exact Subtype.ext ((hex _).2 ⟨_, rfl⟩)
  have h4 := (invMap a hp).finrank_range_add_finrank_ker
  rw [e2.linearMap_ker_eq, LinearMap.finrank_range_of_inj e1] at h4
  have h5 := p.finrank_range_add_finrank_ker
  rw [h2.linearMap_ker_eq, LinearMap.finrank_range_of_inj h1, LinearMap.range_eq_top.2 h3, finrank_top] at h5
  have h6 := (LinearMap.range (invMap a hp)).finrank_le
  rw [← h5, mul_add] at h
  exact ⟨by omega, by omega⟩

private theorem sub_quot (n : ℕ)
    (hb : ∀ (W : Type) [AddCommGroup W] [Module Q W] [FiniteDimensional Q W] (σ : Representation Q G W),
      Module.Finite Q (invT a σ) ∧ finrank Q (invT a σ) ≤ n * finrank Q W)
    {V V' : Type} [AddCommGroup V] [Module Q V] [AddCommGroup V'] [Module Q V']
    [FiniteDimensional Q V] [FiniteDimensional Q V']
    {ρ : Representation Q G V} {ρ' : Representation Q G V'} {f : V →ₗ[Q] V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    (Function.Injective f → finrank Q (invT a ρ') = n * finrank Q V' → finrank Q (invT a ρ) = n * finrank Q V) ∧
    (Function.Surjective f → finrank Q (invT a ρ) = n * finrank Q V →
      finrank Q (invT a ρ') = n * finrank Q V') := by
  have := (hb V ρ).1
  have := (hb V' ρ').1
  refine ⟨fun hi h => ?_, fun hs h => ?_⟩
  · have hst : ∀ g, LinearMap.range f ≤ (LinearMap.range f).comap (ρ' g) := by
      rintro g _ ⟨v, rfl⟩
      exact ⟨ρ g v, hf g v⟩
    have := (hb _ (ρ'.quotient (LinearMap.range f) hst)).1
    exact (of_exact a (ρ' := ρ'.quotient (LinearMap.range f) hst) hf (fun g v => rfl) hi
      (LinearMap.exact_map_mkQ_range f) (LinearMap.range f).mkQ_surjective n (hb V ρ).2 (hb _ _).2 h).1
  · have hst : ∀ g, LinearMap.ker f ≤ (LinearMap.ker f).comap (ρ g) := by
      intro g v hv
      rw [Submodule.mem_comap, LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hv, map_zero]
    exact (of_exact a (ρ₀ := ρ.subrepresentation (LinearMap.ker f) hst) (fun g v => rfl) hf
      (LinearMap.ker f).injective_subtype (LinearMap.exact_subtype_ker_map f) hs n (hb _ _).2 (hb V' ρ').2 h).2

end Generic

private theorem bound {G H Q K B : Type} [Group G] [Group H] [Field Q] [Field K] [Algebra Q K] [CommRing B]
    [IsDomain B] [Algebra Q B] [Algebra K B] [IsScalarTower Q K B] [FiniteDimensional Q K]
    (e : G ≃* H) (act : H →* (B ≃ₐ[K] B))
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (a : G → B →ₗ[Q] B) (ha : ∀ g b, a g b = act (e g) b)
    (W : Type) [AddCommGroup W] [Module Q W] [FiniteDimensional Q W] (σ : Representation Q G W) :
    Module.Finite Q (invT a σ) ∧ finrank Q (invT a σ) ≤ finrank Q K * finrank Q W := by
  have h := GlobalTheory.Per.FontaineBound.finite_finrank_le_base (Qp := Q) (act.comp e.toMonoidHom)
    (fun b b' hb h => hreg b b' hb fun g => by simpa using h (e.symm g)) σ
  have : a = fun g => ((act.comp e.toMonoidHom g).toAlgHom.toLinearMap).restrictScalars Q :=
    funext fun g => LinearMap.ext fun b => ha g b
  subst this
  exact h

theorem UpperTheory.V.Loc.isCrys_isDR_sub_quot :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {A' : Type} [CommRing A'] [Algebra ℚ_[l] A'] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A' V'] (ρ : Representation A G V) (ρ' : Representation A' G V'), ContAction ρ → ContAction ρ' → ∀ f : V →ₗ[ℚ_[l]] V', (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → (IsCr φ ρ' → IsCr φ ρ) ∧ (IsDr φ ρ' → IsDr φ ρ)) ∧ (Function.Surjective f → (IsCr φ ρ → IsCr φ ρ') ∧ (IsDr φ ρ → IsDr φ ρ')) := by
  intro l _ G _ _ _ φ hφ A _ _ A' _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ' _ _ f hf
  obtain ⟨K, e, -, -, he, -, hK, hK0⟩ := openField φ hφ
  obtain ⟨T⟩ := tiedP l
  have hF := GlobalTheory.Per.FontaineBound.isField_of_tied T
  have := GlobalTheory.Per.FontaineBound.isDomain_cris (PD := (PP l).PD K) hF
  have := hF.isDomain
  have := ((PP l).PD K).finK₀
  have := K.2
  have hφe : ∀ g, φ g = (e g : GQ l) := fun g => by rw [← he]; rfl
  have hc := sub_quot (fun g => ((PP l).actQ (φ g)).toLinearMap) _
    (bound e ((PP l).PD K).actB (fun b b' hb h =>
      GlobalTheory.Per.FracInv.tied_frac_invariant l (PP l) (AIP l) T K b' b hb fun g hg => by
        have h1 := h ⟨g, hg⟩
        rw [(PP l).PD_actB, (PP l).PD_actB] at h1
        rw [mul_comm, h1, mul_comm]) _ fun g b => by rw [(PP l).PD_actB, hφe]; rfl)
    (ρ := resCoef ℚ_[l] ρ) (ρ' := resCoef ℚ_[l] ρ') (f := f) hf
  have hd := sub_quot (fun g => ((PP l).actQdR (φ g)).toLinearMap) _
    (bound e ((PP l).PD K).actdR (GlobalTheory.Per.FontaineBound.frac_dR ((PP l).PD K) hF) _
      fun g b => by rw [(PP l).PD_actdR, hφe]; rfl)
    (ρ := resCoef ℚ_[l] ρ) (ρ' := resCoef ℚ_[l] ρ') (f := f) hf
  unfold IsCr IsDr
  rw [hK, hK0]
  exact ⟨fun h => ⟨hc.1 h, hd.1 h⟩, fun h => ⟨hc.2 h, hd.2 h⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CardCoinvariantsModPowEqModPowCoinvariants
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.card_coinvariants_mod_pow_eq_mod_pow_coinvariants :
    ∀ {l : ℕ} [Fact l.Prime] {G X : Type} [Group G] [AddCommGroup X] [Module ℤ_[l] X] (χ : G →* ℤ_[l]ˣ) (ρ : Representation ℤ_[l] G X) (m : ℕ), Nat.card ((X ⧸ lSub l X m) ⧸ coSub χ (redRep ρ m)) = Nat.card ((X ⧸ coSub χ ρ) ⧸ lSub l (X ⧸ coSub χ ρ) m) := by
  intro l _ G X _ _ _ χ ρ m
  have hq : ∀ g x, UpperTheory.V.Loc.redRep ρ m g ((lSub l X m).mkQ x) = (lSub l X m).mkQ (ρ g x) :=
    fun g x => rfl
  have hC : coSub χ (UpperTheory.V.Loc.redRep ρ m) = (coSub χ ρ).map (lSub l X m).mkQ := by
    unfold coSub
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨g, x, rfl⟩
      obtain ⟨x, rfl⟩ := (lSub l X m).mkQ_surjective x
      exact ⟨ρ g x - (χ g : ℤ_[l]) • x, ⟨g, x, rfl⟩, by rw [map_sub, map_smul, hq]⟩
    · rintro ⟨_, ⟨g, x, rfl⟩, rfl⟩
      exact ⟨g, (lSub l X m).mkQ x, by rw [map_sub, map_smul, hq]⟩
  have hL : lSub l (X ⧸ coSub χ ρ) m = (lSub l X m).map (coSub χ ρ).mkQ := by
    ext y
    rw [mem_lSub, Submodule.mem_map]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨z, rfl⟩ := (coSub χ ρ).mkQ_surjective z
      exact ⟨(l : ℤ_[l]) ^ m • z, mem_lSub.2 ⟨z, rfl⟩, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := mem_lSub.1 hx
      exact ⟨(coSub χ ρ).mkQ z, by simp⟩
  rw [hC, hL]
  exact Nat.card_congr ((Submodule.quotientQuotientEquivQuotientSup _ _).toEquiv.trans
    ((Submodule.quotEquivOfEq _ _ (sup_comm _ _)).toEquiv.trans
      (Submodule.quotientQuotientEquivQuotientSup _ _).symm.toEquiv))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecJFacts
section
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

theorem UpperTheory.V.Loc.decJFacts :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l), IsOpenEmbedding ((MonoidHom.snd _ _).comp (UpperTheory.V.Af.decJ F j).subtype) ∧ IsEmbedding ((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype) ∧ ((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype).range = Dec (F := F) (placeJ j) := by
  intro F Ω _ _ _ _ _ _ l _ j
  haveI : IsAlgClosure ℚ Ω := Examples₂.LB.isAlgClosureQ F Ω
  have hj : ∀ x : Ω, x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := by
    intro x
    change (Valued.v : Valuation (Om l) NNReal) (j x) ≤ 1 ↔ _
    rw [← NNReal.coe_le_coe]
    exact Iff.rfl
  let e := Examples₂.LB.eDec (E := F) hj
  have he : Continuous e := Examples₂.LB.continuous_eDec hj
  have hes : Continuous e.symm := Examples₂.LB.continuous_eDec_symm hj
  have hc : ∀ g x, ((e g : _) : GQ l) (j x) = j ((g : G F Ω) x) := Examples₂.LB.eDec_comm hj
  have hK : ∀ x : ↥(UpperTheory.V.Af.decJ F j), x.1.2 ∈ (Examples₂.LB.KwF (E := F) j).fixingSubgroup := by
    intro x
    refine Examples₂.LB.mem_GK_of_fix j _ fun y => ?_
    have := x.2 (algebraMap F Ω y)
    rw [AlgEquiv.commutes] at this
    exact this
  have hfst : ∀ x : ↥(UpperTheory.V.Af.decJ F j), ((e.symm ⟨x.1.2, hK x⟩ : _) : G F Ω) = x.1.1 := by
    intro x
    refine AlgEquiv.ext fun y => j.injective ?_
    rw [← hc, MulEquiv.apply_symm_apply]
    exact x.2 y
  let h : ↥(UpperTheory.V.Af.decJ F j) ≃ₜ ↥(Examples₂.LB.KwF (E := F) j).fixingSubgroup :=
    { toFun := fun x => ⟨x.1.2, hK x⟩
      invFun := fun σ => ⟨(((e.symm σ : _) : G F Ω), σ.1), fun y => by
        have := hc (e.symm σ) y
        rw [MulEquiv.apply_symm_apply] at this
        exact this⟩
      left_inv := fun x => Subtype.ext (Prod.ext (hfst x) rfl)
      right_inv := fun σ => rfl
      continuous_toFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := ((continuous_subtype_val.comp hes).prodMk continuous_subtype_val).subtype_mk _ }
  let e' : ↥(Examples₂.LB.KwF (E := F) j).fixingSubgroup ≃ₜ ↥(Dec (F := F) (placeJ j)) :=
    { toEquiv := e.symm.toEquiv, continuous_toFun := hes, continuous_invFun := he }
  have h1 : ⇑((MonoidHom.fst _ _).comp (UpperTheory.V.Af.decJ F j).subtype) = Subtype.val ∘ (h.trans e') :=
    funext fun x => (hfst x).symm
  refine ⟨?_, ?_, ?_⟩
  · exact (IntermediateField.fixingSubgroup_isOpen (Examples₂.LB.KwF (E := F) j)).isOpenEmbedding_subtypeVal.comp
      h.isOpenEmbedding
  · rw [h1]
    exact IsEmbedding.subtypeVal.comp (h.trans e').isEmbedding
  · apply SetLike.coe_injective
    rw [MonoidHom.coe_range, h1, Set.range_comp, (h.trans e').surjective.range_eq, Set.image_univ, Subtype.range_coe_subtype]
    rfl
end

