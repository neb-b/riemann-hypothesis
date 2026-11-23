module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CohFinite
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0005

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SectionBasis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}}

lemma IsBasisOn.isUnit_smul {P : PMod X} {U : X.Opens} {s : P.obj (op U)} (hs : IsBasisOn P U s)
    {a : ringOn X U} (ha : IsUnit a) : IsBasisOn P U (a • s) := by
  intro V h
  have e : resM P h (a • s) = resR h a • resM P h s := resM_smul P h a s
  have hu : IsUnit (resR h a) := ha.map _
  have : (fun r : ringOn X V => r • resM P h (a • s)) =
      (fun r : ringOn X V => r • resM P h s) ∘ (fun r => r * resR h a) := by
    funext r
    simp only [Function.comp_apply, e, mul_smul]
  rw [this]
  refine (hs V h).comp ⟨fun r r' hrr => hu.mul_left_injective hrr, fun r => ⟨r * hu.unit⁻¹, ?_⟩⟩
  change r * ↑hu.unit⁻¹ * resR h a = r
  rw [mul_assoc, hu.val_inv_mul, mul_one]

theorem exists_isBasisOn_generatingSection (L : X.Modules) [L.IsQuasicoherent]
    (hL : IsInvertibleSheaf L) (σ : L.GeneratingSections) [σ.IsFiniteType] (x : X) :
    ∃ (k : σ.I) (W : X.Opens), x ∈ W ∧
      IsBasisOn ((preMod X).obj L) W
        (resM ((preMod X).obj L) le_top (show Γ(L, ⊤) from (σ.s k).val (op ⊤))) := by
  classical
  set P := (preMod X).obj L
  obtain ⟨U, hxU, e, he⟩ := hL x
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  replace hVU : V ≤ U := hVU
  have hb : IsBasisOn P V (resM P hVU e) := he.restrict hVU
  let φ : ringOn X V ≃ₗ[ringOn X V] P.obj (op V) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton (ringOn X V) _ (resM P hVU e))
      (by
        have h := hb V le_rfl
        rwa [show resM P (le_refl V) (resM P hVU e) = resM P hVU e by
          rw [resM_resM]] at h)
  let g : σ.I → P.obj (op V) := fun k => resM P le_top (show Γ(L, ⊤) from (σ.s k).val (op ⊤))
  let a : σ.I → ringOn X V := fun k => φ.symm (g k)
  have hga : ∀ k, g k = a k • resM P hVU e := fun k => by
    change g k = φ (a k)
    simp [a]
  have hspan : Submodule.span (ringOn X V) (Set.range g) = ⊤ :=
    span_eq_top_of_generatingSections L σ hVaff
  have hIdeal : Ideal.span (Set.range a) = ⊤ := by
    have h2 : Submodule.map φ.symm.toLinearMap (Submodule.span (ringOn X V) (Set.range g)) = ⊤ := by
      rw [hspan, Submodule.map_top,
        LinearMap.range_eq_top]
      exact φ.symm.surjective
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  have hxcov : V ≤ ⨆ k, X.basicOpen (a k) := by
    have := (hVaff.self_le_iSup_basicOpen_iff (s := Set.range a)).2 hIdeal
    intro y hy
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := Opens.mem_iSup.1 (this hy)
    exact Opens.mem_iSup.2 ⟨k, hk⟩
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hxcov hxV)
  have hWV : X.basicOpen (a k) ≤ V := X.basicOpen_le _
  refine ⟨k, X.basicOpen (a k), hk, ?_⟩
  have hu : IsUnit (resR hWV (a k)) := X.toRingedSpace.isUnit_res_basicOpen (a k)
  have key : resM P le_top (show Γ(L, ⊤) from (σ.s k).val (op ⊤)) =
      resR hWV (a k) • resM P hWV (resM P hVU e) := by
    have h1 : resM P hWV (g k) = resM P (hWV.trans le_top) _ := resM_resM P le_top hWV _
    rw [hga k, resM_smul] at h1
    exact h1.symm
  rw [key]
  exact (hb.restrict hWV).isUnit_smul hu

end

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SupportMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
open scoped ZeroObject

universe w' u

noncomputable section

variable {X : Scheme.{u}}

lemma eq_zero_of_isTerminal {T : AddCommGrpCat.{u}} (hT : IsTerminal T) (s : T) : s = 0 := by
  let f : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ T :=
    AddCommGrpCat.ofHom ((zmultiplesHom T s).comp AddEquiv.ulift.toAddMonoidHom)
  have h := congrArg (fun g : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ T => g.hom (⟨1⟩ : ULift.{u} ℤ))
    (hT.hom_ext f 0)
  have h1 : (AddEquiv.ulift (⟨1⟩ : ULift.{u} ℤ) : ℤ) = 1 := rfl
  simp only [f] at h
  rwa [AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h1, zmultiplesHom_apply, one_smul] at h

lemma eq_zero_of_bot (F : X.Modules) (s : Γ(F, ⊥)) : s = 0 :=
  eq_zero_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty (modulesAb F)) s

lemma isZero_of_forall_eq_zero (F : X.Modules) (h : ∀ (U : X.Opens) (s : Γ(F, U)), s = 0) :
    IsZero F := by
  have : IsIso (0 : F ⟶ 0) := isIso_of_bijective_app _ fun U =>
    ⟨fun a b _ => (h U a).trans (h U b).symm,
     fun t => ⟨0, (eq_zero_of_isZero (isZero_zero _) U t).symm ▸ map_zero _⟩⟩
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

namespace Scheme.Modules.SupportedIn

lemma univ (F : X.Modules) : Scheme.Modules.SupportedIn F Set.univ := by
  intro U hU s
  have hU' : U = ⊥ := by
    ext x
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => Set.disjoint_left.1 hU hx trivial
  subst hU'
  exact eq_zero_of_bot F s

lemma inter {F : X.Modules} {T₁ T₂ : Set X} (h₁ : Scheme.Modules.SupportedIn F T₁)
    (h₂ : Scheme.Modules.SupportedIn F T₂) (hT₁ : IsClosed T₁) (hT₂ : IsClosed T₂) :
    Scheme.Modules.SupportedIn F (T₁ ∩ T₂) := by
  intro U hU s
  let U₁ : X.Opens := U ⊓ ⟨T₁ᶜ, hT₁.isOpen_compl⟩
  let U₂ : X.Opens := U ⊓ ⟨T₂ᶜ, hT₂.isOpen_compl⟩
  have hcov : U ≤ U₁ ⊔ U₂ := by
    intro x hx
    by_cases hx₁ : x ∈ T₁
    · refine Or.inr ⟨hx, fun hx₂ => Set.disjoint_left.1 hU hx ⟨hx₁, hx₂⟩⟩
    · exact Or.inl ⟨hx, hx₁⟩
  refine TopCat.Sheaf.eq_of_locally_eq₂ (modulesAb F) (homOfLE inf_le_left)
    (homOfLE inf_le_left) hcov s 0 ?_ ?_
  · rw [map_zero]
    exact h₁ U₁ (Set.disjoint_left.2 fun x hx hxT => hx.2 hxT) _
  · rw [map_zero]
    exact h₂ U₂ (Set.disjoint_left.2 fun x hx hxT => hx.2 hxT) _

lemma of_mono {F G : X.Modules} (m : F ⟶ G) [Mono m] {T : Set X}
    (h : Scheme.Modules.SupportedIn G T) : Scheme.Modules.SupportedIn F T := by
  intro U hU s
  have h1 : Mono ((Scheme.Modules.toPresheaf X).map m) := Functor.map_mono _ m
  have h2 : Mono (((Scheme.Modules.toPresheaf X).map m).app (op U)) := inferInstance
  have hinj : Function.Injective (m.app U) := (AddCommGrpCat.mono_iff_injective _).1 h2
  apply hinj
  rw [map_zero]
  exact h U hU _

lemma isZero_restrict {F : X.Modules} {T : Set X} (h : Scheme.Modules.SupportedIn F T)
    (U : X.Opens) (hU : Disjoint (U : Set X) T) :
    IsZero ((Scheme.Modules.restrictFunctor U.ι).obj F) := by
  refine isZero_of_forall_eq_zero _ fun V s => h (U.ι ''ᵁ V) ?_ s
  refine hU.mono_left ?_
  exact (U.ι.image_le_opensRange V).trans (by simp)

lemma of_isZero_restrict {F : X.Modules} {T : Set X}
    (h : ∀ U : X.Opens, Disjoint (U : Set X) T →
      IsZero ((Scheme.Modules.restrictFunctor U.ι).obj F)) :
    Scheme.Modules.SupportedIn F T := by
  intro U hU s
  have hE : U.ι ''ᵁ (U.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_idem U
  have h0 : F.presheaf.map (eqToHom hE).op s = 0 :=
    eq_zero_of_isZero (h U hU) (U.ι ⁻¹ᵁ U) _
  have hinv : F.presheaf.map (eqToHom hE.symm).op (F.presheaf.map (eqToHom hE).op s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
      op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [← hinv, h0, map_zero]

lemma of_epi {F G : X.Modules} (e : F ⟶ G) [Epi e] {T : Set X}
    (h : Scheme.Modules.SupportedIn F T) : Scheme.Modules.SupportedIn G T := by
  refine of_isZero_restrict fun U hU => ?_
  have : Epi ((Scheme.Modules.restrictFunctor U.ι).map e) := Functor.map_epi _ e
  exact (isZero_restrict h U hU).of_epi ((Scheme.Modules.restrictFunctor U.ι).map e)

lemma isZero_of_empty {F : X.Modules} (h : Scheme.Modules.SupportedIn F ∅) : IsZero F :=
  isZero_of_forall_eq_zero F fun U s => h U (Set.disjoint_empty _) s

end Scheme.Modules.SupportedIn

section Cohomology

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]

lemma H_eq_zero_of_isZero {F : X.Modules} (hF : IsZero F) {p : ℕ}
    (x : Sheaf.H.{w'} (modulesAb F) p) : x = 0 := by
  have hF' : IsZero (modulesAb F) := Functor.map_isZero _ hF
  change Abelian.Ext _ _ p at x
  rw [← Abelian.Ext.comp_mk₀_id x, hF'.eq_of_src (𝟙 _) 0, Abelian.Ext.mk₀_zero,
    Abelian.Ext.comp_zero]

theorem FiniteH.of_isZero (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)] {F : X.Modules}
    (hF : IsZero F) : FiniteH.{w'} A F := fun p =>
  have : Subsingleton (Sheaf.H.{w'} (modulesAb F) p) :=
    ⟨fun x y => (H_eq_zero_of_isZero hF x).trans (H_eq_zero_of_isZero hF y).symm⟩
  Module.Finite.of_finite

end Cohomology

end

end GroundTheory.Arith.SchemeCoh
end

