module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SheafHEquiv
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionCech
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Annihilator
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0006

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.AcyclicLeray
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

noncomputable section

open CategoryTheory Opposite TopologicalSpace Limits Abelian AlgebraicGeometry

universe w w' u

section Top

variable {X : TopCat.{u}} [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  {ι : Type w} (U : ι → Opens X)

def HAcyclicOn (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Prop :=
  ∀ {n : ℕ} (i : Fin (n + 1) → ι) (q : ℕ), Subsingleton (G.H' (q + 1) (inter U i))

variable {U}

lemma surjective_app_of_subsingleton_H'
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})} (hS : S.ShortExact)
    (V : Opens X) [Subsingleton (S.X₁.H' 1 V)] : Function.Surjective (S.g.hom.app (op V)) := by
  intro y
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ (freeSheaf (Opens.grothendieckTopology X) V) hS
    ((H'.equiv₀ S.X₃ V).symm y) rfl (Subsingleton.elim (α := S.X₁.H' 1 V) _ _)
  have key : H'.equiv₀ S.X₃ V (x.comp (Ext.mk₀ S.g) (add_zero 0)) =
      S.g.hom.app (op V) (H'.equiv₀ S.X₂ V x) := H'.equiv₀_naturality S.g V x
  exact ⟨H'.equiv₀ S.X₂ V x, by rw [← key, hx, AddEquiv.apply_symm_apply]⟩

lemma subsingleton_H'_of_injective
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})} (hS : S.ShortExact)
    [Injective S.X₂] (V : Opens X) (q : ℕ) [Subsingleton (S.X₁.H' (q + 2) V)] :
    Subsingleton (S.X₃.H' (q + 1) V) := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ (freeSheaf (Opens.grothendieckTopology X) V) hS
    y rfl (Subsingleton.elim (α := S.X₁.H' (q + 2) V) _ _)
  have : Subsingleton (S.X₂.H' (q + 1) V) := H'.subsingleton_of_injective S.X₂ q V
  have hx0 : x = 0 := Subsingleton.elim (α := S.X₂.H' (q + 1) V) _ _
  rw [← hx, hx0, Ext.zero_comp]
  rfl

variable (U)

lemma injectiveSequence_isCechShortExact_of_acyclic
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hG : HAcyclicOn.{w, w'} U G) :
    IsCechShortExact U (injectiveSequence G).f.hom (injectiveSequence G).g.hom :=
  isCechShortExact_of_surjective (injectiveSequence_shortExact G) U fun i =>
    have : Subsingleton ((injectiveSequence G).X₁.H' 1 (inter U i)) := hG i 0
    surjective_app_of_subsingleton_H'.{w'} (injectiveSequence_shortExact G) _

lemma injectiveSequence_hAcyclicOn
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hG : HAcyclicOn.{w, w'} U G) :
    HAcyclicOn.{w, w'} U (injectiveSequence G).X₃ := fun i q =>
  have : Subsingleton ((injectiveSequence G).X₁.H' (q + 2) (inter U i)) := hG i (q + 1)
  have : Injective (injectiveSequence G).X₂ := inferInstanceAs (Injective (Injective.under G))
  subsingleton_H'_of_injective (injectiveSequence_shortExact G) _ q

variable (hU : iSup U = ⊤)

def cechHEquivOfAcyclic : ∀ (n : ℕ) (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
    HAcyclicOn.{w, w'} U G → (cechH G.obj U n ≃+ Sheaf.H.{w'} G n)
  | 0, G, _ => cechHZeroEquivH G U hU
  | 1, G, hG => cechHOneEquiv (S := injectiveSequence G) U hU (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact_of_acyclic U G hG) (injectiveSequence_cechAcyclic G U)
  | m + 2, G, hG => cechHEquivStep (S := injectiveSequence G) U (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact_of_acyclic U G hG) (injectiveSequence_cechAcyclic G U) m
      (cechHEquivOfAcyclic (m + 1) _ (injectiveSequence_hAcyclicOn U G hG))

theorem cechHEquivOfAcyclic_naturality : ∀ (n : ℕ)
    {G G' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (hG : HAcyclicOn.{w, w'} U G) (hG' : HAcyclicOn.{w, w'} U G') (φ : G ⟶ G')
    (x : cechH G.obj U n),
    cechHEquivOfAcyclic U hU n G' hG' (cechHMap U φ.hom n x) =
      Sheaf.H.map.{w'} φ n (cechHEquivOfAcyclic U hU n G hG x)
  | 0, _, _, _, _, φ, x => cechHZeroEquivH_naturality U φ hU x
  | 1, G, G', hG, hG', φ, x =>
      cechHOneEquiv_naturality (S := injectiveSequence G) (S' := injectiveSequence G') U hU
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact_of_acyclic U G hG)
        (injectiveSequence_cechAcyclic G U) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact_of_acyclic U G' hG') (injectiveSequence_cechAcyclic G' U)
        (injectiveSequenceMap φ) x
  | m + 2, G, G', hG, hG', φ, x =>
      cechHEquivStep_naturality (S := injectiveSequence G) (S' := injectiveSequence G') U
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact_of_acyclic U G hG)
        (injectiveSequence_cechAcyclic G U) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact_of_acyclic U G' hG') (injectiveSequence_cechAcyclic G' U)
        (injectiveSequenceMap φ) m
        (cechHEquivOfAcyclic U hU (m + 1) _ (injectiveSequence_hAcyclicOn U G hG))
        (cechHEquivOfAcyclic U hU (m + 1) _ (injectiveSequence_hAcyclicOn U G' hG'))
        (fun y => cechHEquivOfAcyclic_naturality (m + 1) (injectiveSequence_hAcyclicOn U G hG)
          (injectiveSequence_hAcyclicOn U G' hG') (injectiveSequenceMap φ).τ₃ y) x

end Top

section Scheme

variable {X : Scheme.{u}} [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  {ι : Type w} (U : ι → X.Opens) (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]

def cechHLinearEquivHOfAcyclic (hU : iSup U = ⊤) (F : X.Modules)
    (hF : HAcyclicOn.{w, w'} (X := X.toTopCat) U (modulesAb F)) (n : ℕ) :
    cechH (modulesAb F).obj U n ≃ₗ[A] Sheaf.H.{w'} (modulesAb F) n :=
  (cechHEquivOfAcyclic (X := X.toTopCat) U hU n (modulesAb F) hF).toLinearEquiv fun a x =>
    cechHEquivOfAcyclic_naturality (X := X.toTopCat) U hU n hF hF
      (modulesAbMap (smulHom F (algebraMap A Γ(X, ⊤) a))) x

variable [∀ V : X.Opens,
    HasExt.{w'} (Sheaf ((Opens.grothendieckTopology X.toTopCat).over V) AddCommGrpCat.{u})]
  [∀ V : X.Opens, HasExt.{w'} (Sheaf (Opens.grothendieckTopology V.toScheme.toTopCat) AddCommGrpCat.{u})]

lemma hAcyclicOn_of_restrict (F : X.Modules)
    (h : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (q : ℕ),
      Subsingleton (Sheaf.H.{w'} (modulesAb (F.restrict (⨅ a, U (i a)).ι)) (q + 1))) :
    HAcyclicOn.{w, w'} (X := X.toTopCat) U (modulesAb F) := fun {n} i q => by
  have := h n i q
  rw [inter_eq_iInf]
  exact subsingleton_H'_of_restrict.{w'} (⨅ a, U (i a)) F (q + 1)

end Scheme

section Pushforward

variable {X X' : Scheme.{u}} (ψ : X' ⟶ X) (A : Type u) [CommRing A] [X.Over (Spec (.of A))]
  [X'.Over (Spec (.of A))] [ψ.IsOver (Spec (.of A))]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X'.toTopCat) AddCommGrpCat.{u})]
  [∀ V : X'.Opens,
    HasExt.{w'} (Sheaf ((Opens.grothendieckTopology X'.toTopCat).over V) AddCommGrpCat.{u})]
  [∀ V : X'.Opens, HasExt.{w'} (Sheaf (Opens.grothendieckTopology V.toScheme.toTopCat) AddCommGrpCat.{u})]
  {ι : Type w} (V : ι → X.Opens) (hV : iSup V = ⊤)
  (hVaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, V (i a)))

attribute [local instance] algebraOfOver

def HLinearEquivPushforwardOfAcyclic (G : X'.Modules)
    [((Scheme.Modules.pushforward ψ).obj G).IsQuasicoherent]
    (hG : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (q : ℕ),
      Subsingleton (Sheaf.H.{w'} (modulesAb (G.restrict (ψ ⁻¹ᵁ ⨅ a, V (i a)).ι)) (q + 1)))
    (p : ℕ) :
    Sheaf.H.{w'} (modulesAb G) p ≃ₗ[A]
      Sheaf.H.{w'} (modulesAb ((Scheme.Modules.pushforward ψ).obj G)) p :=
  have hV' : iSup (fun j => ψ ⁻¹ᵁ V j) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hV]
    rfl
  have hG' : HAcyclicOn.{w, w'} (X := X'.toTopCat) (fun j => ψ ⁻¹ᵁ V j) (modulesAb G) :=
    hAcyclicOn_of_restrict _ G fun n i q => by
      have e := preimage_inter ψ V i
      rw [inter_eq_iInf, inter_eq_iInf] at e
      have h1 := hG n i q
      rw [e] at h1
      exact h1
  (cechHLinearEquivHOfAcyclic (fun j => ψ ⁻¹ᵁ V j) A hV' G hG' p).symm ≪≫ₗ
    (cechHPushforwardLinearEquiv ψ A G V p).symm ≪≫ₗ cechHLinearEquivH V hV hVaff A _ p

end Pushforward

end

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackCoherent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

lemma finite_of_semilinear {R R' M M' : Type*} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R' M'] (σ : R →+* R') (hσ : Function.Surjective σ)
    (e : M ≃+ M') (he : ∀ (r : R) (m : M), e (r • m) = σ r • e m) [Module.Finite R' M'] :
    Module.Finite R M := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R') (M := M')
  refine ⟨⟨s.image e.symm, ?_⟩⟩
  rw [eq_top_iff]
  intro m _
  have key : ∀ x ∈ Submodule.span R' (s : Set M'),
      e.symm x ∈ Submodule.span R ((s.image e.symm : Finset M) : Set M) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨y, hy, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r' y _ hy =>
      obtain ⟨r, rfl⟩ := hσ r'
      have : e.symm (σ r • y) = r • e.symm y := by
        apply e.injective
        rw [he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      rw [this]
      exact Submodule.smul_mem _ _ hy
  simpa using key (e m) (hs ▸ Submodule.mem_top)

section Affine

variable {T U : Scheme.{u}}

theorem isQuasicoherent_pullback_of_isAffine (g : T ⟶ U) [IsAffine T] [IsAffine U]
    (N : U.Modules) [N.IsQuasicoherent] : ((Scheme.Modules.pullback g).obj N).IsQuasicoherent := by
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = T.isoSpec.inv ≫ g ≫ U.isoSpec.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hg : g = T.isoSpec.hom ≫ Spec.map φ ≫ U.isoSpec.inv := by simp [hφ]
  rw [hg]
  let N₁ := (Scheme.Modules.pullback U.isoSpec.inv).obj N
  have : N₁.IsQuasicoherent := Etale.isQuasicoherent_pullback_of_isIso _ N
  have : IsIso N₁.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ N₁).mp inferInstance
  let N₂ := (Scheme.Modules.pullback (Spec.map φ)).obj N₁
  have : N₂.IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ N₂).mpr (Etale.isIso_fromTildeΓ_pullback φ N₁)
  have : ((Scheme.Modules.pullback T.isoSpec.hom).obj N₂).IsQuasicoherent :=
    Etale.isQuasicoherent_pullback_of_isIso _ N₂
  let e : (Scheme.Modules.pullback T.isoSpec.hom).obj N₂ ≅
      (Scheme.Modules.pullback (T.isoSpec.hom ≫ Spec.map φ ≫ U.isoSpec.inv)).obj N :=
    (Scheme.Modules.pullback T.isoSpec.hom).mapIso
        ((Scheme.Modules.pullbackComp (Spec.map φ) U.isoSpec.inv).app N) ≪≫
      (Scheme.Modules.pullbackComp T.isoSpec.hom (Spec.map φ ≫ U.isoSpec.inv)).app N
  exact (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso e inferInstance

theorem finite_pullback_of_isAffine (g : T ⟶ U) [IsAffine T] [IsAffine U] (N : U.Modules)
    [N.IsQuasicoherent] [Module.Finite Γ(U, ⊤) Γ(N, ⊤)] :
    Module.Finite Γ(T, ⊤) Γ((Scheme.Modules.pullback g).obj N, ⊤) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Γ(U, ⊤)) (M := Γ(N, ⊤))
  let P := Γ((Scheme.Modules.pullback g).obj N, ⊤)
  let L : Submodule Γ(T, ⊤) P :=
    Submodule.span Γ(T, ⊤) ((s.image (Etale.pullbackSection g N) : Finset P) : Set P)
  have hmem : ∀ n : Γ(N, ⊤), Etale.pullbackSection g N n ∈ L := by
    intro n
    have hn : n ∈ Submodule.span Γ(U, ⊤) (s : Set Γ(N, ⊤)) := hs ▸ Submodule.mem_top
    induction hn using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact L.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact L.add_mem hx hy
    | smul r x _ hx => rw [Etale.pullbackSection_smul]; exact L.smul_mem _ hx
  have hL : L = ⊤ := by
    obtain ⟨ψ', -, huniq⟩ := Etale.existsUnique_pullbackSection g N (P ⧸ L) 0
      (fun a n => by simp)
    have h0 : (0 : P →ₗ[Γ(T, ⊤)] (P ⧸ L)) = ψ' := huniq 0 (fun n => by simp)
    have h1 : L.mkQ = ψ' := huniq L.mkQ (fun n => by
      simpa using (Submodule.Quotient.mk_eq_zero L).2 (hmem n))
    rw [eq_top_iff]
    intro q _
    have := LinearMap.congr_fun (h1.trans h0.symm) q
    exact (Submodule.Quotient.mk_eq_zero L).1 this
  exact ⟨⟨s.image (Etale.pullbackSection g N), hL⟩⟩

end Affine

section Pullback

variable {X Y : Scheme.{u}}

lemma finite_restrict_top (F : X.Modules) (U : X.Opens)
    [Module.Finite Γ(X, U.ι ''ᵁ ⊤) Γ(F, U.ι ''ᵁ ⊤)] :
    Module.Finite Γ(U, ⊤) Γ(F.restrict U.ι, ⊤) := by
  refine finite_of_semilinear (U.ι.appIso ⊤).inv.hom
    (ConcreteCategory.bijective_of_isIso (U.ι.appIso ⊤).inv).2
    (F.restrictAppIso U.ι ⊤).addCommGroupIsoToAddEquiv fun r m => ?_
  have hs := congrArg (fun φ : Γ(F.restrict U.ι, ⊤) ⟶ Γ(F, U.ι ''ᵁ ⊤) => φ m)
    (Scheme.Modules.smul_restrictAppIso_hom U.ι F ⊤ r)
  exact hs

lemma finite_of_finite_restrict_top (F : X.Modules) (U : X.Opens)
    [Module.Finite Γ(U, ⊤) Γ(F.restrict U.ι, ⊤)] :
    Module.Finite Γ(X, U.ι ''ᵁ ⊤) Γ(F, U.ι ''ᵁ ⊤) := by
  refine finite_of_semilinear (U.ι.appIso ⊤).hom.hom
    (ConcreteCategory.bijective_of_isIso (U.ι.appIso ⊤).hom).2
    (F.restrictAppIso U.ι ⊤).addCommGroupIsoToAddEquiv.symm fun r m => ?_
  have hs := congrArg (fun φ : Γ(F, U.ι ''ᵁ ⊤) ⟶ Γ(F.restrict U.ι, ⊤) => φ m)
    (Scheme.Modules.smul_restrictAppIso_inv U.ι F ⊤ r)
  exact hs

lemma isQuasicoherent_restrict_fromSpec (M : Y.Modules) {V : Y.Opens} (hV : IsAffineOpen V)
    (h : (M.restrict V.ι).IsQuasicoherent) : (M.restrict hV.fromSpec).IsQuasicoherent := by
  have : IsAffine V := hV
  let e : (M.restrict V.ι).restrict hV.isoSpec.inv ≅ M.restrict hV.fromSpec :=
    ((Scheme.Modules.restrictFunctorComp hV.isoSpec.inv V.ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hV.isoSpec_inv_ι).app M
  have h2 : ((M.restrict V.ι).restrict hV.isoSpec.inv).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  exact (SheafOfModules.isQuasicoherent (Spec Γ(Y, V)).ringCatSheaf).prop_of_iso e h2

lemma isQuasicoherent_of_restrict_affine (M : Y.Modules) {ι : Type u} (V : ι → Y.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcov : iSup V = ⊤)
    (h : ∀ i, (M.restrict (V i).ι).IsQuasicoherent) : M.IsQuasicoherent :=
  isQuasicoherent_of_restrict M V hcov fun i =>
    nonempty_presentation_restrict M (hV i) (isQuasicoherent_restrict_fromSpec M (hV i) (h i))

def restrictPullbackIso (ψ : Y ⟶ X) (F : X.Modules) (U : X.Opens) (V : Y.Opens)
    (h : V ≤ ψ ⁻¹ᵁ U) :
    ((Scheme.Modules.pullback ψ).obj F).restrict V.ι ≅
      (Scheme.Modules.pullback (ψ.resLE U V h)).obj (F.restrict U.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback V.ι).app _ ≪≫
    (Scheme.Modules.pullbackComp V.ι ψ).app F ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.Hom.resLE_comp_ι ψ h).symm).app F ≪≫
    ((Scheme.Modules.pullbackComp (ψ.resLE U V h) U.ι).app F).symm ≪≫
    (Scheme.Modules.pullback (ψ.resLE U V h)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm

lemma finite_of_iso_app {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N) (W : Z.Opens)
    [Module.Finite Γ(Z, W) Γ(M, W)] : Module.Finite Γ(Z, W) Γ(N, W) :=
  Module.Finite.equiv
    { toFun := e.hom.app W
      invFun := e.inv.app W
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul e.hom
      left_inv := fun x => by
        rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]; rfl
      right_inv := fun x => by
        rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]; rfl }

theorem isCoherent_pullback (ψ : Y ⟶ X) {F : X.Modules} (hF : IsCoherent F) :
    IsCoherent ((Scheme.Modules.pullback ψ).obj F) := by
  have := hF.1
  let ι := {p : X.affineOpens × Y.affineOpens // p.2.1 ≤ ψ ⁻¹ᵁ p.1.1}
  let Vo : ι → Y.Opens := fun i => i.1.2.1
  have hcov : iSup Vo = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hyU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (ψ.base y)) isOpen_univ
    obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hyV, hVU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ ψ ⁻¹ᵁ U₀ from hyU)
        (ψ ⁻¹ᵁ U₀).isOpen
    exact Opens.mem_iSup.2 ⟨⟨(⟨U₀, hU₀⟩, ⟨V₀, hV₀⟩), hVU⟩, hyV⟩
  let F' := (Scheme.Modules.pullback ψ).obj F
  have hloc : ∀ i : ι, (F'.restrict (Vo i).ι).IsQuasicoherent ∧
      Module.Finite Γ(Vo i, ⊤) Γ(F'.restrict (Vo i).ι, ⊤) := by
    intro i
    have hU := i.1.1.2
    have hV := i.1.2.2
    have : IsAffine i.1.1.1 := hU
    have : IsAffine i.1.2.1 := hV
    have hfin : Module.Finite Γ(X, i.1.1.1.ι ''ᵁ ⊤) Γ(F, i.1.1.1.ι ''ᵁ ⊤) :=
      hF.2 _ ((isAffineOpen_top _).image_of_isOpenImmersion _)
    have : Module.Finite Γ(i.1.1.1, ⊤) Γ(F.restrict i.1.1.1.ι, ⊤) := finite_restrict_top F _
    let e := restrictPullbackIso ψ F i.1.1.1 i.1.2.1 i.2
    have := isQuasicoherent_pullback_of_isAffine (ψ.resLE _ _ i.2) (F.restrict i.1.1.1.ι)
    have := finite_pullback_of_isAffine (ψ.resLE _ _ i.2) (F.restrict i.1.1.1.ι)
    exact ⟨(SheafOfModules.isQuasicoherent (Vo i).toScheme.ringCatSheaf).prop_of_iso e.symm
      inferInstance, finite_of_iso_app e.symm ⊤⟩
  have : F'.IsQuasicoherent :=
    isQuasicoherent_of_restrict_affine F' Vo (fun i => i.1.2.2) hcov fun i => (hloc i).1
  refine isCoherent_of_affineCover F' (fun i => (Vo i).ι ''ᵁ ⊤)
    (fun i => (isAffineOpen_top _).image_of_isOpenImmersion _) ?_ fun i => ?_
  · simp only [Scheme.Opens.ι_image_top]
    exact hcov
  · have : IsAffine (Vo i) := i.1.2.2
    have := (hloc i).2
    exact finite_of_finite_restrict_top F' (Vo i)

end Pullback

section Support

variable {X : Scheme.{u}}

theorem exists_pushforward_iso_of_supportedIn (F : X.Modules) (hF : IsCoherent F) {T : Set X}
    (hT : IsClosed T) (hFT : Scheme.Modules.SupportedIn F T) :
    ∃ I : X.IdealSheafData, (I.support : Set X) ⊆ T ∧ ∃ G : I.subscheme.Modules, IsCoherent G ∧
      Nonempty ((Scheme.Modules.pushforward I.subschemeι).obj G ≅ F) := by
  have := hF.1
  let I := annihilatorIdealSheaf F hF
  refine ⟨I, support_annihilatorIdealSheaf_subset F hF hT hFT,
    (Scheme.Modules.pullback I.subschemeι).obj F, isCoherent_pullback _ hF, ?_⟩
  let adj := Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι
  have : IsClosedImmersion (I.subschemeι ∣_ ⊤) := inferInstance
  have : IsIso (adj.unit.app F) := by
    refine isIso_of_bijective_app _ fun V => ?_
    refine bijective_unit_app_of_le I.subschemeι F ⊤ (fun V hV _ a ha m => ?_) V le_top
    have hker : a ∈ RingHom.ker (I.subschemeι.app V).hom := ha
    rw [I.ker_subschemeι_app ⟨V, hV⟩] at hker
    exact mem_annihilatorIdeal.1 hker m
  exact ⟨(asIso (adj.unit.app F)).symm⟩

end Support

end

end GroundTheory.Arith.SchemeCoh
end

