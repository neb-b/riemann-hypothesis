module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.RealPlaces.InducedDefs
public import GroundTheory.ProfiniteCohomology.RealPlaces.ConeMap

@[expose] public section

-- bundled from GroundTheory.ProfiniteCohomology.RealPlaces.InducedDropOut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section ProdSeq

variable {k : Type u} [CommRing k] (M N : CochainComplex (ModuleCat.{u} k) ℕ)

noncomputable def prodInr : N ⟶ prodComplex M N :=
  prodLift 0 (𝟙 N)

theorem prodInr_f_hom_apply (n : ℕ) (y : N.X n) :
    ((prodInr M N).f n).hom y = ((0 : M.X n), y) :=
  rfl

noncomputable def prodSeq : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (prodInr M N) (prodFst M N)
    (HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

theorem prodSeq_shortExact : (prodSeq M N).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => {
    exact := by
      rw [ShortComplex.moduleCat_exact_iff]
      intro (p : M.X n × N.X n) hp
      exact ⟨p.2, Prod.ext hp.symm rfl⟩
    mono_f := (ModuleCat.mono_iff_injective _).2 fun _ _ h => congrArg Prod.snd h
    epi_g := (ModuleCat.epi_iff_surjective _).2 fun (x : M.X n) =>
      ⟨((x, 0) : M.X n × N.X n), rfl⟩ }

end ProdSeq

section NormClass

variable {k F' : Type u} [CommRing k] [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
  [Fintype F'] (B : Rep.{u} k F') [IsDiscreteRep B]

theorem exists_normClass_eq (hB : ∀ x ∈ B.ρ.invariants, ∃ m, B.ρ.norm m = x) (c : cohomology B 0) :
    ∃ m, normClass B m = c := by
  obtain ⟨z, rfl⟩ := homologyπ_hom_surjective (cochainsComplex B) 0 c
  obtain ⟨v, hx⟩ : ∃ v, ((cochainsComplex B).iCycles 0).hom z = zeroCochain B v := by
    refine ⟨cochainOf B (((cochainsComplex B).iCycles 0).hom z) Fin.elim0, ?_⟩
    apply cochainOf_injective
    funext σ
    rw [cochainOf_zeroCochain, Subsingleton.elim σ Fin.elim0]
  have hd : ((cochainsComplex B).d 0 1).hom (zeroCochain B v) = 0 := by
    rw [← hx]
    exact (hom_apply_hom_apply_of_comp_eq ((cochainsComplex B).iCycles_d 0 1) z).trans rfl
  have hinv : v ∈ B.ρ.invariants := fun g => by
    have h := congrFun (congrArg (cochainOf B) hd) (fun _ => g)
    rw [cochainOf_d_zeroCochain, cochainOf_zero] at h
    exact sub_eq_zero.1 h
  obtain ⟨m, hm⟩ := hB v hinv
  refine ⟨m, ?_⟩
  unfold normClass
  congr 1
  apply iCycles_hom_injective
  exact (((cochainsComplex B).i_cyclesMk _ _ _ _).trans (congrArg (zeroCochain B) hm)).trans hx.symm

end NormClass

section Tate

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (A : Rep.{u} k G) [IsDiscreteRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsDiscreteRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsDiscreteRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w)

theorem normCochains_prodInr :
    normCochains Aᵣ ≫ prodInr _ _ = prodInr _ _ ≫ tateCompactRes φ ψ A Aᵥ a Aᵣ ar := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  change ((prodInr _ _).f n).hom (((normCochains Aᵣ).f n).hom m) =
    ((tateCompactRes φ ψ A Aᵥ a Aᵣ ar).f n).hom (((prodInr _ _).f n).hom m)
  rw [prodInr_f_hom_apply, prodInr_f_hom_apply]
  refine Prod.ext ?_ ?_
  · change (0 : (piComplex fun v => cochainsComplex (Aᵥ v)).X n) = ((localRes φ A Aᵥ a).f n).hom 0
    exact (map_zero _).symm
  · change ((normCochains Aᵣ).f n).hom m =
      ((localRes ψ A Aᵣ ar).f n).hom 0 + ((normCochains Aᵣ).f n).hom m
    rw [map_zero, zero_add]

noncomputable def tateResSeqHom :
    prodSeq (cochainsComplex A) (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))) ⟶
      prodSeq (piComplex fun v => cochainsComplex (Aᵥ v)) (piComplex fun w => cochainsComplex (Aᵣ w)) where
  τ₁ := normCochains Aᵣ
  τ₂ := tateCompactRes φ ψ A Aᵥ a Aᵣ ar
  τ₃ := localRes φ A Aᵥ a
  comm₁₂ := normCochains_prodInr φ ψ A Aᵥ a Aᵣ ar
  comm₂₃ := tateCompactRes_prodFst φ ψ A Aᵥ a Aᵣ ar

theorem tateForgetShortComplex_shortExact :
    (mappingCoconeNat.mapShortComplex (tateResSeqHom φ ψ A Aᵥ a Aᵣ ar)).ShortExact :=
  mappingCoconeNat.shortExact_mapShortComplex _ (prodSeq_shortExact _ _) (prodSeq_shortExact _ _)

theorem isZero_homology_normCocone (hcoh : ∀ w n, IsZero (cohomology (Aᵣ w) (n + 1)))
    (hnorm : ∀ w, ∀ x ∈ (Aᵣ w).ρ.invariants, ∃ m, (Aᵣ w).ρ.norm m = x) (n : ℕ) :
    IsZero ((mappingCoconeNat (normCochains Aᵣ)).homology (n + 1)) := by
  have hK : IsZero ((degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).homology (n + 1)) :=
    isZero_degZeroComplex_homology_succ _ n
  have hepi : Epi (HomologicalComplex.homologyMap (normCochains Aᵣ) n) := by
    cases n with
    | zero =>
      rw [ModuleCat.epi_iff_surjective]
      intro z
      choose m hm using fun w =>
        exists_normClass_eq (Aᵣ w) (hnorm w) ((localCohomologyIso Aᵣ 0).hom.hom z w)
      refine ⟨(degZeroHomologyIso (ModuleCat.of k (∀ w, Aᵣ w))).inv.hom
        (show ModuleCat.of k (∀ w, Aᵣ w) from m), ?_⟩
      have hinj : Function.Injective (localCohomologyIso Aᵣ 0).hom.hom :=
        (ModuleCat.mono_iff_injective _).1 inferInstance
      apply hinj
      rw [localCohomologyIso_homologyMap_normCochains, hom_apply_hom_apply_of_comp_eq
        (Iso.inv_hom_id (degZeroHomologyIso (ModuleCat.of k (∀ w, Aᵣ w))))]
      exact funext hm
    | succ n =>
      have hsub : ∀ w, Subsingleton (cohomology (Aᵣ w) (n + 1)) := fun w =>
        ModuleCat.isZero_iff_subsingleton.1 (hcoh w n)
      have hL : IsZero ((piComplex fun w => cochainsComplex (Aᵣ w)).homology (n + 1)) :=
        IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) (localCohomologyIso Aᵣ (n + 1))
      exact ⟨fun _ _ _ => hL.eq_of_src _ _⟩
  have hex := mappingCoconeNat.homology_exact₂ (normCochains Aᵣ) n
  have hδ : mappingCoconeNat.homologyδ (normCochains Aᵣ) n = 0 :=
    (cancel_epi (HomologicalComplex.homologyMap (normCochains Aᵣ) n)).1
      ((mappingCoconeNat.homologyMap_homologyδ _ n).trans comp_zero.symm)
  exact hex.isZero_X₂ hδ (hK.eq_of_tgt _ _)

theorem isIso_tateForget (hcoh : ∀ w n, IsZero (cohomology (Aᵣ w) (n + 1)))
    (hnorm : ∀ w, ∀ x ∈ (Aᵣ w).ρ.invariants, ∃ m, (Aᵣ w).ρ.norm m = x) (n : ℕ) :
    IsIso (tateForget φ ψ A Aᵥ a Aᵣ ar (n + 1)) := by
  have hS := tateForgetShortComplex_shortExact φ ψ A Aᵥ a Aᵣ ar
  have h0 := isZero_homology_normCocone Aᵣ hcoh hnorm n
  have h1 := isZero_homology_normCocone Aᵣ hcoh hnorm (n + 1)
  have hmono := (hS.homology_exact₂ (n + 1)).mono_g (h0.eq_of_src _ _)
  have hepi := (hS.homology_exact₃ (n + 1) (n + 1 + 1) rfl).epi_f (h1.eq_of_tgt _ _)
  exact @isIso_of_mono_of_epi _ _ _ _ _ (tateForget φ ψ A Aᵥ a Aᵣ ar (n + 1)) hmono hepi

noncomputable def tateForgetIso (hcoh : ∀ w n, IsZero (cohomology (Aᵣ w) (n + 1)))
    (hnorm : ∀ w, ∀ x ∈ (Aᵣ w).ρ.invariants, ∃ m, (Aᵣ w).ρ.norm m = x) (n : ℕ) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar (n + 1) ≅ compactCohomology φ A Aᵥ a (n + 1) :=
  @asIso _ _ _ _ (tateForget φ ψ A Aᵥ a Aᵣ ar (n + 1))
    (isIso_tateForget φ ψ A Aᵥ a Aᵣ ar hcoh hnorm n)

end Tate

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.RealPlaces.VanishingCriterion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section Tate

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

section General

variable (A : Rep.{u} k G) [IsDiscreteRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsDiscreteRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsDiscreteRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w)

theorem tateCompactCohomology_eq_zero_of_surjective_of_injective (n : ℕ)
    (hs : Function.Surjective (tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1)).hom)
    (hi : Function.Injective (tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 2)).hom)
    (x : tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar (n + 2)) : x = 0 := by
  have h1 : (tateToGlobal φ ψ A Aᵥ a Aᵣ ar (n + 2)).hom x = 0 := by
    apply hi
    rw [map_zero]
    exact hom_apply_hom_apply_of_comp_eq (tateToGlobal_tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1)) x
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (tateCompactCohomology_exact_compact φ ψ A Aᵥ a Aᵣ ar (n + 1)) x h1
  obtain ⟨y, rfl⟩ := hs z
  rw [← hz]
  exact hom_apply_hom_apply_of_comp_eq (tateGlobalToLocal_tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar n) y

theorem injective_tateGlobalToLocal_of_eq_zero (n : ℕ)
    (h : ∀ x : tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar (n + 1), x = 0) :
    Function.Injective (tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1)).hom := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨x, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (tateCompactCohomology_exact_global φ ψ A Aᵥ a Aᵣ ar n) y hy
  rw [h x]
  exact map_zero _

theorem surjective_tateGlobalToLocal_of_eq_zero (n : ℕ)
    (h : ∀ x : tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar (n + 2), x = 0) :
    Function.Surjective (tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar (n + 1)).hom := fun z =>
  (ShortComplex.moduleCat_exact_iff _).1 (tateCompactCohomology_exact_local φ ψ A Aᵥ a Aᵣ ar n) z
    (h _)


omit [∀ w, Fintype (F w)] in
theorem injective_tateGlobalToLocal_iff (n : ℕ) (hv : ∀ v, Subsingleton (cohomology (Aᵥ v) n)) :
    Function.Injective (tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar n).hom ↔
      Function.Injective (globalToLocal ψ A Aᵣ ar n).hom := by
  constructor
  · intro h x y hxy
    refine h (Prod.ext (funext fun v => Subsingleton.elim _ _) ?_)
    exact hxy
  · intro h x y hxy
    exact h (congrArg Prod.snd hxy)


omit [∀ w, Fintype (F w)] in
theorem surjective_tateGlobalToLocal_iff (n : ℕ) (hv : ∀ v, Subsingleton (cohomology (Aᵥ v) n)) :
    Function.Surjective (tateGlobalToLocal φ ψ A Aᵥ a Aᵣ ar n).hom ↔
      Function.Surjective (globalToLocal ψ A Aᵣ ar n).hom := by
  constructor
  · intro h z
    obtain ⟨x, hx⟩ := h (0, z)
    exact ⟨x, congrArg Prod.snd hx⟩
  · intro h z
    obtain ⟨x, hx⟩ := h z.2
    exact ⟨x, Prod.ext (funext fun v => Subsingleton.elim _ _) hx⟩

end General

section Res

attribute [local instance 2000] Rep.hV2

theorem eq_zero_tateCompactCohomologyRes_of_shortExact {S : ShortComplex (Rep.{u} k G)}
    [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] (hS : S.ShortExact) (n : ℕ)
    (h₁ : ∀ x : tateCompactCohomologyRes φ ψ S.X₁ n, x = 0)
    (h₃ : ∀ x : tateCompactCohomologyRes φ ψ S.X₃ n, x = 0)
    (x : tateCompactCohomologyRes φ ψ S.X₂ n) : x = 0 := by
  have : ∀ v, IsDiscreteRep (S.map (Rep.resFunctor (φ v).toMonoidHom)).X₁ := fun v =>
    IsDiscreteRep.res (continuous_toMonoidHom (φ v)) _
  have : ∀ v, IsDiscreteRep (S.map (Rep.resFunctor (φ v).toMonoidHom)).X₂ := fun v =>
    IsDiscreteRep.res (continuous_toMonoidHom (φ v)) _
  have : ∀ v, IsDiscreteRep (S.map (Rep.resFunctor (φ v).toMonoidHom)).X₃ := fun v =>
    IsDiscreteRep.res (continuous_toMonoidHom (φ v)) _
  have : ∀ w, IsDiscreteRep (S.map (Rep.resFunctor (ψ w).toMonoidHom)).X₁ := fun w =>
    IsDiscreteRep.res (continuous_toMonoidHom (ψ w)) _
  have : ∀ w, IsDiscreteRep (S.map (Rep.resFunctor (ψ w).toMonoidHom)).X₂ := fun w =>
    IsDiscreteRep.res (continuous_toMonoidHom (ψ w)) _
  have : ∀ w, IsDiscreteRep (S.map (Rep.resFunctor (ψ w).toMonoidHom)).X₃ := fun w =>
    IsDiscreteRep.res (continuous_toMonoidHom (ψ w)) _
  have hE := tateCompactCohomology_exact₂ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom))
    (fun _ => 𝟙 _) (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)
    (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hS) n
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 hE x (h₃ _)
  rw [← hy, h₁ y]
  exact map_zero _

theorem tateCompactCohomologyMap_eq_id {A : Rep.{u} k G} [IsDiscreteRep A] {Aᵥ : ∀ v, Rep.{u} k (H v)}
    [∀ v, IsDiscreteRep (Aᵥ v)] {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v}
    {Aᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Aᵣ w)] {ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w}
    (g : A ⟶ A) (gᵥ : ∀ v, Aᵥ v ⟶ Aᵥ v) (gᵣ : ∀ w, Aᵣ w ⟶ Aᵣ w)
    (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v).toMonoidHom).map g ≫ a v)
    (hgr : ∀ w, ar w ≫ gᵣ w = (Rep.resFunctor (ψ w).toMonoidHom).map g ≫ ar w)
    (e : g = 𝟙 A) (eᵥ : ∀ v, gᵥ v = 𝟙 _) (eᵣ : ∀ w, gᵣ w = 𝟙 _) (n : ℕ) :
    tateCompactCohomologyMap φ ψ g gᵥ gᵣ hg hgr n = 𝟙 _ := by
  subst e
  obtain rfl : gᵥ = fun v => 𝟙 (Aᵥ v) := funext eᵥ
  obtain rfl : gᵣ = fun w => 𝟙 (Aᵣ w) := funext eᵣ
  exact tateCompactCohomologyMap_id φ ψ n

theorem eq_zero_tateCompactCohomologyRes_of_retract {A B : Rep.{u} k G} [IsDiscreteRep A]
    [IsDiscreteRep B] (i : A ⟶ B) (p : B ⟶ A) (hip : i ≫ p = 𝟙 A) (n : ℕ)
    (hB : ∀ x : tateCompactCohomologyRes φ ψ B n, x = 0) (x : tateCompactCohomologyRes φ ψ A n) :
    x = 0 := by
  have hi : ∀ v, 𝟙 (Rep.res (φ v).toMonoidHom A) ≫ (Rep.resFunctor (φ v).toMonoidHom).map i =
      (Rep.resFunctor (φ v).toMonoidHom).map i ≫ 𝟙 _ := fun _ =>
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hir : ∀ w, 𝟙 (Rep.res (ψ w).toMonoidHom A) ≫ (Rep.resFunctor (ψ w).toMonoidHom).map i =
      (Rep.resFunctor (ψ w).toMonoidHom).map i ≫ 𝟙 _ := fun _ =>
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hp : ∀ v, 𝟙 (Rep.res (φ v).toMonoidHom B) ≫ (Rep.resFunctor (φ v).toMonoidHom).map p =
      (Rep.resFunctor (φ v).toMonoidHom).map p ≫ 𝟙 _ := fun _ =>
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hpr : ∀ w, 𝟙 (Rep.res (ψ w).toMonoidHom B) ≫ (Rep.resFunctor (ψ w).toMonoidHom).map p =
      (Rep.resFunctor (ψ w).toMonoidHom).map p ≫ 𝟙 _ := fun _ =>
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hcomp := tateCompactCohomologyMap_comp φ ψ i (fun v => (Rep.resFunctor (φ v).toMonoidHom).map i)
    (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map i) hi hir p
    (fun v => (Rep.resFunctor (φ v).toMonoidHom).map p) (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map p)
    hp hpr n
  rw [tateCompactCohomologyMap_eq_id φ ψ _ _ _ _ _ hip
    (fun v => by rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id])
    (fun w => by rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id])] at hcomp
  have hx := congrArg (fun f => f.hom x) hcomp
  change x = _ at hx
  rw [hx]
  change (tateCompactCohomologyMap φ ψ p _ _ hp hpr n).hom
    ((tateCompactCohomologyMap φ ψ i _ _ hi hir n).hom x) = 0
  rw [hB ((tateCompactCohomologyMap φ ψ i _ _ hi hir n).hom x)]
  exact map_zero _

end Res

end Tate

end GroundTheory.ProfCoh
end

