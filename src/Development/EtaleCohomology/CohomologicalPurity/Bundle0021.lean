module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0013
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0016
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0015

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafExcSpPfCone
section
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

open GlobalTheory.EtC in
theorem leafConeCok : LeafConeCok := by
  intro R _ K L K' L' f f' a b comm hf hf' hi
  have hm : Mono f := HomologicalComplex.mono_of_mono_f _ hf
  have hm' : Mono f' := HomologicalComplex.mono_of_mono_f _ hf'
  let S₁ := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let S₂ := ShortComplex.mk f' (cokernel.π f') (cokernel.condition f')
  have h₁ : S₁.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)) hm inferInstance
  have h₂ : S₂.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f')) hm' inferInstance
  let τ : S₁ ⟶ S₂ := { τ₁ := a, τ₂ := b, τ₃ := cokernel.map f f' a b comm, comm₁₂ := comm.symm, comm₂₃ := by simp [S₁, S₂] }
  have iso3 : IsIso (cokernel.map f f' a b comm) := by
    have : ∀ n, IsIso ((cokernel.map f f' a b comm).f n) := by
      intro n
      have e₁ := (h₁.map_of_exact (HomologicalComplex.eval _ _ n)).gIsCokernel
      have e₂ := (h₂.map_of_exact (HomologicalComplex.eval _ _ n)).gIsCokernel
      let i₁ : cokernel (f.f n) ≅ (cokernel f).X n := (colimit.isColimit _).coconePointUniqueUpToIso e₁
      let i₂ : cokernel (f'.f n) ≅ (cokernel f').X n := (colimit.isColimit _).coconePointUniqueUpToIso e₂
      have key : (cokernel.map f f' a b comm).f n = i₁.inv ≫ cokernel.map _ _ _ _ (sqw comm n) ≫ i₂.hom := by
        rw [Iso.eq_inv_comp]
        refine (cancel_epi (cokernel.π (f.f n))).1 ?_
        have p₁ : cokernel.π (f.f n) ≫ i₁.hom = (cokernel.π f).f n :=
          (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom e₁ WalkingParallelPair.one
        have p₂ : cokernel.π (f'.f n) ≫ i₂.hom = (cokernel.π f').f n :=
          (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom e₂ WalkingParallelPair.one
        rw [← Category.assoc, p₁, cokernel.π_desc_assoc, Category.assoc, p₂, ← HomologicalComplex.comp_f,
          ← HomologicalComplex.comp_f, cokernel.π_desc]
      rw [key]; infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  have q1 := CochainComplex.mappingCone.quasiIso_descShortComplex h₁
  have q2 := CochainComplex.mappingCone.quasiIso_descShortComplex h₂
  have e := CochainComplex.mappingCone.map_descShortComplex S₁ S₂ τ
  have : QuasiIso (CochainComplex.mappingCone.map f f' a b comm ≫ CochainComplex.mappingCone.descShortComplex S₂) := by
    rw [show CochainComplex.mappingCone.map f f' a b comm = CochainComplex.mappingCone.map S₁.f S₂.f τ.τ₁ τ.τ₂ τ.comm₁₂.symm from rfl, e]
    infer_instance
  exact (quasiIso_iff_comp_right _ (CochainComplex.mappingCone.descShortComplex S₂)).1 this

theorem etaleSplitExcision_of_mono_cokernel_relative (hM : LeafChainsMono) (hK : LeafCokIso) (hR : LeafHsRel) : LateralTheory.CohomologicalPurity.Thom.LeafExcSp :=
  leafExcSp_of' hM hK leafConeCok hR

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafFreeCokPfSurj
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

variable {R : Type} [CommRing R]

theorem imageSieve_add' {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G) {T : Scheme.{0}}
    (s₁ s₂ : G.obj (op T)) :
    Presheaf.imageSieve f s₁ ⊓ Presheaf.imageSieve f s₂ ≤ Presheaf.imageSieve f (s₁ + s₂) := by
  rintro V g ⟨⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩
  exact ⟨t₁ + t₂, by rw [map_add (f := _), map_add (f := _), h₁, h₂]⟩

theorem imageSieve_smul' {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G) {T : Scheme.{0}}
    (r : ULift.{1} R) (s : G.obj (op T)) :
    Presheaf.imageSieve f s ≤ Presheaf.imageSieve f (r • s) := by
  rintro V g ⟨t, h⟩
  exact ⟨r • t, by rw [map_smul, map_smul, h]⟩

theorem imageSieve_zero' {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G) {T : Scheme.{0}} :
    Presheaf.imageSieve f (0 : G.obj (op T)) = ⊤ := by
  ext V g
  simp only [Sieve.top_apply, iff_true]
  exact ⟨0, by rw [map_zero, map_zero]⟩

theorem pcok_π_apply (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (w : i' ≫ b = a ≫ i) (V : Scheme.{0}ᵒᵖ) (m : ((freeP R).obj B').obj V) :
    (pcok R i' i a b w).app V ((cokernel.π ((freeP R).map i')).app V m) =
      (cokernel.π ((freeP R).map i)).app V (((freeP R).map b).app V m) := by
  have e : cokernel.π ((freeP R).map i') ≫ pcok R i' i a b w = (freeP R).map b ≫ cokernel.π _ := by
    simp [pcok]
  have := ConcreteCategory.congr_hom (NatTrans.congr_app e V) m
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using this

theorem π_freeP_apply (R : Type) [CommRing R] {A B : PSh} (i : A ⟶ B) (V : Scheme.{0}ᵒᵖ)
    (m : ((freeP R).obj A).obj V) :
    (cokernel.π ((freeP R).map i)).app V (((freeP R).map i).app V m) = 0 := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (cokernel.condition ((freeP R).map i)) V) m
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
  rw [this]; rfl

theorem freePresheaf_map_freeMk (R : Type) [CommRing R] {A B : PSh} (i : A ⟶ B) (V : Scheme.{0}ᵒᵖ) (x : A.obj V) :
    ((freeP R).map i).app V (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (i.app V x)) := by
  exact ModuleCat.free_map_apply _ _

theorem freePresheaf_obj_map_freeMk (R : Type) [CommRing R] (B : PSh) {V W : Scheme.{0}ᵒᵖ} (g : V ⟶ W) (x : B.obj V) :
    ((freeP R).obj B).map g (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (B.map g x)) := by
  exact ModuleCat.free_map_apply _ _

theorem π_app_surj (R : Type) [CommRing R] {A B : PSh} (i : A ⟶ B) (V : Scheme.{0}ᵒᵖ) :
    Function.Surjective ((cokernel.π ((freeP R).map i)).app V) := by
  have : Epi ((cokernel.π ((freeP R).map i)).app V) := inferInstance
  exact (ModuleCat.epi_iff_surjective _).1 this

theorem exists_finset_adjoin_laurent_preimage (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (w : i' ≫ b = a ≫ i)
    (h2 : ∀ (T : Scheme.{0}) (y : B.obj (op T)), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      (∃ x : A.obj (op V), i.app (op V) x = B.map g.op y) ∨ ∃ y' : B'.obj (op V), b.app (op V) y' = B.map g.op y)
    (T : Scheme.{0}) (v : ((freeP R).obj B).obj (op T)) :
    Presheaf.imageSieve (pcok R i' i a b w) ((cokernel.π ((freeP R).map i)).app (op T) v) ∈
      Scheme.etaleTopology T := by
  let J := Scheme.etaleTopology.{0}
  let N : Submodule (ULift.{1} R) (((freeP R).obj B).obj (op T)) :=
    { carrier := {v | Presheaf.imageSieve (pcok R i' i a b w) ((cokernel.π ((freeP R).map i)).app (op T) v) ∈ J T}
      zero_mem' := by
        simp only [Set.mem_setOf_eq]; rw [map_zero, imageSieve_zero']; exact J.top_mem T
      add_mem' := fun {v₁ v₂} h₁ h₂ => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_add (f := _)]; exact J.superset_covering (imageSieve_add' _ _ _) (J.intersection_covering h₁ h₂)
      smul_mem' := fun r v h => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_smul]; exact J.superset_covering (imageSieve_smul' _ _ _) h }
  have gen : ∀ x, ModuleCat.freeMk x ∈ N := by
    rintro ⟨y⟩
    show Presheaf.imageSieve _ _ ∈ J T
    obtain ⟨S, hS, hS'⟩ := h2 T y
    refine J.superset_covering ?_ hS
    intro V g hg
    have nat := NatTrans.naturality_apply (cokernel.π ((freeP R).map i)) g.op (ModuleCat.freeMk (ULift.up y))
    rcases hS' g hg with ⟨x₀, hx₀⟩ | ⟨y', hy'⟩
    · refine ⟨0, ?_⟩
      rw [map_zero]; erw [← nat]
      rw [freePresheaf_obj_map_freeMk]; erw [← hx₀]; rw [← freePresheaf_map_freeMk R i (op V) x₀]; exact (π_freeP_apply R i (op V) _).symm
    · refine ⟨_, (pcok_π_apply R i' i a b w (op V) (ModuleCat.freeMk (ULift.up y'))).trans ?_⟩
      rw [freePresheaf_map_freeMk R b (op V) y']; erw [hy', ← freePresheaf_obj_map_freeMk R B g.op y]; exact nat
  show v ∈ N
  induction v using Finsupp.induction_linear with
  | zero => exact N.zero_mem
  | add v₁ v₂ h₁ h₂ => exact N.add_mem h₁ h₂
  | single x r =>
    have := N.smul_mem r (gen x)
    convert this using 1
    first
    | exact (Finsupp.smul_single_one x r).symm
    | (unfold ModuleCat.freeMk; erw [Finsupp.smul_single_one])

theorem leafFreeCokSurj : LeafFreeCokSurj := by
  intro R _ A' B' A B i' i a b w h2
  constructor
  intro T s
  obtain ⟨v, rfl⟩ := π_app_surj R i (op T) s
  exact exists_finset_adjoin_laurent_preimage R i' i a b w h2 T v

theorem LeafFreeCok_of_inj (hI : LeafFreeCokInj) : LeafFreeCok := LeafFreeCok_of leafFreeCokSurj hI

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafHKSplitPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

section Gen
variable {C : Type*} [Category C] [Abelian C] {A B D Q I : CochainComplex C ℤ}

def hsCok (f : A ⟶ B) (l r : B ⟶ D) (hpo : IsPushout f f l r) (p : D ⟶ cokernel f)
    (hl : l ≫ p = cokernel.π f) (hr : r ≫ p = 0) : IsColimit (CokernelCofork.ofπ p hr) :=
  CokernelCofork.IsColimit.ofπ p hr
    (fun g' _ => cokernel.desc f (l ≫ g') (by rw [← Category.assoc, hpo.w, Category.assoc]; simp [*]))
    (fun g' eq' => by
      apply hpo.hom_ext
      · rw [← Category.assoc, hl, cokernel.π_desc]
      · rw [← Category.assoc, hr, zero_comp, eq'])
    (fun g' eq' m hm => by
      apply (cancel_epi (cokernel.π f)).1
      rw [cokernel.π_desc, ← hl, Category.assoc, hm])

def hsCokDeg {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) (k : ℤ) :
    IsColimit ((CokernelCofork.ofπ p hr).map (HomologicalComplex.eval C _ k)) :=
  CokernelCofork.mapIsColimit _ hc _

def hsCokDeg' {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) (k : ℤ) :
    IsColimit (CokernelCofork.ofπ (f := r.f k) (p.f k) (by rw [← HomologicalComplex.comp_f, hr]; rfl)) :=
  hsCokDeg hr hc k

theorem hsFac {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) {m : ℤ}
    (z : Cochain D I m) (hz : (Cochain.ofHom r).comp z (zero_add m) = 0) :
    ∃ y : Cochain Q I m, (Cochain.ofHom p).comp y (zero_add m) = z := by
  have key : ∀ a b (h : a + m = b), r.f a ≫ z.v a b h = 0 := fun a b h => by
    have := congrArg (fun w => w.v a b h) hz
    simpa [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using this
  refine ⟨Cochain.mk (fun a b h => (CokernelCofork.IsColimit.desc' (hsCokDeg' hr hc a) (z.v a b h) (key a b h)).1), ?_⟩
  ext a b h
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
  exact (CokernelCofork.IsColimit.desc' (hsCokDeg' hr hc a) (z.v a b h) (key a b h)).2

theorem hsCancel {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hr)) {m : ℤ}
    (y₁ y₂ : Cochain Q I m) (h : (Cochain.ofHom p).comp y₁ (zero_add m) = (Cochain.ofHom p).comp y₂ (zero_add m)) :
    y₁ = y₂ := by
  ext a b hab
  have := congrArg (fun w => w.v a b hab) h
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at this
  have : Epi (p.f a) := epi_of_isColimit_cofork (hsCokDeg' hr hc a)
  exact (cancel_epi (p.f a)).1 ‹_›

theorem hsRS {r : B ⟶ D} {s : D ⟶ B} (hrs : r ≫ s = 𝟙 _) {m : ℤ} (z : Cochain B I m) :
    (Cochain.ofHom r).comp ((Cochain.ofHom s).comp z (zero_add m)) (zero_add m) = z := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, hrs]
  ext a b h
  simp

theorem hsRP {r : B ⟶ D} {p : D ⟶ Q} (hr : r ≫ p = 0) {m : ℤ} (z : Cochain Q I m) :
    (Cochain.ofHom r).comp ((Cochain.ofHom p).comp z (zero_add m)) (zero_add m) = 0 := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, hr, Cochain.ofHom_zero, Cochain.zero_comp]

theorem hsInj {r : B ⟶ D} {s : D ⟶ B} {p : D ⟶ Q} (hrs : r ≫ s = 𝟙 _) (hr : r ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ p hr)) (n : ℤ) :
    Function.Injective (cpre (Cocycle.ofHom p) I n n (zero_add n)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hx
  obtain ⟨β, hβ⟩ := hx
  change δ (n - 1) n β = (Cochain.ofHom p).comp x.1 (zero_add n) at hβ
  obtain ⟨γ, hγ⟩ := hsFac hr hc (β - (Cochain.ofHom s).comp ((Cochain.ofHom r).comp β (zero_add _)) (zero_add _))
    (by rw [Cochain.comp_sub, hsRS hrs, sub_self])
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨γ, hsCancel hr hc _ _ ?_⟩
  rw [← δ_ofHom_comp, hγ, δ_sub, δ_ofHom_comp, δ_ofHom_comp, hβ, hsRP hr, Cochain.comp_zero, sub_zero]

theorem hsExact {r : B ⟶ D} {s : D ⟶ B} {p : D ⟶ Q} (hrs : r ≫ s = 𝟙 _) (hr : r ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ p hr)) (n : ℤ) (x : CohomologyClass D I n)
    (hx : cpre (Cocycle.ofHom r) I n n (zero_add n) x = 0) :
    ∃ y, cpre (Cocycle.ofHom p) I n n (zero_add n) y = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hx
  obtain ⟨β, hβ⟩ := hx
  change δ (n - 1) n β = (Cochain.ofHom r).comp x.1 (zero_add n) at hβ
  obtain ⟨y, hy⟩ := hsFac hr hc (x.1 - δ (n - 1) n ((Cochain.ofHom s).comp β (zero_add _)))
    (by rw [Cochain.comp_sub, δ_ofHom_comp, hsRS hrs, hβ, sub_self])
  have hδ : δ n (n + 1) y = 0 := by
    apply hsCancel hr hc
    rw [← δ_ofHom_comp, hy, δ_sub, δ_δ, Cocycle.δ_eq_zero, sub_zero, Cochain.comp_zero]
  refine ⟨CohomologyClass.mk (Cocycle.mk y (n + 1) rfl hδ), ?_⟩
  change CohomologyClass.mk _ = _
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨-((Cochain.ofHom s).comp β (zero_add _)), ?_⟩
  change _ = (Cochain.ofHom p).comp y (zero_add n) - x.1
  rw [hy, δ_neg]; abel

end Gen

theorem LeafHKSplit_of : LeafHKSplit := by
  intro R _ F n A B D f l r s hpo hrs p hl hr
  have hc := hsCok f l r hpo p hl hr
  exact ⟨hsInj hrs hr hc n, fun x hx => hsExact hrs hr hc n x hx⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafHtpyMVPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def LeafFreeCov : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (U V : X.Opens),
  Epi (biprod.desc ((free R).map (yoneda.map (X.homOfLE (le_sup_left : U ≤ U ⊔ V))))
    ((free R).map (yoneda.map (X.homOfLE (le_sup_right : V ≤ U ⊔ V)))))

namespace HtpyMVPf

theorem bij_pull_iso (R : Type) [CommRing R] (F : Shv R) {A B : Spc} (e : A ≅ B) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine ⟨fun x y h => ?_, fun y => ⟨pull R e.inv F n y, ?_⟩⟩
  · have hx := pull_comp R e.inv e.hom F n x
    have hy := pull_comp R e.inv e.hom F n y
    rw [e.inv_hom_id, pull_id] at hx hy
    rw [hx, hy, h]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem eqv_of_sq (R : Type) [CommRing R] (F : Shv R) {A B A' B' : Spc} (f : A ⟶ B) (g : A' ⟶ B')
    (α : A ≅ A') (β : B ≅ B') (w : α.hom ≫ g = f ≫ β.hom) (hf : Eqv R f F) : Eqv R g F := by
  intro n
  have h1 : (pull R α.hom F n) ∘ (pull R g F n) = (pull R f F n) ∘ (pull R β.hom F n) := by
    funext x; simp only [Function.comp_apply, ← pull_comp, w]
  have h2 : Function.Bijective ((pull R α.hom F n) ∘ (pull R g F n)) := by
    rw [h1]; exact (hf n).comp (bij_pull_iso R F β n)
  exact (Function.Bijective.of_comp_iff' (bij_pull_iso R F α n) _).1 h2

theorem mono_sch {Y Z : Scheme.{0}} (f : Y ⟶ Z) [Mono f] : Mono (sch.map f) := by
  have hy : Mono (yoneda.map f) := by
    have : ∀ T, Mono ((yoneda.map f).app T) := fun T => by
      rw [mono_iff_injective]
      intro a b h
      exact (cancel_mono f).1 h
    exact NatTrans.mono_of_mono_app _
  have : ∀ n, Mono ((sch.map f).app n) := fun _ => hy
  exact NatTrans.mono_of_mono_app _

theorem sch_pres : PreservesLimitsOfShape WalkingCospan sch := by
  unfold sch; infer_instance

end HtpyMVPf

theorem LeafHtpyMV_of (hF : LeafFreeCov) : LeafHtpyMV := by
  intro a4 R _ F X' X p U V U' V' hU hV hI hS hu hv hi
  have cov : ∀ (Y : Scheme.{0}) (A B : Y.Opens),
      Cover2 R (sch.map (Y.homOfLE (le_sup_left : A ≤ A ⊔ B))) (sch.map (Y.homOfLE (le_sup_right : B ≤ A ⊔ B))) :=
    fun Y A B => ⟨HtpyMVPf.mono_sch _, HtpyMVPf.mono_sch _, fun _ => hF R Y A B⟩
  have eu : X'.homOfLE (le_sup_left : U' ≤ U' ⊔ V') ≫ p.resLE (U ⊔ V) (U' ⊔ V') hS =
      p.resLE U U' hU ≫ X.homOfLE (le_sup_left : U ≤ U ⊔ V) := by
    simp
  have ev : X'.homOfLE (le_sup_right : V' ≤ U' ⊔ V') ≫ p.resLE (U ⊔ V) (U' ⊔ V') hS =
      p.resLE V V' hV ≫ X.homOfLE (le_sup_right : V ≤ U ⊔ V) := by
    simp
  have hu' := congrArg sch.map eu
  have hv' := congrArg sch.map ev
  rw [sch.map_comp, sch.map_comp] at hu' hv'
  refine a4 R _ _ _ _ _ _ _ hu' hv' F (cov X' U' V') (cov X U V) hu hv ?_
  have := HtpyMVPf.sch_pres
  have P' := (isPullback_opens_inf_le (X := X') (le_sup_left : U' ≤ U' ⊔ V') (le_sup_right : V' ≤ U' ⊔ V')).map sch
  have P := (isPullback_opens_inf_le (X := X) (le_sup_left : U ≤ U ⊔ V) (le_sup_right : V ≤ U ⊔ V)).map sch
  refine HtpyMVPf.eqv_of_sq R F _ _ P'.isoPullback P.isoPullback ?_ hi
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc, Category.assoc,
      IsPullback.isoPullback_hom_fst, ← sch.map_comp, ← sch.map_comp]
    congr 1
    simp
  · rw [Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc, Category.assoc,
      IsPullback.isoPullback_hom_snd, ← sch.map_comp, ← sch.map_comp]
    congr 1
    simp

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafHtpyOnePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.CohomologicalPurity.Thom

namespace HtpyOnePf

theorem pull_bij_of_iso {R : Type} [CommRing R] (F : Shv R) {E E' : Spc} (a : E ⟶ E') [IsIso a] (n : ℤ) :
    Function.Bijective (pull R a F n) :=
  Function.bijective_iff_has_inverse.2 ⟨pull R (inv a) F n,
    fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id],
    fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩

theorem eqv_of_sq {R : Type} [CommRing R] (F : Shv R) {E1 E2 E3 E4 : Spc} (f : E1 ⟶ E2) (g : E3 ⟶ E4)
    (a : E3 ⟶ E1) (b : E4 ⟶ E2) [IsIso a] [IsIso b] (w : a ≫ f = g ≫ b) (hg : Eqv R g F) : Eqv R f F := by
  intro n
  have h1 : (pull R a F n) ∘ (pull R f F n) = (pull R g F n) ∘ (pull R b F n) := by
    funext x; simp only [Function.comp_apply]; rw [← pull_comp, ← pull_comp, w]
  have h2 : Function.Bijective ((pull R a F n) ∘ (pull R f F n)) := by
    rw [h1]; exact (hg n).comp (pull_bij_of_iso F b n)
  exact (Function.Bijective.of_comp_iff' (pull_bij_of_iso F a n) _).1 h2

theorem off_span (A : Type) [CommRing A] (x : A) :
    off A (Ideal.span {x}) = PrimeSpectrum.basicOpen x := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus ((Ideal.span {x} : Ideal A) : Set A))ᶜ = _
  rw [PrimeSpectrum.zeroLocus_span]; exact (PrimeSpectrum.basicOpen_eq_zeroLocus_compl x).symm

theorem off_span_C (A : Type) [CommRing A] (x : A) :
    off (Polynomial A) ((Ideal.span {x}).map Polynomial.C) = PrimeSpectrum.basicOpen (C x) := by
  rw [Ideal.map_span, Set.image_singleton]; exact off_span _ _

attribute [local instance] Polynomial.algebra in
theorem away_poly (A : Type) [CommRing A] (x : A) :
    IsLocalization.Away (C x) (Polynomial (Localization.Away x)) := by
  have := Polynomial.isLocalization (Submonoid.powers x) (Localization.Away x)
  rw [Submonoid.map_powers] at this
  exact this

theorem sq (A : Type) [CommRing A] (x : A)
    (h : off (Polynomial A) ((Ideal.span {x}).map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A (Ideal.span {x})) :
    ∃ (eT : Spec (CommRingCat.of (Polynomial (Localization.Away x))) ≅
        (off (Polynomial A) ((Ideal.span {x}).map Polynomial.C)).toScheme)
      (eB : Spec (CommRingCat.of (Localization.Away x)) ≅ (off A (Ideal.span {x})).toScheme),
      eT.hom ≫ (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h =
        Spec.map (CommRingCat.ofHom (Polynomial.C : Localization.Away x →+* _)) ≫ eB.hom := by
  letI : Algebra (Polynomial A) (Polynomial (Localization.Away x)) := Polynomial.algebra A (Localization.Away x)
  have := away_poly A x
  let jB := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))
  let jT := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial A) (Polynomial (Localization.Away x))))
  have : IsOpenImmersion jT := IsOpenImmersion.of_isLocalization (C x)
  have rB : Set.range jB = Set.range (off A (Ideal.span {x})).ι := by
    rw [Scheme.Opens.range_ι, off_span]
    exact PrimeSpectrum.localization_away_comap_range _ x
  have rT : Set.range jT = Set.range (off (Polynomial A) ((Ideal.span {x}).map Polynomial.C)).ι := by
    rw [Scheme.Opens.range_ι, off_span_C]
    exact PrimeSpectrum.localization_away_comap_range _ (C x)
  refine ⟨IsOpenImmersion.isoOfRangeEq jT _ rT, IsOpenImmersion.isoOfRangeEq jB _ rB, ?_⟩
  rw [← cancel_mono (off A (Ideal.span {x})).ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
  simp only [jT, jB, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a : 2
  simp [Polynomial.algebraMap_def]

end HtpyOnePf

theorem LeafHtpyOne_of : LeafHtpyOne := by
  intro _ c4 q _ A _ x hq h i
  obtain ⟨eT, eB, w⟩ := HtpyOnePf.sq A x h
  have hqB : IsUnit ((q : ℕ) : Localization.Away x) := by
    simpa using hq.map (algebraMap A (Localization.Away x))
  refine HtpyOnePf.eqv_of_sq _ _ (sch.map (Spec.map (CommRingCat.ofHom (Polynomial.C : Localization.Away x →+* _))))
    (sch.map eT.hom) (sch.map eB.hom) ?_ (c4 q (Localization.Away x) hqB i)
  rw [← Functor.map_comp, ← Functor.map_comp, w]

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafMLevPf
section
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

abbrev levF (n : SimplexCategoryᵒᵖ) : Spc ⥤ Spc := (evaluation SimplexCategoryᵒᵖ PSh).obj n ⋙ disc

theorem LeafMLev_of : LeafMLev := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro P' P φ n
  let F := levF n
  have hc : F.map (P'.hom ≫ φ.right) = F.map P'.hom ≫ F.map φ.right := F.map_comp _ _
  let a : disc.obj ((MM φ).obj n) ≅ MM ((lev n).map φ) :=
    (PreservesPushout.iso F P'.hom (P'.hom ≫ φ.right)).symm ≪≫ pushout.congrHom rfl hc
  let b : disc.obj ((dbl P).obj n) ≅ dbl ((lev n).obj P) :=
    (PreservesPushout.iso F P.hom P.hom).symm
  refine ⟨a, b, ?_⟩
  rw [← Iso.inv_comp_eq]
  change (pushout.congrHom rfl hc).inv ≫ (PreservesPushout.iso F P'.hom (P'.hom ≫ φ.right)).hom ≫ F.map (gM φ) ≫
    (PreservesPushout.iso F P.hom P.hom).inv = gM ((lev n).map φ)
  apply pushout.hom_ext
  · rw [pushout.congrHom_inv, pushout.inl_desc_assoc, Category.id_comp]
    erw [PreservesPushout.inl_iso_hom_assoc, ← F.map_comp_assoc, pushout.inl_desc, pushout.inl_desc, F.map_comp_assoc]
    erw [PreservesPushout.inl_iso_inv]
    rfl
  · rw [pushout.congrHom_inv, pushout.inr_desc_assoc, Category.id_comp]
    erw [PreservesPushout.inr_iso_hom_assoc, ← F.map_comp_assoc, pushout.inr_desc, pushout.inr_desc]
    erw [PreservesPushout.inr_iso_inv]
    rfl

end LateralTheory.CohomologicalPurity.TubeCut
end
end

