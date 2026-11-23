module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0021
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0020
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0023

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafExcSpPfMono
section
noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem free_mono (R : Type) [CommRing R] {A B : PSh} (g : A ⟶ B) [Mono g] : Mono ((free R).map g) := by
  have : Mono ((freeP R).map g) := by
    rw [NatTrans.mono_iff_mono_app]
    intro U
    have hg : Function.Injective (g.app U) := (mono_iff_injective _).1 (inferInstance)
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map (g.app U))).hom
    have hu : Function.Injective (uliftFunctor.{1}.map (g.app U)) := by
      intro a b h
      exact ULift.ext (hg (congrArg ULift.down h))
    exact Finsupp.mapDomain_injective hu
  change Mono ((presheafToSheaf _ _).map ((freeP R).map g))
  infer_instance

theorem leafChainsMono : LeafChainsMono := by
  intro R _ E' E f hf n
  by_cases hn : ∃ p : ℕ, -(p : ℤ) = n
  · obtain ⟨p, rfl⟩ := hn
    have h : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl
    change Mono ((HomologicalComplex.extendMap ((chainsN R).map f) _).f _)
    rw [HomologicalComplex.extendMap_f _ _ h]
    have : Mono (f.app (op (SimplexCategory.mk p))) := by
      rw [NatTrans.mono_iff_mono_app] at hf
      exact hf _
    have : Mono (((chainsN R).map f).f p) := by
      change Mono ((AlgebraicTopology.AlternatingFaceMapComplex.map _).f p)
      rw [AlgebraicTopology.AlternatingFaceMapComplex.map_f]
      exact free_mono R _
    infer_instance
  · push Not at hn
    refine ⟨fun g h _ => ?_⟩
    exact (HomologicalComplex.isZero_extend_X _ _ _ (fun i => hn i)).eq_of_tgt _ _

theorem etaleSplitExcision_of_cokernel_relative (hK : LeafCokIso) (hR : LeafHsRel) : LateralTheory.CohomologicalPurity.Thom.LeafExcSp :=
  etaleSplitExcision_of_mono_cokernel_relative leafChainsMono hK hR

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafFreeCokInjPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
namespace LateralTheory.CohomologicalPurity

theorem exact_app_of_π {R : Type} [CommRing R] {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G)
    (V : Scheme.{0}ᵒᵖ) (m : G.obj V) (hm : (cokernel.π f).app V m = 0) : ∃ n, f.app V n = m := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.Exact := S.exact_of_g_is_cokernel (cokernelIsCokernel f)
  have h2 := hS.map ((evaluation _ _).obj V)
  rw [ShortComplex.moduleCat_exact_iff] at h2
  exact h2 m hm

theorem mapDomain_apply_eq_sum {α β M : Type*} [AddCommMonoid M] [DecidableEq β] (v : α →₀ M) (f : α → β) (t : β) :
    Finsupp.mapDomain f v t = ∑ a ∈ v.support with f a = t, v a := by
  classical
  unfold Finsupp.mapDomain
  rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.single_apply]

theorem core {α β γ M : Type*} [AddCommMonoid M] (v : α →₀ M) (f : α → β) (r : α → γ)
    (Q : β → Prop) (P : γ → Prop)
    (hv : ∀ t, ¬ Q t → Finsupp.mapDomain f v t = 0)
    (hQ : ∀ a, Q (f a) → P (r a))
    (hP : ∀ a₁ a₂, f a₁ = f a₂ → P (r a₁) → P (r a₂))
    (h : ∀ a₁ ∈ v.support, ∀ a₂ ∈ v.support, f a₁ = f a₂ → r a₁ = r a₂ ∨ P (r a₁)) :
    ∀ z, ¬ P z → Finsupp.mapDomain r v z = 0 := by
  classical
  intro z hz
  rw [mapDomain_apply_eq_sum]
  set s' := v.support.filter (fun a => r a = z)
  rw [← Finset.sum_fiberwise_of_maps_to (s := s') (t := s'.image f) (g := f)
    (fun a ha => Finset.mem_image_of_mem f ha)]
  refine Finset.sum_eq_zero fun t ht => ?_
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 ht
  have ha₀' := Finset.mem_filter.1 ha₀
  have hQ0 : ¬ Q (f a₀) := fun hq => hz (ha₀'.2 ▸ hQ a₀ hq)
  have e : (s'.filter fun a => f a = f a₀) = v.support.filter (fun a => f a = f a₀) := by
    ext a
    simp only [s', Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rcases h a h1 a₀ ha₀'.1 h3 with e | p
      · rw [e, ha₀'.2]
      · exact absurd (ha₀'.2 ▸ hP a a₀ h3 p) hz
  rw [e]
  have := mapDomain_apply_eq_sum v f (f a₀)
  rw [hv _ hQ0] at this
  convert this.symm

theorem exists_covering_finset {T : Scheme.{0}} {ι : Type*} (s : Finset ι)
    (Pr : ι → ∀ ⦃V : Scheme.{0}⦄, (V ⟶ T) → Prop)
    (hPr : ∀ p ∈ s, ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g → Pr p g) :
    ∃ S ∈ Scheme.etaleTopology T, ∀ p ∈ s, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g → Pr p g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, Scheme.etaleTopology.top_mem T, by simp⟩
  | insert q s hq ih =>
    obtain ⟨S₁, h₁, H₁⟩ := ih (fun p hp => hPr p (Finset.mem_insert_of_mem hp))
    obtain ⟨S₂, h₂, H₂⟩ := hPr q (Finset.mem_insert_self q s)
    refine ⟨S₁ ⊓ S₂, Scheme.etaleTopology.intersection_covering h₁ h₂, ?_⟩
    intro p hp V g hg
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact H₂ g hg.2
    · exact H₁ p hp g hg.1

theorem mem_range_mapDomain {α β M : Type*} [AddCommMonoid M] (u : α → β) (w : β →₀ M)
    (hw : ∀ z, (¬ ∃ x, u x = z) → w z = 0) : ∃ n : α →₀ M, Finsupp.mapDomain u n = w := by
  have hmem : w ∈ Finsupp.supported M ℕ (u '' Set.univ) := by
    rw [Finsupp.mem_supported]
    intro z hz
    by_contra hc
    exact (Finsupp.mem_support_iff.1 hz) (hw z (fun ⟨x, hx⟩ => hc ⟨x, trivial, hx⟩))
  rw [← Finsupp.lmapDomain_supported] at hmem
  obtain ⟨n, _, hn⟩ := hmem
  exact ⟨n, hn⟩

theorem leafFreeCokInj : LeafFreeCokInj := by
  intro R _ A' B' A B i' i a b w h1 h3
  have key : ∀ (T : Scheme.{0}) (z : (cokernel ((freeP R).map i')).obj (op T)),
      (pcok R i' i a b w).app (op T) z = 0 → Presheaf.equalizerSieve z 0 ∈ Scheme.etaleTopology T := by
    intro T z hz
    obtain ⟨v, rfl⟩ := π_app_surj R i' (op T) z
    rw [pcok_π_apply] at hz
    obtain ⟨n, hn⟩ := exact_app_of_π _ _ _ hz
    have hn' : Finsupp.mapDomain (fun x : ULift.{1} (A.obj (op T)) => ULift.up (i.app (op T) x.down)) n =
        Finsupp.mapDomain (fun x : ULift.{1} (B'.obj (op T)) => ULift.up (b.app (op T) x.down)) v := hn
    let Pr : (ULift.{1} (B'.obj (op T)) × ULift.{1} (B'.obj (op T))) → ∀ ⦃V : Scheme.{0}⦄, (V ⟶ T) → Prop :=
      fun p V g => b.app (op T) p.1.down = b.app (op T) p.2.down →
        B'.map g.op p.1.down = B'.map g.op p.2.down ∨
          ∃ x : A.obj (op V), i.app (op V) x = b.app (op V) (B'.map g.op p.1.down)
    obtain ⟨S, hS, HS⟩ := exists_covering_finset (v.support ×ˢ v.support) Pr (by
      intro p _
      by_cases he : b.app (op T) p.1.down = b.app (op T) p.2.down
      · obtain ⟨S, hS, H⟩ := h3 T p.1.down p.2.down he
        exact ⟨S, hS, fun V g hg _ => H g hg⟩
      · exact ⟨⊤, Scheme.etaleTopology.top_mem T, fun V g _ he' => absurd he' he⟩)
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V g hg
    show (cokernel ((freeP R).map i')).map g.op _ = (cokernel ((freeP R).map i')).map g.op 0
    rw [map_zero, ← NatTrans.naturality_apply]
    have hcore := core v (fun x : ULift.{1} (B'.obj (op T)) => (ULift.up.{1} (b.app (op T) x.down) : ULift.{1} (B.obj (op T))))
      (fun x : ULift.{1} (B'.obj (op T)) => ULift.up (B'.map g.op x.down))
      (fun t : ULift.{1} (B.obj (op T)) => ∃ x, i.app (op T) x = t.down) (fun z => ∃ x', i'.app (op V) x' = z.down)
      (by
        intro t ht
        have := Finsupp.mapDomain_notin_range n t (by
          rintro ⟨x, hx⟩
          exact ht ⟨x.down, congrArg ULift.down hx⟩)
        exact (DFunLike.congr_fun hn' t).symm.trans this)
      (by
        rintro a₀ ⟨x, hx⟩
        obtain ⟨x', hx'⟩ := h1 T a₀.down x hx
        exact ⟨A'.map g.op x', by rw [NatTrans.naturality_apply, hx']⟩)
      (by
        rintro a₁ a₂ he ⟨x', hx'⟩
        have he' : b.app (op T) a₁.down = b.app (op T) a₂.down := congrArg ULift.down he
        refine h1 V (B'.map g.op a₂.down) (a.app (op V) x') ?_
        have := ConcreteCategory.congr_hom (NatTrans.congr_app w (op V)) x'
        simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
        rw [← this, hx', NatTrans.naturality_apply, NatTrans.naturality_apply, he'])
      (by
        intro a₁ ha₁ a₂ ha₂ he
        rcases HS (a₁, a₂) (Finset.mem_product.2 ⟨ha₁, ha₂⟩) g hg (congrArg ULift.down he) with e | ⟨x, hx⟩
        · left; exact congrArg ULift.up e
        · right; exact h1 V _ x hx)
    obtain ⟨n', hn''⟩ := mem_range_mapDomain (fun x : ULift.{1} (A'.obj (op V)) => ULift.up (i'.app (op V) x.down)) _
      (fun z hz => hcore z (fun ⟨x', hx'⟩ => hz ⟨ULift.up x', congrArg ULift.up hx' |>.trans rfl⟩))
    have e2 : ((freeP R).obj B').map g.op v = ((freeP R).map i').app (op V) n' := hn''.symm
    rw [e2]
    exact π_freeP_apply R i' (op V) n'
  constructor
  intro X x y hxy
  cases X with | op T =>
  refine Scheme.etaleTopology.superset_covering ?_ (key T (x - y) (by rw [map_sub, hxy, sub_self]))
  intro V g hg
  have hg' : (cokernel ((freeP R).map i')).map g.op (x - y) = (cokernel ((freeP R).map i')).map g.op 0 := hg
  rw [map_sub, map_zero, sub_eq_zero] at hg'
  exact hg'

theorem LeafFreeCokInj_of : LeafFreeCokInj := leafFreeCokInj

end LateralTheory.CohomologicalPurity
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafFreeCovPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.FreeCovPf

variable {X : Scheme.{0}} (U V : X.Opens)

def pieces : Bool → Scheme.{0}
  | true => U.toScheme
  | false => V.toScheme

def incl : (b : Bool) → pieces U V b ⟶ (U ⊔ V : X.Opens).toScheme
  | true => X.homOfLE le_sup_left
  | false => X.homOfLE le_sup_right

theorem cover_mem :
    Sieve.ofArrows (pieces U V) (incl U V) ∈ Scheme.etaleTopology.{0} (U ⊔ V : X.Opens).toScheme := by
  apply Precoverage.generate_mem_toGrothendieck
  refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun x => ?_, fun b => ?_⟩
  · have hx : x.1 ∈ U ⊔ V := x.2
    rcases (TopologicalSpace.Opens.mem_sup.1 hx) with h | h
    · exact ⟨true, ⟨⟨x.1, h⟩, Subtype.ext (Scheme.homOfLE_apply (le_sup_left : U ≤ U ⊔ V) _)⟩⟩
    · exact ⟨false, ⟨⟨x.1, h⟩, Subtype.ext (Scheme.homOfLE_apply (le_sup_right : V ≤ U ⊔ V) _)⟩⟩
  · cases b
    · exact (inferInstance : Etale (X.homOfLE (le_sup_right : V ≤ U ⊔ V)))
    · exact (inferInstance : Etale (X.homOfLE (le_sup_left : U ≤ U ⊔ V)))

theorem sec_zero (R : Type) [CommRing R] (Zs : Shv R) (z : Zs.obj.obj (op (U ⊔ V : X.Opens).toScheme))
    (h : ∀ b, Zs.obj.map (incl U V b).op z = 0) : z = 0 := by
  have e := Presheaf.IsSheaf.hom_ext_ofArrows Zs.property (incl U V) (cover_mem U V)
    (E := ModuleCat.of (ULift.{1} R) (ULift.{1} R))
    (x := ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ z)) (y := 0) (fun b => by
      ext1
      apply LinearMap.ext_ring
      simp [h b])
  have := congrArg (fun φ => φ.hom (1 : ULift.{1} R)) e
  simpa using this

theorem main (R : Type) [CommRing R] :
    Epi (biprod.desc ((free R).map (yoneda.map (X.homOfLE (le_sup_left : U ≤ U ⊔ V))))
      ((free R).map (yoneda.map (X.homOfLE (le_sup_right : V ≤ U ⊔ V))))) := by
  apply Preadditive.epi_of_cancel_zero
  intro Zs g hg
  have ha := congrArg (fun k => biprod.inl ≫ k) hg
  have hb := congrArg (fun k => biprod.inr ≫ k) hg
  simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, comp_zero] at ha hb
  let adj := sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  let W := (U ⊔ V : X.Opens).toScheme
  let g' := adj.homEquiv _ _ g
  let z := g'.app (op W) (ModuleCat.freeMk (ULift.up (𝟙 W)))
  have hval : ∀ (T : Scheme.{0}) (t : T ⟶ W),
      g'.app (op T) (ModuleCat.freeMk (ULift.up t : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op T)))) = Zs.obj.map t.op z := by
    intro T t
    have := congrArg (fun φ => φ.hom (ModuleCat.freeMk (ULift.up (𝟙 W) : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op W))))) (g'.naturality t.op)
    have key : ((freeP R).obj (yoneda.obj W)).map t.op (ModuleCat.freeMk (ULift.up (𝟙 W) : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op W)))) = ModuleCat.freeMk (ULift.up t : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op T))) := by
      simp [freeP, ModuleCat.freeMk, ModuleCat.free]
      erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rfl
    exact (congrArg (fun v => (g'.app (op T)) v) key).symm.trans this
  have h0 : ∀ (P : PSh), adj.homEquiv _ _ (0 : (presheafToSheaf _ _).obj ((freeP R).obj P) ⟶ Zs) = 0 := by
    intro P
    rw [Adjunction.homEquiv_unit]
    simp
  have hres : ∀ {Y : Scheme.{0}} (i : Y ⟶ W), (free R).map (yoneda.map i) ≫ g = 0 → Zs.obj.map i.op z = 0 := by
    intro Y i hi
    have h1 : adj.homEquiv _ _ ((presheafToSheaf _ _).map ((freeP R).map (yoneda.map i)) ≫ g) =
        (freeP R).map (yoneda.map i) ≫ g' :=
      adj.homEquiv_naturality_left _ _
    have hi' : (presheafToSheaf _ _).map ((freeP R).map (yoneda.map i)) ≫ g = 0 := hi
    rw [hi', h0] at h1
    have h2 := congrArg (fun φ => (φ.app (op Y)).hom (ModuleCat.freeMk (ULift.up (𝟙 Y) : uliftFunctor.{1, 0}.obj ((yoneda.obj Y).obj (op Y))))) h1
    have key : ((freeP R).map (yoneda.map i)).app (op Y) (ModuleCat.freeMk (ULift.up (𝟙 Y) : uliftFunctor.{1, 0}.obj ((yoneda.obj Y).obj (op Y)))) = ModuleCat.freeMk (ULift.up i : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op Y))) := by
      simp [freeP, ModuleCat.freeMk, ModuleCat.free]
      erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rfl
    rw [← hval]
    exact ((congrArg (fun v => (g'.app (op Y)) v) key).symm.trans h2.symm)
  have hz : z = 0 := sec_zero U V R Zs z (fun b => by
    cases b
    · exact hres _ hb
    · exact hres _ ha)
  have hg' : g' = 0 := by
    apply NatTrans.ext
    funext T
    induction T using Opposite.rec with | op T => ?_
    apply ModuleCat.free_hom_ext
    rintro ⟨t⟩
    erw [hval T t]
    rw [hz, map_zero]
    rfl
  exact (adj.homEquiv _ _).injective (hg'.trans (h0 _).symm)

theorem LeafFreeCov_of : LateralTheory.CohomologicalPurity.Thom.LeafFreeCov := fun R _ _ U V => main U V R

end LateralTheory.CohomologicalPurity.FreeCovPf
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafHomLocPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.TubeCut
namespace HomLocPf

variable {R : Type} [CommRing R]

lemma exact_cyc (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) :
    ((ShortComplex.mk (K.iCycles n) (K.d n ((ComplexShape.down ℕ).next n)) (K.iCycles_d _ _)).map
      ((evaluation _ _).obj T)).Exact :=
  (ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel n _ rfl)).map _

lemma exact_bdy (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) :
    ((ShortComplex.mk (K.toCycles (n + 1) n) (K.homologyπ n)
      (K.toCycles_comp_homologyπ _ _)).map ((evaluation _ _).obj T)).Exact :=
  (ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel _ n (ChainComplex.prev ℕ n))).map _

lemma iCyc_inj (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) : Function.Injective ((K.iCycles n).app T).hom := by
  rw [← ModuleCat.mono_iff_injective]
  exact (inferInstance : Mono (((evaluation _ _).obj T).map (K.iCycles n)))

lemma π_surj (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) : Function.Surjective ((K.homologyπ n).app T).hom := by
  rw [← ModuleCat.epi_iff_surjective]
  exact (inferInstance : Epi (((evaluation _ _).obj T).map (K.homologyπ n)))

lemma lift_cyc (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : (K.X n).obj T) (hx : Cyc K n T x) :
    ∃ y, ((K.iCycles n).app T).hom y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (exact_cyc K n T) x (hx _)

lemma cyc_i (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) : Cyc K n T (((K.iCycles n).app T).hom y) := by
  intro m
  change ((K.iCycles n ≫ K.d n m).app T).hom y = 0
  rw [K.iCycles_d]; rfl

lemma π_zero_iff (K : PCx R) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) :
    ((K.homologyπ n).app T).hom y = 0 ↔ Bdy K n T (((K.iCycles n).app T).hom y) := by
  have ti : ∀ z, ((K.iCycles n).app T).hom (((K.toCycles (n + 1) n).app T).hom z) = ((K.d (n + 1) n).app T).hom z := by
    intro z
    change ((K.toCycles (n + 1) n ≫ K.iCycles n).app T).hom z = _
    rw [K.toCycles_i]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (exact_bdy K n T) y h
    exact ⟨z, (ti z).symm.trans (congrArg _ hz)⟩
  · rintro ⟨z, hz⟩
    rw [← ti] at hz
    rw [← iCyc_inj K n T hz]
    change ((K.toCycles (n + 1) n ≫ K.homologyπ n).app T).hom z = 0
    rw [K.toCycles_comp_homologyπ]; rfl

lemma nat_i (K : PCx R) (n : ℕ) {T U : Scheme.{0}ᵒᵖ} (g : T ⟶ U) (y) :
    ((K.X n).map g).hom (((K.iCycles n).app T).hom y) = ((K.iCycles n).app U).hom (((K.cycles n).map g).hom y) := by
  change (((K.iCycles n).app T ≫ (K.X n).map g)).hom y = (((K.cycles n).map g ≫ (K.iCycles n).app U)).hom y
  rw [(K.iCycles n).naturality]

lemma nat_π (K : PCx R) (n : ℕ) {T U : Scheme.{0}ᵒᵖ} (g : T ⟶ U) (y) :
    ((K.homology n).map g).hom (((K.homologyπ n).app T).hom y) = ((K.homologyπ n).app U).hom (((K.cycles n).map g).hom y) := by
  change (((K.homologyπ n).app T ≫ (K.homology n).map g)).hom y = (((K.cycles n).map g ≫ (K.homologyπ n).app U)).hom y
  rw [(K.homologyπ n).naturality]

lemma cm_i {K L : PCx R} (φ : K ⟶ L) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) :
    ((L.iCycles n).app T).hom (((HomologicalComplex.cyclesMap φ n).app T).hom y) =
      ((φ.f n).app T).hom (((K.iCycles n).app T).hom y) := by
  change ((HomologicalComplex.cyclesMap φ n ≫ L.iCycles n).app T).hom y = ((K.iCycles n ≫ φ.f n).app T).hom y
  rw [HomologicalComplex.cyclesMap_i]

lemma hm_π {K L : PCx R} (φ : K ⟶ L) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (y) :
    ((HomologicalComplex.homologyMap φ n).app T).hom (((K.homologyπ n).app T).hom y) =
      ((L.homologyπ n).app T).hom (((HomologicalComplex.cyclesMap φ n).app T).hom y) := by
  change ((K.homologyπ n ≫ HomologicalComplex.homologyMap φ n).app T).hom y =
    ((HomologicalComplex.cyclesMap φ n ≫ L.homologyπ n).app T).hom y
  rw [HomologicalComplex.homologyπ_naturality]

end HomLocPf

open HomLocPf in
theorem LeafHomLoc_of : LeafHomLoc := by
  intro R _ K L φ n hinj hsurj
  refine ⟨⟨fun {X} a b h => ?_⟩, ⟨fun {U} s => ?_⟩⟩
  · change ((HomologicalComplex.homologyMap φ n).app X).hom a = ((HomologicalComplex.homologyMap φ n).app X).hom b at h
    obtain ⟨y, hy⟩ := π_surj K n X (a - b)
    have hb : Bdy L n X (((φ.f n).app X).hom (((K.iCycles n).app X).hom y)) := by
      rw [← cm_i, ← π_zero_iff, ← hm_π, hy, map_sub, h, sub_self]
    obtain ⟨S, hS, hSx⟩ := hinj X _ (cyc_i K n X y) hb
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V f hf
    rw [Presheaf.equalizerSieve_apply]
    change ((K.homology n).map f.op).hom a = ((K.homology n).map f.op).hom b
    rw [← sub_eq_zero, ← map_sub, ← hy, nat_π, π_zero_iff, ← nat_i]
    exact hSx f hf
  · obtain ⟨y, rfl⟩ := π_surj L n _ s
    obtain ⟨S, hS, hSx⟩ := hsurj (op U) _ (cyc_i L n _ y)
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V f hf
    obtain ⟨x', hx', hb⟩ := hSx f hf
    obtain ⟨y', rfl⟩ := lift_cyc K n _ x' hx'
    refine ⟨((K.homologyπ n).app (op V)).hom y', ?_⟩
    change ((HomologicalComplex.homologyMap φ n).app (op V)).hom (((K.homologyπ n).app (op V)).hom y') =
      ((L.homology n).map f.op).hom (((L.homologyπ n).app (op U)).hom y)
    rw [hm_π, nat_π, ← sub_eq_zero, ← map_sub, π_zero_iff, map_sub, cm_i, ← nat_i]
    exact hb

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPrdAffPfNbhd
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem indNbhd_of_nbhd {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (h : Nbhd φ I) :
    IndNbhd φ I :=
  ⟨Discrete PUnit, inferInstance, inferInstance, (Functor.const _).obj (CommRingCat.of B),
    (Functor.const _).map (CommRingCat.ofHom φ), 𝟙 _, ⟨isColimitConstCocone (Discrete PUnit) (CommRingCat.of B)⟩,
    fun _ => ⟨h, Category.comp_id _⟩⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafTailNervePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def UtsR (m : ℕ) : CommRingCat.{0} ⥤ Type where
  obj A := Fin m → Aˣ
  map f := TypeCat.ofHom fun u i => Units.map f.hom.toMonoidHom (u i)
  map_id A := by ext u i; rfl
  map_comp f g := by ext u i; rfl

def Uts (m : ℕ) : Scheme.{0}ᵒᵖ ⥤ Type := Scheme.Γ ⋙ UtsR m

def evP (n : SimplexCategoryᵒᵖ) (A B : Spc) : (A ⨯ B).obj n ≅ A.obj n ⨯ B.obj n :=
  PreservesLimitPair.iso ((evaluation SimplexCategoryᵒᵖ (Scheme.{0}ᵒᵖ ⥤ Type)).obj n) A B

@[reassoc] theorem evalProdIso_hom_naturality (n : SimplexCategoryᵒᵖ) {A B A' B' : Spc} (f : A ⟶ A') (g : B ⟶ B') :
    (prod.map f g).app n ≫ (evP n A' B').hom = (evP n A B).hom ≫ prod.map (f.app n) (g.app n) := by
  simp only [evP, PreservesLimitPair.iso_hom]
  exact prodComparison_natural ((evaluation SimplexCategoryᵒᵖ (Scheme.{0}ᵒᵖ ⥤ Type)).obj n) f g

def LeafNerveSplit : Prop := ∀ (d : ℕ) (n : SimplexCategoryᵒᵖ),
  ∃ (a₁ : (Pj (d + 1) 1).obj n ≅ (Pj (d + 1) 1).obj (op (SimplexCategory.mk 0)) ⨯ Uts n.unop.len)
    (a₀ : (Pj d 0).obj n ≅ (Pj d 0).obj (op (SimplexCategory.mk 0)) ⨯ Uts n.unop.len),
    (Pj.tail d).app n ≫ a₀.hom = a₁.hom ≫ prod.map ((Pj.tail d).app (op (SimplexCategory.mk 0))) (𝟙 _)

def LeafUnitsRep : Prop := ∀ (R : Type) [CommRing R] (m : ℕ),
  ∃ (R' : Type) (_ : CommRing R') (_ : R →+* R'),
    Nonempty (Uts m ⨯ yoneda.obj (Spec (CommRingCat.of R)) ≅ yoneda.obj (Spec (CommRingCat.of R')))

theorem evalProdIso_inv_naturality (n : SimplexCategoryᵒᵖ) {A B A' B' : Spc} (f : A ⟶ A') (g : B ⟶ B') :
    (evP n A B).inv ≫ (prod.map f g).app n = prod.map (f.app n) (g.app n) ≫ (evP n A' B').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← evalProdIso_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem LeafTailNerve_of (hN : LeafNerveSplit) (hU : LeafUnitsRep) : LeafTailNerve := by
  intro d R _ n
  obtain ⟨R', _, ψ, ⟨r⟩⟩ := hU R n.unop.len
  obtain ⟨a₁, a₀, w⟩ := hN d n
  let r' : Uts n.unop.len ⨯ (sp R).obj n ≅ (sp R').obj (op (SimplexCategory.mk 0)) := r
  let f₁ : (PR (d + 1) 1 R).obj n ≅ (PR (d + 1) 1 R').obj (op (SimplexCategory.mk 0)) :=
    evP n _ _ ≪≫ prod.mapIso a₁ (Iso.refl _) ≪≫ prod.associator _ _ _ ≪≫ prod.mapIso (Iso.refl _) r' ≪≫
      (evP (op (SimplexCategory.mk 0)) (Pj (d + 1) 1) (sp R')).symm
  let f₀ : (PR d 0 R).obj n ≅ (PR d 0 R').obj (op (SimplexCategory.mk 0)) :=
    evP n _ _ ≪≫ prod.mapIso a₀ (Iso.refl _) ≪≫ prod.associator _ _ _ ≪≫ prod.mapIso (Iso.refl _) r' ≪≫
      (evP (op (SimplexCategory.mk 0)) (Pj d 0) (sp R')).symm
  have w1 : (Pj.tail d).app n ≫ a₀.hom ≫ prod.fst = a₁.hom ≫ prod.fst ≫ (Pj.tail d).app (op (SimplexCategory.mk 0)) := by
    rw [reassoc_of% w]; simp
  have w2 : (Pj.tail d).app n ≫ a₀.hom ≫ prod.snd = a₁.hom ≫ prod.snd := by
    rw [reassoc_of% w]; simp
  refine ⟨R', inferInstance, ψ, f₁, f₀, ?_⟩
  simp only [f₁, f₀, Iso.trans_hom, Iso.symm_hom, prod.mapIso_hom, Iso.refl_hom, Category.assoc]
  erw [evalProdIso_inv_naturality, evalProdIso_hom_naturality_assoc]
  congr 1
  simp only [← Category.assoc]
  congr 1
  apply prod.hom_ext
  · simp [w1, w2]
  · simp [w1, w2]

end LateralTheory.CohomologicalPurity.Thom
end
end

