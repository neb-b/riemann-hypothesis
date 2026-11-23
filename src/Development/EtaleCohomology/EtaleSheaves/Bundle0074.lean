module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0068
public import Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism.LeafShIsoOf
public import Development.EtaleCohomology.EtaleSheaves.PropertyDescent.LeafPropsDescendOf
public import Development.EtaleCohomology.EtaleSheaves.Bundle0013
public import Development.EtaleCohomology.EtaleSheaves.Bundle0049
public import Development.EtaleCohomology.EtaleSheaves.PullMonoPf
public import Development.EtaleCohomology.EtaleSheaves.Bundle0070
public import Development.EtaleCohomology.EtaleSheaves.Bundle0067

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafQCQSInductPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf

namespace LateralTheory.E.LeafQCQSInductPf

def Cov (X : Scheme.{0}) (L : List X.Opens) : Prop :=
  (∀ u ∈ L, IsAffineOpen u) ∧ ∀ x : X, ∃ u ∈ L, x ∈ u

lemma sep_of {X Y : Scheme.{0}} (g : Y ⟶ X) [IsOpenImmersion g] [X.IsSeparated] : Y.IsSeparated :=
  ⟨by rw [← terminal.comp_from g]; infer_instance⟩

lemma fp_res {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S) (hf : FP f) (W : X.Opens)
    (hW : IsCompact (W : Set X)) : FP (W.ι ≫ f) := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨inferInstance, ?_, inferInstance⟩
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW
  exact quasiCompact_of_compactSpace _

lemma cov_pull {X : Scheme.{0}} (W : X.Opens) (L : List X.Opens) (hA : ∀ u ∈ L, IsAffineOpen u)
    (hle : ∀ u ∈ L, u ≤ W) (hc : ∀ x ∈ W, ∃ u ∈ L, x ∈ u) :
    Cov W.toScheme (L.map (W.ι ⁻¹ᵁ ·)) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact (hA u hu).preimage_of_isOpenImmersion W.ι (by simpa using hle u hu)
  · intro x
    obtain ⟨u, hu, hx⟩ := hc (W.ι x) (by
      have := Set.mem_range_self (f := W.ι) x
      rwa [Scheme.Opens.range_ι] at this)
    exact ⟨_, List.mem_map.mpr ⟨u, hu, rfl⟩, by simpa using hx⟩

lemma exists_list {X : Scheme.{0}} (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∃ L : List X.Opens, (∀ u ∈ L, IsAffineOpen u) ∧ (∀ u ∈ L, u ≤ W) ∧ ∀ x ∈ W, ∃ u ∈ L, x ∈ u := by
  obtain ⟨s, hs, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hW
  refine ⟨hs.toFinset.toList.map (fun a : X.affineOpens => a.1), ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hu
    exact a.prop
  · intro u hu
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
    rw [e]
    exact le_iSup₂ (f := fun (i : X.affineOpens) (_ : i ∈ s) => (i : X.Opens)) a (by simpa using ha)
  · intro x hx
    rw [e] at hx
    simp only [TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    exact ⟨a, List.mem_map.mpr ⟨a, by simpa using ha, rfl⟩, hxa⟩

lemma compact_of_cover {X : Scheme.{0}} (W : X.Opens) (L : List X.Opens) (hA : ∀ u ∈ L, IsAffineOpen u)
    (hle : ∀ u ∈ L, u ≤ W) (hc : ∀ x ∈ W, ∃ u ∈ L, x ∈ u) : IsCompact (W : Set X) := by
  have : (W : Set X) = ⋃ u ∈ L, (u : Set X) := by
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun hx => let ⟨u, hu, h⟩ := hc x hx; ⟨u, hu, h⟩, fun ⟨u, hu, h⟩ => hle u hu h⟩
  rw [this]
  exact L.finite_toSet.isCompact_biUnion fun u hu => (hA u hu).isCompact

lemma mem_V {X : Scheme.{0}} (L : List X.Opens) (x : X) :
    x ∈ (⨆ u ∈ L, u : X.Opens) ↔ ∃ u ∈ L, x ∈ u := by
  simp

section
variable {S : Scheme.{0}} [IsAffine S] (P : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop)
  (hA : ∀ {X : Scheme.{0}} (f : X ⟶ S), IsAffine X → FP f → P f)
  (hG : ∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
      P (U.ι ≫ f) → P (V.ι ≫ f) → P ((U ⊓ V).ι ≫ f) → P f)
include hA hG

lemma glue_step {X : Scheme.{0}} (f : X ⟶ S) (hf : FP f) (U : X.Opens) (L' : List X.Opens)
    (hc : Cov X (U :: L'))
    (hV : Cov (⨆ u ∈ L', u : X.Opens).toScheme
        (L'.map ((⨆ u ∈ L', u : X.Opens).ι ⁻¹ᵁ ·)) → P ((⨆ u ∈ L', u : X.Opens).ι ≫ f))
    (hW : P ((U ⊓ ⨆ u ∈ L', u : X.Opens).ι ≫ f)) :
    P f := by
  have hU : IsAffineOpen U := hc.1 U (by simp)
  have hL' : ∀ u ∈ L', IsAffineOpen u := fun u hu => hc.1 u (by simp [hu])
  have hUV : U ⊔ (⨆ u ∈ L', u : X.Opens) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨u, hu, hx⟩ := hc.2 x
    rcases List.mem_cons.mp hu with rfl | hu
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl hx)
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inr ((mem_V L' x).mpr ⟨u, hu, hx⟩))
  refine hG f hf U _ hUV ?_ ?_ ?_
  · haveI : IsAffine U := hU
    exact hA _ inferInstance (fp_res f hf U hU.isCompact)
  · refine hV (cov_pull _ L' hL' (fun u hu => ?_) (fun x hx => (mem_V L' x).mp hx))
    exact le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu
  · exact hW

end

section
variable {S : Scheme.{0}} [IsAffine S] (P : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop)
  (hA : ∀ {X : Scheme.{0}} (f : X ⟶ S), IsAffine X → FP f → P f)
  (hG : ∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
      P (U.ι ≫ f) → P (V.ι ≫ f) → P ((U ⊓ V).ι ≫ f) → P f)
include hA hG

lemma empty_case {X : Scheme.{0}} (f : X ⟶ S) (hf : FP f) (hc : Cov X []) : P f := by
  have : IsEmpty X := ⟨fun x => by obtain ⟨u, hu, _⟩ := hc.2 x; simp at hu⟩
  exact hA f inferInstance hf

lemma stepA : ∀ (n : ℕ) {X : Scheme.{0}} (f : X ⟶ S) (L : List X.Opens), L.length = n → FP f →
    X.IsSeparated → Cov X L → P f := by
  intro n
  induction n with
  | zero =>
    intro X f L hl hf _ hc
    rw [List.eq_nil_of_length_eq_zero hl] at hc
    exact empty_case P hA hG f hf hc
  | succ n ih =>
    intro X f L hl hf hs hc
    obtain ⟨U, L', rfl⟩ : ∃ U L', L = U :: L' := by
      cases L with
      | nil => simp at hl
      | cons U L' => exact ⟨U, L', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hU : IsAffineOpen U := hc.1 U (by simp)
    have hL' : ∀ u ∈ L', IsAffineOpen u := fun u hu => hc.1 u (by simp [hu])
    refine glue_step P hA hG f hf U L' hc ?_ ?_
    · intro hcV
      have : (⨆ u ∈ L', u : X.Opens).toScheme.IsSeparated := sep_of (⨆ u ∈ L', u : X.Opens).ι
      refine ih _ _ (by simp [hl]) (fp_res f hf _ ?_) this hcV
      exact compact_of_cover _ L' hL' (fun u hu => le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu)
        (fun x hx => (mem_V L' x).mp hx)
    · set W : X.Opens := U ⊓ ⨆ u ∈ L', u
      have hA' : ∀ v ∈ L'.map (U ⊓ ·), IsAffineOpen v := by
        intro v hv
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        exact hU.inf (hL' u hu)
      have hle : ∀ v ∈ L'.map (U ⊓ ·), v ≤ W := by
        intro v hv
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        exact inf_le_inf_left U (le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu)
      have hcW : ∀ x ∈ W, ∃ v ∈ L'.map (U ⊓ ·), x ∈ v := by
        intro x hx
        obtain ⟨hxU, hxV⟩ := hx
        obtain ⟨u, hu, h⟩ := (mem_V L' x).mp hxV
        exact ⟨U ⊓ u, List.mem_map.mpr ⟨u, hu, rfl⟩, ⟨hxU, h⟩⟩
      have : W.toScheme.IsSeparated := sep_of W.ι
      exact ih _ ((L'.map (U ⊓ ·)).map (W.ι ⁻¹ᵁ ·)) (by simp [hl])
        (fp_res f hf W (compact_of_cover W _ hA' hle hcW)) this (cov_pull W _ hA' hle hcW)

lemma stepB : ∀ (n : ℕ) {X : Scheme.{0}} (f : X ⟶ S) (L : List X.Opens), L.length = n → FP f →
    Cov X L → P f := by
  intro n
  induction n with
  | zero =>
    intro X f L hl hf hc
    rw [List.eq_nil_of_length_eq_zero hl] at hc
    exact empty_case P hA hG f hf hc
  | succ n ih =>
    intro X f L hl hf hc
    obtain ⟨U, L', rfl⟩ : ∃ U L', L = U :: L' := by
      cases L with
      | nil => simp at hl
      | cons U L' => exact ⟨U, L', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hU : IsAffineOpen U := hc.1 U (by simp)
    have hL' : ∀ u ∈ L', IsAffineOpen u := fun u hu => hc.1 u (by simp [hu])
    have hVc : IsCompact ((⨆ u ∈ L', u : X.Opens) : Set X) :=
      compact_of_cover _ L' hL' (fun u hu => le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu)
        (fun x hx => (mem_V L' x).mp hx)
    refine glue_step P hA hG f hf U L' hc ?_ ?_
    · intro hcV
      exact ih _ _ (by simp [hl]) (fp_res f hf _ hVc) hcV
    · set W : X.Opens := U ⊓ ⨆ u ∈ L', u
      have : QuasiSeparated f := hf.2.2
      have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
      have hWc : IsCompact (W : Set X) :=
        QuasiSeparatedSpace.inter_isCompact _ _ U.2 hU.isCompact (⨆ u ∈ L', u : X.Opens).2 hVc
      obtain ⟨L2, h1, h2, h3⟩ := exists_list W hWc
      haveI : IsAffine U := hU
      have : W.toScheme.IsSeparated := sep_of (X.homOfLE (inf_le_left : W ≤ U))
      exact stepA P hA hG _ (W.ι ≫ f) (L2.map (W.ι ⁻¹ᵁ ·)) rfl (fp_res f hf W hWc) this
        (cov_pull W L2 h1 h2 h3)

end

theorem LeafQCQSInduct_of : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct := by
  intro S _ P hA hG X f hf
  have : QuasiCompact f := hf.2.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨L, h1, -, h3⟩ := exists_list (⊤ : X.Opens) (by simpa using isCompact_univ)
  exact stepB P hA hG _ f L rfl hf ⟨h1, fun x => h3 x trivial⟩

end LateralTheory.E.LeafQCQSInductPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSecRepPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafSecRepPf
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf LateralTheory.E.LeafShIsoPf.Sh

section General
universe u
variable {C : Type u} [Category.{0} C] (R : Type 1) [Ring R]

def FP : C ⥤ (Cᵒᵖ ⥤ ModuleCat.{1} R) :=
  yoneda ⋙ (Functor.whiskeringRight Cᵒᵖ (Type 0) (ModuleCat.{1} R)).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free R)

def gen {U V : C} (a : V ⟶ U) : ((FP R).obj U).obj (op V) :=
  ModuleCat.freeMk (R := R) (X := ULift.{1} (V ⟶ U)) (ULift.up a)

theorem map_gen {U V W : C} (a : V ⟶ U) (b : W ⟶ V) :
    ((FP R).obj U).map b.op (gen R a) = gen R (b ≫ a) :=
  ModuleCat.free_map_apply (R := R) _ _

theorem app_gen {U U' V : C} (a : V ⟶ U') (b : U' ⟶ U) :
    ((FP R).map b).app (op V) (gen R a) = gen R (a ≫ b) :=
  ModuleCat.free_map_apply (R := R) _ _

theorem freePresheaf_hom_ext {U V : C} {M : ModuleCat.{1} R} {f g : ((FP R).obj U).obj (op V) ⟶ M}
    (h : ∀ a : V ⟶ U, f (gen R a) = g (gen R a)) : f = g :=
  ModuleCat.free_hom_ext (R := R) (X := ULift.{1} (V ⟶ U)) (fun x => h x.down)

def desc (G : Cᵒᵖ ⥤ ModuleCat.{1} R) (U : C) (s : G.obj (op U)) (V : C) :
    ((FP R).obj U).obj (op V) ⟶ G.obj (op V) :=
  ModuleCat.freeDesc (R := R) (X := ULift.{1} (V ⟶ U)) (↾fun x => G.map x.down.op s)

theorem desc_gen (G : Cᵒᵖ ⥤ ModuleCat.{1} R) (U : C) (s : G.obj (op U)) {V : C} (a : V ⟶ U) :
    desc R G U s V (gen R a) = G.map a.op s :=
  ModuleCat.freeDesc_apply (R := R) _ _

theorem nat_gen {G : Cᵒᵖ ⥤ ModuleCat.{1} R} {U V : C} (η : (FP R).obj U ⟶ G) (a : V ⟶ U) :
    η.app (op V) (gen R a) = G.map a.op (η.app (op U) (gen R (𝟙 U))) := by
  have h := ConcreteCategory.congr_hom (η.naturality a.op) (gen R (𝟙 U))
  simp only [ConcreteCategory.comp_apply] at h
  rw [map_gen, Category.comp_id] at h
  exact h

def yE (G : Cᵒᵖ ⥤ ModuleCat.{1} R) (U : C) : ((FP R).obj U ⟶ G) ≃ G.obj (op U) where
  toFun η := η.app (op U) (gen R (𝟙 U))
  invFun s :=
    { app := fun V => desc R G U s V.unop
      naturality := by
        rintro ⟨V⟩ ⟨W⟩ ⟨b⟩
        apply freePresheaf_hom_ext
        intro a
        simp only [ConcreteCategory.comp_apply]
        have h := map_gen R a b
        erw [h, desc_gen, desc_gen]
        rw [op_comp, G.map_comp, ConcreteCategory.comp_apply]
        rfl }
  left_inv η := by
    ext1
    funext ⟨V⟩
    apply freePresheaf_hom_ext
    intro a
    exact (desc_gen R G U _ a).trans (nat_gen R η a).symm
  right_inv s := by
    refine (desc_gen R G U s (𝟙 U)).trans ?_
    simp

theorem yE_res {G : Cᵒᵖ ⥤ ModuleCat.{1} R} {U U' : C} (a : U' ⟶ U) (η : (FP R).obj U ⟶ G) :
    yE R G U' ((FP R).map a ≫ η) = G.map a.op (yE R G U η) := by
  change η.app (op U') (((FP R).map a).app (op U') (gen R (𝟙 U'))) = _
  rw [app_gen, Category.id_comp]
  exact nat_gen R η a

theorem yE_sub {G : Cᵒᵖ ⥤ ModuleCat.{1} R} (U : C) (η η' : (FP R).obj U ⟶ G) :
    yE R G U (η - η') = yE R G U η - yE R G U η' := rfl

variable (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{1} R)]

theorem general (T : C ⥤ Sheaf J (ModuleCat.{1} R)) (i : FP R ⋙ presheafToSheaf J _ ≅ T) :
    ∃ e : ∀ (F : Sheaf J (ModuleCat.{1} R)) (U : C), (T.obj U ⟶ F) ≃ F.obj.obj (op U),
  (∀ (F G : Sheaf J (ModuleCat.{1} R)) (g : F ⟶ G) (U : C) (t : T.obj U ⟶ F),
    e G U (t ≫ g) = g.hom.app (op U) (e F U t)) ∧
  (∀ (F : Sheaf J (ModuleCat.{1} R)) (U U' : C) (a : U' ⟶ U) (t : T.obj U ⟶ F),
    e F U' (T.map a ≫ t) = F.obj.map a.op (e F U t)) ∧
  (∀ (F : Sheaf J (ModuleCat.{1} R)) (U : C) (t t' : T.obj U ⟶ F), e F U (t - t') = e F U t - e F U t') := by
  let adj := sheafificationAdjunction J (ModuleCat.{1} R)
  refine ⟨fun F U => ((Iso.homCongr (i.app U).symm (Iso.refl F)).trans
    (adj.homEquiv ((FP R).obj U) F)).trans (yE R F.obj U), ?_, ?_, ?_⟩
  · intro F G g U t
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
    rfl
  · intro F U U' a t
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    have h : (i.app U').hom ≫ T.map a ≫ t =
        (presheafToSheaf J _).map ((FP R).map a) ≫ (i.app U).hom ≫ t := by
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      exact (i.hom.naturality a).symm
    rw [h]
    erw [Adjunction.homEquiv_naturality_left]
    exact yE_res R a _
  · intro F U t t'
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [Preadditive.comp_sub, ← yE_sub]
    congr 1

end General

theorem LeafSecRep_of : LeafSecRep := by
  intro B q
  let i : FP (C := B.Etale) (ULift.{1} (ZMod q)) ⋙ presheafToSheaf (EtTop B) _ ≅ OU B q ⋙ H0 B q :=
    (Functor.isoWhiskerLeft (FP (C := B.Etale) (ULift.{1} (ZMod q)) ⋙ presheafToSheaf (EtTop B) _)
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0)).symm
  exact general (ULift.{1} (ZMod q)) (EtTop B) (OU B q ⋙ H0 B q) i

end LateralTheory.E.LeafSecRepPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSpreadProperPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf

namespace LateralTheory.E.LeafSpreadProperPf

def LeafSpreadSeparated : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → IsSeparated c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → IsSeparated q'

end LateralTheory.E.LeafSpreadProperPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSpreadSmoothPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf LateralTheory.E.LeafPropsDescendPf.Split

namespace LateralTheory.E.LeafSpreadSmoothPf

def LeafSpreadSmoothAff : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    LocallyOfFinitePresentation q → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → SmoothOfRelativeDimension 1 q'

def LeafSpreadSmoothAffAt : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    LocallyOfFinitePresentation q → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧ SmoothOfRelativeDimension 1 (pullback.snd q (incl h))

theorem incl_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R S R' : Subalgebra k Ω} (h1 : R ≤ S)
    (h2 : S ≤ R') : incl h2 ≫ incl h1 = incl (h1.trans h2) := by
  rw [← Spec.map_comp]; rfl

theorem LeafSpreadSmoothAff_of (hA : LeafSpreadSmoothAffAt) : LeafSpreadSmoothAff := by
  intro k _ Ω _ _ R hR C D c q v hD hlfp hs hv
  obtain ⟨S, hRS, hSfg, hsm⟩ := hA k Ω R hR c q v hD hlfp hs hv
  refine ⟨S, hRS, hSfg, fun R' hSR' hRR' E q' r hE => ?_⟩
  have hw : r ≫ q = (q' ≫ incl hSR') ≫ incl hRS := by
    rw [Category.assoc, incl_incl]; exact hE.w
  have hsq : IsPullback (pullback.lift r (q' ≫ incl hSR') hw) q' (pullback.snd q (incl hRS)) (incl hSR') := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl hRS))
    rw [pullback.lift_fst, incl_incl]; exact hE
  exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hsq hsm

theorem fg_finset_sup {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {ι : Type} (t : Finset ι)
    (S : ι → Subalgebra k Ω) (h : ∀ i, (S i).FG) : (t.sup S).FG := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (Subalgebra.fg_bot : (⊥ : Subalgebra k Ω).FG)
  | insert a t _ ih => rw [Finset.sup_insert]; exact (h a).sup ih

theorem LeafSpreadSmooth_of_aff (hA : LeafSpreadSmoothAff) : LeafSpreadSmooth := by
  intro k _ Ω _ _ R hR C D c q v hf hs hv
  obtain ⟨hlfp, hqc, hqs⟩ := hf
  have hL : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  have := hlfp; have := hqc; have := hs
  have : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace q

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i : D.affineOpens => ((i : D.Opens) : Set D))
    (fun i => (i : D.Opens).isOpen) (by
      intro x _
      have : x ∈ (⊤ : D.Opens) := trivial
      rw [← iSup_affineOpens_eq_top D] at this
      simpa [TopologicalSpace.Opens.mem_iSup] using this)

  have piece : ∀ U : D.affineOpens, ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' →
      ∀ (hR : R ≤ R') (E : Scheme.{0}) (q' : E ⟶ Sp R') (r : E ⟶ (U : D.Opens)),
      IsPullback r q' ((U : D.Opens).ι ≫ q) (incl hR) → SmoothOfRelativeDimension 1 q' := by
    intro U
    have : IsAffine (U : D.Opens) := U.2
    have h1 := (isPullback_morphismRestrict v (U : D.Opens)).paste_vert hv
    exact hA k Ω R hR (((v ⁻¹ᵁ (U : D.Opens)).ι) ≫ c) ((U : D.Opens).ι ≫ q) (v ∣_ (U : D.Opens)) U.2
      inferInstance (IsZariskiLocalAtSource.comp hs _) h1
  choose S hRS hSfg hS using piece
  refine ⟨R ⊔ t.sup S, le_sup_left, hR.sup (fg_finset_sup t S hSfg), ?_⟩
  intro R' hR' hRR E q' r hE
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)
    (fun j : t => r ⁻¹ᵁ ((j.1 : D.Opens))) ?_ ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (r x)))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hx⟩
  · intro j
    have h2 := (isPullback_morphismRestrict r (j.1 : D.Opens)).paste_vert hE
    exact hS j.1 R' ((Finset.le_sup j.2).trans (le_sup_right.trans hR')) hRR _ _ (r ∣_ (j.1 : D.Opens)) h2

def LeafSpreadSmoothAffSm : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    LocallyOfFinitePresentation q → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧ Smooth (pullback.snd q (incl h))

def LeafSpreadRelDim : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    LocallyOfFinitePresentation q → Smooth q → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → SmoothOfRelativeDimension 1 q'

theorem LeafSpreadSmoothAffAt_of (hA : LeafSpreadSmoothAffSm) (hB : LeafSpreadRelDim) : LeafSpreadSmoothAffAt := by
  intro k _ Ω _ _ R hR C D c q v hD hlfp hs hv
  obtain ⟨S1, h1, f1, hsm1⟩ := hA k Ω R hR c q v hD hlfp hs hv
  have ht : toR S1 ≫ incl h1 = toR R := by
    rw [← Spec.map_comp]; rfl
  have hw1 : v ≫ q = (c ≫ toR S1) ≫ incl h1 := by
    rw [Category.assoc, ht]; exact hv.w
  have sq1 : IsPullback (pullback.lift v (c ≫ toR S1) hw1) c
      (pullback.snd q (incl h1)) (toR S1) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl h1))
    rw [pullback.lift_fst, ht]; exact hv
  obtain ⟨S2, h12, f2, H⟩ := hB k Ω S1 f1 c (pullback.snd q (incl h1)) _ inferInstance inferInstance hsm1 hs sq1
  refine ⟨S2, h1.trans h12, f2, ?_⟩
  have hw : pullback.fst q (incl (h1.trans h12)) ≫ q = (pullback.snd q (incl (h1.trans h12)) ≫ incl h12) ≫ incl h1 := by
    rw [Category.assoc, incl_incl]; exact pullback.condition
  refine H S2 le_rfl h12 _ _ (pullback.lift _ _ hw) ?_
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl h1))
  rw [pullback.lift_fst, incl_incl]; exact IsPullback.of_hasPullback q (incl (h1.trans h12))

theorem LeafSpreadSmooth_of (hA : LeafSpreadSmoothAffSm) (hB : LeafSpreadRelDim) : LeafSpreadSmooth :=
  LeafSpreadSmooth_of_aff (LeafSpreadSmoothAff_of (LeafSpreadSmoothAffAt_of hA hB))

end LateralTheory.E.LeafSpreadSmoothPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwistIsoPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTwistIsoPf

theorem leafLoc : LateralTheory.E.LeafTwistPf.LeafLoc :=
  LateralTheory.E.LeafLocPf.LeafLoc_of' (LateralTheory.E.LocSecPfC.LocSec_of LateralTheory.E.ClassSecPf.ClassSec_of)
    (LateralTheory.E.LocSlicePf.LocSlice_of' LateralTheory.E.PullMonoPf.PullMono_of)

theorem leafTwSec : LateralTheory.E.LeafTwistPf.LeafTwSec :=
  LateralTheory.E.LeafTwSecPf.LeafTwSec_of' LateralTheory.E.LeafTwInjPf.LeafTwInj_of LateralTheory.E.LeafTwSecPf.LeafTwSurj_of

end LateralTheory.E.LeafTwistIsoPf

end
end

