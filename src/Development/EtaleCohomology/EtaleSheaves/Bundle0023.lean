module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0009
public import Development.EtaleCohomology.EtaleSheaves.Bundle0010
public import Development.EtaleCohomology.EtaleSheaves.Bundle0014
public import Development.EtaleCohomology.EtaleSheaves.Bundle0013

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.ContIndPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.ContIndPf

section lists
variable {X : Scheme.{0}}

def lsup (l : List X.Opens) : X.Opens := l.foldr (· ⊔ ·) ⊥

lemma lsup_cons (a : X.Opens) (l : List X.Opens) : lsup (a :: l) = a ⊔ lsup l := rfl
lemma lsup_nil : lsup ([] : List X.Opens) = ⊥ := rfl

lemma le_lsup {l : List X.Opens} {B : X.Opens} (h : B ∈ l) : B ≤ lsup l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [lsup_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_sup_left
    · exact (ih h).trans le_sup_right

lemma lsup_le {l : List X.Opens} {W : X.Opens} (h : ∀ B ∈ l, B ≤ W) : lsup l ≤ W := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih =>
    rw [lsup_cons]
    exact sup_le (h a (by simp)) (ih fun B hB => h B (by simp [hB]))

lemma isCompact_lsup (l : List X.Opens) (h : ∀ B ∈ l, IsCompact (B : Set X)) : IsCompact (lsup l : Set X) := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih =>
    rw [lsup_cons, TopologicalSpace.Opens.coe_sup]
    exact (h a (by simp)).union (ih fun B hB => h B (by simp [hB]))

lemma preimage_lsup {Y : Scheme.{0}} (f : Y ⟶ X) (l : List X.Opens) :
    f ⁻¹ᵁ lsup l = lsup (l.map (f ⁻¹ᵁ ·)) := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih =>
    rw [lsup_cons, List.map_cons, lsup_cons, ← ih]
    rfl

lemma lsup_inf (l : List X.Opens) (A : X.Opens) : lsup l ⊓ A = lsup (l.map (· ⊓ A)) := by
  induction l with
  | nil => simp [lsup_nil]
  | cons a l ih => rw [List.map_cons, lsup_cons, lsup_cons, inf_sup_right, ih]

end lists

section opens
variable {X : Scheme.{0}}

lemma image_le_range {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (A : Y.Opens) : f ''ᵁ A ≤ f.opensRange := by
  rw [← Scheme.Hom.image_top_eq_opensRange]
  exact (f.image_le_image_iff _ _).2 le_top

lemma image_inf {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (A B : Y.Opens) :
    f ''ᵁ (A ⊓ B) = f ''ᵁ A ⊓ f ''ᵁ B := by
  apply le_antisymm
  · exact le_inf ((f.image_le_image_iff _ _).2 inf_le_left) ((f.image_le_image_iff _ _).2 inf_le_right)
  · have hC : f ''ᵁ A ⊓ f ''ᵁ B = f ''ᵁ (f ⁻¹ᵁ (f ''ᵁ A ⊓ f ''ᵁ B)) := by
      rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.2 (inf_le_left.trans (image_le_range f A))]
    rw [hC, f.image_le_image_iff]
    have : f ⁻¹ᵁ (f ''ᵁ A ⊓ f ''ᵁ B) = f ⁻¹ᵁ (f ''ᵁ A) ⊓ f ⁻¹ᵁ (f ''ᵁ B) := rfl
    rw [this, f.preimage_image_eq, f.preimage_image_eq]

lemma image_le (W : X.Opens) (A : W.toScheme.Opens) : W.ι ''ᵁ A ≤ W :=
  (image_le_range W.ι A).trans (Scheme.Opens.opensRange_ι W).le

lemma affine_preimage (W : X.Opens) {B : X.Opens} (h : B ≤ W) (hB : IsAffineOpen B) :
    IsAffineOpen (W.ι ⁻¹ᵁ B) := by
  apply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion W.ι).mp
  rwa [W.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 h]

def Good (Y : Scheme.{0}) : Prop :=
  ∀ A B : Y.Opens, IsAffineOpen A → IsAffineOpen B → IsAffineOpen (A ⊓ B)

def Good2 (Y : Scheme.{0}) : Prop :=
  ∀ A B : Y.Opens, IsAffineOpen A → IsAffineOpen B → IsCompact ((A ⊓ B : Y.Opens) : Set Y)

lemma good_of (W : X.Opens)
    (h : ∀ C D : X.Opens, C ≤ W → D ≤ W → IsAffineOpen C → IsAffineOpen D → IsAffineOpen (C ⊓ D)) :
    Good W.toScheme := by
  intro A B hA hB
  apply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion W.ι).mp
  rw [image_inf]
  exact h _ _ (image_le W A) (image_le W B) (hA.image_of_isOpenImmersion _) (hB.image_of_isOpenImmersion _)

lemma good_open (hX : Good X) (W : X.Opens) : Good W.toScheme :=
  good_of W (fun C D _ _ hC hD => hX C D hC hD)

lemma good_affine (A W : X.Opens) (hA : IsAffineOpen A) (hW : W ≤ A) : Good W.toScheme := by
  apply good_of W
  intro C D hC hD hC' hD'
  have : IsAffine A.toScheme := hA
  have h1 := (affine_preimage A (hC.trans hW) hC').inf (affine_preimage A (hD.trans hW) hD')
  have h2 := h1.image_of_isOpenImmersion A.ι
  rwa [image_inf, A.ι.image_preimage_eq_opensRange_inf, A.ι.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_eq_right.2 (hC.trans hW), inf_eq_right.2 (hD.trans hW)] at h2

lemma hasCompactAffineIntersections_open_subscheme (hX : Good2 X) (W : X.Opens) : Good2 W.toScheme := by
  intro A B hA hB
  have h := hX _ _ (hA.image_of_isOpenImmersion W.ι) (hB.image_of_isOpenImmersion W.ι)
  rw [← image_inf] at h
  rw [W.ι.isOpenEmbedding.isEmbedding.isCompact_iff]
  convert h using 1
  simp

lemma exists_cover (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∃ l : List X.Opens, (∀ B ∈ l, IsAffineOpen B ∧ B ≤ W) ∧ lsup l = W := by
  let ι := {B : X.Opens // IsAffineOpen B ∧ B ≤ W}
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover (fun i : ι => ((i.1 : X.Opens) : Set X)) (fun i => i.1.isOpen)
    (by
      intro x hx
      have hb : ∀ {U : X.Opens} {x : X}, x ∈ U → ∃ U' ∈ X.affineOpens, x ∈ U' ∧ U' ≤ U :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens X)
      obtain ⟨B, hB, hxB, hBW⟩ := hb (U := W) hx
      exact Set.mem_iUnion.2 ⟨⟨B, hB, hBW⟩, hxB⟩)
  refine ⟨t.toList.map Subtype.val, ?_, ?_⟩
  · intro B hB
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hB
    exact i.2
  · apply le_antisymm
    · apply lsup_le
      intro B hB
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hB
      exact i.2.2
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
      exact le_lsup (List.mem_map.2 ⟨i, Finset.mem_toList.2 hi, rfl⟩) hxi

end opens

section ind
variable (P : Scheme.{0} → Prop) (hA : ∀ (X : Scheme.{0}) [IsAffine X], P X)
  (hS : ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) → U ⊔ V = ⊤ →
    P U.toScheme → P V.toScheme → P (U ⊓ V).toScheme → P X)
include hA hS

omit hS in
lemma empty_case (Y : Scheme.{0}) (htop : lsup ([] : List Y.Opens) = ⊤) : P Y := by
  have : IsEmpty Y := by
    constructor
    intro x
    have hx : x ∈ (⊤ : Y.Opens) := trivial
    rw [← htop, lsup_nil] at hx
    exact hx
  exact hA Y

lemma stage1 (n : ℕ) : ∀ (Y : Scheme.{0}) (l : List Y.Opens), l.length = n → Good Y →
    (∀ B ∈ l, IsAffineOpen B) → lsup l = ⊤ → P Y := by
  induction n with
  | zero =>
    intro Y l hl _ _ htop
    rw [List.eq_nil_of_length_eq_zero hl] at htop
    exact empty_case P hA Y htop
  | succ n ih =>
    intro Y l hl hG hl' htop
    cases l with
    | nil => simp at hl
    | cons A l =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hAff : IsAffineOpen A := hl' A (by simp)
      have hlA : ∀ B ∈ l, IsAffineOpen B := fun B hB => hl' B (by simp [hB])
      have htop' : lsup l ⊔ A = ⊤ := by rw [sup_comm, ← lsup_cons]; exact htop
      apply hS Y (lsup l) A (isCompact_lsup l fun B hB => (hlA B hB).isCompact) hAff.isCompact htop'
      · apply ih (lsup l).toScheme (l.map ((lsup l).ι ⁻¹ᵁ ·)) (by simp [hl]) (good_open hG _)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          exact affine_preimage _ (le_lsup hC) (hlA C hC)
        · rw [← preimage_lsup, Scheme.Opens.ι_preimage_self]
      · have : IsAffine A.toScheme := hAff
        exact hA A.toScheme
      · apply ih (lsup l ⊓ A).toScheme ((l.map (· ⊓ A)).map ((lsup l ⊓ A).ι ⁻¹ᵁ ·)) (by simp [hl])
          (good_open hG _)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hC
          refine affine_preimage _ ?_ (hG D A (hlA D hD) hAff)
          rw [lsup_inf]
          exact le_lsup (List.mem_map.2 ⟨D, hD, rfl⟩)
        · rw [← preimage_lsup, ← lsup_inf, Scheme.Opens.ι_preimage_self]

lemma stage2 (n : ℕ) : ∀ (Y : Scheme.{0}) (l : List Y.Opens), l.length = n → Good2 Y →
    (∀ B ∈ l, IsAffineOpen B) → lsup l = ⊤ → P Y := by
  induction n with
  | zero =>
    intro Y l hl _ _ htop
    rw [List.eq_nil_of_length_eq_zero hl] at htop
    exact empty_case P hA Y htop
  | succ n ih =>
    intro Y l hl hG hl' htop
    cases l with
    | nil => simp at hl
    | cons A l =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hAff : IsAffineOpen A := hl' A (by simp)
      have hlA : ∀ B ∈ l, IsAffineOpen B := fun B hB => hl' B (by simp [hB])
      have htop' : lsup l ⊔ A = ⊤ := by rw [sup_comm, ← lsup_cons]; exact htop
      apply hS Y (lsup l) A (isCompact_lsup l fun B hB => (hlA B hB).isCompact) hAff.isCompact htop'
      · apply ih (lsup l).toScheme (l.map ((lsup l).ι ⁻¹ᵁ ·)) (by simp [hl]) (hasCompactAffineIntersections_open_subscheme hG _)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          exact affine_preimage _ (le_lsup hC) (hlA C hC)
        · rw [← preimage_lsup, Scheme.Opens.ι_preimage_self]
      · have : IsAffine A.toScheme := hAff
        exact hA A.toScheme
      · have hc : IsCompact ((lsup l ⊓ A : Y.Opens) : Set Y) := by
          rw [lsup_inf]
          apply isCompact_lsup
          intro B hB
          obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hB
          exact hG D A (hlA D hD) hAff
        obtain ⟨l2, hl2, hs2⟩ := exists_cover _ hc
        apply stage1 P hA hS l2.length (lsup l ⊓ A).toScheme (l2.map ((lsup l ⊓ A).ι ⁻¹ᵁ ·)) (by simp)
          (good_affine A _ hAff inf_le_right)
        · intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hB
          exact affine_preimage _ (hl2 C hC).2 (hl2 C hC).1
        · rw [← preimage_lsup, hs2, Scheme.Opens.ι_preimage_self]

end ind

theorem ContInd_of : LateralTheory.E.ContPf.ContInd := by
  intro P hA hS X _ _
  have hc : IsCompact ((⊤ : X.Opens) : Set X) := by simpa using isCompact_univ
  obtain ⟨l, hl, hs⟩ := exists_cover (⊤ : X.Opens) hc
  refine stage2 P hA hS l.length X l rfl ?_ (fun B hB => (hl B hB).1) hs
  intro A B hA' hB'
  rw [TopologicalSpace.Opens.coe_inf]
  exact QuasiSeparatedSpace.inter_isCompact _ _ A.isOpen hA'.isCompact B.isOpen hB'.isCompact

end LateralTheory.E.ContIndPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DiscLvlPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.DiscLvlPf

variable (R : Type) [CommRing R]

def e0 (E : Spc) : ((chains R).obj E).X 0 ≅ (free R).obj (E.obj (op (SimplexCategory.mk 0))) :=
  ((chainsN R).obj E).extendXIso ComplexShape.embeddingDownNat (i := 0) rfl

theorem etale_discrete_chains_degree_zero_iso_free_naturality {E E' : Spc} (g : E ⟶ E') :
    ((chains R).map g).f 0 ≫ (e0 R E').hom = (e0 R E).hom ≫ (free R).map (g.app (op (SimplexCategory.mk 0))) := by
  have : ((chains R).map g).f 0 = (e0 R E).hom ≫ ((chainsN R).map g).f 0 ≫ (e0 R E').inv :=
    HomologicalComplex.extendMap_f (φ := (chainsN R).map g) (e := ComplexShape.embeddingDownNat) (i := 0) (i' := 0) rfl
  rw [this]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem d_zero (P : PSh) : ((chains R).obj (disc.obj P)).d (-1) 0 = 0 := by
  change (HomologicalComplex.extend ((chainsN R).obj (disc.obj P)) ComplexShape.embeddingDownNat).d (-1) 0 = 0
  rw [HomologicalComplex.extend_d_eq (K := (chainsN R).obj (disc.obj P)) (e := ComplexShape.embeddingDownNat) (i' := -1) (j' := 0) (i := 1) (j := 0) rfl rfl]
  have : ((chainsN R).obj (disc.obj P)).d 1 0 = 0 := by
    change (AlgebraicTopology.AlternatingFaceMapComplex.obj (((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj P))).d (0 + 1) 0 = 0
    have h01 : (((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj P)).δ (0 : Fin 2) =
      (((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj P)).δ (1 : Fin 2) := rfl
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, Fin.sum_univ_two, h01]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul, add_neg_cancel]
  rw [this, zero_comp, comp_zero]

def e0d (P : PSh) : ((chains R).obj (disc.obj P)).X 0 ≅ (free R).obj P := e0 R (disc.obj P)

@[reassoc]
theorem etale_discrete_simplicial_chains_degree_zero_iso_naturality {P Q : PSh} (h : P ⟶ Q) :
    ((chains R).map (disc.map h)).f 0 ≫ (e0d R Q).hom = (e0d R P).hom ≫ (free R).map h :=
  etale_discrete_chains_degree_zero_iso_free_naturality R (disc.map h)

def pr (P : PSh) : (chains R).obj (disc.obj P) ⟶ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj P) :=
  HomologicalComplex.mkHomToSingle (e0d R P).hom (fun i hi => by
    have hi' : i = -1 := by simp at hi; omega
    subst hi'
    rw [d_zero, zero_comp])

def sec (P : PSh) : (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj P) ⟶ (chains R).obj (disc.obj P) :=
  HomologicalComplex.mkHomFromSingle (e0d R P).inv (fun k hk =>
    (LateralTheory.E.CechFiltPf.chains_isZero R (disc.obj P) k (by simp at hk; omega)).eq_of_tgt _ _)

theorem sec_pr (P : PSh) : sec R P ≫ pr R P = 𝟙 _ := by
  ext
  simp [sec, pr]

theorem pr_comm {P Q : PSh} (h : P ⟶ Q) :
    (chains R).map (disc.map h) ≫ pr R Q = pr R P ≫ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h) := by
  ext
  simp [pr, etale_discrete_simplicial_chains_degree_zero_iso_naturality_assoc, HomologicalComplex.single_map_f_self]

theorem sec_comm {P Q : PSh} (h : P ⟶ Q) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h) ≫ sec R Q = sec R P ≫ (chains R).map (disc.map h) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, sec, HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  rw [Iso.eq_inv_comp, ← etale_discrete_simplicial_chains_degree_zero_iso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

theorem cone_map_congr {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) {a a' : K₁ ⟶ K₂} {b b' : L₁ ⟶ L₂}
    (c : φ₁ ≫ b = a ≫ φ₂) (c' : φ₁ ≫ b' = a' ≫ φ₂) (ha : a = a') (hb : b = b') :
    mappingCone.map φ₁ φ₂ a b c = mappingCone.map φ₁ φ₂ a' b' c' := by
  subst ha hb; rfl

theorem pull_comp' {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem pull_id' (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

end LateralTheory.E.DiscLvlPf

open LateralTheory.E.DiscLvlPf in
theorem LateralTheory.E.DiscLvlPf.DiscLvl_of : LateralTheory.E.CechFiltPf.DiscLvl := by
  intro R _ F P Q h m hs
  let φ₁ := (chains R).map (disc.map h)
  let φ₂ := (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h)
  let Pm := mappingCone.map φ₁ φ₂ (pr R P) (pr R Q) (pr_comm R h)
  let Sm := mappingCone.map φ₂ φ₁ (sec R P) (sec R Q) (sec_comm R h)
  have hSP : Sm ≫ Pm = 𝟙 _ := by
    rw [← mappingCone.map_comp]
    rw [cone_map_congr R φ₂ φ₂ _ (by rw [Category.id_comp, Category.comp_id]) (sec_pr R P) (sec_pr R Q)]
    exact mappingCone.map_id φ₂
  have : Subsingleton (HK R (mappingCone φ₁) F m) := hs
  refine Function.Injective.subsingleton (f := HK.pull R Pm F m) ?_
  intro x y hxy
  have := congrArg (HK.pull R Sm F m) hxy
  rwa [← pull_comp', ← pull_comp', hSP, pull_id', pull_id'] at this
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EmptyVan2
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.EmptyVan₂

theorem sec_subsingleton {R : Type} [CommRing R] (G : Shv R) (X : Scheme.{0}) [IsEmpty X] :
    Subsingleton (G.obj.obj (op X)) := by
  have h := Sheaf.isTerminalOfBotCover G X (Scheme.bot_mem_grothendieckTopology X)
  constructor
  intro a b
  have e := h.hom_ext (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ a))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ b))
  have := congrArg (fun f => f.hom (1 : ULift.{1} R)) e
  simpa using this

theorem free_isZero {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] :
    IsZero ((free R).obj (yoneda.obj X)) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).injective
  ext U x
  rcases isEmpty_or_nonempty U.unop with hU | hU
  · have := sec_subsingleton (R := R) ((free R).obj (yoneda.obj X)) U.unop
    exact @Subsingleton.elim _ this _ _
  · have : IsEmpty ((yoneda.obj X).obj U) := ⟨fun (f : U.unop ⟶ X) => IsEmpty.false (f.base (Classical.arbitrary U.unop))⟩
    have hx : x = 0 := Subsingleton.elim (α := ULift.{1} ((yoneda.obj X).obj U) →₀ ULift.{1} R) x 0
    rw [hx, map_zero, map_zero]

theorem chains_X_isZero {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] (m : ℤ) :
    IsZero (((chains R).obj (sch.obj X)).X m) := by
  rcases le_or_gt m 0 with h | h
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, m = -(p : ℤ) := ⟨(-m).toNat, by omega⟩
    exact (free_isZero (R := R) X).of_iso (chainsXIso R _ p)
  · exact HomologicalComplex.isZero_extend_X _ _ m (fun i => by
      change -(i : ℤ) ≠ m; omega)

theorem cc_subsingleton {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ}
    (hK : ∀ m, IsZero (K.X m)) (n : ℤ) : Subsingleton (CohomologyClass K L n) := by
  have : Subsingleton (Cochain K L n) :=
    ⟨fun a b => Cochain.ext _ _ fun p q hpq => (hK p).eq_of_src _ _⟩
  have : Subsingleton (Cocycle K L n) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  constructor
  intro a b
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [Subsingleton.elim a b]

theorem EmptyVan_of : LateralTheory.E.CoverPf.EmptyVan := by
  intro _ q _ i n S _ hS x
  have : IsEmpty (Spec (CommRingCat.of S)) :=
    ⟨fun p => (p : PrimeSpectrum S).isPrime.ne_top (Subsingleton.elim _ _)⟩
  have := cc_subsingleton (L := res (ZMod q) (tw q i)) (chains_X_isZero (R := ZMod q) (Spec (CommRingCat.of S))) (n + 1)
  exact Subsingleton.elim _ _

end LateralTheory.E.EmptyVan₂
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtAlgPf
section
open CategoryTheory LateralTheory.E.t_E3Cut

namespace LateralTheory.E.EtAlgPf

theorem key (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B] (Q : Ideal B) [Q.IsPrime]
    (c : B) : ∃ p : Polynomial A, (∃ n, algebraMap A B (p.coeff n) ∉ Q) ∧ p.eval₂ (algebraMap A B) c ∈ Q := by
  let P := Q.comap (algebraMap A B)
  have : Q.LiesOver P := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  have : Algebra.IsUnramifiedAt A Q := inferInstance
  have : Module.Finite P.ResidueField Q.ResidueField := inferInstance
  have : IsScalarTower A P.ResidueField Q.ResidueField := inferInstance
  set x := algebraMap B Q.ResidueField c
  have hx : IsIntegral P.ResidueField x := Algebra.IsIntegral.isIntegral x
  let p := minpoly P.ResidueField x
  have hp0 : p ≠ 0 := minpoly.ne_zero hx
  let M := nonZeroDivisors (A ⧸ P)
  let q := IsLocalization.integerNormalization M p
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_spec M p
  have hq0 : q ≠ 0 := by
    intro h; exact hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl p).1 h)
  have hqm : q.map (algebraMap (A ⧸ P) P.ResidueField) = Polynomial.C (algebraMap (A ⧸ P) P.ResidueField b) * p := by
    rw [hb.2, ← Polynomial.smul_eq_C_mul, algebraMap_smul]
  obtain ⟨r, hr⟩ := Polynomial.map_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective q
  obtain ⟨n, hn⟩ : ∃ n, q.coeff n ≠ 0 := by
    by_contra h; push_neg at h; exact hq0 (Polynomial.ext h)
  refine ⟨r, ⟨n, ?_⟩, ?_⟩
  · intro hm; apply hn
    rw [← hr, Polynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]; exact hm
  · rw [← Ideal.algebraMap_residueField_eq_zero, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq]
    have e1 : algebraMap A Q.ResidueField = (algebraMap P.ResidueField Q.ResidueField).comp
        ((algebraMap (A ⧸ P) P.ResidueField).comp (Ideal.Quotient.mk P)) := by
      ext a
      rw [RingHom.comp_apply, RingHom.comp_apply, ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply A (A ⧸ P) P.ResidueField,
        ← IsScalarTower.algebraMap_apply A P.ResidueField Q.ResidueField]
    rw [e1, ← Polynomial.eval₂_map, ← Polynomial.map_map, hr, hqm, ← Polynomial.aeval_def, map_mul,
      minpoly.aeval, mul_zero]

theorem EtAlg_of : LateralTheory.E.AlgResPropsPf.EtAlg := by
  intro A B f hf
  let _ := f.hom.toAlgebra
  have : Algebra.Etale A B := hf
  intro Q hQ c
  exact key A B Q c

end LateralTheory.E.EtAlgPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GlueRelPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 CochainComplex.HomComplex

namespace LateralTheory.E.GlueRelPf

def obs (q : ℕ) [NeZero q] {U E : Spc} (u : U ⟶ E) (i m : ℤ) : Ht q U m i →+ Hrel (ZMod q) u (tw q i) (m + 1) :=
  HK.pre (ZMod q) (CochainComplex.mappingCone.fst ((chains (ZMod q)).map u)) (tw q i) m (m + 1) (add_comm 1 m)

def ConeExact : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ),
  Function.Exact (HK.pull R φ F m) (HK.pre R (CochainComplex.mappingCone.fst φ) F m (m + 1) (add_comm 1 m))

end LateralTheory.E.GlueRelPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LSecGluePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.L_sec_gluePf

theorem typeSheaf {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property

end LateralTheory.E.L_sec_gluePf
end
end

