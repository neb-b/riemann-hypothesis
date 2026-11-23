module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalRingCardinality.DataLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueLineBundles
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GlueLineBundle

variable {X W : Scheme.{0}}

def imU (j : W ⟶ X) [IsOpenImmersion j] (V : W.Opens) : Γ(W, V)ˣ →* Γ(X, j ''ᵁ V)ˣ :=
  Units.map (j.appIso V).inv.hom

theorem res_pull_imU (j : W ⟶ X) [IsOpenImmersion j] (V : W.Opens) (v : Γ(W, V)ˣ) :
    res (j.preimage_image_eq V).ge (pullU j _ (imU j V v)) = v := by
  apply Units.ext
  have h := congrArg (fun q => q.hom v.val) (j.appIso_inv_appLE (U := V) (V := V) (j.preimage_image_eq V).ge)
  have e : (homOfLE (le_refl V)) = 𝟙 V := rfl
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  refine h.trans ?_
  show (W.presheaf.map (𝟙 (Opposite.op V))).hom v.val = v.val
  rw [W.presheaf.map_id]; rfl

theorem gm_imU (j : W ⟶ X) [IsOpenImmersion j] {Y : Scheme.{0}} (f : Y ⟶ W) (y : Y) (V : W.Opens)
    (hy : f y ∈ V) (v : Γ(W, V)ˣ) : gm (f ≫ j) y (j ''ᵁ V) (imU j V v) = gm f y V v := by
  have h1 : j (f y) ∈ j ''ᵁ V := j.apply_mem_image_iff.2 hy
  rw [← gm_pull f j y _ h1, ← gm_res f y (j.preimage_image_eq V).ge hy, res_pull_imU]

end GlobalTheory.GlueLineBundle

namespace GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}}

theorem gm_id_val {O : X.Opens} {x : X} (hx : x ∈ O) (a : Γ(X, O)ˣ) :
    (gm (𝟙 X) x O a).val = X.presheaf.germ O x hx a.val := by
  rw [gm_val _ x O hx]; rfl

theorem unit_ext_imm {O : X.Opens} {a b : Γ(X, O)ˣ}
    (h : ∀ x ∈ O, ∃ (W : Scheme.{0}) (j : W ⟶ X) (_ : IsOpenImmersion j) (w : W), j w = x ∧
      gm j w O a = gm j w O b) : a = b := by
  apply unit_ext
  intro x hx
  obtain ⟨W, j, hj, w, rfl, e⟩ := h x hx
  apply Units.ext
  rw [gm_id_val hx, gm_id_val hx]
  have e' := congrArg Units.val e
  rw [gm_val j w O hx, gm_val j w O hx, ← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply] at e'
  exact (asIso (j.stalkMap w)).commRingCatIsoToRingEquiv.injective e'

end GlobalTheory.GlueLineBundle

namespace GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} (V : A → X.Opens) (M : ∀ a, LB (V a).toScheme)

abbrev NU (p : Σ a, (M a).ι) : X.Opens := (V p.1).ι ''ᵁ (M p.1).U p.2

def GSpec (p q : Σ a, (M a).ι) (u : Γ(X, NU V M p ⊓ NU V M q)ˣ) : Prop :=
  ∀ (c : A) (Y : Scheme.{0}) (f : Y ⟶ (V c).toScheme) (y : Y) (j l : (M c).ι),
    (⟨c, j⟩ : Σ a, (M a).ι) = p → (⟨c, l⟩ : Σ a, (M a).ι) = q → f y ∈ (M c).U j → f y ∈ (M c).U l →
    gm (f ≫ (V c).ι) y (NU V M p ⊓ NU V M q) u = gm f y ((M c).U j ⊓ (M c).U l) ((M c).g j l)

theorem mem_of_mem_NU {p : Σ a, (M a).ι} {x : X} (hx : x ∈ NU V M p) : x ∈ V p.1 :=
  Scheme.Opens.ι_image_le _ _ hx

theorem exists_gSpec (p q : Σ a, (M a).ι) : ∃ u, GSpec V M p q u := by
  obtain ⟨a, i⟩ := p
  obtain ⟨b, k⟩ := q
  by_cases hab : a = b
  · subst hab
    have hle : (V a).ι ''ᵁ (M a).U i ⊓ (V a).ι ''ᵁ (M a).U k ≤ (V a).ι ''ᵁ ((M a).U i ⊓ (M a).U k) :=
      fun x hx => by
        obtain ⟨w, hw, rfl⟩ := hx.1
        exact (V a).ι.apply_mem_image_iff.2 ⟨hw, (V a).ι.apply_mem_image_iff.1 hx.2⟩
    refine ⟨res hle (imU (V a).ι _ ((M a).g i k)), ?_⟩
    intro c Y f y j l h1 h2 hj hl
    obtain ⟨rfl, h1'⟩ := Sigma.mk.inj_iff.1 h1
    obtain rfl := eq_of_heq h1'
    obtain rfl := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
    have hm : (f ≫ (V c).ι) y ∈ (V c).ι ''ᵁ (M c).U j ⊓ (V c).ι ''ᵁ (M c).U l :=
      ⟨(V c).ι.apply_mem_image_iff.2 hj, (V c).ι.apply_mem_image_iff.2 hl⟩
    exact (gm_res (f ≫ (V c).ι) y hle hm _).trans (gm_imU (V c).ι f y ((M c).U j ⊓ (M c).U l) ⟨hj, hl⟩ _)
  · refine ⟨1, ?_⟩
    intro c Y f y j l h1 h2
    exact absurd ((Sigma.mk.inj_iff.1 h1).1.symm.trans (Sigma.mk.inj_iff.1 h2).1) hab

def glue : LB X where
  ι := Σ a, (M a).ι
  U := NU V M
  g p q := Classical.choose (exists_gSpec V M p q)

theorem gm_glue_g (a : A) {Y : Scheme.{0}} (f : Y ⟶ (V a).toScheme) (y : Y) (i k : (M a).ι)
    (hi : f y ∈ (M a).U i) (hk : f y ∈ (M a).U k) :
    gm (f ≫ (V a).ι) y _ ((glue V M).g ⟨a, i⟩ ⟨a, k⟩) = gm f y ((M a).U i ⊓ (M a).U k) ((M a).g i k) :=
  Classical.choose_spec (exists_gSpec V M ⟨a, i⟩ ⟨a, k⟩) a Y f y i k rfl rfl hi hk

theorem gm_glue_g' (a : A) (w : (V a).toScheme) (i k : (M a).ι)
    (hi : w ∈ (M a).U i) (hk : w ∈ (M a).U k) :
    gm (V a).ι w _ ((glue V M).g ⟨a, i⟩ ⟨a, k⟩) = gm (𝟙 _) w ((M a).U i ⊓ (M a).U k) ((M a).g i k) := by
  have := gm_glue_g V M a (𝟙 _) w i k hi hk
  rwa [Category.id_comp] at this

variable {V M}

theorem eq_of_mem (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) {a b : A} (w : (V a).toScheme) {k : (M b).ι}
    (h : (V a).ι w ∈ NU V M ⟨b, k⟩) : a = b :=
  hdisj a b _ w.2 (mem_of_mem_NU V M h)

theorem glue_isLB (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) (hcov : ∀ x, ∃ a, x ∈ V a)
    (hM : ∀ a, (M a).IsLB) : (glue V M).IsLB := {
  cover := top_le_iff.1 fun x _ => by
    obtain ⟨a, ha⟩ := hcov x
    obtain ⟨w, rfl⟩ : ∃ w : (V a).toScheme, (V a).ι w = x := ⟨⟨x, ha⟩, rfl⟩
    obtain ⟨i, hi⟩ := exists_chart (hM a) w
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, i⟩, (V a).ι.apply_mem_image_iff.2 hi⟩
  g_self p := by
    obtain ⟨a, i⟩ := p
    apply unit_ext_imm
    intro x hx
    have hx2 : x ∈ (V a).ι ''ᵁ (M a).U i := hx
    obtain ⟨w, hw, rfl⟩ := hx2
    have hx' : (V a).ι w ∈ (glue V M).U ⟨a, i⟩ := hx
    refine ⟨_, (V a).ι, inferInstance, w, rfl, ?_⟩
    rw [gm_res (V a).ι w _ hx', map_one, gm_glue_g' V M a w i i hw hw]
    exact gm_self (hM a) (𝟙 _) w hw
  cocycle p q r := by
    obtain ⟨a, i⟩ := p
    obtain ⟨b, k⟩ := q
    obtain ⟨c, l⟩ := r
    apply unit_ext_imm
    intro x hx
    have h1 : x ∈ (V a).ι ''ᵁ (M a).U i := hx.1.1
    obtain ⟨w, hw, rfl⟩ := h1
    have h2 : (V a).ι w ∈ NU V M ⟨b, k⟩ := hx.1.2
    have h3 : (V a).ι w ∈ NU V M ⟨c, l⟩ := hx.2
    have hb := eq_of_mem hdisj w h2
    have hc := eq_of_mem hdisj w h3
    subst hb hc
    have hx' : (V a).ι w ∈ (glue V M).U ⟨a, i⟩ ⊓ (glue V M).U ⟨a, k⟩ ⊓ (glue V M).U ⟨a, l⟩ := hx
    have hk := (V a).ι.apply_mem_image_iff.1 h2
    have hl := (V a).ι.apply_mem_image_iff.1 h3
    refine ⟨_, (V a).ι, inferInstance, w, rfl, ?_⟩
    rw [map_mul, gm_res (V a).ι w _ hx', gm_res (V a).ι w _ hx', gm_res (V a).ι w _ hx', gm_glue_g' V M a w i k hw hk,
      gm_glue_g' V M a w k l hk hl, gm_glue_g' V M a w i l hw hl]
    exact gm_cocycle (hM a) (𝟙 _) w hw hk hl }

end GlobalTheory.GlueLineBundle

namespace GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} {V : A → X.Opens} {M : ∀ a, LB (V a).toScheme}

theorem exists_isoUnit (a : A) (J : PUnit → (glue V M).ι) (k : (M a).ι) :
    ∃ u : Γ((V a).toScheme, ((glue V M).pull (V a).ι).U J ⊓ (M a).U k)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ (V a).toScheme) (y : Y) (i : (M a).ι),
        J PUnit.unit = (⟨a, i⟩ : Σ a, (M a).ι) → f y ∈ (M a).U i → f y ∈ (M a).U k →
        gm f y _ u = gm f y ((M a).U i ⊓ (M a).U k) ((M a).g i k) := by
  by_cases h : ∃ i' : (M a).ι, J PUnit.unit = (⟨a, i'⟩ : Σ a, (M a).ι)
  · obtain ⟨i', hi'⟩ := h
    have hle : ((glue V M).pull (V a).ι).U J ⊓ (M a).U k ≤ (M a).U i' ⊓ (M a).U k := fun w hw => by
      have h1 : (V a).ι w ∈ (glue V M).U (J PUnit.unit) := mem_pull.1 hw.1
      rw [hi'] at h1
      exact ⟨(V a).ι.apply_mem_image_iff.1 h1, hw.2⟩
    refine ⟨res hle ((M a).g i' k), fun Y f y i hJ hi hk => ?_⟩
    obtain rfl := sigma_mk_injective (hi'.symm.trans hJ)
    have hm : f y ∈ ((glue V M).pull (V a).ι).U J ⊓ (M a).U k := by
      refine ⟨mem_pull.2 ?_, hk⟩
      show (V a).ι (f y) ∈ (glue V M).U (J PUnit.unit)
      rw [hi']
      exact (V a).ι.apply_mem_image_iff.2 hi
    exact gm_res f y hle hm _
  · exact ⟨1, fun Y f y i hJ => absurd ⟨i, hJ⟩ h⟩

def isoGen (a : A) : LB.Iso (M a) ((glue V M).pull (V a).ι) :=
  ⟨fun p => Classical.choose (exists_isoUnit a p.1 p.2)⟩

theorem pgen_isoGen (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) (hM : ∀ a, (M a).IsLB) (a : A) :
    PGen (isoGen (V := V) (M := M) a) := by
  intro Y f y j j' k k' hj hj' hk hk'
  obtain ⟨b, i⟩ := j
  obtain ⟨b', i'⟩ := j'
  have hb : a = b := eq_of_mem hdisj (f y) hj
  have hb' : a = b' := eq_of_mem hdisj (f y) hj'
  subst hb hb'
  have hi : f y ∈ (M a).U i := (V a).ι.apply_mem_image_iff.1 hj
  have hi' : f y ∈ (M a).U i' := (V a).ι.apply_mem_image_iff.1 hj'
  have e1 : gw (isoGen a) f y ⟨a, i⟩ k = gm f y _ ((M a).g i k) :=
    Classical.choose_spec (exists_isoUnit (V := V) (M := M) a (fun _ => ⟨a, i⟩) k) Y f y i rfl hi hk
  have e2 : gw (isoGen a) f y ⟨a, i'⟩ k' = gm f y _ ((M a).g i' k') :=
    Classical.choose_spec (exists_isoUnit (V := V) (M := M) a (fun _ => ⟨a, i'⟩) k') Y f y i' rfl hi' hk'
  rw [e1, e2, gm_glue_g V M a f y i i' hi hi', mul_right_comm, gm_cocycle (hM a) f y hi hi' hk',
    ← gm_cocycle (hM a) f y hi hk hk', mul_inv_cancel_right]

end GlobalTheory.GlueLineBundle


open GlobalTheory.GlueLineBundle in
theorem GlobalTheory.glue_lineBundles : ∀ (X : Scheme.{0}) (A : Type) (V : A → X.Opens), (∀ a b x, x ∈ V a → x ∈ V b → a = b) → (∀ x, ∃ a, x ∈ V a) → ∀ (M : ∀ a, LB (V a).toScheme), (∀ a, (M a).IsLB) → ∃ N : LB X, N.IsLB ∧ ∀ a, LBIso (N.pull (V a).ι) (M a) := by
  intro X A V hdisj hcov M hM
  exact ⟨glue V M, glue_isLB hdisj hcov hM, fun a =>
    LBIso.symm ⟨isoGen a, (isGen_iff _).2 (pgen_isoGen hdisj hM a)⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImageFiniteMemSubringStatement
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_image_mem_subring : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (iq : FractionRing O →+* Qbar l), (∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) → ∃ T : Finset (Qbar l), ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) → (↑T ⊆ (R : Set (Qbar l))) → ∀ x : O, iq (algebraMap O (FractionRing O) x) ∈ R := by
  first | exact @GlobalTheory.image_finite_mem_subring | exact GlobalTheory.image_finite_mem_subring | (intros; apply GlobalTheory.image_finite_mem_subring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoOfDisjointCover
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.DisjointCoverLB

theorem gm_imageUnit {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsOpenImmersion ι] (V : Z.Opens) (v : Γ(Z, V)ˣ) (z : Z)
    (hz : z ∈ V) :
    gm ι z (ι ''ᵁ V) (GlobalTheory.ExtendLineBundle.imageUnit ι V v) = gm (𝟙 Z) z V v := by
  have hz' : ι z ∈ ι ''ᵁ V := ι.apply_mem_image_iff.2 hz
  apply Units.ext
  rw [gm_val ι z _ hz', gm_val (𝟙 Z) z V hz]
  have e := congrArg (fun q => q.hom v.val) (ι.appIso_inv_app V)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  change (Z.presheaf.germ _ z _).hom ((ι.app _).hom ((ι.appIso V).inv.hom v.val)) = _
  rw [e]
  exact TopCat.Presheaf.germ_res_apply Z.presheaf _ z _ _

theorem units_eq_of_gm {X : Scheme.{0}} {V : X.Opens} {a b : Γ(X, V)ˣ}
    (h : ∀ x ∈ V, ∃ (Z : Scheme.{0}) (ι : Z ⟶ X) (_ : IsOpenImmersion ι) (z : Z), ι z = x ∧ gm ι z V a = gm ι z V b) :
    a = b := by
  refine unit_ext fun x hx => ?_
  obtain ⟨Z, ι, hι, z, rfl, e⟩ := h x hx
  have e' := congrArg Units.val e
  rw [gm_val ι z V hx, gm_val ι z V hx, ← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply] at e'
  have key := (ConcreteCategory.bijective_of_isIso (ι.stalkMap z)).1 e'
  apply Units.ext
  rw [gm_val (𝟙 X) (ι z) V hx, gm_val (𝟙 X) (ι z) V hx]
  exact key

end GlobalTheory.DisjointCoverLB

namespace GlobalTheory.DisjointCoverLB

theorem lbIso_of_disjoint_cover : ∀ (Y : Scheme.{0}) (A : Type) (W : A → Y.Opens), (∀ a b y, y ∈ W a → y ∈ W b → a = b) →
    (∀ y, ∃ a, y ∈ W a) → ∀ (P Q : LB Y), P.IsLB → Q.IsLB → (∀ a, LBIso (P.pull (W a).ι) (Q.pull (W a).ι)) →
    LBIso P Q := by
  intro Y A W hdisj hcov P Q hP hQ hw
  choose w hwg using hw
  have hmemC : ∀ a (c : Q.ι × P.ι) (y : W a), (W a).ι y ∈ (LB.div Q P).U c →
      y ∈ (LB.div (Q.pull (W a).ι) (P.pull (W a).ι)).U (fun _ => c.1, fun _ => c.2) :=
    fun a c y hy => ⟨mem_pull.2 hy.1, mem_pull.2 hy.2⟩
  have hpt : ∀ a (x : Y) (hx : x ∈ W a), ∃ y : W a, (W a).ι y = x := fun a x hx => ⟨⟨x, hx⟩, rfl⟩
  have hin : ∀ a (y : W a), (W a).ι y ∈ W a := fun a y => y.2
  have hle : ∀ a (c : Q.ι × P.ι), (LB.div Q P).U c ⊓ W a ≤
      (W a).ι ''ᵁ (LB.div (Q.pull (W a).ι) (P.pull (W a).ι)).U (fun _ => c.1, fun _ => c.2) := by
    intro a c x hx
    obtain ⟨y, rfl⟩ := hpt a x hx.2
    exact (W a).ι.apply_mem_image_iff.2 (hmemC a c y hx.1)
  let u : ∀ (c : Q.ι × P.ι) a, Γ(Y, (LB.div Q P).U c ⊓ W a)ˣ := fun c a =>
    res (hle a c) (GlobalTheory.ExtendLineBundle.imageUnit (W a).ι _ ((w a).s (fun _ => c.1, fun _ => c.2)))
  have glue : ∀ c : Q.ι × P.ι, ∃ s : Γ(Y, (LB.div Q P).U c)ˣ,
      ∀ a, res (inf_le_left : (LB.div Q P).U c ⊓ W a ≤ _) s = u c a := fun c =>
    glue_unit _ (fun a => (LB.div Q P).U c ⊓ W a) (fun a => inf_le_left)
      (fun x hx => by obtain ⟨a, ha⟩ := hcov x; exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hx, ha⟩) (u c)
      (fun a b x hx => by obtain rfl := hdisj a b x hx.1.2 hx.2.2; rfl)
  choose s hs using glue
  have key : ∀ (c : Q.ι × P.ι) a (y : W a), (W a).ι y ∈ (LB.div Q P).U c →
      gm (W a).ι y ((LB.div Q P).U c) (s c) = gw (w a) (𝟙 _) y c.1 (fun _ => c.2) := by
    intro c a y hy
    have hyW : (W a).ι y ∈ (LB.div Q P).U c ⊓ W a := ⟨hy, hin a y⟩
    calc gm (W a).ι y ((LB.div Q P).U c) (s c) = gm (W a).ι y _ (res (inf_le_left : (LB.div Q P).U c ⊓ W a ≤ _) (s c)) :=
          (gm_res (W a).ι y inf_le_left hyW _).symm
      _ = gm (W a).ι y _ (u c a) := by rw [hs c a]
      _ = gm (W a).ι y _ (GlobalTheory.ExtendLineBundle.imageUnit (W a).ι _ ((w a).s (fun _ => c.1, fun _ => c.2))) :=
          by show gm (W a).ι y _ (res (hle a c) _) = _; exact gm_res (W a).ι y (hle a c) hyW _
      _ = gm (𝟙 _) y _ ((w a).s (fun _ => c.1, fun _ => c.2)) := by
          exact gm_imageUnit (W a).ι _ ((w a).s (fun _ => c.1, fun _ => c.2)) y (hmemC a c y hy)
  refine ⟨⟨s⟩, fun c c' => units_eq_of_gm fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := hcov x
  obtain ⟨y, rfl⟩ := hpt a x ha
  refine ⟨W a, (W a).ι, inferInstance, y, rfl, ?_⟩
  have h1 : (W a).ι y ∈ (LB.div Q P).U c := hx.1
  have h2 : (W a).ι y ∈ (LB.div Q P).U c' := hx.2
  have pg := (isGen_iff (w a)).1 (hwg a) (W a) (𝟙 _) y c.1 c'.1 (fun _ => c.2) (fun _ => c'.2) h1.1 h2.1
    (mem_pull.2 h1.2) (mem_pull.2 h2.2)
  rw [gm_pull_g P (W a).ι (𝟙 _) y _ _ (mem_pull.2 h1.2) (mem_pull.2 h2.2), Category.id_comp] at pg
  dsimp only
  refine (gm_res (W a).ι y _ hx _).trans ?_
  rw [key c a y h1]
  refine pg.trans ?_
  refine Eq.trans ?_ (map_mul _ _ _).symm
  exact congrArg₂ (· * ·) (gm_div P Q (W a).ι y c c' hx).symm
    ((gm_res (W a).ι y _ hx _).trans (key c' a y h2)).symm

end GlobalTheory.DisjointCoverLB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocLEqIntVOfDvdUnit
section
open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory

theorem natCast_inv_mem_adicCompletionIntegers {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (hT : (T : 𝓞 F) ∉ v.asIdeal) :
    ((T : v.adicCompletion F) ≠ 0) ∧ (T : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : Valued.v (((T : 𝓞 F) : F) : v.adicCompletion F) = 1 := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) (v := v)).2 hT
  have h2 : (((T : 𝓞 F) : F) : v.adicCompletion F) = (T : v.adicCompletion F) := by
    have : ((T : 𝓞 F) : F) = (T : F) := by push_cast; rfl
    rw [this]
    exact map_natCast (algebraMap F (v.adicCompletion F)) T
  rw [h2] at h1
  have hne : (T : v.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at h1; exact zero_ne_one h1
  refine ⟨hne, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem locL_eq_intV_of_dvd_unit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Fin n → Prop)
    (π c : 𝓞 E) (T : ℕ) (hT : (T : 𝓞 F) ∉ v.asIdeal) (hπc : π * c = (T : 𝓞 E))
    (hΛ : ∀ y, y ∈ Λ ↔ ∀ a, ∃ r : 𝓞 E, y a = r ∧ (P a → π ∣ r)) (y : Fin n → E ⊗[F] v.adicCompletion F) :
    (y ∈ Formalism.L2.Herm.locL v Λ ↔ ∀ a, y a ∈ Formalism.BasicNotions.intV E v) := by
  classical
  have hleft : ∀ r : 𝓞 E, ((r : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ Formalism.BasicNotions.intV E v := fun r =>
    Subring.subset_closure (Or.inl ⟨⟨(r : E), ⟨r, rfl⟩⟩, rfl⟩)
  have hright : ∀ t ∈ v.adicCompletionIntegers F, ((1 : E) ⊗ₜ[F] t) ∈ Formalism.BasicNotions.intV E v := fun t ht =>
    Subring.subset_closure (Or.inr ⟨⟨t, ht⟩, rfl⟩)
  constructor
  · intro hy
    let M : Submodule (Formalism.BasicNotions.intV E v) (Fin n → E ⊗[F] v.adicCompletion F) :=
      { carrier := {y | ∀ a, y a ∈ Formalism.BasicNotions.intV E v}
        add_mem' := fun ha hb a => (Formalism.BasicNotions.intV E v).add_mem (ha a) (hb a)
        zero_mem' := fun _ => (Formalism.BasicNotions.intV E v).zero_mem
        smul_mem' := fun s _ hy a => (Formalism.BasicNotions.intV E v).mul_mem s.2 (hy a) }
    have hle : Formalism.L2.Herm.locL v Λ ≤ M := by
      unfold Formalism.L2.Herm.locL Formalism.UG.latS
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩ a
      obtain ⟨r, hr, -⟩ := (hΛ x).1 hx a
      show Formalism.UG.inclE _ (x a) ∈ Formalism.BasicNotions.intV E v
      rw [hr]; exact hleft r
    exact hle hy
  · intro hy
    obtain ⟨_, hinv⟩ := natCast_inv_mem_adicCompletionIntegers v T hT
    have he : ∀ a, (Pi.single a (1 : E ⊗[F] v.adicCompletion F)) ∈ Formalism.L2.Herm.locL v Λ := by
      intro a
      have hx : (Pi.single a ((π : 𝓞 E) : E) : Fin n → E) ∈ Λ := by
        rw [hΛ]
        intro b
        refine ⟨(Pi.single a π : Fin n → 𝓞 E) b, ?_, fun _ => ?_⟩
        · by_cases h : b = a
          · subst h; simp
          · simp [h]
        · by_cases h : b = a
          · subst h; simp
          · simp [h]
      have hg : (Pi.single a (((π : E)) ⊗ₜ[F] (1 : v.adicCompletion F)) : Fin n → _) ∈
          Formalism.L2.Herm.locL v Λ := by
        unfold Formalism.L2.Herm.locL Formalism.UG.latS
        apply Submodule.subset_span
        refine ⟨_, hx, ?_⟩
        funext b
        by_cases h : b = a
        · subst h; simp [Formalism.UG.inclE]
        · simp [h, Formalism.UG.inclE]
      let s : Formalism.BasicNotions.intV E v :=
        ⟨((c : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹),
          (Formalism.BasicNotions.intV E v).mul_mem (hleft c) (hright _ hinv)⟩
      have hs : (s : E ⊗[F] v.adicCompletion F) * ((π : E) ⊗ₜ[F] (1 : v.adicCompletion F)) = 1 := by
        obtain ⟨hne, -⟩ := natCast_inv_mem_adicCompletionIntegers v T hT
        show ((c : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹) *
          ((π : E) ⊗ₜ[F] (1 : v.adicCompletion F)) = 1
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        have hcπ : (c : E) * (π : E) = (T : E) := by
          rw [mul_comm]; exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hπc
        rw [hcπ]
        have hT1 : (T : E) ⊗ₜ[F] (1 : v.adicCompletion F) = (1 : E) ⊗ₜ[F] (T : v.adicCompletion F) := by
          have e1 := map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E)
            (B := v.adicCompletion F)) T
          have e2 := map_natCast (Algebra.TensorProduct.includeRight (R := F) (A := E)
            (B := v.adicCompletion F)) T
          rw [Algebra.TensorProduct.includeLeftRingHom_apply] at e1
          rw [Algebra.TensorProduct.includeRight_apply] at e2
          rw [e1, e2]
        calc (T : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹
            = ((T : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹) := by
              simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          _ = 1 := by
              rw [hT1, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hne]
              rfl
      have := (Formalism.L2.Herm.locL v Λ).smul_mem s hg
      convert this using 1
      funext b
      by_cases h : b = a
      · subst h
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_same, Pi.single_eq_same, hs]
      · rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, mul_zero]
    have hsum : y = ∑ a, (⟨y a, hy a⟩ : Formalism.BasicNotions.intV E v) • Pi.single a (1 : E ⊗[F] v.adicCompletion F) := by
      funext b
      rw [Finset.sum_apply, Finset.sum_eq_single b]
      · rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_same, mul_one]
      · intro a _ hab
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Pi.single_eq_of_ne (Ne.symm hab), mul_zero]
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [hsum]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (he a)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLawsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localPeriodRingsData_unramified_laws : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, (∀ c : ↥(MaximalUnramifiedExtension l), Per.φB l (C.u c) = C.u (C.σ c)) ∧ (∀ (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)), g (c : Om l) = (c' : Om l) → Per.σB g (C.u c) = C.u c') ∧ (∀ z : ℤ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) = Per.zB l z) ∧ Function.Injective C.ι ∧ (∀ (g : GQ l) (b : Per.Bcris l), C.ι (Per.σB g b) = Per.σD g (C.ι b)) ∧ Per.IsCrisDR l C.ι := by
  first | exact @GlobalTheory.MemLoc.ULaws.u_laws | exact GlobalTheory.MemLoc.ULaws.u_laws | (intros; apply GlobalTheory.MemLoc.ULaws.u_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelLocalGroupEqOfAgreeOffPlacesStatement
section
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepLevel_localGroup_eq_of_agree_off_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad bad' : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (S' : StepLevel F E σ J T f bad') (Q : Set (HeightOneSpectrum (𝓞 F))), (∀ x, (∀ v ∈ Q, bc (prV (E := E) v) x = 1) → (x ∈ S.U ↔ x ∈ S'.U)) → ∀ v, v ∉ Q → S.Uloc v = S'.Uloc v := by
  first | exact @GlobalTheory.stepLevel_uloc_eq_of_agree | exact GlobalTheory.stepLevel_uloc_eq_of_agree | (intros; apply GlobalTheory.stepLevel_uloc_eq_of_agree <;> assumption)
end

