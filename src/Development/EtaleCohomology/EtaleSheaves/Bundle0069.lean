module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0061
public import Development.EtaleCohomology.EtaleSheaves.LeafGlueProperPf
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Development.EtaleCohomology.EtaleSheaves.Bundle0062
public import Development.EtaleCohomology.EtaleSheaves.Bundle0064
public import Development.EtaleCohomology.TateTwists.Bundle0034

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.HensQuot
section
noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC Polynomial IsLocalRing

namespace LateralTheory.E.LeafClosedSH0PfQuot
open LateralTheory.E.E4 LateralTheory.E.LeafClosedSH0Pf

theorem hensQuot {A C : Type} [CommRing A] [HenselianLocalRing A] [CommRing C] [IsLocalRing C] (g : A →+* C)
    (hg : Function.Surjective g) : HenselianLocalRing C := by
  have hloc : IsLocalHom g := IsLocalHom.of_surjective g hg
  refine { is_henselian := ?_ }
  intro p hp a0 h0 h1
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.lifts_iff_coeff_lifts p |>.mpr (fun n => hg _)) hp
  obtain ⟨b0, rfl⟩ := hg a0
  have e : ∀ (Q : A[X]) (x : A), g (Q.eval x) = (Q.map g).eval (g x) := fun Q x => by
    rw [Polynomial.eval_map, eval₂_at_apply]
  have hb0 : P.eval b0 ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]; intro hu
    have := hu.map g
    rw [e, hPmap] at this
    exact (mem_maximalIdeal _).mp h0 this
  have hb1 : IsUnit ((derivative P).eval b0) := by
    apply (isUnit_map_iff g _).mp
    rw [e, ← derivative_map, hPmap]; exact h1
  obtain ⟨b, hb, hbm⟩ := HenselianLocalRing.is_henselian P hPm b0 hb0 hb1
  refine ⟨g b, ?_, ?_⟩
  · change p.eval (g b) = 0
    rw [← hPmap, ← e, hb.eq_zero, map_zero]
  · rw [← map_sub, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
    exact (mem_maximalIdeal _).mp hbm

theorem sepQuot {A C : Type} [CommRing A] [IsLocalRing A] [CommRing C] [IsLocalRing C] (g : A →+* C)
    (hg : Function.Surjective g) [IsLocalHom g] [IsSepClosed (ResidueField A)] : IsSepClosed (ResidueField C) := by
  have hbij : Function.Bijective (ResidueField.map g) := by
    refine ⟨(ResidueField.map g).injective, ?_⟩
    intro y
    obtain ⟨c, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hg c
    exact ⟨residue A a, by simp⟩
  let e := RingEquiv.ofBijective _ hbij
  refine IsSepClosed.of_exists_root _ (fun p _ hirr hsep => ?_)
  obtain ⟨x, hx⟩ := IsSepClosed.exists_eval₂_eq_zero_of_injective (e.symm : ResidueField C →+* ResidueField A)
    e.symm.injective p (degree_pos_of_irreducible hirr).ne' hsep
  refine ⟨e x, ?_⟩
  have h2 := congrArg e hx
  rw [map_zero] at h2
  rw [show (e : ResidueField A → ResidueField C) = (e : ResidueField A →+* ResidueField C) from rfl,
    Polynomial.hom_eval₂, RingEquiv.comp_symm] at h2
  exact h2

theorem shQuot : LeafSHQuot := by
  intro A _ hA W' ι' _
  obtain ⟨hH, hS⟩ := hA
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ι'
  let g : CommRingCat.of A ⟶ Γ(W', ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ι'.appTop
  have hg : Function.Surjective g :=
    hsurj.comp (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective
  by_cases hC : Nontrivial Γ(W', ⊤)
  · right
    have hLC : IsLocalRing Γ(W', ⊤) := IsLocalRing.of_surjective' g.hom hg
    have hHC := hensQuot g.hom hg
    have : IsLocalHom g.hom := IsLocalHom.of_surjective g.hom hg
    exact ⟨hHC, sepQuot g.hom hg⟩
  · left
    rw [not_nontrivial_iff_subsingleton] at hC
    refine ⟨fun x => ?_⟩
    have h10 : (1 : Γ(W', ⊤)) = 0 := Subsingleton.elim _ _
    have := congrArg (W'.presheaf.germ ⊤ x trivial).hom h10
    rw [map_one, map_zero] at this
    exact one_ne_zero this

end LateralTheory.E.LeafClosedSH0PfQuot
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGlueDimPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 Order TopologicalSpace Topology

namespace LateralTheory.E.LeafGlueDimPf

theorem dim_le_of_cover {X U V : Type*} [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace V]
    (f : U → X) (g : V → X) (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (hc : Set.range f ∪ Set.range g = Set.univ) :
    topologicalKrullDim X ≤ max (topologicalKrullDim U) (topologicalKrullDim V) := by
  unfold topologicalKrullDim
  rw [krullDim_eq_iSup_coheight]
  refine iSup_le fun Z => ?_
  obtain ⟨z, hz⟩ := Z.2.nonempty
  have hzu : z ∈ Set.range f ∪ Set.range g := hc ▸ Set.mem_univ z
  rcases hzu with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · let T := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).symm ⟨Z, ⟨w, hz⟩⟩
    have hT : IrreducibleCloseds.map f hf.continuous T = Z := by
      have := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).apply_symm_apply ⟨Z, ⟨w, hz⟩⟩
      exact congrArg Subtype.val this
    rw [← hT, hf.coheight_map]
    exact le_trans (coheight_le_krullDim T) le_sup_left
  · let T := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding g hg).symm ⟨Z, ⟨w, hz⟩⟩
    have hT : IrreducibleCloseds.map g hg.continuous T = Z := by
      have := (IrreducibleCloseds.orderIsoOfIsOpenEmbedding g hg).apply_symm_apply ⟨Z, ⟨w, hz⟩⟩
      exact congrArg Subtype.val this
    rw [← hT, hg.coheight_map]
    exact le_trans (coheight_le_krullDim T) le_sup_right

theorem dim_eq_of_cover {X U V : Type*} [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace V]
    (f : U → X) (g : V → X) (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g)
    (hc : Set.range f ∪ Set.range g = Set.univ) :
    topologicalKrullDim X = max (topologicalKrullDim U) (topologicalKrullDim V) :=
  le_antisymm (dim_le_of_cover f g hf hg hc)
    (max_le hf.isInducing.topologicalKrullDim_le hg.isInducing.topologicalKrullDim_le)

theorem dim_Sp {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A : Subalgebra Ω L) :
    topologicalKrullDim (Sp A) = ringKrullDim A :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

theorem LeafGlueDim_of : LateralTheory.E.LeafGlueProperPf.LeafGlueDim := by
  intro Ω L _ _ _ A B u h G
  have hA : topologicalKrullDim (Sp A) = 1 := (dim_Sp A).trans h.2.2.2.2.2.2.2.1
  have hB : topologicalKrullDim (Sp B) = 1 := (dim_Sp B).trans h.2.2.2.2.2.2.2.2.1
  have := G.hiA; have := G.hiB
  rw [dim_eq_of_cover G.iA.base G.iB.base G.iA.isOpenEmbedding G.iB.isOpenEmbedding G.cover, hA, hB, max_self]

end LateralTheory.E.LeafGlueDimPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGlueGenericPf
section
noncomputable section
open AlgebraicGeometry.StructureSheaf CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.LeafGlueGenericPf

def eta (A : Type) [CommRing A] [IsDomain A] : Sp A := ⟨⊥, Ideal.isPrime_bot⟩

theorem eta_generic (A : Type) [CommRing A] [IsDomain A] : IsGenericPoint (eta A) (⊤ : Set (Sp A)) := by
  rw [isGenericPoint_iff_specializes]
  intro y
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
  exact (PrimeSpectrum.le_iff_specializes (eta A) y).1 bot_le

def etaT (A : Type) [CommRing A] [IsDomain A] : PrimeSpectrum.Top A := ⟨⊥, Ideal.isPrime_bot⟩

def psi0 {A L : Type} [CommRing A] [IsDomain A] [Field L] [Algebra A L] [IsFractionRing A L] :
    L →+* (structurePresheafInCommRingCat A).stalk (etaT A) := by
  have : (etaT A).asIdeal.IsPrime := Ideal.isPrime_bot
  exact IsLocalization.lift (M := nonZeroDivisors A) (S := L)
    (g := algebraMap A ((structurePresheafInCommRingCat A).stalk (etaT A))) (by
      intro y
      have hy : (y : A) ∈ (etaT A).asIdeal.primeCompl := by
        intro h0; exact nonZeroDivisors.ne_zero y.2 h0
      exact IsLocalization.map_units ((structurePresheafInCommRingCat A).stalk (etaT A))
        (⟨y, hy⟩ : (etaT A).asIdeal.primeCompl))

theorem fractionFieldToGenericStalk_algebraMap_eq {A L : Type} [CommRing A] [IsDomain A] [Field L] [Algebra A L] [IsFractionRing A L] (a : A) :
    psi0 (L := L) (algebraMap A L a) = StructureSheaf.toStalk A (etaT A) a := by
  unfold psi0; simp only [IsLocalization.lift_eq]; rfl

theorem glued_curve_generic_point_maps_to_function_field : LeafGlueGeneric := by
  intro Ω L _ _ _ A B u h G
  have := G.hiA
  have : IsFractionRing A L := h.2.2.2.2.2.2.2.2.2.1
  have : IsIntegral G.C0 := glued_affine_curve_is_integral_scheme Ω L A B u h G
  let s := G.iA.stalkMap (eta A)
  refine ⟨G.iA.base (eta A), Spec.map (inv s) ≫ Spec.map (CommRingCat.ofHom (psi0 (L := L))), ?_, ?_⟩
  · have hg := (eta_generic A).image G.iA.base.hom.continuous
    rw [Set.top_eq_univ, Set.image_univ,
      (G.iA.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)).closure_eq] at hg
    exact hg
  · have key := Scheme.SpecMap_stalkMap_fromSpecStalk G.iA (x := eta A)
    have hinv : G.C0.fromSpecStalk (G.iA.base (eta A)) =
        Spec.map (inv s) ≫ (Sp A).fromSpecStalk (eta A) ≫ G.iA := by
      rw [← key, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
    rw [Category.assoc, hinv, Category.assoc, Category.assoc, G.hcA]
    congr 1
    rw [Spec.fromSpecStalk_eq']
    erw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    have ha : algebraMap Ω L a = algebraMap A L (algebraMap Ω A a) := rfl
    change psi0 (L := L) (algebraMap Ω L a) = StructureSheaf.toStalk A (etaT A) (algebraMap Ω A a)
    rw [ha, fractionFieldToGenericStalk_algebraMap_eq]

end LateralTheory.E.LeafGlueGenericPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGlueIsProperPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.LeafGlueIsProperPf

variable {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {A B : Subalgebra Ω L} {u : L}

def cov {hAD hBD} (G : Glued Ω L A B (Dr Ω A u) hAD hBD) : G.C0.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Bool (fun b => cond b (Sp A) (Sp B))
    (fun | true => G.iA | false => G.iB)
    (by
      intro x
      have hx : x ∈ Set.range G.iA.base ∪ Set.range G.iB.base := G.cover ▸ Set.mem_univ x
      rcases hx with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · exact ⟨true, z, rfl⟩
      · exact ⟨false, z, rfl⟩)
    (by intro b; cases b <;> [exact G.hiB; exact G.hiA])

set_option backward.isDefEq.respectTransparency false in
theorem lft (h : GH Ω L A B u) {hAD hBD} (G : Glued Ω L A B (Dr Ω A u) hAD hBD) :
    LocallyOfFiniteType G.c0 := by
  refine IsZariskiLocalAtSource.of_openCover (P := @AlgebraicGeometry.LocallyOfFiniteType) (cov G) ?_
  intro b
  cases b
  · show LocallyOfFiniteType (G.iB ≫ G.c0)
    rw [G.hcB, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr h.2.2.2.2.1
  · show LocallyOfFiniteType (G.iA ≫ G.c0)
    rw [G.hcA, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr h.2.2.2.1

set_option backward.isDefEq.respectTransparency false in
theorem qc {hAD hBD} (G : Glued Ω L A B (Dr Ω A u) hAD hBD) : QuasiCompact G.c0 := by
  rw [HasAffineProperty.iff_of_isAffine (P := @AlgebraicGeometry.QuasiCompact)]
  refine ⟨?_⟩
  rw [← G.cover]
  exact (isCompact_range G.iA.base.hom.continuous).union (isCompact_range G.iB.base.hom.continuous)

def LeafGlueSep : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsSeparated G.c0

def LeafGlueExistence : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  ValuativeCriterion.Existence G.c0

theorem LeafGlueIsProper_of (hS : LeafGlueSep) (hE : LeafGlueExistence) : LeafGlueIsProper := by
  intro Ω L _ _ _ A B u h G
  have := hS Ω L A B u h G
  have := qc G
  have := lft h G
  have : UniversallyClosed G.c0 := UniversallyClosed.of_valuativeCriterion _ (hE Ω L A B u h G)
  exact {}

end LateralTheory.E.LeafGlueIsProperPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPairFPPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.LeafPairFPPf

theorem toR_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R') :
    toR R' ≫ incl h = toR R := by
  simp only [toR, incl, ← Spec.map_comp]
  congr 1

theorem fp_snd {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (hf : FP f) : FP (pullback.snd f g) := by
  obtain ⟨h1, h2, h3⟩ := hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem raise {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R')
    {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D) (hq : FP q)
    (hs : IsPullback v c q (toR R)) :
    ∃ (E : Scheme.{0}) (q' : E ⟶ Sp R') (w : C ⟶ E), FP q' ∧ IsPullback w c q' (toR R') := by
  refine ⟨pullback q (incl h), pullback.snd _ _, pullback.lift v (c ≫ toR R') ?_, fp_snd _ _ hq, ?_⟩
  · rw [Category.assoc, toR_incl, hs.w]
  · refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (h₂₂ := incl h) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_fst, toR_incl]
    exact hs

def LeafMapFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) {D0 D1 : Scheme.{0}} (q : D0 ⟶ Sp R) (q1 : D1 ⟶ Sp R)
    (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1), FP q → FP q1 → IsPullback v0 c0 q (toR R) →
    IsPullback v1 (γ1 ≫ c0) q1 (toR R) →
    ∃ (R' : Subalgebra k Ω), R'.FG ∧ ∃ (E0 E1 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (w0 : C0 ⟶ E0)
      (w1 : C1 ⟶ E1), FP q' ∧ FP (e1 ≫ q') ∧ IsPullback w0 c0 q' (toR R') ∧
      IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1

theorem pairDescent_of_objects_morphisms (hO : LeafObjFP) (hM : LeafMapFP) : LeafPairFP := by
  intro k _ Ω _ _ R hR C0 C1 c0 γ1 h1 D0 q v0 hq hsq
  obtain ⟨R1, hR1, D1, q1, v1, hq1, hs1⟩ := hO k Ω (γ1 ≫ c0) h1
  obtain ⟨E0, q0', w0, hq0', hs0'⟩ := raise (le_sup_left : R ≤ R ⊔ R1) c0 q v0 hq hsq
  obtain ⟨E1, q1', w1, hq1', hs1'⟩ := raise (le_sup_right : R1 ≤ R ⊔ R1) (γ1 ≫ c0) q1 v1 hq1 hs1
  exact hM k Ω (R ⊔ R1) (hR.sup hR1) c0 γ1 q0' q1' w0 w1 hq0' hq1' hs0' hs1'

end LateralTheory.E.LeafPairFPPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPreTensLocInjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.E.LeafPreTensLocInjPf
open LateralTheory.E.LeafTensMonoPf LateralTheory.E.LeafTwPairExistsPf LateralTheory.E.LeafPairExtPf2

section
variable {R : Type} [CommRing R]

theorem sec_sgl_zero (F : Shv R) {s : ℤ} (hs : s ≠ 0) {U : Scheme.{0}} (a : Sec ((sgl F).X s) U) : a = 0 := by
  have hZ : IsZero ((sgl F).X s) := HomologicalComplex.isZero_single_obj_X _ _ _ _ hs
  have h1 : (𝟙 ((sgl F).X s)) = 0 := hZ.eq_of_src _ _
  have h2 : Sec.map (𝟙 ((sgl F).X s)) a = a := rfl
  rw [← h2, h1]
  rfl

theorem tens_zero_left (F : Shv R) {J : Cx R} {s t : ℤ} (hs : s ≠ 0) {U : Scheme.{0}}
    (z : Sec ((sgl F).X s) U ⊗[ULift.{1} R] Sec (J.X t) U) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul a b => rw [sec_sgl_zero F hs a, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

abbrev p0 (w : ℤ) : {p : ℤ × ℤ // p.1 + p.2 = w} := ⟨(0, w), by simp⟩

theorem tens_single (F : Shv R) {J : Cx R} {U : Scheme.{0}} {w : ℤ} (x : Tens (sgl F) J U w) :
    x = DirectSum.of _ (p0 w) (x (p0 w)) := by
  classical
  ext p
  by_cases hp : p = p0 w
  · subst hp; simp
  · rw [DirectSum.of_eq_of_ne _ _ _ hp]
    have : p.1.1 ≠ 0 := by
      intro h; apply hp; apply Subtype.ext; ext
      · exact h
      · simp; have := p.2; omega
    exact tens_zero_left F this _

theorem tens_res_of {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (t : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.of _ p t) =
      DirectSum.of _ p (TensorProduct.map ((I.X p.1.1).obj.map g.op).hom ((J.X p.1.2).obj.map g.op).hom t) := by
  classical
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  unfold Tens.res
  rw [DirectSum.lmap_lof]
  rfl

theorem lift_of {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (t : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    μ.lift U w (DirectSum.of _ p t) = TensorProduct.lift (μ.mul U p.1.1 p.1.2 w p.2) t := by
  classical
  unfold Pair.lift
  exact DirectSum.toModule_lof (ULift.{1} R)
    (M := fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p t

end

section
variable {R : Type} [CommRing R]
theorem tens_res_comp {I J : Cx R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (w : ℤ) (z : Tens I J U w) :
    Tens.res (k ≫ g) w z = Tens.res k w (Tens.res g w z) := by
  classical
  have : (Tens.res (I := I) (J := J) (k ≫ g) w) = (Tens.res k w).comp (Tens.res g w) := by
    apply DirectSum.linearMap_ext; intro p
    apply TensorProduct.ext'; intro a b
    simp [Tens.res]
  exact LinearMap.congr_fun this z
end

theorem LeafPreTensLocInj_of (hS : LeafTw0LocSplit) : LeafPreTensLocInj := by
  intro q _ i T τ hτ U w x hx
  classical
  obtain ⟨S, hS0⟩ := TensorProduct.exists_finset (x (p0 w))
  set a : Fin S.card → Sec ((sgl (tw q 0)).X 0) U := fun k => (S.equivFin.symm k).1.1 with ha
  set b : Fin S.card → Sec ((res _ (tw q i)).X w) U := fun k => (S.equivFin.symm k).1.2 with hb
  have hxp : x (p0 w) = ∑ k, a k ⊗ₜ[ULift.{1} (ZMod q)] b k := by
    rw [hS0, ← Finset.sum_coe_sort S]
    exact (Equiv.sum_comp S.equivFin.symm (fun i : S => i.1.1 ⊗ₜ[ULift.{1} (ZMod q)] i.1.2)).symm
  have hx' : x = DirectSum.of _ (p0 w) (∑ k, a k ⊗ₜ[ULift.{1} (ZMod q)] b k) := by
    rw [← hxp]; exact tens_single _ x
  set y : Tens (res _ (tw q 0)) (res _ (tw q i)) U w :=
    DirectSum.of _ (p0 w) (∑ k, Sec.map ((resAug (tw q 0)).f 0) (a k) ⊗ₜ[ULift.{1} (ZMod q)] b k) with hydef
  have hy : τ.lift U w y = 0 := by
    rw [← hx, hx', hydef, lift_of, lift_of]
    simp [pre]
  refine loc_trans (hτ.2 U w y hy) ?_
  intro V g hg
  refine loc_trans (hS q V S.card (fun k => Sec.res g (a k))) ?_
  rintro W k ⟨e, c, hac, he⟩
  suffices h : Tens.res (k ≫ g) w x = 0 from
    ⟨⊤, GrothendieckTopology.top_mem _ W, fun W' k' _ => by dsimp only; rw [Category.assoc, tens_res_comp, h, map_zero]⟩
  set bb : Sec ((res _ (tw q i)).X w) W := ∑ j, c j • Sec.res (k ≫ g) (b j) with hbb
  have hres : Tens.res (k ≫ g) w x = DirectSum.of _ (p0 w) (e ⊗ₜ[ULift.{1} (ZMod q)] bb) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx', tens_res_of, map_sum]
    congr 1
    rw [hbb, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.map_tmul, ← TensorProduct.smul_tmul]
    congr 1
    show Sec.res (k ≫ g) (a j) = c j • e
    rw [res_comp]; exact hac j
  have hy0 : Tens.res (k ≫ g) w y =
      DirectSum.of _ (p0 w) (Sec.map ((resAug (tw q 0)).f 0) e ⊗ₜ[ULift.{1} (ZMod q)] bb) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hydef, tens_res_of, map_sum]
    congr 1
    rw [hbb, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.map_tmul, ← TensorProduct.smul_tmul]
    congr 1
    show Sec.res (k ≫ g) (Sec.map ((resAug (tw q 0)).f 0) (a j)) = c j • Sec.map ((resAug (tw q 0)).f 0) e
    rw [res_map, res_comp, hac j]
    exact map_smul (((resAug (tw q 0)).f 0).hom.app (op W)).hom (c j) e
  have hg0 : Tens.res (k ≫ g) w y = 0 := by rw [tens_res_comp, hg, map_zero]
  have ht : Sec.map ((resAug (tw q 0)).f 0) e ⊗ₜ[ULift.{1} (ZMod q)] bb = 0 :=
    DirectSum.of_injective (p0 w) (hy0.symm.trans (hg0.trans (map_zero _).symm))
  rw [hres]
  rcases he with he | ⟨r, hr⟩
  · rw [he, TensorProduct.zero_tmul, map_zero]
  · have hbb0 : bb = 0 := by
      have := congrArg (fun z => TensorProduct.lid (ULift.{1} (ZMod q)) _ (TensorProduct.map r LinearMap.id z)) ht
      simpa [hr] using this
    rw [hbb0, TensorProduct.tmul_zero, map_zero]

end LateralTheory.E.LeafPreTensLocInjPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoGenPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensQIsoGenPf

theorem loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology.{0}).top_mem U, fun V g _ => h V g⟩

theorem flatS_of_sec {R : Type} [CommRing R] (M : Shv R)
    (h : ∀ U : Scheme.{0}, Module.Flat (ULift.{1} R) (Sec M U)) : FlatS M := by
  refine ⟨M.obj, 𝟙 _, ?_, ?_, ?_⟩
  · intro U y
    exact loc_top U _ (fun V g => ⟨Sec.res g y, rfl⟩)
  · intro U x hx
    have hx0 : x = 0 := hx
    subst hx0
    exact loc_top U _ (fun V g => map_zero _)
  · intro U _
    exact h U

theorem LeafTensQIsoGen_of : LateralTheory.E.LeafTensQIsoPf.LeafTensQIsoGen := by
  intro R _ I I' J S T f hf hI hI' hJ hflat σ τ hσ hτ ι hι
  exact LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso.intersectionNumber_baseChange R σ τ hσ hτ (fun t => flatS_of_sec _ (hflat t)) f ι
    (fun U s t w h a b => by rw [hι U s t w h a b]; rfl)

end LateralTheory.E.LeafTensQIsoGenPf
end
end

