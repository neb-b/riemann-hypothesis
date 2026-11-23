module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0076
public import Development.EtaleCohomology.EtaleSheaves.Bundle0078
public import Development.EtaleCohomology.EtaleSheaves.Bundle0077
public import Mathlib

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.FMrangePfQc
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut LateralTheory.E.SysFMPf LateralTheory.E.FMrangePf

namespace LateralTheory.E.FMrangePfQc

theorem finset_idem {W : Type} [CommRing W] (hW : ProdACF W) (t : Finset W) :
    ∃ e : W, IsIdempotentElem e ∧ ∀ p : PrimeSpectrum W, p ∈ (PrimeSpectrum.zeroLocus (t : Set W))ᶜ ↔ e ∉ p.asIdeal := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, IsIdempotentElem.zero, fun p => by simp⟩
  | insert a t _ ih =>
    obtain ⟨e, he, hpe⟩ := ih
    obtain ⟨f, u, hf, hu, rfl⟩ := hW.2 a
    refine ⟨f + e - f * e, ?_, fun p => ?_⟩
    · unfold IsIdempotentElem at *
      linear_combination (1 - e + (e * e - e)) * hf + (1 - f) * he
    · have hfe : f * (f + e - f * e) = f := by
        have := hf.eq; linear_combination (1 - e) * this
      have hef : e * (f + e - f * e) = e := by
        have := he.eq; linear_combination (1 - f) * this
      have key : f + e - f * e ∈ p.asIdeal ↔ f ∈ p.asIdeal ∧ e ∈ p.asIdeal := by
        constructor
        · intro h
          exact ⟨hfe ▸ p.asIdeal.mul_mem_left f h, hef ▸ p.asIdeal.mul_mem_left e h⟩
        · rintro ⟨h1, h2⟩
          exact p.asIdeal.sub_mem (p.asIdeal.add_mem h1 h2) (p.asIdeal.mul_mem_right e h1)
      have hfu : f * u ∈ p.asIdeal ↔ f ∈ p.asIdeal := by
        constructor
        · intro h
          obtain ⟨v, hv⟩ := hu.exists_right_inv
          have := p.asIdeal.mul_mem_right v h
          rwa [mul_assoc, hv, mul_one] at this
        · exact fun h => p.asIdeal.mul_mem_right u h
      have h1 := hpe p
      simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Finset.coe_insert, Set.insert_subset_iff] at h1 ⊢
      rw [key]
      simp only [SetLike.mem_coe, hfu, not_iff_not.mp h1]

theorem QcIdem_pf : QcIdem := by
  intro W _ hW U hU
  obtain ⟨t, ht⟩ := (@PrimeSpectrum.isCompact_isOpen_iff W _ (U : Set (Spec (CommRingCat.of W)))).1 ⟨hU, U.isOpen⟩
  obtain ⟨e, he, hpe⟩ := finset_idem hW t
  refine ⟨e, he, fun p => ?_⟩
  rw [← hpe p, ht]
  rfl

theorem FMrange_of (hI : IdemLift) : FMrange :=
  FMrange_of_leaves hI QcIdem_pf

end LateralTheory.E.FMrangePfQc
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GluedCurveChartOverlapIsPullback
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

theorem mem_adj {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (B : Subalgebra Ω L) (u : L) (hu : u ≠ 0)
    (huB : u⁻¹ ∈ B) (d : L) (hd : d ∈ Algebra.adjoin Ω ((B : Set L) ∪ {u})) : ∃ n : ℕ, d * u⁻¹ ^ n ∈ B := by
  induction hd using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff.mp hx]; exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hu]; exact B.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using B.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * u⁻¹ ^ (n + m) = (x * u⁻¹ ^ n) * u⁻¹ ^ m + (y * u⁻¹ ^ m) * u⁻¹ ^ n := by ring
    rw [this]
    exact B.add_mem (B.mul_mem hn (B.pow_mem huB _)) (B.mul_mem hm (B.pow_mem huB _))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x * y) * u⁻¹ ^ (n + m) = (x * u⁻¹ ^ n) * (y * u⁻¹ ^ m) := by ring
    rw [this]; exact B.mul_mem hn hm

theorem away {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (B D : Subalgebra Ω L) (hB : B ≤ D) (u : L)
    (hu : u ≠ 0) (huB : u⁻¹ ∈ B) (huD : u ∈ D) (hD : D ≤ Algebra.adjoin Ω ((B : Set L) ∪ {u})) :
    letI : Algebra B D := (Subalgebra.inclusion hB).toRingHom.toAlgebra
    IsLocalization.Away (⟨u⁻¹, huB⟩ : B) D := by
  letI : Algebra B D := (Subalgebra.inclusion hB).toRingHom.toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    show IsUnit (algebraMap B D ((⟨u⁻¹, huB⟩ : B) ^ n))
    rw [map_pow]
    refine IsUnit.pow n ?_
    exact ⟨⟨algebraMap B D ⟨u⁻¹, huB⟩, ⟨u, huD⟩, Subtype.ext (inv_mul_cancel₀ hu),
      Subtype.ext (mul_inv_cancel₀ hu)⟩, rfl⟩
  · intro d
    obtain ⟨n, hn⟩ := mem_adj B u hu huB d (hD d.2)
    refine ⟨(⟨d * u⁻¹ ^ n, hn⟩, ⟨_, n, rfl⟩), Subtype.ext ?_⟩
    show d * u⁻¹ ^ n = (d : L) * (u⁻¹ ^ n)
    rfl
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (x : L) = (y : L) := by
      have h2 := congrArg (fun z : D => (z : L)) hxy
      exact h2
    simp [Subtype.ext this]

set_option backward.isDefEq.respectTransparency false in
theorem glued_curve_chart_overlap_is_pullback : LeafGluePullback := by
  intro Ω L _ _ _ A B u h G
  haveI := G.hiA; haveI := G.hiB
  have hadj := h.2.2.2.2.2.2.2.2.2.2.2.1
  have huD : u ∈ Dr Ω A u := Algebra.subset_adjoin (Or.inl h.2.1)
  have hD : Dr Ω A u ≤ Algebra.adjoin Ω ((B : Set L) ∪ {u}) := hadj.le
  haveI hjB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom)) := by
    letI : Algebra B (Dr Ω A u) := (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom.toAlgebra
    haveI := away B (Dr Ω A u) (le_Dr_B A B u hadj) u h.1 h.2.2.1 huD hD
    exact IsOpenImmersion.of_isLocalization (S := Dr Ω A u) (⟨u⁻¹, h.2.2.1⟩ : B)
  refine IsOpenImmersion.isPullback _ _ _ _ G.agree.symm ?_
  ext x
  show G.iB.base x ∈ Set.range G.iA.base ↔ x ∈ Set.range _
  constructor
  · intro hx
    have hx' : G.iB.base x ∈ Set.range G.iA.base ∩ Set.range G.iB.base := ⟨hx, x, rfl⟩
    rw [G.inter, G.agree] at hx'
    obtain ⟨y, hy⟩ := hx'
    refine ⟨y, G.iB.isOpenEmbedding.injective ?_⟩
    rw [← hy]; rfl
  · rintro ⟨y, rfl⟩
    refine ⟨(Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_A A u)).toRingHom)).base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, G.agree]; rfl

end LateralTheory.E.GluedCurveChartOverlaps

namespace LateralTheory.E.GluedCurveSeparated

theorem LeafGlueSep_of : LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep :=
  LateralTheory.E.GluedCurveChartOverlaps.LeafGlueSep_of LateralTheory.E.GluedCurveChartOverlaps.glued_curve_chart_overlap_is_pullback
    LateralTheory.E.GluedCurveChartOverlaps.spec_subalgebra_pullback_lift_is_closed_immersion

end LateralTheory.E.GluedCurveSeparated
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IdemLiftOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial LateralTheory.E.BuildCut LateralTheory.E.SysFMPf LateralTheory.E.FMrangePf

namespace LateralTheory.E.IdempotentLifting

abbrev Aq : Type := AdjoinRoot (X ^ 2 - X : ℤ[X])

lemma monic_q : (X ^ 2 - X : ℤ[X]).Monic := by
  apply Polynomial.monic_X_pow_sub
  rw [degree_X]; decide

lemma integral_q : (algebraMap ℤ Aq).IsIntegral := by
  have := monic_q.finite_adjoinRoot
  exact fun x => Algebra.IsIntegral.isIntegral x

def toW {W : Type} [CommRing W] (e : W) (he : IsIdempotentElem e) : Aq →+* W :=
  AdjoinRoot.lift (Int.castRingHom W) e (by simp [sq, he.eq])

theorem IdemLift_of : IdemLift := by
  intro P _ _ W _ w _ e he
  let Z : Scheme.{0} := Spec (CommRingCat.of Aq)
  let t : Z ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ Aq))
  have : IsIntegralHom t := IsIntegralHom.SpecMap_iff.2 integral_q
  let g : Spec (CommRingCat.of W) ⟶ Z := Spec.map (CommRingCat.ofHom (toW e he))
  let f₁ : Spec (CommRingCat.of W) ⟶ pullback (specZIsTerminal.from P) t :=
    pullback.lift w g (specZIsTerminal.hom_ext _ _)
  have H : w = f₁ ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
  let d := w.normalizationDesc f₁ (pullback.fst _ _) H
  let r : Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Aq)).inv (AdjoinRoot.root _)
  refine ⟨d.appTop ((pullback.snd (specZIsTerminal.from P) t).appTop r), ?_⟩
  have key : w.toNormalization ≫ d ≫ pullback.snd (specZIsTerminal.from P) t = g := by
    rw [← Category.assoc, w.toNormalization_normalizationDesc, pullback.lift_snd]
  have h1 : w.toNormalization.appTop (d.appTop ((pullback.snd (specZIsTerminal.from P) t).appTop r)) =
      g.appTop r := by
    rw [← key]; simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of W)).hom (g.appTop r) = e := by
    rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
    simp [r, toW, AdjoinRoot.lift_root]
  unfold phi
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  exact (congrArg _ h1).trans h2

end LateralTheory.E.IdempotentLifting
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGlueTwoPfFP
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafGlueTwoPf GlobalTheory.GlueModels

namespace LateralTheory.E.LeafGlueTwoPfFP

def LeafPushoutQS : Prop := ∀ {DW DU DV : Scheme.{0}} (φU : DW ⟶ DU) (φV : DW ⟶ DV) [IsOpenImmersion φU]
    [IsOpenImmersion φV], CompactSpace DW → QuasiSeparatedSpace DW → QuasiSeparatedSpace DU →
    QuasiSeparatedSpace DV → QuasiSeparatedSpace (pushout φU φV : Scheme.{0})

set_option backward.isDefEq.respectTransparency false in
theorem pushout_finitePresentation_of_quasiSeparated (hQ : LeafPushoutQS) : LeafPushoutFP := by
  intro DW DU DV S φU φV _ _ qU qV h hS ⟨l1, c1, s1⟩ ⟨l2, c2, s2⟩ ⟨l3, c3, s3⟩
  have : CompactSpace DU := QuasiCompact.compactSpace_of_compactSpace qU
  have : CompactSpace DV := QuasiCompact.compactSpace_of_compactSpace qV
  have : CompactSpace DW := QuasiCompact.compactSpace_of_compactSpace (φU ≫ qU)
  have : QuasiSeparatedSpace DU := quasiSeparatedSpace_of_quasiSeparated qU
  have : QuasiSeparatedSpace DV := quasiSeparatedSpace_of_quasiSeparated qV
  have : QuasiSeparatedSpace DW := quasiSeparatedSpace_of_quasiSeparated (φU ≫ qU)
  have := isOpenImmersion_inl φU φV
  have := isOpenImmersion_inr φU φV
  let T : Bool → Scheme.{0} := fun i => Bool.rec DU DV i
  let t : ∀ i, T i ⟶ pushout φU φV := fun i => Bool.rec (motive := fun i => T i ⟶ pushout φU φV)
    (pushout.inl φU φV) (pushout.inr φU φV) i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  let 𝒰 : (pushout φU φV).OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases pushout_cover φU φV x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  have hL : LocallyOfFinitePresentation (pushout.desc qU qV h) := by
    refine IsZariskiLocalAtSource.of_openCover 𝒰 ?_
    rintro (_ | _)
    · change LocallyOfFinitePresentation (pushout.inl φU φV ≫ pushout.desc qU qV h)
      rw [pushout.inl_desc]; exact l1
    · change LocallyOfFinitePresentation (pushout.inr φU φV ≫ pushout.desc qU qV h)
      rw [pushout.inr_desc]; exact l2
  have hC : CompactSpace (pushout φU φV : Scheme.{0}) := by
    refine ⟨?_⟩
    have hu : (Set.univ : Set (pushout φU φV : Scheme.{0})) =
        Set.range (pushout.inl φU φV) ∪ Set.range (pushout.inr φU φV) := by
      ext x; simpa using pushout_cover φU φV x
    rw [hu]
    exact (isCompact_range (pushout.inl φU φV).continuous).union (isCompact_range (pushout.inr φU φV).continuous)
  have hQS := hQ φU φV inferInstance inferInstance inferInstance inferInstance
  exact ⟨hL, inferInstance, inferInstance⟩

end LateralTheory.E.LeafGlueTwoPfFP

theorem LateralTheory.E.LeafGlueTwoPfFP.LeafGlueTwo_of' (hQ : LateralTheory.E.LeafGlueTwoPfFP.LeafPushoutQS) :
    LateralTheory.E.LeafObjGluePf.LeafGlueTwo :=
  LateralTheory.E.LeafGlueTwoPf.LeafGlueTwo_of (LateralTheory.E.LeafGlueTwoPfFP.pushout_finitePresentation_of_quasiSeparated hQ)

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafInclPiecePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf LateralTheory.E.LeafInclDescendPf

namespace LateralTheory.E.LeafInclPiecePf

theorem incl_comp {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1)
    (h : R ≤ R'') (h1' : R1 ≤ R'') : incl h1' ≫ incl h1 = incl h := by
  simp only [incl]
  rw [← Spec.map_comp]
  rfl

def lvl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R'')
    (h1' : R1 ≤ R'') {D : Scheme.{0}} (q : D ⟶ Sp R) : pullback q (incl h) ⟶ pullback q (incl h1) :=
  pullback.lift (pullback.fst q (incl h)) (pullback.snd q (incl h) ≫ incl h1') (by
    rw [pullback.condition, Category.assoc, incl_comp h1 h h1'])

def descMap {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1) (h : R ≤ R'')
    (h1' : R1 ≤ R'') {DU DW : Scheme.{0}} (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R)
    (ψ : pullback qW (incl h1) ⟶ pullback qU (incl h1)) (hψ : ψ ≫ pullback.snd qU (incl h1) = pullback.snd qW (incl h1)) :
    pullback qW (incl h) ⟶ pullback qU (incl h) :=
  pullback.lift (lvl h1 h h1' qW ≫ ψ ≫ pullback.fst qU (incl h1)) (pullback.snd qW (incl h)) (by
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hψ, lvl, pullback.lift_snd_assoc, Category.assoc, incl_comp h1 h h1'])

theorem bcLift_lvl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R1 R'' : Subalgebra k Ω} (h1 : R ≤ R1)
    (h : R ≤ R'') (h1' : R1 ≤ R'') {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω} {q : D ⟶ Sp R} {v : Y ⟶ D}
    (w : v ≫ q = g ≫ toR R) : bcLift h w ≫ lvl h1 h h1' q = bcLift h1 w := by
  apply pullback.hom_ext
  · unfold lvl bcLift
    rw [Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
  · unfold lvl bcLift
    rw [Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd, Category.assoc, toR_eq]

def LeafInclMap : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U W : X.Opens) (hWU : W ≤ U) (R : Subalgebra k Ω), R.FG →
    ∀ (DU DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R) (vU : U.toScheme ⟶ DU) (vW : W.toScheme ⟶ DW),
    FP qU → FP qW → ∀ (hU : IsPullback vU (U.ι ≫ f) qU (toR R)) (hW : IsPullback vW (W.ι ≫ f) qW (toR R)),
    ∃ (R1 : Subalgebra k Ω) (h1 : R ≤ R1), R1.FG ∧
      ∃ ψ : pullback qW (incl h1) ⟶ pullback qU (incl h1),
        ψ ≫ pullback.snd qU (incl h1) = pullback.snd qW (incl h1) ∧
        bcLift h1 hW.w ≫ ψ = X.homOfLE hWU ≫ bcLift h1 hU.w

def LeafInclOpen : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U W : X.Opens) (hWU : W ≤ U) (R : Subalgebra k Ω), R.FG →
    ∀ (DU DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R) (vU : U.toScheme ⟶ DU) (vW : W.toScheme ⟶ DW),
    FP qU → FP qW → ∀ (hU : IsPullback vU (U.ι ≫ f) qU (toR R)) (hW : IsPullback vW (W.ι ≫ f) qW (toR R))
    (R1 : Subalgebra k Ω) (h1 : R ≤ R1), R1.FG →
    ∀ (ψ : pullback qW (incl h1) ⟶ pullback qU (incl h1))
      (hψ : ψ ≫ pullback.snd qU (incl h1) = pullback.snd qW (incl h1)),
      bcLift h1 hW.w ≫ ψ = X.homOfLE hWU ≫ bcLift h1 hU.w →
    ∃ R' : Subalgebra k Ω, R1 ≤ R' ∧ R'.FG ∧ ∀ (R'' : Subalgebra k Ω) (h : R ≤ R'') (h1' : R1 ≤ R''), R' ≤ R'' →
      IsOpenImmersion (descMap h1 h h1' qU qW ψ hψ)

theorem LeafInclPiece_of (hA : LeafInclMap) (hB : LeafInclOpen) : LeafInclPiece := by
  intro k _ Ω _ _ X f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW
  obtain ⟨R1, h1, hR1, ψ, hψ, hc⟩ := hA k Ω f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW
  obtain ⟨R', h1R', hR', H⟩ := hB k Ω f hf U W hWU R hR DU DW qU qW vU vW hqU hqW hU hW R1 h1 hR1 ψ hψ hc
  refine ⟨R', h1.trans h1R', hR', fun R'' h hR'' => ?_⟩
  have h1' : R1 ≤ R'' := h1R'.trans hR''
  refine ⟨descMap h1 h h1' qU qW ψ hψ, H R'' h h1' hR'', pullback.lift_snd _ _ _, ?_⟩
  apply pullback.hom_ext
  · simp only [descMap, Category.assoc, pullback.lift_fst]
    rw [reassoc_of% (bcLift_lvl h1 h h1' hW.w), reassoc_of% hc]
    unfold bcLift
    erw [pullback.lift_fst, pullback.lift_fst]
  · simp only [descMap, Category.assoc, pullback.lift_snd]
    unfold bcLift
    erw [pullback.lift_snd, pullback.lift_snd]
    simp only [Category.assoc, Scheme.homOfLE_ι_assoc]

end LateralTheory.E.LeafInclPiecePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSpreadLQFGraphOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LocallyQuasiFiniteGraphSpreadingOut

theorem toR_sk {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) :
    toR R ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  rw [← Spec.map_comp]; rfl

theorem incl_sk {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R') :
    incl hR ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k R')) := by
  rw [← Spec.map_comp]; rfl

abbrev cmp {A B K X : Scheme.{0}} (p : X ⟶ K) (a : A ⟶ B) (b : B ⟶ K) (c : A ⟶ K) (h : a ≫ b = c) :
    pullback c p ⟶ pullback b p :=
  pullback.lift (pullback.fst c p ≫ a) (pullback.snd _ _)
    (by rw [Category.assoc, h]; exact pullback.condition)

theorem paste {A B K X : Scheme.{0}} (p : X ⟶ K) (a : A ⟶ B) (b : B ⟶ K) (c : A ⟶ K) (h : a ≫ b = c) :
    IsPullback (cmp p a b c h) (pullback.fst c p) (pullback.fst b p) a := by
  subst h
  refine IsPullback.of_right (h₁₂ := pullback.snd b p) (v₁₃ := p) (h₂₂ := b) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback b p).flip
  rw [pullback.lift_snd]; exact (IsPullback.of_hasPullback (a ≫ b) p).flip

theorem LeafSpreadLQFGraph_of (hM : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFGraph := by
  intro k _ X p _ Ω _ _ R hRfg C0 D0 c0 q v0 f e he hf hq hpb hve hlqf
  have hLFT : LocallyOfFinitePresentation (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) p) := by
    infer_instance
  obtain ⟨S, hRS, hSfg, hS⟩ := hM k Ω R hRfg
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p) (pullback.lift c0 e he.symm)
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R))) p) (pullback.lift q f hf.symm) v0
    (cmp p (toR R) _ _ (toR_sk R))
    ⟨hLFT, inferInstance, inferInstance⟩ (by rw [pullback.lift_fst]; exact hq) (paste p _ _ _ (toR_sk R))
    (by rw [pullback.lift_fst, pullback.lift_fst]; exact hpb) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact hpb.w.symm
      · simp only [Category.assoc, pullback.lift_snd]; exact hve.symm) hlqf
  refine ⟨S, hRS, hSfg, fun R' hSR' hR E0 q' r hr hf' => ?_⟩
  refine hS R' hSR' hR E0 _ (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k R'))) p)
    (pullback.lift q' (r ≫ f) hf'.symm) r (cmp p (incl hR) _ _ (incl_sk hR)) (paste p _ _ _ (incl_sk hR))
    (by rw [pullback.lift_fst, pullback.lift_fst]; exact hr) ?_
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact hr.w.symm
  · simp only [Category.assoc, pullback.lift_snd]

end LateralTheory.E.LocallyQuasiFiniteGraphSpreadingOut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSpreadSmooth1Of
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut TensorProduct

namespace LateralTheory.E.SpreadingOutSmoothness

theorem stepB {R K B A : Type} [CommRing R] [CommRing K] [CommRing B] [CommRing A] [Algebra R K] [Algebra R A]
    [Algebra R B] [Algebra K B] [IsScalarTower R K B] [Algebra A B] [IsScalarTower R A B] (M : Submonoid R)
    [IsLocalization M K] [IsLocalization (Algebra.algebraMapSubmonoid A M) B] [Algebra.Smooth K B]
    (Q : Ideal B) [Q.IsPrime] : Algebra.IsSmoothAt R (Q.comap (algebraMap A B)) := by
  haveI : Algebra.FormallySmooth R K := Algebra.FormallySmooth.of_isLocalization M
  haveI : Algebra.FormallySmooth K (Localization.AtPrime Q) := inferInstance
  haveI : Algebra.FormallySmooth R (Localization.AtPrime Q) := Algebra.FormallySmooth.comp R K _
  haveI := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid A M) (Localization.AtPrime Q) Q
  exact Algebra.FormallySmooth.of_equiv ((IsLocalization.algEquiv (Q.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime Q) _).restrictScalars R)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem algDescend (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
    (A : Type) [CommRing A] [Algebra R A] (hfp : Algebra.FinitePresentation R A) (hs : Algebra.Smooth Ω (Ω ⊗[R] A))
    (P : PrimeSpectrum (Ω ⊗[R] A)) :
    PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom P ∈ Algebra.smoothLocus R A := by
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : IsScalarTower R (FractionRing R) Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  let e := Algebra.TensorProduct.cancelBaseChange R (FractionRing R) Ω Ω A
  haveI : Algebra.Smooth Ω (Ω ⊗[FractionRing R] (FractionRing R ⊗[R] A)) := Algebra.Smooth.of_equiv e.symm
  haveI : Module.Free (FractionRing R) Ω := Module.Free.of_divisionRing _ Ω
  haveI : Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] A) :=
    Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat Ω
  letI : Algebra A (FractionRing R ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) (FractionRing R ⊗[R] A) :=
    IsLocalization.tensorRight _ _
  let φ : FractionRing R ⊗[R] A →+* Ω ⊗[R] A := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : FractionRing R ⊗[R] A →ₐ[FractionRing R] Ω ⊗[FractionRing R] _).toRingHom
  haveI : (P.asIdeal.comap φ).IsPrime := Ideal.comap_isPrime _ _
  have hφ : φ.comp (algebraMap A (FractionRing R ⊗[R] A)) =
      (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom := by
    ext a
    show e (1 ⊗ₜ (1 ⊗ₜ a)) = 1 ⊗ₜ a
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  have hc : PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom P =
      ⟨(P.asIdeal.comap φ).comap (algebraMap A (FractionRing R ⊗[R] A)), inferInstance⟩ := by
    ext1; simp only [PrimeSpectrum.comap_asIdeal, Ideal.comap_comap, hφ]
  rw [hc]
  exact stepB (K := FractionRing R) (nonZeroDivisors R) (P.asIdeal.comap φ)

def LeafAlgDescend : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
    (A : Type) [CommRing A] [Algebra R A], Algebra.FinitePresentation R A → Algebra.Smooth Ω (Ω ⊗[R] A) →
    ∀ P : PrimeSpectrum (Ω ⊗[R] A),
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] Ω ⊗[R] A).toRingHom P ∈ Algebra.smoothLocus R A

def LeafStalkOfAlg : Prop := LeafAlgDescend → LateralTheory.E.LeafSpreadSmoothAffSmPf.LeafStalkDescend

theorem leafAlgDescend : LeafAlgDescend := fun k _ Ω _ _ R A _ _ hfp hs P => algDescend k Ω R A hfp hs P

theorem LeafSpreadSmooth1_of (hB : LateralTheory.E.LeafSpreadSmoothPf.LeafSpreadRelDim) (hT : LeafStalkOfAlg) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadSmooth1 :=
  LateralTheory.E.LeafSpreadSmoothPf.LeafSpreadSmooth_of
    (LateralTheory.E.LeafSpreadSmoothAffSmPf.LeafSpreadSmoothAffSm_of (hT leafAlgDescend)) hB

end LateralTheory.E.SpreadingOutSmoothness

end
end

