module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.DChartEx
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0005
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0004
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ExChart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpSmooth
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem stdC (A : Type) [CommRing A] (D : ℕ) :
    (MvPolynomial.C : A →+* MvPolynomial (Fin D) A).IsStandardSmoothOfRelativeDimension D := by
  rw [← MvPolynomial.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  let v : PEmpty.{1} → MvPolynomial (Fin D) A := PEmpty.elim
  let P0 := Algebra.PreSubmersivePresentation.naive (R := A) (v := v) (σ := Fin D)
    (ι := PEmpty.{1}) PEmpty.elim (fun a => a.elim)
  let P1 : Algebra.SubmersivePresentation A _ (Fin D) PEmpty.{1} :=
    { toPreSubmersivePresentation := P0
      jacobian_isUnit := by
        classical
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  have hv : Ideal.span (Set.range v) = ⊥ := by simp [v]
  let e : (MvPolynomial (Fin D) A ⧸ Ideal.span (Set.range v)) ≃ₐ[A] MvPolynomial (Fin D) A :=
    (Ideal.quotientEquivAlgOfEq A hv).trans (AlgEquiv.quotientBot A _)
  exact ⟨⟨Fin D, PEmpty.{1}, inferInstance, inferInstance, P1.ofAlgEquiv e,
    by simp [Algebra.Presentation.dimension]⟩⟩

private theorem chart {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ) {U : Y.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (h : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom) :
    SmoothOfRelativeDimension n (V.ι ≫ f) := by
  haveI : IsAffine U := hU
  haveI : IsAffine V := hV
  have H := (HasRingHomProperty.isLocal_ringHomProperty
    (@SmoothOfRelativeDimension n)).respectsIso
  have hr : SmoothOfRelativeDimension n (f.resLE U V e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.hom_comp, H.cancel_left_isIso,
      CommRingCat.hom_comp, H.cancel_right_isIso]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ h
  haveI : SmoothOfRelativeDimension 0 U.ι := by
    rw [← Etale.iff_smoothOfRelativeDimension_zero]
    infer_instance
  rw [← Scheme.Hom.resLE_comp_ι f e]
  simpa using smoothOfRelativeDimension_comp n 0 (f.resLE U V e) U.ι

private theorem ofPts {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ)
    (H : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ SmoothOfRelativeDimension n (O.ι ≫ f)) :
    SmoothOfRelativeDimension n f := by
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  choose O hxO hO using H
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) O
    (top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxO x⟩) hO

theorem blSmooth : BlowUpSmooth := by
  intro R _ _ Z W D _ _ π hπ
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  haveI : Smooth (Over.hom Z) := SmoothOfRelativeDimension.smooth (n := D) (f := Over.hom Z)
  haveI : LocallyOfFiniteType (Over.hom Z) := inferInstance
  obtain ⟨-, -, hoff⟩ := blOff R π hπ
  have hp1 : SmoothOfRelativeDimension D (Over.Hom.left (p1 Z)) := by
    change SmoothOfRelativeDimension D (pullback.fst (Over.hom Z) (Over.hom Z))
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := D)
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip ‹_›
  have h1 : SmoothOfRelativeDimension D (Over.Hom.left (π ≫ p1 Z)) := by
    apply ofPts
    intro w
    by_cases hw : Over.Hom.left π w ∈ Set.range (Over.Hom.left (dg Z))
    · obtain ⟨z, hz⟩ := hw
      obtain ⟨U, u, hzU, hc⟩ := coordEx R Z D z
      obtain ⟨c, -, -, hcN⟩ := (dChartEx R Z D).1 U u hc z hzU
      obtain ⟨b⟩ := blChart R π hπ D c
      have hwN : w ∈ Over.Hom.left π ⁻¹ᵁ c.N := by
        show Over.Hom.left π w ∈ c.N
        rw [← hz]
        exact hcN
      rw [← b.cov] at hwN
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hwN
      refine ⟨b.V j, hj, chart _ D c.coord.1 (b.aff j) (fun x hx => c.h1 (b.le j hx)) ?_⟩
      change RingHom.IsStandardSmoothOfRelativeDimension D
        (Scheme.Hom.appLE (Over.Hom.left π ≫ Over.Hom.left (p1 Z)) c.U (b.V j) _).hom
      rw [← Scheme.Hom.appLE_comp_appLE _ _ c.U c.N (b.V j) c.h1 (b.le j), CommRingCat.hom_comp]
      have hg := RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.mp (bCoord R π D c b j)
      have hcomp := hg.comp (stdC _ D)
      rw [MvPolynomial.eval₂Hom_comp_C, zero_add] at hcomp
      exact hcomp
    · haveI : IsClosedImmersion (Over.Hom.left (dg Z)) := by
        change IsClosedImmersion (pullback.diagonal (Over.hom Z))
        infer_instance
      let O0 : (Over.left (XX Z)).Opens :=
        ⟨(Set.range (Over.Hom.left (dg Z)))ᶜ,
          (Over.Hom.left (dg Z)).isClosedEmbedding.isClosed_range.isOpen_compl⟩
      obtain ⟨hiso, -⟩ := hoff O0 rfl
      refine ⟨Over.Hom.left π ⁻¹ᵁ O0, hw, ?_⟩
      change SmoothOfRelativeDimension D
        ((Over.Hom.left π ⁻¹ᵁ O0).ι ≫ Over.Hom.left π ≫ Over.Hom.left (p1 Z))
      rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      exact IsZariskiLocalAtSource.comp (IsZariskiLocalAtSource.comp hp1 _) _
  refine ⟨h1, ?_⟩
  rw [← Over.w (π ≫ p1 Z)]
  exact smoothOfRelativeDimension_comp D D _ _

end UpperTheory.Gal.KunnethLefschetz.G
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.CrossOfRel
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace UpperTheory.Gal.KunnethLefschetz.G

private lemma cross_of_rel {A : Type*} [CommRing A] {T T' b Cl Ck Dl Dk : A} (hT : T ∈ nonZeroDivisors A)
    (hT' : T' ∈ nonZeroDivisors A) (hb : IsUnit b) {n : ℕ}
    (hl : T * Cl * b ^ n = T' * Dl) (hk : T * Ck * b ^ n = T' * Dk) :
    Cl * Dk = Ck * Dl := by
  have h0 : (Cl * Dk - Ck * Dl) * (T * T' * b ^ n) = 0 := by
    linear_combination (T' * Dk) * hl - (T' * Dl) * hk
  have hu : T * T' * b ^ n ∈ nonZeroDivisors A :=
    mul_mem (mul_mem hT hT') (hb.pow n).mem_nonZeroDivisors
  exact sub_eq_zero.1 ((mul_right_mem_nonZeroDivisors_eq_zero_iff hu).1 h0)

theorem blEmb : BlowUpEmbedding := by
  intro R _ _ Z W p hp I π hπ
  obtain ⟨N, i, hi, rfl⟩ := hp
  obtain ⟨n, M, F, hF, hgen⟩ := UpperTheory.exists_homogeneous_generators_idealSheaf_closedImmersion i I
  have hU : ∀ a : Fin (N + 1), IsAffineOpen (i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)) :=
    fun a => (isAffineOpen_stdOpen a).preimage i
  let U : Fin (N + 1) → Z.affineOpens := fun a => ⟨_, hU a⟩
  let g : ∀ a, Fin (M + 1) → Γ(Z, (U a).1) := fun a m => i.appLE _ _ le_rfl (chartHom a (F m))
  choose V le c hVa hVc hc1 hc2 hc3 hc4 hc5 using
    fun a => UpperTheory.exists_blowup_affine_chart_cover_of_span_eq I π hπ (U a) (g a) (hgen a (hU a))
  have hle : ∀ a m, V a m ≤ (π ≫ i) ⁻¹ᵁ Proj.basicOpen (grading R N) (X a) := le
  have key : ∀ a m (O : W.Opens) (hO : O ≤ V a m) l,
      W.presheaf.map (homOfLE hO).op (π.appLE _ _ (le a m) (g a l)) =
        (π ≫ i).appLE _ O (hO.trans (hle a m)) (chartHom a (F l)) := by
    intro a m O hO l
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
    simp only [g]
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have hcross : ∀ (x y : Fin (N + 1) × Fin (M + 1)) (l k : Fin (M + 1)),
      W.presheaf.map (homOfLE (inf_le_left : V x.1 x.2 ⊓ V y.1 y.2 ≤ V x.1 x.2)).op (c x.1 x.2 l) *
        W.presheaf.map (homOfLE (inf_le_right : V x.1 x.2 ⊓ V y.1 y.2 ≤ V y.1 y.2)).op (c y.1 y.2 k) =
      W.presheaf.map (homOfLE (inf_le_left : V x.1 x.2 ⊓ V y.1 y.2 ≤ V x.1 x.2)).op (c x.1 x.2 k) *
        W.presheaf.map (homOfLE (inf_le_right : V x.1 x.2 ⊓ V y.1 y.2 ≤ V y.1 y.2)).op (c y.1 y.2 l) := by
    rintro ⟨a, m⟩ ⟨b, m'⟩ l k
    dsimp only
    have h1 : V a m ⊓ V b m' ≤ V a m := inf_le_left
    have h2 : V a m ⊓ V b m' ≤ V b m' := inf_le_right
    obtain ⟨hu, hrel⟩ := UpperTheory.isUnit_chart_coord_and_homogeneous_chart_transition (π ≫ i) (V a m ⊓ V b m') a b (h1.trans (hle a m)) (h2.trans (hle b m'))
    have e1 : ∀ l, (π ≫ i).appLE _ _ (h1.trans (hle a m)) (chartHom a (F l)) =
        W.presheaf.map (homOfLE h1).op (π.appLE _ _ (le a m) (g a m)) *
          W.presheaf.map (homOfLE h1).op (c a m l) := fun l => by
      rw [← key a m _ h1 l, hc1, map_mul]
    have e2 : ∀ l, (π ≫ i).appLE _ _ (h2.trans (hle b m')) (chartHom b (F l)) =
        W.presheaf.map (homOfLE h2).op (π.appLE _ _ (le b m') (g b m')) *
          W.presheaf.map (homOfLE h2).op (c b m' l) := fun l => by
      rw [← key b m' _ h2 l, hc1, map_mul]
    have r : ∀ l, W.presheaf.map (homOfLE h1).op (π.appLE _ _ (le a m) (g a m)) *
          W.presheaf.map (homOfLE h1).op (c a m l) *
          (π ≫ i).appLE _ _ (h2.trans (hle b m')) (chartHom b (X a : MvPolynomial (Fin (N + 1)) R)) ^ n =
        W.presheaf.map (homOfLE h2).op (π.appLE _ _ (le b m') (g b m')) *
          W.presheaf.map (homOfLE h2).op (c b m' l) := fun l => by
      rw [← e1, ← e2]; exact hrel n (F l) (hF l)
    exact cross_of_rel (UpperTheory.restrict_mem_nonZeroDivisors_of_isAffineOpen (hVa a m) h1 _ (hc3 a m))
      (UpperTheory.restrict_mem_nonZeroDivisors_of_isAffineOpen (hVa b m') h2 _ (hc3 b m')) hu (r l) (r k)
  have hcov : iSup (fun x : Fin (N + 1) × Fin (M + 1) => V x.1 x.2) = ⊤ := by
    rw [iSup_prod]
    simp_rw [hVc]
    change ⨆ a, (π ≫ i) ⁻¹ᵁ Proj.basicOpen (grading R N) (X a) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_basicOpen_X]
    rfl
  obtain ⟨f, hfs, hf⟩ := UpperTheory.cech_cocycle_line_bundle (π ≫ i ≫ PSpace.str R N) M
    (fun x : Fin (N + 1) × Fin (M + 1) => V x.1 x.2) hcov (fun x => x.2) (fun x => c x.1 x.2)
    (fun x => hc2 x.1 x.2) hcross
  choose hD hcoord using hf
  have hpf : ∀ a m m', W.basicOpen (c a m' m) = V a m' ⊓ f ⁻¹ᵁ (Proj.basicOpen (grading R M) (X m') ⊓
      Proj.basicOpen (grading R M) (X m)) := by
    intro a m m'
    rw [← hcoord (a, m') m, Scheme.basicOpen_appLE, basicOpen_chartHom_X]
  have eV : ∀ a m, V a m = π ⁻¹ᵁ (U a).1 ⊓ f ⁻¹ᵁ Proj.basicOpen (grading R M) (X m) := by
    intro a m
    refine _root_.le_antisymm (le_inf (le a m) (hD (a, m))) ?_
    rintro w ⟨hw1, hw2⟩
    have hw : w ∈ iSup (V a) := by rw [hVc]; exact hw1
    obtain ⟨m', hm'⟩ := TopologicalSpace.Opens.mem_iSup.1 hw
    have hb : w ∈ W.basicOpen (c a m' m) := by
      rw [hpf]
      exact ⟨hm', hD (a, m') hm', hw2⟩
    rw [← hc5] at hb
    exact hb.2
  have cU : iSup (fun a => (U a).1) = ⊤ := by
    change ⨆ a, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_basicOpen_X]
    rfl
  refine ⟨M, f, hfs.symm, UpperTheory.sections_generated_over_affine_product_cover (i ≫ PSpace.str R N) (PSpace.str R M) π f hfs.symm
    (fun a => (U a).1) (fun m => Proj.basicOpen (grading R M) (X m)) (fun a => hU a)
    (fun m => isAffineOpen_stdOpen m) cU iSup_basicOpen_X V hVa eV ?_⟩
  intro a m s
  obtain ⟨P, rfl⟩ := hc4 a m s
  induction P using MvPolynomial.induction_on with
  | C r =>
    rw [coe_eval₂Hom, eval₂_C]
    exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact add_mem hp hq
  | mul_X p l hp =>
    rw [map_mul, coe_eval₂Hom, eval₂_X]
    exact mul_mem hp (Subring.subset_closure (Or.inr ⟨chartHom m (X l), hcoord (a, m) l⟩))

end UpperTheory.Gal.KunnethLefschetz.G
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ExSmooth
section
open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem stdSmooth_of_bijective {A B σ : Type} [CommRing A] [CommRing B] [Fintype σ] {d : ℕ}
    (hd : Fintype.card σ = d) (φ : A →+* B) (y : σ → B)
    (hb : Function.Bijective (MvPolynomial.eval₂Hom φ y)) :
    φ.IsStandardSmoothOfRelativeDimension d := by
  have h0 : (algebraMap A (MvPolynomial (Fin d) A)).IsStandardSmoothOfRelativeDimension d :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := d)).mpr
      (GlobalTheory.CompanionTheory.Ar.LieInh.stdSmooth_mvPolynomial A d)
  let e₁ : MvPolynomial (Fin d) A ≃+* MvPolynomial σ A :=
    (MvPolynomial.renameEquiv A (Fintype.equivFinOfCardEq hd).symm).toRingEquiv
  let e₂ : MvPolynomial σ A ≃+* B := RingEquiv.ofBijective _ hb
  have hφ : φ = (e₁.trans e₂).toRingHom.comp (algebraMap A (MvPolynomial (Fin d) A)) := by
    ext a
    simp [e₁, e₂, MvPolynomial.algebraMap_eq]
  rw [hφ]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ _ h0

private theorem comap_surjective_of_bijective {A B σ : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (y : σ → B) (hb : Function.Bijective (MvPolynomial.eval₂Hom φ y)) :
    Function.Surjective (PrimeSpectrum.comap φ) := by
  let e : MvPolynomial σ A ≃+* B := RingEquiv.ofBijective _ hb
  let ρ : B →+* A := (MvPolynomial.eval₂Hom (RingHom.id A) fun _ => 0).comp e.symm.toRingHom
  have hρ : ρ.comp φ = RingHom.id A := by
    ext a
    have : e.symm (φ a) = MvPolynomial.C a :=
      e.symm_apply_eq.2 (by simp [e])
    simp [ρ, this]
  intro p
  refine ⟨PrimeSpectrum.comap ρ p, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply, hρ, PrimeSpectrum.comap_id]

private theorem exists_apply_eq {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (hs : Function.Surjective (PrimeSpectrum.comap (f.appLE U V e).hom)) {y : Y} (hy : y ∈ U) :
    ∃ x, f x = y := by
  obtain ⟨p, rfl⟩ : y ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hy
  obtain ⟨q, rfl⟩ := hs p
  refine ⟨hV.fromSpec q, ?_⟩
  have h := congr($(IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e) q)
  simp only [Scheme.Hom.comp_apply] at h
  exact h.symm

private theorem isProper_snd {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (hf : IsProper f) :
    IsProper (pullback.snd f g) :=
  haveI := hf; inferInstance

private theorem exists_chart {R : Type} [CommRing R] {Z W : Sch R} (d : ℕ) [IsSeparated Z.hom]
    [SmoothOfRelativeDimension (d + 1) Z.hom] (π : W ⟶ XX Z) (hπ : IsBl π) (z : Z.left) :
    ∃ (c : DChart Z (d + 1)) (_ : BChart π c.N c.s), (dg Z).left z ∈ c.N := by
  obtain ⟨U, u, hz, hc⟩ := coordEx R Z (d + 1) z
  obtain ⟨c, -, -, hN⟩ := (dChartEx R Z (d + 1)).1 U u hc z hz
  exact ⟨c, (blChart R π hπ (d + 1) c).some, hN⟩

theorem exSmooth : ExSmooth := by
  intro R _ _ Z W d _ _ π hπ
  haveI : Smooth Z.hom := SmoothOfRelativeDimension.smooth (d + 1) Z.hom
  refine ⟨⟨fun x => ?_⟩, ?_, ⟨fun z => ?_⟩⟩
  · obtain ⟨c, b, hN⟩ := exists_chart d π hπ ((exG π).left x)
    have e : (exI π).left ≫ π.left = (exG π).left ≫ (dg Z).left := pullback.condition
    have hW : (exI π).left x ∈ π.left ⁻¹ᵁ c.N := by
      have h := congr($e x)
      simp only [Scheme.Hom.comp_apply] at h
      change π.left ((exI π).left x) ∈ c.N
      rw [h]
      exact hN
    rw [← b.cov] at hW
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hW
    obtain ⟨hA, hB, -, h, hbij⟩ := exChart R π (d + 1) c b j
    exact ⟨_, hA, _, hB, hj, h, stdSmooth_of_bijective (by simp [Fintype.card_subtype_compl]) _ _ hbij⟩
  · exact isProper_snd π.left (dg Z).left (blOff R π hπ).1
  · obtain ⟨c, b, hN⟩ := exists_chart d π hπ z
    obtain ⟨hA, hB, -, h, hbij⟩ := exChart R π (d + 1) c b 0
    exact exists_apply_eq _ hA hB h (comap_surjective_of_bijective _ _ hbij) hN

end UpperTheory.Gal.KunnethLefschetz.G
end

