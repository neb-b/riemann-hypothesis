module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.EtaleTrace.Bundle0001
public import Development.EtaleCohomology.EtaleTrace.Bundle0008
public import Development.EtaleCohomology.EtaleTrace.Bundle0009
public import Development.EtaleCohomology.EtaleTrace.LProperPf
public import Development.EtaleCohomology.EtaleTrace.Bundle0006
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveSpaceChart
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PPnCls
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz.PnClsPf

private theorem sm_open {A B C : Scheme.{0}} (i : A ⟶ B) [IsOpenImmersion i] (f : B ⟶ C) (n : ℕ)
    (h : SmoothOfRelativeDimension n f) : SmoothOfRelativeDimension n (i ≫ f) := by
  have := smoothOfRelativeDimension_comp (n := 0) (m := n) i f
  simpa using this

private theorem empty_v (l : ℕ) [Fact l.Prime] (hI : In) (X : Scheme.{0}) (hX : IsEmpty X) (n : ℤ) :
    Subsingleton (V l X n) := by
  have hE := LEmptyPf.LEmpty_of hI.a5 hI.a9
  haveI h1 : ∀ k, Subsingleton (HtL l k (sch.obj X) n 0) := fun k => hE _ X hX _ n
  haveI h2 : Subsingleton (Hl l (sch.obj X) n 0) := by
    show Subsingleton (HlSub l (sch.obj X) n 0)
    infer_instance
  show Subsingleton (ℚ_[l] ⊗[ℤ_[l]] Hl l (sch.obj X) n 0)
  infer_instance

private theorem iso_sub {A B : Scheme.{0}} (e : A ≅ B) (q : ℕ) (n : ℤ)
    (h : Subsingleton (Ht q (sch.obj B) n 0)) : Subsingleton (Ht q (sch.obj A) n 0) := by
  have key : ∀ z : Ht q (sch.obj A) n 0,
      pull (ZMod q) (sch.map e.hom) (tw q 0) n (pull (ZMod q) (sch.map e.inv) (tw q 0) n z) = z := by
    intro z
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, pull_id]
  constructor
  intro x y
  rw [← key x, ← key y,
    Subsingleton.elim (pull (ZMod q) (sch.map e.inv) (tw q 0) n x)
      (pull (ZMod q) (sch.map e.inv) (tw q 0) n y)]

end UpperTheory.Gal.KunnethLefschetz.PnClsPf

open UpperTheory.Gal.KunnethLefschetz.PnClsPf in
theorem UpperTheory.Gal.KunnethLefschetz.pnCls_holds :
    UpperTheory.Gal.KunnethLefschetz.PnCls := by
  intro hI hF hH hO l _ k _ _ hl hR hL hA hG
  obtain ⟨gq⟩ := hG
  have one_ne : oneV l (S k) ≠ 0 := by
    intro h0
    obtain ⟨r, -, hr⟩ := Low.line hL 0
    have h1 := hr 0 (by simp)
    have h2 := hr 1 (by simp [h0])
    exact one_ne_zero (h2.trans h1.symm)
  have key : ∀ d : ℕ, ∃ t : Pt (PNto k d), IsClosedImmersion t.1 ∧
      ∃ U : (PN k d).Opens, Off t.1 U ∧
        ∃ z : V l (PN k d) (2 * (d : ℤ)), z ≠ 0 ∧ pb l U.ι (2 * (d : ℤ)) z = 0 := by
    intro d
    induction d with
    | zero =>
      haveI := (hF k 0).2.2.2
      refine ⟨⟨inv (PNto k 0), IsIso.inv_hom_id _⟩, inferInstance, ⊥, ?_, ?_⟩
      · show ((⊥ : (PN k 0).Opens) : Set (PN k 0)) = (Set.range (inv (PNto k 0)).base)ᶜ
        rw [Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso (inv (PNto k 0)).base).2]
        simp
      · refine ⟨oneV l (PN k 0), ?_, ?_⟩
        · intro h0
          apply one_ne
          have hu := Ring.one_nat hR (inv (PNto k 0))
            (LPdCut.unit_of (PNto k 0) (isUnit_iff_ne_zero.mpr hl))
          rw [← hu]
          change pb l (inv (PNto k 0)) 0 (oneV l (PN k 0)) = 0
          rw [h0, map_zero]
        · have he : IsEmpty ((⊥ : (PN k 0).Opens) : Scheme) := ⟨fun x => by simpa using x.2⟩
          haveI := empty_v l hI ((⊥ : (PN k 0).Opens) : Scheme) he (2 * ((0 : ℕ) : ℤ))
          exact Subsingleton.elim _ _
    | succ d ih =>
      obtain ⟨t, htc, U, hU, z, hz, hzU⟩ := ih
      obtain ⟨ι, U0, hιc, hιp, hoff0, ⟨eU0⟩⟩ := hH k d
      haveI := htc
      haveI := hιc
      let t' : Pt (PNto k (d + 1)) := Pt.map ι hιp t
      have htc' : IsClosedImmersion t'.1 := by
        show IsClosedImmersion (t.1 ≫ ι)
        infer_instance
      obtain ⟨U', hU'⟩ := hO.1 t'.1 htc'
      have hP : IsPair 1 d (PNto k (d + 1)) ι :=
        ⟨hιc, (hF k (d + 1)).1.2, by rw [hιp]; exact (hF k d).1.2⟩
      have hn : 2 * (d : ℤ) + 2 * ((1 : ℕ) : ℤ) = 2 * ((d + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      refine ⟨t', htc', U', hU', gq.g hP hn z, ?_, ?_⟩
      · intro h0
        apply hz
        have hinj := gq.inj hP hn U0 hoff0 (fun j =>
          iso_sub eU0 (l ^ j) _ (hA j (d + 1) _ (by push_cast; omega)))
        apply hinj
        rw [h0, map_zero]
      · have hinj : Function.Injective ι.base := ι.isClosedEmbedding.injective
        have hVU : ι ⁻¹ᵁ U' = U := by
          apply TopologicalSpace.Opens.ext
          rw [hU]
          show ι.base ⁻¹' (U' : Set (PN k (d + 1))) = _
          rw [hU']
          ext x
          simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range, t', Pt.map]
          constructor
          · rintro h ⟨y, rfl⟩
            exact h ⟨y, rfl⟩
          · rintro h ⟨y, hy⟩
            apply h
            refine ⟨y, hinj ?_⟩
            rw [← hy]
            rfl
        subst hVU
        have hP' : IsPair 1 d (U'.ι ≫ PNto k (d + 1)) (ι ∣_ U') := by
          refine ⟨inferInstance, sm_open U'.ι _ _ (hF k (d + 1)).1.2, ?_⟩
          rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hιp]
          exact sm_open _ _ _ (hF k d).1.2
        rw [gq.nat hP' hP U'.ι (ι ⁻¹ᵁ U').ι rfl (isPullback_morphismRestrict ι U') hn z, hzU,
          map_zero]
  intro d
  obtain ⟨t, -, U, hU, z, hz, hzU⟩ := key d
  exact ⟨t, U, z, hU, hz, hzU⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PPnFacts
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum
attribute [local instance] MvPolynomial.gradedAlgebra

namespace UpperTheory.Gal.KunnethLefschetz.PnF
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

private def chartE (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)) :
    Chart k i ≃+* MvPolynomial (Fin N) k :=
  (chartEquiv k i).trans (MvPolynomial.renameEquiv k (finSuccAboveEquiv i).symm).toRingEquiv

private theorem chartE_C (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)) (a : k) :
    chartE k N i (HomogeneousLocalization.fromZeroRingHom (grading k N) _
      (algebraMap k (grading k N 0) a)) = MvPolynomial.C a := by
  have h : HomogeneousLocalization.fromZeroRingHom (grading k N) _
      (algebraMap k (grading k N 0) a) = polyToChart k i (MvPolynomial.C a) := by
    simp [polyToChart]
  rw [h]
  have h2 : chartToPoly k i (polyToChart k i (MvPolynomial.C a)) = MvPolynomial.C a := by
    rw [← RingHom.comp_apply, chartToPoly_polyToChart]
    rfl
  simp only [chartE, RingEquiv.trans_apply]
  change (MvPolynomial.renameEquiv k (finSuccAboveEquiv i).symm)
    (chartToPoly k i (polyToChart k i (MvPolynomial.C a))) = _
  rw [h2]
  simp

private theorem chart_holds : LPdCut.LChart := by
  intro k _ N i
  let e := chartE k N i
  let ι := Proj.awayι (grading k N) (MvPolynomial.X i) (X_mem i) one_pos
  have hiso : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
    have : IsIso (CommRingCat.ofHom e.toRingHom) :=
      (RingEquiv.toCommRingCatIso e).isIso_hom
    infer_instance
  refine ⟨Spec.map (CommRingCat.ofHom e.toRingHom) ≫ ι, inferInstance, ?_, ?_⟩
  · simp only [PNto, Category.assoc]
    rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact congrArg (AddMonoidAlgebra.coeff · _) (chartE_C k N i a)
  · have h := Scheme.Hom.opensRange_comp_of_isIso (Spec.map (CommRingCat.ofHom e.toRingHom)) ι
    rw [Proj.opensRange_awayι] at h
    exact congrArg (fun U : (PN k N).Opens => (U : Set (PN k N))) h

private theorem locNml (k : Type) [Field k] (d : ℕ) : TranscendenceTraces.LocNml (PN k d) := by
  intro s
  have hs : s ∈ (⊤ : (PN k d).Opens) := trivial
  rw [← LSmoothPf.Dp_cover k d] at hs
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hs
  obtain ⟨j, hj, -, hr⟩ := chart_holds k d i
  haveI := hj
  have hU : j.opensRange = LPdCut.Dp k d i := TopologicalSpace.Opens.ext hr
  refine ⟨j.opensRange, isAffineOpen_opensRange j, hU ▸ hi, ?_⟩
  have e1 := j.appIso ⊤
  rw [Scheme.Hom.image_top_eq_opensRange] at e1
  have e := (e1 ≪≫ Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv
  exact ⟨MulEquiv.isDomain _ e.toMulEquiv, IsIntegrallyClosed.of_equiv e.symm⟩

private theorem iso0 (k : Type) [Field k] : IsIso (PNto k 0) := by
  obtain ⟨j, hj, hc, hr⟩ := chart_holds k 0 0
  have htop : LPdCut.Dp k 0 0 = ⊤ := by
    have := LSmoothPf.Dp_cover k 0
    simpa using this
  have hjiso : IsIso j := by
    refine (isIso_iff_isOpenImmersion_and_surjective j).2 ⟨hj, ⟨fun x => ?_⟩⟩
    have : x ∈ Set.range j := by
      rw [hr, htop]
      trivial
    exact this
  have hCiso : IsIso (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin 0) k)) := by
    have hb : Function.Bijective (MvPolynomial.C : k →+* MvPolynomial (Fin 0) k) :=
      ⟨MvPolynomial.C_injective _ _, MvPolynomial.C_surjective _⟩
    exact (RingEquiv.toCommRingCatIso (RingEquiv.ofBijective _ hb)).isIso_hom
  have hP : PNto k 0 = inv j ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin 0) k)) := by
    rw [← hc, IsIso.inv_hom_id_assoc]
  rw [hP]
  infer_instance

end UpperTheory.Gal.KunnethLefschetz.PnF

theorem UpperTheory.Gal.KunnethLefschetz.pnFacts_holds :
    UpperTheory.Gal.KunnethLefschetz.PnFacts := by
  unfold UpperTheory.Gal.KunnethLefschetz.PnFacts
  intro k _ d
  exact ⟨⟨LProperPf.LProper_of k d, LSmoothPf.LSmooth_of PnF.chart_holds k d⟩, Cov.PNIntegral_of k d, PnF.locNml k d, PnF.iso0 k⟩
end
end

