module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0477
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConnectedGlobalSections

variable {q : ℕ} [NeZero q] {i : ℤ}

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (t : Sec F U) :
    Sec.res g (n • t) = n • Sec.res g t := map_nsmul ((F.obj.map g.op).hom) n t

theorem res_twGen {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 V U g ζ

theorem prim_map_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    (ζ.map g.appTop.hom).map k.appTop.hom = ζ.map (k ≫ g).appTop.hom := by
  apply Subtype.ext
  simp [Prim.map]
  rfl

theorem nsmul_eq_up {U : Scheme.{0}} (n : ℕ) (t : Sec (tw q i) U) : n • t = (ULift.up (n : ZMod q)) • t := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  rfl

theorem scalar_eq {U : Scheme.{0}} [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c d : ZMod q)
    (h : c.val • twGen i ζ = d.val • twGen i ζ) : c = d := by
  have h0 : (c - d).val • twGen i ζ = 0 := by
    rw [nsmul_eq_up, ZMod.natCast_zmod_val]
    rw [nsmul_eq_up, nsmul_eq_up, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h
    have : (ULift.up (c - d) : ULift.{1} (ZMod q)) = ULift.up c - ULift.up d := rfl
    rw [this, sub_smul, h, sub_self]
  have hd := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 U ζ _ h0
  have hv : (c - d).val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt _)
  exact sub_eq_zero.1 ((ZMod.val_eq_zero _).1 hv)

theorem q_nsmul {U : Scheme.{0}} (t : Sec (tw q i) U) (k : ℕ) : (q * k) • t = 0 := by
  rw [nsmul_eq_up]
  have : ((q * k : ℕ) : ZMod q) = 0 := by simp
  rw [this]
  exact zero_smul _ t

theorem sec_eq_nsmul (X : Scheme.{0}) [Nonempty X] (hX : ∀ s : Set X, IsClopen s → s = ∅ ∨ s = Set.univ)
    (ζ : Prim q Γ(X, ⊤)) (y : Sec (tw q i) X) : ∃ c : ℕ, y = c • twGen i ζ := by
  classical
  let P : ∀ V : Scheme.{0}, (V ⟶ X) → ℕ → Prop := fun V g c => Sec.res g y = c • twGen i (ζ.map g.appTop.hom)
  have hstab : ∀ c (V W : Scheme.{0}) (g : V ⟶ X) (k : W ⟶ V), P V g c → P W (k ≫ g) c := by
    intro c V W g k h
    simp only [P] at h ⊢
    rw [res_comp, h, res_nsmul, res_twGen, prim_map_comp]
  have hloc := (loc_iff_etale_affine_points X (fun V g => ∃ c, P V g c)
    (fun V W g k ⟨c, h⟩ => ⟨c, hstab c V W g k h⟩)).1 ((GlobalTheory.T.tateTwist_sections_locally_generated q i).2.1 X ζ y)
  let S : ZMod q → Set X := fun c =>
    {x | ∃ (V : Scheme.{0}) (g : V ⟶ X), IsAffine V ∧ Etale g ∧ x ∈ Set.range g ∧ P V g c.val}
  have hopen : ∀ c, IsOpen (S c) := by
    intro c
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨V, g, hV, hg, hx, hP⟩
    haveI := hg
    refine ⟨Set.range g, ?_, g.isOpenMap.isOpen_range, hx⟩
    rintro _ ⟨v, rfl⟩
    exact ⟨V, g, hV, hg, ⟨v, rfl⟩, hP⟩
  have hcov : ∀ x, ∃ c, x ∈ S c := by
    intro x
    obtain ⟨V, g, hV, hg, hx, n, hn⟩ := hloc x
    refine ⟨(n : ZMod q), V, g, hV, hg, hx, ?_⟩
    simp only [P] at hn ⊢
    rw [hn, nsmul_eq_up, nsmul_eq_up, ZMod.natCast_zmod_val]
  have hdisj : ∀ c d x, x ∈ S c → x ∈ S d → c = d := by
    rintro c d x ⟨V, g, -, -, ⟨v, rfl⟩, hP⟩ ⟨V', g', -, -, ⟨v', hv'⟩, hP'⟩
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := g') v v' hv'.symm
    haveI : Nonempty ↥(Limits.pullback g g') := ⟨z⟩
    have h1 := hstab _ _ _ g (pullback.fst g g') hP
    have h2 := hstab _ _ _ g' (pullback.snd g g') hP'
    simp only [P] at h1 h2
    rw [pullback.condition] at h1
    exact scalar_eq _ c d (h1.symm.trans h2)
  obtain ⟨x0⟩ := ‹Nonempty X›
  obtain ⟨c0, hx0⟩ := hcov x0
  have hcompl : (S c0)ᶜ = ⋃ d ∈ ({c0}ᶜ : Set (ZMod q)), S d := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hx
      obtain ⟨d, hd⟩ := hcov x
      exact ⟨d, fun h => hx (h ▸ hd), hd⟩
    · rintro ⟨d, hd, hxd⟩ hx
      exact hd (hdisj d c0 x hxd hx)
  have hclopen : IsClopen (S c0) := by
    refine ⟨?_, hopen c0⟩
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_biUnion fun d _ => hopen d
  have huniv : S c0 = Set.univ := by
    rcases hX _ hclopen with h | h
    · rw [h] at hx0; exact absurd hx0 (Set.notMem_empty _)
    · exact h
  refine ⟨c0.val, (sec_ext_glue (ZMod q) (tw q i) X).1 _ _ ?_⟩
  refine (loc_iff_etale_affine_points X (fun _ g => Sec.res g y = Sec.res g (c0.val • twGen i ζ))
    (fun V W g k h => by rw [res_comp, res_comp, h])).2 ?_
  intro x
  obtain ⟨V, g, hV, hg, hx, hP⟩ : x ∈ S c0 := huniv ▸ Set.mem_univ x
  refine ⟨V, g, hV, hg, hx, ?_⟩
  rw [hP, res_nsmul, res_twGen]

end GlobalTheory.EtC.ConnectedGlobalSections

namespace GlobalTheory.EtC.ConnectedGlobalSections

theorem clopen_of_idem (B : Type) [CommRing B] (hB : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (s : Set (Spec (CommRingCat.of B))) (hs : IsClopen s) : s = ∅ ∨ s = Set.univ := by
  obtain ⟨e, he, h⟩ := PrimeSpectrum.isClopen_iff.1 (show IsClopen (X := PrimeSpectrum B) s from hs)
  rcases hB e he with rfl | rfl
  · left
    change (s : Set (PrimeSpectrum B)) = ∅
    rw [h]; simp <;> rfl
  · right
    change (s : Set (PrimeSpectrum B)) = Set.univ
    rw [h]; simp <;> rfl

end GlobalTheory.EtC.ConnectedGlobalSections


open GlobalTheory.EtC.ConnectedGlobalSections in
theorem GlobalTheory.EtC.h_zero_pull_bijective : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A'),
    IsUnit (q : A) → (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → Nontrivial A' →
    (∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) → (∀ e : A', IsIdempotentElem e → e = 0 ∨ e = 1) →
    ∀ i : ℤ, Function.Bijective (pull _ (spMap f) (tw q i) 0) := by
  intro q _ A A' _ _ f hq ⟨ζ0, hζ0⟩ hA' hidA hidA' i
  haveI : Nontrivial A := f.domain_nontrivial
  obtain ⟨-, e, he, -⟩ := _root_.GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero (ZMod q) (tw q i)
  let g : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom f)
  haveI : Nonempty (Spec (CommRingCat.of A)) := inferInstance
  haveI : Nonempty (Spec (CommRingCat.of A')) := inferInstance
  let ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤) :=
    Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ⟨ζ0, hq, hζ0⟩
  have hres : Function.Bijective (Sec.res (F := tw q i) g) := by
    constructor
    · change Function.Injective ((tw q i).obj.map g.op).hom
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨c, rfl⟩ := sec_eq_nsmul _ (clopen_of_idem A hidA) ζ y
      have h0 : c • twGen i (ζ.map g.appTop.hom) = 0 := by
        rw [← res_twGen, ← res_nsmul]; exact hy
      obtain ⟨k, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 _ _ _ h0
      exact q_nsmul _ k
    · intro y
      obtain ⟨c, rfl⟩ := sec_eq_nsmul _ (clopen_of_idem A' hidA') (ζ.map g.appTop.hom) y
      exact ⟨c • twGen i ζ, by rw [res_nsmul, res_twGen]⟩
  have key : ∀ s, pull _ (spMap f) (tw q i) 0 (e _ s) = e _ (Sec.res g s) := fun s => he g s
  have hfun : ⇑(pull _ (spMap f) (tw q i) 0) = e _ ∘ Sec.res g ∘ (e _).symm := by
    funext x
    obtain ⟨s, rfl⟩ := (e _).surjective x
    simp [key]
  rw [hfun]
  exact (e _).bijective.comp (hres.comp (e _).symm.bijective)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralThetaMellinInterchange
section
noncomputable section

open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellin

theorem hasSum_integral_theta (I : Type) [Fintype I] (ι : Type) [Countable ι] (e : ι → I → ℂ) (a : ι → ℂ) (C : ℝ)
    (hC : ∀ j, ‖a j‖ ≤ C) (n : I → ℤ) (s : ℂ) (p : (I → ℝ) → ℝ) (hp : Measurable p) (hp0 : ∀ y, 0 ≤ p y)
    (hp1 : ∀ y, p y ≤ 1) (hint : ∀ j, Integrable (GlobalTheory.HeckeMellin.term n s (e j)))
    (hsum : Summable (fun j => ∫ y, p y * ‖GlobalTheory.HeckeMellin.term n s (e j) y‖)) :
    HasSum (fun j => a j * ∫ y, (p y : ℂ) * GlobalTheory.HeckeMellin.term n s (e j) y)
      (∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) := by
  set F : ι → (I → ℝ) → ℂ := fun j y => a j * ((p y : ℂ) * term n s (e j) y) with hF
  have hpm : AEStronglyMeasurable (fun y => (p y : ℂ)) volume :=
    (Complex.measurable_ofReal.comp hp).aestronglyMeasurable
  have hpb : ∀ᵐ y ∂(volume : Measure (I → ℝ)), ‖(p y : ℂ)‖ ≤ 1 := by
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 y)]; exact hp1 y
  have hpint : ∀ j, Integrable (fun y => (p y : ℂ) * term n s (e j) y) :=
    fun j => (hint j).bdd_mul hpm hpb
  have hFint : ∀ j, Integrable (F j) := fun j => (hpint j).const_mul (a j)
  have hnorm : ∀ j y, ‖F j y‖ = ‖a j‖ * (p y * ‖term n s (e j) y‖) := by
    intro j y
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 y)]
  have hFsum : Summable fun j => ∫ y, ‖F j y‖ := by
    have hi : ∀ j, ∫ y, ‖F j y‖ = ‖a j‖ * ∫ y, p y * ‖term n s (e j) y‖ := by
      intro j; simp_rw [hnorm]; exact integral_const_mul _ _
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun y => norm_nonneg _) (fun j => ?_) (hsum.mul_left C)
    rw [hi]
    exact mul_le_mul_of_nonneg_right (hC j)
      (integral_nonneg fun y => mul_nonneg (hp0 y) (norm_nonneg _))
  have h := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hl : (fun j => ∫ y, F j y) = fun j => a j * ∫ y, (p y : ℂ) * term n s (e j) y := by
    funext j; exact integral_const_mul _ _
  have hr : (fun y => ∑' j, F j y) =
      fun y => (p y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) := by
    funext y
    simp only [hF, GlobalTheory.HeckeTheta.theta, term]
    rw [← tsum_mul_left, ← tsum_mul_right]
    congr 1; funext j; ring
  rw [hl, hr] at h
  exact h

end GlobalTheory.HeckeMellin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIteratedComplexPartialDerivTermwise
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open Set Filter Topology in
open NumberField IsDedekindDomain in
open scoped ContDiff nonZeroDivisors in
private lemma partialD_eqOn_fderiv_single {I : Type} [Fintype I] [DecidableEq I] {U : Set (I → ℂ)}
    {h : (I → ℂ) → ℂ} (hU : IsOpen U) (hh : DifferentiableOn ℂ h U) (i : I) :
    EqOn (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD i h) (fun z ↦ fderiv ℂ h z (Pi.single i 1)) U := by
  intro z hz
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD
  exact (hh.differentiableAt (hU.mem_nhds hz)).lineDeriv_eq_fderiv

open Set Filter Topology in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma iterD_eqOn_iteratedFDeriv_single {I : Type} [Fintype I] [DecidableEq I]
    {U : Set (I → ℂ)} {h : (I → ℂ) → ℂ} (hU : IsOpen U) (hh : DifferentiableOn ℂ h U) :
    ∀ l : List I, EqOn (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD l h)
      (fun z ↦ iteratedFDeriv ℂ l.length h z (fun k ↦ Pi.single (l.get k) 1)) U
  | [] => by
    intro z _
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD]
  | i :: l => by
    intro z hz
    have ih := iterD_eqOn_iteratedFDeriv_single hU hh l
    have hG : DifferentiableOn ℂ
        (fun z ↦ iteratedFDeriv ℂ l.length h z (fun k ↦ Pi.single (l.get k) 1)) U :=
      (_root_.GlobalTheory.SCV.differentiableOn_iteratedFDeriv hU hh l.length).continuousMultilinear_apply_const _
    have hd : DifferentiableOn ℂ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD l h) U := hG.congr ih
    have hstep : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD (i :: l) h z =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD i (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD l h) z := by
      simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD]
    have hev : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD l h =ᶠ[𝓝 z]
        fun z ↦ iteratedFDeriv ℂ l.length h z (fun k ↦ Pi.single (l.get k) 1) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hz) ih
    rw [hstep, partialD_eqOn_fderiv_single hU hd i hz]
    simp only
    rw [hev.fderiv_eq, fderiv_continuousMultilinear_apply_const_apply
      ((_root_.GlobalTheory.SCV.differentiableOn_iteratedFDeriv hU hh l.length).differentiableAt (hU.mem_nhds hz))]
    exact (iteratedFDeriv_succ_apply_left (f := h) (x := z) (n := l.length)
      (fun k ↦ Pi.single ((i :: l).get k) 1)).symm


open Set Filter Topology in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hasSum_iterD_termwise : ∀ (I : Type) [Fintype I] [DecidableEq I] (Ξ : Type) (u : List I) (r : ℝ)
    (f : Ξ → (I → ℂ) → ℂ) (g : (I → ℂ) → ℂ) (M : Ξ → ℝ), 0 < r → Summable M →
    (∀ ξ, DifferentiableOn ℂ (f ξ) (Metric.ball 0 r)) →
    (∀ ξ, ∀ z ∈ Metric.ball (0 : I → ℂ) r, ‖f ξ z‖ ≤ M ξ) →
    (∀ z ∈ Metric.ball (0 : I → ℂ) r, HasSum (fun ξ ↦ f ξ z) (g z)) →
    HasSum (fun ξ ↦ _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u (f ξ) 0) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0) := by
  intro I _ _ Ξ u r f g M hr hM hf hbound hsum
  have hU : IsOpen (Metric.ball (0 : I → ℂ) r) := Metric.isOpen_ball
  have h0 : (0 : I → ℂ) ∈ Metric.ball (0 : I → ℂ) r := Metric.mem_ball_self hr
  have hloc : ∀ x ∈ Metric.ball (0 : I → ℂ) r, ∃ t ∈ 𝓝 x, ∃ v : Ξ → ℝ, Summable v ∧
      ∀ ξ, ∀ z ∈ t, ‖f ξ z‖ ≤ v ξ :=
    fun x hx ↦ ⟨_, hU.mem_nhds hx, M, hM, hbound⟩
  have hg_eq : EqOn g (fun w ↦ ∑' ξ, f ξ w) (Metric.ball 0 r) :=
    fun z hz ↦ (hsum z hz).tsum_eq.symm
  have hg : DifferentiableOn ℂ g (Metric.ball 0 r) :=
    (_root_.GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal hU hf hloc).congr hg_eq
  have hev : g =ᶠ[𝓝 0] fun w ↦ ∑' ξ, f ξ w := Filter.eventuallyEq_of_mem (hU.mem_nhds h0) hg_eq
  have hS := _root_.GlobalTheory.SCV.hasSum_iteratedFDeriv_of_locally_normal hU hf hloc u.length h0
  rw [← (hev.iteratedFDeriv ℂ u.length).eq_of_nhds] at hS
  rw [iterD_eqOn_iteratedFDeriv_single hU hg u h0]
  simp only [iterD_eqOn_iteratedFDeriv_single hU (hf _) u h0]
  exact ContinuousMultilinearMap.hasSum_eval hS _

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeIdealEuclideanLatticeIsZLattice
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

noncomputable section

namespace GlobalTheory.HeckePoisson

open GlobalTheory.CMVal InfinitePlace ComplexConjugate
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {I : Type} [Fintype I]

def toMixed {φ : I → K →+* ℂ} (h : IsCMType φ) : EuclideanSpace ℂ I ≃ₗ[ℝ] mixedEmbedding.mixedSpace K := by
  classical
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩
  let b : I ≃ InfinitePlace K := Equiv.ofBijective _ (GlobalTheory.CMVal.Model.IsCMType.bijective h)
  exact
  { toFun := fun z => (0, fun w => if φ (b.symm w.1) = (InfinitePlace.mk (φ (b.symm w.1))).embedding
        then z (b.symm w.1) else conj (z (b.symm w.1)))
    invFun := fun x => WithLp.toLp 2 (fun i => if φ i = (InfinitePlace.mk (φ i)).embedding
        then x.2 ⟨InfinitePlace.mk (φ i), IsTotallyComplex.isComplex _⟩
        else conj (x.2 ⟨InfinitePlace.mk (φ i), IsTotallyComplex.isComplex _⟩))
    map_add' := fun x y => Prod.ext (by simp) (funext fun w => by
      simp only [Prod.snd_add, Pi.add_apply, PiLp.add_apply]; split_ifs <;> simp)
    map_smul' := fun r x => Prod.ext (by simp) (funext fun w => by
      simp only [Prod.smul_snd, Pi.smul_apply, PiLp.smul_apply, RingHom.id_apply]
      split_ifs <;> simp [Complex.real_smul])
    left_inv := fun z => by
      ext i
      have hi : b.symm (InfinitePlace.mk (φ i)) = i := b.symm_apply_apply i
      simp only [hi]
      split_ifs <;> simp
    right_inv := fun x => by
      refine Prod.ext (Subsingleton.elim _ _) (funext fun w => ?_)
      have e : (⟨InfinitePlace.mk (φ (b.symm w.1)), IsTotallyComplex.isComplex _⟩ : {w : InfinitePlace K // w.IsComplex}) = w :=
        Subtype.ext (b.apply_symm_apply w.1)
      simp only [e]
      split_ifs <;> simp }

theorem toMixed_embA {φ : I → K →+* ℂ} (h : IsCMType φ) (α : 𝓞 K) :
    toMixed h (embA φ α) = mixedEmbedding K (α : K) := by
  classical
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩
  refine Prod.ext (Subsingleton.elim _ _) (funext fun w => ?_)
  rw [mixedEmbedding.mixedEmbedding_apply_isComplex]
  simp only [toMixed, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, embA_apply]
  set i := (Equiv.ofBijective _ (GlobalTheory.CMVal.Model.IsCMType.bijective h)).symm w.1 with hi
  have hw : InfinitePlace.mk (φ i) = w.1 :=
    (Equiv.ofBijective _ (GlobalTheory.CMVal.Model.IsCMType.bijective h)).apply_symm_apply w.1
  split_ifs with hs
  · rw [hs, hw]
  · have hc := (InfinitePlace.embedding_mk_eq (φ i)).resolve_left (fun e => hs e.symm)
    rw [← hw, hc]
    simp [ComplexEmbedding.conjugate_coe_eq]

open Classical in
theorem lat_eq_comap {φ : I → K →+* ℂ} (h : IsCMType φ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) :
    lat φ M = ZLattice.comap (E := mixedEmbedding.mixedSpace K) (F := EuclideanSpace ℂ I) ℝ (mixedEmbedding.idealLattice K
      (Units.mk0 (M : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hM)))
      (toMixed h).toContinuousLinearEquiv.toLinearMap := by
  ext z
  rw [mem_lat]
  change _ ↔ toMixed h z ∈ mixedEmbedding.idealLattice K _
  rw [mixedEmbedding.mem_idealLattice]
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨(μ : K), (FractionalIdeal.mem_coeIdeal _).2 ⟨μ, hμ, rfl⟩, (toMixed_embA h μ).symm⟩
  · rintro ⟨y, hy, hyz⟩
    have hy' : y ∈ (M : FractionalIdeal (𝓞 K)⁰ K) := hy
    obtain ⟨μ, hμ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy'
    exact ⟨μ, hμ, (toMixed h).injective (by rw [toMixed_embA]; exact hyz)⟩

theorem lat_isZLattice : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I]
    (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ M : Ideal (𝓞 K), M ≠ ⊥ →
      ∃ _ : DiscreteTopology (GlobalTheory.HeckePoisson.lat φ M), IsZLattice ℝ (GlobalTheory.HeckePoisson.lat φ M) := by
  intro K _ _ _ I _ φ h M hM
  classical
  rw [lat_eq_comap h M hM]
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.HeckePoisson
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeMellinGaussIntegrandUnitMul
section
open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.HeckeShift

theorem hmon_mul_unit {ζ : ℂ} (hζ : ‖ζ‖ = 1) (n : ℤ) (v : ℂ) :
    GlobalTheory.HeckeTheta.hmon n (ζ * v) = ζ ^ (-n) * GlobalTheory.HeckeTheta.hmon n v := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · have hc : starRingEnd ℂ ζ = ζ⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hζ]; simp
    rw [map_mul, mul_pow, hc, inv_pow, ← zpow_natCast, ← zpow_neg, Int.toNat_of_nonneg h]
  · rw [mul_pow, ← zpow_natCast ζ, Int.toNat_of_nonneg (by omega)]

theorem factor_shift (n : ℤ) (y : ℝ) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    GlobalTheory.HeckeTheta.hmon n ((Real.exp (y / 2) : ℂ) * (z * w)) *
                 Complex.exp ((-2 * Real.pi * ‖(Real.exp (y / 2) : ℂ) * (z * w)‖ ^ 2 : ℝ) : ℂ) =
      (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) *
        (GlobalTheory.HeckeTheta.hmon n ((Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w) *
          Complex.exp ((-2 * Real.pi * ‖(Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w‖ ^ 2 : ℝ) : ℂ)) := by
  have hn0 : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
  have hE : Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) = Real.exp (y / 2) * ‖z‖ := by
    rw [Real.log_pow, add_div, Real.exp_add]
    congr 1
    rw [show ((2 : ℕ) : ℝ) * Real.log ‖z‖ / 2 = Real.log ‖z‖ by push_cast; ring, Real.exp_log hn0]
  have hzc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hζ : ‖z / ((‖z‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn0.ne']
  have hv : (Real.exp (y / 2) : ℂ) * (z * w) =
      (z / ((‖z‖ : ℝ) : ℂ)) * ((Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w) := by
    rw [hE]; push_cast; field_simp
  rw [hv, hmon_mul_unit hζ, norm_mul, hζ, one_mul, mul_assoc]

theorem sum_ulog {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {I : Type} [Fintype I]
    (φ : I → K →+* ℂ) (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) : ∑ i, GlobalTheory.HeckeTheta.ulog φ u i = 0 := by
  have hbij : Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
    constructor
    · intro i j hij
      obtain ⟨k, _, hk⟩ := hφ (φ i)
      have hi := hk i (Or.inl rfl)
      rcases InfinitePlace.mk_eq_iff.1 hij with h | h
      · rw [hi, hk j (Or.inl h)]
      · rw [hi, hk j (Or.inr (by rw [← h]; ext x; simp [ComplexEmbedding.conjugate_coe_eq]))]
    · intro w
      obtain ⟨k, hk, _⟩ := hφ w.embedding
      refine ⟨k, ?_⟩
      rcases hk with h | h
      · simp only; rw [← h, InfinitePlace.mk_embedding]
      · simp only; rw [← InfinitePlace.mk_conjugate_eq (φ k), ← h, InfinitePlace.mk_embedding]
  have h0 := NumberField.Units.sum_mult_mul_log u
  rw [← (Equiv.ofBijective _ hbij).sum_comp] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : (InfinitePlace.mk (φ i)).mult = 2 :=
    InfinitePlace.mult_isComplex ⟨_, IsTotallyComplex.isComplex _⟩
  simp only [Equiv.ofBijective_apply, InfinitePlace.apply, hm, GlobalTheory.HeckeTheta.ulog, Real.log_pow]

end GlobalTheory.HeckeShift

theorem GlobalTheory.HeckeShift.term_unit_mul : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I]
    (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ) (u : (𝓞 K)ˣ) (α : K) (y : I → ℝ),
    GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (((u : 𝓞 K) : K) * α)) y =
      GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) *
        GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ α) (y + GlobalTheory.HeckeTheta.ulog φ u) := by
  intro K _ _ _ I _ φ hφ n s u α y
  have hsum : (∑ i, (y + GlobalTheory.HeckeTheta.ulog φ u) i) = ∑ i, y i := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, GlobalTheory.HeckeShift.sum_ulog φ hφ u, add_zero]
  have hu0 : ((u : 𝓞 K) : K) ≠ 0 := by
    intro h
    exact (Units.ne_zero u) (by exact_mod_cast h)
  unfold GlobalTheory.HeckeMellin.term
  rw [hsum, ← mul_assoc]
  congr 1
  unfold GlobalTheory.HeckeTheta.gauss GlobalTheory.HeckeStrip.wt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [GlobalTheory.HeckeTheta.dil, GlobalTheory.HeckeTheta.emb, GlobalTheory.HeckeTheta.ulog, Pi.add_apply, map_mul]
  exact GlobalTheory.HeckeShift.factor_shift (n i) (y i) ((map_ne_zero _).2 hu0) (φ i α)
end
end

