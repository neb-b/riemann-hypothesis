module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SacSuccAbove
public import ReciprocityTheory.SemistableReduction.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AeEvalCircleMapNeZero
section
open MeasureTheory Metric NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.MultiplicativeHeights
open scoped TensorProduct

namespace GlobalTheory

theorem ae_eval_circleMap_ne_zero : ∀ (m : ℕ) (f : MvPolynomial (Fin m) ℂ), f ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)),
      MvPolynomial.eval (fun i => circleMap 0 1 (x i)) f ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro f hf
    refine Filter.Eventually.of_forall fun x => ?_
    rw [MvPolynomial.eq_C_of_isEmpty f] at hf ⊢
    simpa using hf
  | succ m ih =>
    intro f hf
    set P := MvPolynomial.finSuccEquiv ℂ m f with hPdef
    have hP : P ≠ 0 := by
      intro h
      apply hf
      exact (MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hPdef, h, map_zero])
    obtain ⟨k, hk⟩ : ∃ k, P.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      exact hP (Polynomial.ext fun k => by simpa using h k)
    have h1 := ih _ hk
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have he : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ 0
    have hcont : Continuous fun (x : Fin (m + 1) → ℝ) =>
        MvPolynomial.eval (fun i => circleMap 0 1 (x i)) f :=
      (MvPolynomial.continuous_eval f).comp
        (continuous_pi fun i => (continuous_circleMap 0 1).comp (continuous_apply i))
    have hmeas : MeasurableSet {z : ℝ × (Fin m → ℝ) |
        MvPolynomial.eval (fun i => circleMap 0 1 (e.symm z i)) f ≠ 0} :=
      (hcont.measurable.comp e.symm.measurable) (measurableSet_singleton 0).compl
    have key : ∀ᵐ z ∂(volume : Measure (ℝ × (Fin m → ℝ))),
        MvPolynomial.eval (fun i => circleMap 0 1 (e.symm z i)) f ≠ 0 := by
      rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]
      rw [Measure.ae_ae_comm (p := fun y s =>
        MvPolynomial.eval (fun i => circleMap 0 1 (e.symm (y, s) i)) f ≠ 0) hmeas]
      filter_upwards [h1] with s hs
      set w : Fin m → ℂ := fun i => circleMap 0 1 (s i) with hw
      have hQ : Polynomial.map (MvPolynomial.eval w) P ≠ 0 := by
        intro h
        apply hs
        have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q k) h
        simpa [Polynomial.coeff_map] using this
      have hfin : ({y : ℂ | Polynomial.eval y (Polynomial.map (MvPolynomial.eval w) P) = 0}).Finite :=
        Polynomial.finite_setOfPred_isRoot hQ
      have hnull := (hfin.countable.preimage_circleMap 0 one_ne_zero).measure_zero
        (volume : Measure ℝ)
      rw [measure_eq_zero_iff_ae_notMem] at hnull
      filter_upwards [hnull] with y hy
      have hc : (fun i => circleMap 0 1 ((e.symm (y, s) : Fin (m + 1) → ℝ) i)) =
          Fin.cons (circleMap 0 1 y) w := by
        have : (e.symm (y, s) : Fin (m + 1) → ℝ) = Fin.cons y s := by
          simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
        rw [this]
        funext i
        cases i using Fin.cases <;> simp [hw]
      rw [hc, MvPolynomial.eval_eq_eval_mv_eval']
      exact hy
    have := he.quasiMeasurePreserving.ae key
    filter_upwards [this] with x hx
    simpa using hx

theorem ae_eval₂_ne_zero_pi_toSphere (K : Type) [Field K] [Countable K] (sg : K →+* ℂ)
    (D N : ℕ) :
    ∀ᵐ t ∂(MeasureTheory.Measure.pi fun _ : Fin D =>
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere),
      ∀ p : MvPolynomial (Fin D × Fin (N + 1)) K, p ≠ 0 →
        MvPolynomial.eval₂ sg (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) p ≠ 0 := by
  have := NPB.countable_mvPoly (σ := Fin D × Fin (N + 1)) (R := K)
  set μ : Measure (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) :=
    Measure.pi fun _ : Fin D => (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere with hμ
  have hgen : ∀ᵐ z ∂μ, ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → MvPolynomial.eval₂ sg (blockPoint z) p ≠ 0 := by
    rw [ae_all_iff]; intro a
    rw [ae_all_iff]; intro p
    by_cases hp : IsMultiHomogeneous a p ∧ p ≠ 0
    · have hm : IsMultiHomogeneous a (MvPolynomial.map sg p) :=
        fun s hs => hp.1 s (MvPolynomial.support_map_subset _ _ hs)
      have hm0 : MvPolynomial.map sg p ≠ 0 := fun h0 =>
        hp.2 (MvPolynomial.map_injective sg sg.injective (by rw [h0, map_zero]))
      filter_upwards [ae_toSphere D (N + 1) a _ hm0 hm] with z hz _ _
      rwa [MvPolynomial.eval_map] at hz
    · exact Filter.Eventually.of_forall fun z h1 h2 => absurd ⟨h1, h2⟩ hp
  rw [ae_all_iff]; intro p
  by_cases hp : p = 0
  · exact Filter.Eventually.of_forall fun z h => absurd hp h
  set φ : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → ℂ := fun t =>
    MvPolynomial.eval₂ sg (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) p with hφ
  have hφc : Continuous φ := by
    have : φ = fun t => MvPolynomial.eval (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) (MvPolynomial.map sg p) := by
      funext t; rw [MvPolynomial.eval_map]
    rw [this]
    exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun q => by fun_prop)
  set T : (Fin (N + 1 + D) → ℝ) → (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) :=
    fun θ t i => sphereRotation (θ (Fin.natAdd (N + 1) i)) (t i) with hT
  have hTc : Continuous fun x : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) × (Fin (N + 1 + D) → ℝ) =>
      T x.2 x.1 := by
    refine continuous_pi fun i => ?_
    exact (continuous_sphereRotation (E := EuclideanSpace ℂ (Fin (N + 1)))).comp
      (f := fun x : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) × (Fin (N + 1 + D) → ℝ) =>
        (x.2 (Fin.natAdd (N + 1) i), x.1 i)) (by fun_prop)
  have hTμ : ∀ θ, MeasurePreserving (T θ) μ μ := fun θ =>
    measurePreserving_pi _ _ fun i => measurePreserving_sphereRotation (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))) _
  set q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K :=
    MvPolynomial.rename (fun r : Fin D × Fin (N + 1) => (r.1.succ, r.2)) p with hq
  have hq0 : q ≠ 0 := by
    intro h
    apply hp
    refine MvPolynomial.rename_injective (fun r : Fin D × Fin (N + 1) => (r.1.succ, r.2)) ?_
      (by rw [map_zero]; exact h)
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simpa using h
  have h1 : ∀ᵐ t ∂μ, ∀ᵐ θ ∂(volume : Measure (Fin (N + 1 + D) → ℝ)), φ (T θ t) ≠ 0 := by
    filter_upwards [hgen] with t ht
    have hq' : NPB.psi sg (blockPoint t) q ≠ 0 := fun h0 =>
      hq0 (NPB.psi_injective sg (blockPoint t) ht (by rw [h0, map_zero]))
    filter_upwards [ae_eval_circleMap_ne_zero _ _ hq'] with θ hθ
    rw [NPB.eval_psi, hq, MvPolynomial.eval₂_rename] at hθ
    convert hθ using 1
    simp only [hφ]
    congr 1
  rw [Measure.ae_ae_comm (p := fun t θ => φ (T θ t) ≠ 0)
    ((hφc.comp hTc).measurable (measurableSet_singleton 0).compl)] at h1
  have : (ae (volume : Measure (Fin (N + 1 + D) → ℝ))).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨θ, hθ⟩ := h1.exists
  have h2 : ∀ᵐ t ∂μ, φ t ≠ 0 := by
    rw [← (hTμ θ).map_eq, ae_map_iff (p := fun x => φ x ≠ 0)
      (hTμ θ).measurable.aemeasurable
      (hφc.measurable (measurableSet_singleton 0).compl)]
    exact hθ
  filter_upwards [h2] with t ht _ using ht

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AemeasurableFinsumSection
section
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

namespace SectionSum

open MvPolynomial MeasureTheory

theorem sImg_indep_finite (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] (D N : ℕ)
    (j₀ : Fin (N + 1)) (x : Fin N → Ω) (hfg : (⊤ : IntermediateField K Ω).FG)
    (htr : Algebra.trdeg K Ω = D)
    (hJ : ∃ J : Fin D → Fin N, LinearIndependent Ω fun k => KaehlerDifferential.D K Ω (x (J k))) :
    Function.Injective (sHom (K := K) (D := D) j₀ x) ∧
      FiniteDimensional (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x)))
        (OmS Ω D N) := by
  have hfs := ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K Ω D N x hfg htr hJ
  let e : TVar D N ≃ TVar D N :=
    Equiv.prodCongr (Equiv.refl _) (Fin.cycleRange j₀).symm
  have key : (ReciprocityTheory.MultiplicativeHeights.sImage (D := D) x) = (sImg (D := D) j₀ x) ∘ e := by
    funext p
    obtain ⟨i, j⟩ := p
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_zero]
    · simp [e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_succ]
  have hrange : Set.range (ReciprocityTheory.MultiplicativeHeights.sImage (D := D) x) = Set.range (sImg (D := D) j₀ x) := by
    rw [key, EquivLike.range_comp]
  refine ⟨?_, ?_⟩
  · have hind : AlgebraicIndependent K (ReciprocityTheory.MultiplicativeHeights.sImage (D := D) x) := hfs.1
    rw [key] at hind
    have h2 := hind.comp _ e.symm.injective
    have h3 : AlgebraicIndependent K (sImg (D := D) j₀ x) := by
      simpa [Function.comp_def] using h2
    exact h3
  · have h2 := hfs.2
    rw [hrange] at h2
    exact h2

noncomputable def liftS {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    {j₀ : Fin (N + 1)} {x : Fin N → Ω} (h : Function.Injective (sHom (K := K) (D := D) j₀ x)) :
    FractionRing (MvPolynomial (TVar D N) K) →+* OmS Ω D N :=
  IsFractionRing.lift (A := MvPolynomial (TVar D N) K)
    (g := (sHom (K := K) (D := D) j₀ x).toRingHom) h

theorem liftS_algebraMap {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    {j₀ : Fin (N + 1)} {x : Fin N → Ω} (h : Function.Injective (sHom (K := K) (D := D) j₀ x))
    (q : MvPolynomial (TVar D N) K) :
    liftS h (algebraMap _ _ q) = sHom (K := K) (D := D) j₀ x q := by
  rw [liftS, IsFractionRing.lift_algebraMap]; rfl

theorem liftS_fieldRange {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    {j₀ : Fin (N + 1)} {x : Fin N → Ω} (h : Function.Injective (sHom (K := K) (D := D) j₀ x)) :
    (liftS h).fieldRange =
      (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x))).toSubfield := by
  rw [IntermediateField.adjoin_toSubfield, liftS, IsFractionRing.lift_fieldRange]
  apply le_antisymm
  · rw [Subfield.closure_le]
    rintro _ ⟨p, rfl⟩
    induction p using MvPolynomial.induction_on
    next a =>
      exact Subfield.subset_closure (Or.inl ⟨a, by simp [sHom]⟩)
    next p q hp hq =>
      rw [map_add (f := _)]
      exact add_mem hp hq
    next p i hp =>
      rw [map_mul]
      exact mul_mem hp (Subfield.subset_closure (Or.inr ⟨i, by simp [sHom]⟩))
  · rw [Subfield.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨i, rfl⟩)
    · exact Subfield.subset_closure ⟨MvPolynomial.C a, by simp [sHom]⟩
    · exact Subfield.subset_closure ⟨MvPolynomial.X i, by simp [sHom]⟩

theorem liftS_finite {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    {j₀ : Fin (N + 1)} {x : Fin N → Ω} (h : Function.Injective (sHom (K := K) (D := D) j₀ x))
    (hfin : FiniteDimensional (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x)))
        (OmS Ω D N)) :
    letI : Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) := (liftS h).toAlgebra;
    FiniteDimensional (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) := by
  letI : Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) := (liftS h).toAlgebra
  let i : FractionRing (MvPolynomial (TVar D N) K) ≃+*
      (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x))) :=
    (liftS h).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr (liftS_fieldRange h))
  have hc : (algebraMap (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x)))
      (OmS Ω D N)).comp i.toRingHom =
      (RingEquiv.refl (OmS Ω D N)).toRingHom.comp
        (algebraMap (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)) := by
    refine RingHom.ext fun y => ?_
    show ((i y : IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x))) : OmS Ω D N) =
      liftS h y
    rfl
  have hrk := Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) hc
  apply FiniteDimensional.of_finrank_pos
  rw [hrk]
  exact Module.finrank_pos

theorem exists_ae_cons {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (hμ : μ ≠ 0)
    (D : ℕ) (p : (Fin (D + 1) → α) → Prop)
    (hp : ∀ᵐ t ∂(Measure.pi fun _ : Fin (D + 1) => μ), p t) :
    ∃ t₀ : α, ∀ᵐ t ∂(Measure.pi fun _ : Fin D => μ), p (Fin.cons t₀ t) := by
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (D + 1) => μ) 0).symm
  have h1 := hm.quasiMeasurePreserving.ae hp
  have h2 := Measure.ae_ae_of_ae_prod h1
  haveI : (ae μ).NeBot := ae_neBot.2 hμ
  obtain ⟨t₀, ht₀⟩ := h2.exists
  refine ⟨t₀, ht₀.mono fun t ht => ?_⟩
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using ht

theorem sImg_rel {Ω : Type} [Field Ω] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → Ω) (i : Fin D) :
    sImg (D := D) j₀ x (i.succ, j₀) +
      ∑ k, sImg (D := D) j₀ x (i.succ, j₀.succAbove k) * algebraMap Ω (OmS Ω D N) (x k) = 0 := by
  have hC : ∀ a : Ω, algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (C a) =
      algebraMap Ω (OmS Ω D N) a := fun a => by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sImg, sac_self, sac_succAbove, Fin.succ_ne_zero, if_false,
    ↓reduceIte, map_neg, map_sum, map_mul, hC]
  exact neg_add_cancel _

theorem bijOn_restrict {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    (j₀ : Fin (N + 1)) (x : Fin N → Ω) (sg : K →+* ℂ) (pt : TVar D N → ℂ)
    (hext : ∀ Q : Ω →+* ℂ, Q ∈ PT (Ω := Ω) sg →
      (∀ i : Fin D, pt (i.succ, j₀) + ∑ k, pt (i.succ, j₀.succAbove k) * Q (x k) = 0) →
      ∃! P : OmS Ω D N →+* ℂ, (∀ a : Ω, P (algebraMap Ω (OmS Ω D N) a) = Q a) ∧
        ∀ p, P (sImg j₀ x p) = pt p) :
    Set.BijOn (fun P : OmS Ω D N →+* ℂ => P.comp (algebraMap Ω (OmS Ω D N)))
      {P | ∀ p : MvPolynomial (TVar D N) K, P (sHom (K := K) j₀ x p) = eval₂ sg pt p}
      {Q | Q ∈ PT (Ω := Ω) sg ∧
        ∀ i : Fin D, pt (i.succ, j₀) + ∑ k, pt (i.succ, j₀.succAbove k) * Q (x k) = 0} := by
  have hX : ∀ P : OmS Ω D N →+* ℂ,
      (∀ p : MvPolynomial (TVar D N) K, P (sHom (K := K) j₀ x p) = eval₂ sg pt p) →
      ∀ p, P (sImg j₀ x p) = pt p := fun P hP p => by
    simpa [sHom] using hP (X p)
  have hmaps : Set.MapsTo (fun P : OmS Ω D N →+* ℂ => P.comp (algebraMap Ω (OmS Ω D N)))
      {P | ∀ p : MvPolynomial (TVar D N) K, P (sHom (K := K) j₀ x p) = eval₂ sg pt p}
      {Q | Q ∈ PT (Ω := Ω) sg ∧
        ∀ i : Fin D, pt (i.succ, j₀) + ∑ k, pt (i.succ, j₀.succAbove k) * Q (x k) = 0} := by
    intro P hP
    refine ⟨?_, fun i => ?_⟩
    · ext a
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply K Ω (OmS Ω D N)]
      have := hP (C a)
      rwa [show sHom (K := K) (D := D) j₀ x (C a) = algebraMap K _ a by
        rw [← MvPolynomial.algebraMap_eq]; exact (sHom (K := K) (D := D) j₀ x).commutes a,
        eval₂_C] at this
    · have := congrArg P (sImg_rel (D := D) j₀ x i)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_mul, hX P hP] using this
  refine ⟨hmaps, ?_, ?_⟩
  · intro P₁ h₁ P₂ h₂ he
    have hm := hmaps h₁
    refine (hext _ hm.1 hm.2).unique ⟨fun a => rfl, hX _ h₁⟩ ⟨fun a => ?_, hX _ h₂⟩
    exact (DFunLike.congr_fun he a).symm
  · rintro Q ⟨hQ, hrel⟩
    obtain ⟨P, ⟨hP1, hP2⟩, -⟩ := hext Q hQ hrel
    refine ⟨P, fun p => ?_, RingHom.ext hP1⟩
    have : P.comp (sHom (K := K) (D := D) j₀ x).toRingHom = eval₂Hom sg pt := by
      apply MvPolynomial.ringHom_ext
      · intro a
        have h1 : sHom (K := K) (D := D) j₀ x (C a) = algebraMap K _ a := by
          rw [← MvPolynomial.algebraMap_eq]; exact (sHom (K := K) (D := D) j₀ x).commutes a
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1,
          coe_eval₂Hom, eval₂_C]
        rw [IsScalarTower.algebraMap_apply K Ω (OmS Ω D N), hP1]
        exact DFunLike.congr_fun hQ a
      · intro q
        simp [sHom, hP2]
    exact DFunLike.congr_fun this p

end SectionSum


open SectionSum MeasureTheory in
theorem aemeasurable_finsum_section :
    (∀ (K : Type) [Field K] [Countable K] (sg : K →+* ℂ) (D N : ℕ), ∀ᵐ t ∂(MeasureTheory.Measure.pi fun _ : Fin D => (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere), ∀ p : MvPolynomial (Fin D × Fin (N + 1)) K, p ≠ 0 → MvPolynomial.eval₂ sg (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) p ≠ 0) → (∀ (K : Type) [Field K] [CharZero K] (σ : Type) [Fintype σ] (L : Type) [Field L] [Algebra (FractionRing (MvPolynomial σ K)) L] [FiniteDimensional (FractionRing (MvPolynomial σ K)) L] (sg : K →+* ℂ) (m : ℕ) (b : Fin m → L) (Nf : (Fin m → ℂ) → ℝ), Measurable Nf → ∃ Φ : (σ → ℂ) → ℝ, Measurable Φ ∧ ∀ t : σ → ℂ, (∀ p : MvPolynomial σ K, p ≠ 0 → MvPolynomial.eval₂ sg t p ≠ 0) → Φ t = ∑ᶠ P ∈ {P : L →+* ℂ | ∀ p : MvPolynomial σ K, P (algebraMap (FractionRing (MvPolynomial σ K)) L (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p)) = MvPolynomial.eval₂ sg t p}, Nf (fun i => P (b i))) → (∀ (K Ω L : Type) [Field K] [Field Ω] [Algebra K Ω] [Field L] [Algebra K L] (D N : ℕ) (j₀ : Fin (N + 1)) (x : Fin N → Ω) (τ : TVar D N → L) (φ : Ω →ₐ[K] L), Algebra.trdeg K Ω = D → AlgebraicIndependent K τ → (∀ i : Fin D, τ (i.succ, j₀) + ∑ k, τ (i.succ, j₀.succAbove k) * φ (x k) = 0) → ∃! P : OmS Ω D N →+* L, (∀ a : Ω, P (algebraMap Ω (OmS Ω D N) a) = φ a) ∧ ∀ p, P (sImg j₀ x p) = τ p) → ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A), ∀ c : ι, (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → d.w (d.jc c) c ≠ 0 → (∃ J : Fin d.D → Fin d.N, LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))) → ∀ (sg : K →+* ℂ) (m : ℕ) (a : Fin m → Ω c) (Nf : (Fin m → ℂ) → ℝ) (h : (Ω c →+* ℂ) → ℝ), Measurable Nf → (∀ P ∈ PT (Ω := Ω c) sg, h P = Nf (fun i => P (a i))) → AEMeasurable (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 => ∑ᶠ P ∈ d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j), h P) d.sphMeasure := by
  intro hgen hfib hext K _ _ ι _ Ω _ _ WT _ A _ _ _ _ 𝒜 d c hfg htr hw hJ sg m a Nf h hNf hh
  obtain ⟨hinj, hfin⟩ := sImg_indep_finite K (Ω c) d.D d.N (d.jc c) (d.x c) hfg htr hJ
  letI : Algebra (FractionRing (MvPolynomial (TVar d.D d.N) K)) (OmS (Ω c) d.D d.N) :=
    (liftS hinj).toAlgebra
  haveI := liftS_finite hinj hfin
  obtain ⟨Φ, hΦm, hΦ⟩ := hfib K (TVar d.D d.N) (OmS (Ω c) d.D d.N) sg m
    (fun i => algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a i)) Nf hNf
  haveI : Countable K := Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.toEquiv.symm
  obtain ⟨t₀, ht₀⟩ := exists_ae_cons _ (Measure.toSphere_ne_zero _) d.D _
    (hgen K sg (d.D + 1) d.N)
  let F : (Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1) →
      TVar d.D d.N → ℂ := fun t q =>
    ((Fin.cons t₀ t : Fin (d.D + 1) → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1) q.1 :
      EuclideanSpace ℂ (Fin (d.N + 1))) q.2
  have hF : Measurable F := by
    refine Measurable.of_eval fun q => ?_
    obtain ⟨i, j⟩ := q
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [F, Fin.cons_zero]
      exact measurable_const
    · simp only [F, Fin.cons_succ]
      apply Continuous.measurable
      fun_prop
  refine ⟨fun t => Φ (F t), hΦm.comp hF, ?_⟩
  refine ht₀.mono fun t ht => ?_
  have hb := bijOn_restrict (K := K) (d.jc c) (d.x c) sg (F t) (fun Q hQ hrel => by
    letI : Algebra K ℂ := sg.toAlgebra
    let φ : Ω c →ₐ[K] ℂ := { Q with commutes' := fun r => DFunLike.congr_fun hQ r }
    refine hext K (Ω c) ℂ d.D d.N (d.jc c) (d.x c) (F t) φ htr ?_ hrel
    rw [algebraicIndependent_iff]
    intro p hp
    by_contra h0
    exact ht p h0 hp)
  have hST : d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j) =
      {Q | Q ∈ PT (Ω := Ω c) sg ∧ ∀ i : Fin d.D, F t (i.succ, d.jc c) +
        ∑ k, F t (i.succ, (d.jc c).succAbove k) * Q (d.x c k) = 0} := by
    ext Q
    simp only [Data.ST, Set.mem_setOf_eq, F, Fin.cons_succ]
    refine and_congr_right fun _ => forall_congr' fun i => ?_
    rw [Fin.sum_univ_succAbove _ (d.jc c), ratio_self hw, map_one, mul_one]
    rfl
  show _ = Φ (F t)
  beta_reduce
  rw [hΦ (F t) ht, hST]
  symm
  have hset : {P : OmS (Ω c) d.D d.N →+* ℂ | ∀ p : MvPolynomial (TVar d.D d.N) K,
      P (algebraMap (FractionRing (MvPolynomial (TVar d.D d.N) K)) (OmS (Ω c) d.D d.N)
        (algebraMap (MvPolynomial (TVar d.D d.N) K) (FractionRing (MvPolynomial (TVar d.D d.N) K)) p))
        = MvPolynomial.eval₂ sg (F t) p} =
      {P | ∀ p : MvPolynomial (TVar d.D d.N) K,
        P (sHom (K := K) (d.jc c) (d.x c) p) = MvPolynomial.eval₂ sg (F t) p} := by
    ext P
    refine forall_congr' fun p => ?_
    rw [← liftS_algebraMap hinj p]
    rfl
  rw [hset]
  refine finsum_mem_eq_of_bijOn _ hb fun P hP => ?_
  rw [hh _ (hb.mapsTo hP).1]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.DenseMvPolynomialEvalNeZero
section
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

theorem dense_mvPolynomial_eval_ne_zero {D : ℕ} (q : MvPolynomial (Fin D) ℂ) (hq : q ≠ 0) :
    Dense {z : Fin D → ℂ | MvPolynomial.eval z q ≠ 0} := by
  rw [Metric.dense_iff]
  intro z₀ r hr
  by_contra hne
  apply hq
  refine MvPolynomial.funext_set (fun i => Metric.ball (z₀ i) r)
    (fun i => infinite_of_mem_nhds (z₀ i) (Metric.ball_mem_nhds _ hr)) (fun x hx => ?_)
  rw [map_zero]
  by_contra hx0
  apply hne
  refine ⟨x, ?_, hx0⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  exact fun i => hx i (Set.mem_univ i)

theorem exists_algIndep_tuple_near :
    ∀ (K : Type) [Field K] [Countable K] (sg : K →+* ℂ) (D : ℕ) (z₀ : Fin D → ℂ) (ε : ℝ), 0 < ε → ∃ z : Fin D → ℂ, (∀ i, ‖z i - z₀ i‖ < ε) ∧ ∀ p : MvPolynomial (Fin D) K, p ≠ 0 → MvPolynomial.eval₂ sg z p ≠ 0 := by
  intro K _ _ sg D z₀ ε hε
  let S : {p : MvPolynomial (Fin D) K // p ≠ 0} → Set (Fin D → ℂ) :=
    fun p => {z | MvPolynomial.eval z (MvPolynomial.map sg p.1) ≠ 0}
  have : Countable (MvPolynomial (Fin D) K) := by
    refine Function.Surjective.countable (f := fun l : List ((Fin D →₀ ℕ) × K) =>
      (l.map fun mc => MvPolynomial.monomial mc.1 mc.2).sum) fun p => ?_
    refine ⟨p.support.toList.map fun m => (m, AddMonoidAlgebra.coeff p m), ?_⟩
    simp only [List.map_map]
    rw [Finset.sum_map_toList]
    exact p.as_sum.symm
  have hS : Dense (⋂ p, S p) := by
    apply dense_iInter_of_isOpen
    · intro p
      exact isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const
    · intro p
      refine dense_mvPolynomial_eval_ne_zero _ fun h0 => p.2 ?_
      exact MvPolynomial.map_injective sg sg.injective (h0.trans (map_zero _).symm)
  obtain ⟨z, hzS, hz⟩ := hS.exists_mem_open (Metric.isOpen_ball (x := z₀)) (Metric.nonempty_ball.mpr hε)
  refine ⟨z, ?_, fun p hp => ?_⟩
  · rw [Metric.mem_ball, dist_pi_lt_iff hε] at hz
    intro i
    rw [← dist_eq_norm]
    exact hz i
  · rw [← MvPolynomial.eval_map]
    exact Set.mem_iInter.mp hzS ⟨p, hp⟩

end GlobalTheory
end

