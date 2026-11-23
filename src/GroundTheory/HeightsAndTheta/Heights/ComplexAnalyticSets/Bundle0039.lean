module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0003
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermMinimalPolynomialDivides
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

namespace GermMinimalPolynomialDivides

def germsAlong {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) : Subring (Germ (𝓝[X] x) ℂ) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f x ∧ (f : Germ (𝓝[X] x) ℂ) = φ}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  one_mem' := ⟨fun _ => 1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  zero_mem' := ⟨fun _ => 0, analyticAt_const, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

def analyticAtRing {ι : Type} [Fintype ι] (w : ι → ℂ) : Subring ((ι → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f w}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := (analyticAt_const : AnalyticAt ℂ (fun _ : ι → ℂ => (1 : ℂ)) w)
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := (analyticAt_const : AnalyticAt ℂ (fun _ : ι → ℂ => (0 : ℂ)) w)
  neg_mem' := fun hf => hf.neg

def germOf {ι : Type} [Fintype ι] (w : ι → ℂ) : analyticAtRing w →+* holGerms w :=
  ((Germ.coeRingHom (𝓝 w)).comp (analyticAtRing w).subtype).codRestrict (holGerms w)
    fun f => ⟨f.1, f.2, rfl⟩

theorem germOf_surjective {ι : Type} [Fintype ι] (w : ι → ℂ) : Function.Surjective (germOf w) := by
  intro φ
  obtain ⟨f, hf, hφ⟩ := φ.2
  exact ⟨⟨f, hf⟩, Subtype.ext hφ⟩

def germRep {ι : Type} [Fintype ι] (w : ι → ℂ) : holGerms w → analyticAtRing w :=
  Function.surjInv (germOf_surjective w)

theorem germOf_germRep {ι : Type} [Fintype ι] (w : ι → ℂ) (φ : holGerms w) : germOf w (germRep w φ) = φ :=
  Function.surjInv_eq (germOf_surjective w) φ

theorem germOf_eq_zero {ι : Type} [Fintype ι] (w : ι → ℂ) (f : analyticAtRing w) :
    germOf w f = 0 ↔ ∀ᶠ y in 𝓝 w, f.1 y = 0 := by
  rw [← Subtype.coe_inj]
  exact Germ.coe_eq

def alongOf {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) : analyticAtRing x →+* germsAlong X x :=
  ((Germ.coeRingHom (𝓝[X] x)).comp (analyticAtRing x).subtype).codRestrict (germsAlong X x)
    fun f => ⟨f.1, f.2, rfl⟩

def germCompHom {α β : Type} {l : Filter β} {l' : Filter α} (g : α → β) (hg : Tendsto g l' l) :
    Germ l ℂ →+* Germ l' ℂ where
  toFun φ := φ.compTendsto g hg
  map_one' := rfl
  map_mul' φ ψ := Germ.inductionOn₂ φ ψ fun _ _ => rfl
  map_zero' := rfl
  map_add' φ ψ := Germ.inductionOn₂ φ ψ fun _ _ => rfl

theorem tendsto_nhdsWithin_linear {σ : Type} [Fintype σ] {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (X : Set (σ → ℂ)) (x : σ → ℂ) : Tendsto A (𝓝[X] x) (𝓝 (A x)) :=
  (A.continuous.tendsto x).mono_left nhdsWithin_le_nhds

def alongPull {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) :
    holGerms (A x) →+* germsAlong X x :=
  ((germCompHom A (tendsto_nhdsWithin_linear A X x)).comp (holGerms (A x)).subtype).codRestrict _ fun φ => by
    obtain ⟨f, hf, hφ⟩ := φ.2
    refine ⟨f ∘ A, hf.comp (A.analyticAt x), ?_⟩
    change _ = (φ.1 : Germ (𝓝 (A x)) ℂ).compTendsto A (tendsto_nhdsWithin_linear A X x)
    rw [← hφ]
    rfl

def preLinear {σ : Type} [Fintype σ] (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) :
    analyticAtRing (A x) →+* ((σ → ℂ) → ℂ) :=
  (RingHom.pi fun z => Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)).comp (analyticAtRing (A x)).subtype

theorem eventually_of_germ_eq {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {x : σ → ℂ} {f g : (σ → ℂ) → ℂ}
    (h : (f : Germ (𝓝[X] x) ℂ) = g) : ∀ᶠ z in 𝓝 x, z ∈ X → f z = g z :=
  eventually_nhdsWithin_iff.1 (Germ.coe_eq.1 h)

theorem coe_eval₂_map {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (P : (analyticAtRing (A x))[X]) (v : analyticAtRing x) :
    ((eval₂ (alongPull X x A) (alongOf X x v) (P.map (germOf (A x))) : germsAlong X x) : Germ (𝓝[X] x) ℂ) =
      ((eval₂ (preLinear x A) v.1 P : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) := by
  change (germsAlong X x).subtype _ = Germ.coeRingHom _ _
  rw [eval₂_map, hom_eval₂, hom_eval₂]
  rfl

theorem eval₂_monic_apply {σ : Type} [Fintype σ] (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (g : (σ → ℂ) → ℂ) {M : ℕ} (b : Fin M → analyticAtRing (A x)) (z : σ → ℂ) :
    eval₂ (preLinear x A) g (Polynomial.X ^ M + ∑ j, C (b j) * Polynomial.X ^ (j : ℕ)) z =
      g z ^ M + ∑ j, (b j).1 (A z) * g z ^ (j : ℕ) := by
  simp [eval₂_finsetSum, Finset.sum_apply, preLinear]

theorem proof (hF : FiniteFibreGermIntegral.Statement) (hH : HolGermsIntegrallyClosed.Statement) :
    GermMinimalPolynomialDivides.Statement := by
  intro σ _ X w d A hXan hirr hiso hinj g hg
  classical
  obtain ⟨hdom, hic⟩ := hH d (A w)

  have : (𝓝[X] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hirr.1)
  have germ_zero : ∀ f : (σ → ℂ) → ℂ, (∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) →
      (f : Germ (𝓝[X] w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) :=
    fun f h => Germ.coe_eq.2 (eventually_nhdsWithin_iff.2 h)
  have : NoZeroDivisors (germsAlong X w) := by
    refine ⟨fun {a b} hab => ?_⟩
    obtain ⟨f, hf, hfa⟩ := a.2
    obtain ⟨g, hg, hgb⟩ := b.2
    have h0 : ((f * g : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) := by
      rw [Germ.coe_mul, hfa, hgb]
      exact congrArg Subtype.val hab
    rcases hirr.2 f g hf hg ((eventually_of_germ_eq h0).mono fun z hz hzX => by simpa using hz hzX) with h | h
    · exact Or.inl (Subtype.ext (hfa ▸ germ_zero f h))
    · exact Or.inr (Subtype.ext (hgb ▸ germ_zero g h))
  have : IsDomain (germsAlong X w) := NoZeroDivisors.to_isDomain _

  let _ : Algebra (holGerms (A w)) (germsAlong X w) := (alongPull X w A).toAlgebra
  have hα : Function.Injective (algebraMap (holGerms (A w)) (germsAlong X w)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro φ hφ
    obtain ⟨h, hh, hφh⟩ := φ.2
    have h1 : ((h ∘ A : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) := by
      have h2 := congrArg Subtype.val hφ
      change (φ.1 : Germ (𝓝 (A w)) ℂ).compTendsto A (tendsto_nhdsWithin_linear A X w) =
        (0 : Germ (𝓝[X] w) ℂ) at h2
      rw [← hφh] at h2
      exact h2
    have h3 := hinj h hh ((eventually_of_germ_eq h1).mono fun z hz hzX => hz hzX)
    apply Subtype.ext
    rw [← hφh]
    exact Germ.coe_eq.2 h3
  have : FaithfulSMul (holGerms (A w)) (germsAlong X w) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hα

  set s : germsAlong X w := alongOf X w ⟨g, hg⟩ with hs
  have aeval_zero : ∀ P : (analyticAtRing (A w))[X],
      (∀ᶠ z in 𝓝 w, z ∈ X → eval₂ (preLinear w A) g P z = 0) → aeval s (P.map (germOf (A w))) = 0 := by
    intro P hP
    rw [aeval_def]
    apply Subtype.ext
    change ((eval₂ (alongPull X w A) (alongOf X w ⟨g, hg⟩) (P.map (germOf (A w))) : germsAlong X w) :
      Germ (𝓝[X] w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ)
    rw [coe_eval₂_map]
    exact germ_zero _ hP

  have hint : IsIntegral (holGerms (A w)) s := by
    obtain ⟨M, b, hb, hev⟩ := hF σ X w d A hXan hiso g hg
    let bt : Fin M → analyticAtRing (A w) := fun j => ⟨b j, hb j⟩
    refine ⟨(Polynomial.X ^ M + ∑ j, C (bt j) * Polynomial.X ^ (j : ℕ)).map (germOf (A w)),
      (monic_X_pow_add (degree_sum_fin_lt _)).map _, ?_⟩
    rw [← aeval_def]
    exact aeval_zero _ (hev.mono fun z hz hzX => by rw [eval₂_monic_apply]; exact hz hzX)

  set m := minpoly (holGerms (A w)) s with hm
  have hmon : m.Monic := minpoly.monic hint
  let bt : Fin m.natDegree → analyticAtRing (A w) := fun j => germRep (A w) (m.coeff j)
  let P : (analyticAtRing (A w))[X] := Polynomial.X ^ m.natDegree + ∑ j, C (bt j) * Polynomial.X ^ (j : ℕ)
  have hPm : P.map (germOf (A w)) = m := by
    have h1 := hmon.as_sum
    rw [← Fin.sum_univ_eq_sum_range (fun i => C (m.coeff i) * Polynomial.X ^ i)] at h1
    conv_rhs => rw [h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, bt, Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C, germOf_germRep]
  have hPz : ∀ z, eval₂ (preLinear w A) g P z = g z ^ m.natDegree + ∑ j, (bt j).1 (A z) * g z ^ (j : ℕ) :=
    fun z => eval₂_monic_apply w A g bt z
  refine ⟨m.natDegree, fun j => (bt j).1, fun j => (bt j).2, ?_, ?_⟩
  ·
    have h0 : aeval s m = 0 := minpoly.aeval _ _
    rw [← hPm, aeval_def] at h0
    have h1 := congrArg Subtype.val h0
    change ((eval₂ (alongPull X w A) (alongOf X w ⟨g, hg⟩) (P.map (germOf (A w))) : germsAlong X w) :
      Germ (𝓝[X] w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) at h1
    rw [coe_eval₂_map] at h1
    exact (eventually_of_germ_eq h1).mono fun z hz hzX => (hPz z).symm.trans (hz hzX)
  ·
    intro E hE hEz
    have hcoeffs : (↑E.coeffs : Set ((Fin d → ℂ) → ℂ)) ⊆ analyticAtRing (A w) := by
      intro c hc
      obtain ⟨k, -, rfl⟩ := mem_coeffs_iff.1 hc
      exact hE k
    let Et := E.toSubring (analyticAtRing (A w)) hcoeffs
    have hEval : ∀ z, eval₂ (preLinear w A) g Et z = E.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (g z) := by
      intro z
      have hmap : Et.map (analyticAtRing (A w)).subtype = E := map_toSubring _ _ _
      have h1 : eval₂ (preLinear w A) g Et =
          eval₂ (RingHom.pi fun z => Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) g E := by
        rw [← hmap, eval₂_map]
        rfl
      rw [h1]
      exact hom_eval₂ E _ (Pi.evalRingHom (fun _ : σ → ℂ => ℂ) z) g
    have hEt0 : aeval s (Et.map (germOf (A w))) = 0 :=
      aeval_zero Et (hEz.mono fun z hz hzX => (hEval z).trans (hz hzX))
    obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd hint hEt0
    obtain ⟨Q, rfl⟩ := Polynomial.map_surjective _ (germOf_surjective (A w)) q
    have hDz : (Et - P * Q).map (germOf (A w)) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, hPm, hq, sub_self]
    have hDev : ∀ᶠ y in 𝓝 (A w), ∀ k ∈ (Et - P * Q).support, ((Et - P * Q).coeff k).1 y = 0 := by
      rw [eventually_all_finset]
      intro k _
      have : germOf (A w) ((Et - P * Q).coeff k) = 0 := by rw [← coeff_map, hDz, coeff_zero]
      exact (germOf_eq_zero _ _).1 this
    filter_upwards [hDev] with y hy
    let ev : analyticAtRing (A w) →+* ℂ :=
      (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y).comp (analyticAtRing (A w)).subtype
    have hD0 : (Et - P * Q).map ev = 0 := by
      ext k
      rw [coeff_map, coeff_zero]
      by_cases hk : k ∈ (Et - P * Q).support
      · exact hy k hk
      · rw [notMem_support_iff.1 hk, map_zero]
    have hE' : Et.map ev = E.map (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y) := by
      rw [← map_toSubring E (analyticAtRing (A w)) hcoeffs, Polynomial.map_map]
    have hP' : P.map ev =
        Polynomial.X ^ m.natDegree + ∑ j, C ((bt j).1 y) * Polynomial.X ^ (j : ℕ) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [P, ev, Polynomial.map_sum]
    refine ⟨Q.map ev, ?_⟩
    rw [← hE', ← hP', ← Polynomial.map_mul, ← sub_eq_zero, ← Polynomial.map_sub]
    exact hD0

end GermMinimalPolynomialDivides

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGraphAreaHolomorphic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

namespace GraphAreaHolomorphic

theorem norm_sq_sumElim {𝕜 : Type*} [RCLike 𝕜] {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (e : ν ≃ ι ⊕ κ) (a : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 κ) :
    ‖(WithLp.toLp 2 (fun j => Sum.elim (fun i => a i) (fun i => b i) (e j)) : EuclideanSpace 𝕜 ν)‖ ^ 2 =
      ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_equiv e _ (fun s => ‖Sum.elim (fun i => a i) (fun i => b i) s‖ ^ 2) (fun j => rfl),
    Fintype.sum_sum_type]
  all_goals rfl

theorem norm_sq_sumElim' {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 κ) :
    ‖(WithLp.toLp 2 (Sum.elim (fun i => a i) (fun i => b i)) : EuclideanSpace 𝕜 (ι ⊕ κ))‖ ^ 2 =
      ‖a‖ ^ 2 + ‖b‖ ^ 2 :=
  norm_sq_sumElim (Equiv.refl _) a b

theorem adjoint_comp_self_of_norm {E H K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
    (T : E →ₗ[ℝ] K) (L : E →ₗ[ℝ] H) (h : ∀ v, ‖T v‖ ^ 2 = ‖v‖ ^ 2 + ‖L v‖ ^ 2) :
    LinearMap.adjoint T ∘ₗ T = 1 + LinearMap.adjoint L ∘ₗ L := by
  refine LinearMap.ext fun v => ext_inner_right ℝ fun w => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Module.End.one_apply, inner_add_left,
    LinearMap.adjoint_inner_left]
  simp only [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add (f := _)]
  have h1 := h (v + w)
  have h2 := h v
  have h3 := h w
  simp only [sq] at h1 h2 h3
  linarith

theorem det_one_add_comp {E E' H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (φ : E ≃ₗᵢ[ℝ] E') (L : E' →ₗ[ℝ] H) :
    LinearMap.det (1 + LinearMap.adjoint (L ∘ₗ φ.toLinearMap) ∘ₗ (L ∘ₗ φ.toLinearMap)) =
      LinearMap.det (1 + LinearMap.adjoint L ∘ₗ L) := by
  rw [← LinearMap.det_conj (1 + LinearMap.adjoint L ∘ₗ L) φ.symm.toLinearEquiv]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [LinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]

theorem differentiableAt_graphPt_real {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hF : DifferentiableAt ℝ F x) : DifferentiableAt ℝ (graphPt e F) x := by
  rw [differentiableAt_piLp]
  intro j
  show DifferentiableAt ℝ (fun y => Sum.elim (fun i => y i) (fun i => F y i) (e j)) x
  rcases e j with i | i
  · exact (differentiableAt_piLp 2).1 differentiableAt_id i
  · exact (differentiableAt_piLp 2).1 hF i

theorem hasFDerivAt_graphPt_apply {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    {L : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin m)} (hF : HasFDerivAt F L x)
    {T : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n)} (hG : HasFDerivAt (graphPt e F) T x)
    (v : EuclideanSpace ℂ (Fin d)) :
    T v = WithLp.toLp 2 (fun j => Sum.elim (fun i => v i) (fun i => L v i) (e j)) := by
  ext j
  obtain ⟨s, rfl⟩ := e.symm.surjective j
  have hj := (hasFDerivWithinAt_piLp 2).1 (hasFDerivWithinAt_univ.2 hG) (e.symm s)
  rw [hasFDerivWithinAt_univ] at hj
  rcases s with i | i
  · have h' : HasFDerivAt (fun y : EuclideanSpace ℂ (Fin d) => graphPt e F y (e.symm (Sum.inl i)))
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℂ) i) x := by
      simpa [graphPt] using PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x i
    simpa using congrArg (fun M => M v) (hj.unique h')
  · have hfun : (fun y : EuclideanSpace ℂ (Fin d) => graphPt e F y (e.symm (Sum.inr i))) =
        (fun f : EuclideanSpace ℂ (Fin m) => f i) ∘ F := by
      funext y
      simp [graphPt]
    have h' : HasFDerivAt (fun y : EuclideanSpace ℂ (Fin d) => graphPt e F y (e.symm (Sum.inr i)))
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℂ) i).comp L) x := by
      rw [hfun]
      exact (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (F x) i).comp x hF
    simpa using congrArg (fun M => M v) (hj.unique h')

theorem exists_graph_isometry {d m n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : Fin n ≃ Fin d ⊕ Fin m) (φ : EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (φm : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) :
    ∃ ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℝ (ι ⊕ κ), Isometry ψ ∧
      ∀ (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)) x,
        ψ (graphPt e F x) = WithLp.toLp 2 (Sum.elim (fun i => φ x i) (fun i => φm (F x) i)) := by
  let πd : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin d) :=
    { toFun := fun z => WithLp.toLp 2 fun k => z (e.symm (Sum.inl k))
      map_add' := fun z w => by ext; simp
      map_smul' := fun c z => by ext; simp }
  let πm : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) :=
    { toFun := fun z => WithLp.toLp 2 fun k => z (e.symm (Sum.inr k))
      map_add' := fun z w => by ext; simp
      map_smul' := fun c z => by ext; simp }
  have hz : ∀ z : EuclideanSpace ℂ (Fin n),
      z = WithLp.toLp 2 (fun j => Sum.elim (fun i => πd z i) (fun i => πm z i) (e j)) := by
    intro z
    ext j
    obtain ⟨s, rfl⟩ := e.symm.surjective j
    rcases s with i | i <;> simp [πd, πm]
  refine ⟨fun z => WithLp.toLp 2 (Sum.elim (fun i => φ (πd z) i) (fun i => φm (πm z) i)), ?_, ?_⟩
  · refine Isometry.of_dist_eq fun z w => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : (WithLp.toLp 2 (Sum.elim (fun i => φ (πd z) i) (fun i => φm (πm z) i)) :
        EuclideanSpace ℝ (ι ⊕ κ)) - WithLp.toLp 2 (Sum.elim (fun i => φ (πd w) i) (fun i => φm (πm w) i)) =
        WithLp.toLp 2 (Sum.elim (fun i => φ (πd (z - w)) i) (fun i => φm (πm (z - w)) i)) := by
      ext s
      rcases s with i | i <;> simp [map_sub]
    rw [hsub]
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    have hn := norm_sq_sumElim e (πd (z - w)) (πm (z - w))
    rw [← hz (z - w)] at hn
    rw [norm_sq_sumElim', φ.norm_map, φm.norm_map, hn]
  · intro F x
    have h1 : πd (graphPt e F x) = x := by ext k; simp [πd, graphPt]
    have h2 : πm (graphPt e F x) = F x := by ext k; simp [πm, graphPt]
    simp only [h1, h2]

end GraphAreaHolomorphic

open GraphAreaHolomorphic in
theorem GraphAreaHolomorphic.proof (h : AreaGraph.Statement) : GraphAreaHolomorphic.Statement := by
  intro d m n e Ω F hΩ hF A hAΩ hA

  have hFcC : ContDiffOn ℂ 1 F Ω := by
    refine contDiffOn_piLp' 2 fun j x hx => ContDiffAt.contDiffWithinAt ?_
    have hU : IsOpen ((WithLp.toLp 2 : (Fin d → ℂ) → EuclideanSpace ℂ (Fin d)) ⁻¹' Ω) :=
      hΩ.preimage (PiLp.continuous_toLp 2 _)
    have hg : DifferentiableOn ℂ (fun w : Fin d → ℂ => F (WithLp.toLp 2 w) j)
        ((WithLp.toLp 2 : (Fin d → ℂ) → EuclideanSpace ℂ (Fin d)) ⁻¹' Ω) := fun w hw =>
      (((differentiableAt_piLp 2).1 (hF.differentiableAt (hΩ.mem_nhds hw)) j).comp w
        (PiLp.hasFDerivAt_toLp (𝕜 := ℂ) 2 w).differentiableAt).differentiableWithinAt
    exact ((ReciprocityTheory.AnForm.Osgood.osgood d _ _ hU hg (WithLp.ofLp x) hx).contDiffAt).comp x
      PiLp.contDiff_ofLp.contDiffAt
  have hFc : ContDiffOn ℝ 1 F Ω := hFcC.restrict_scalars ℝ
  have hd : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hm : finrank ℝ (EuclideanSpace ℂ (Fin m)) = 2 * m := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  obtain ⟨φ⟩ : Nonempty (EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * d))) :=
    ⟨((stdOrthonormalBasis ℝ _).reindex (finCongr hd)).repr⟩
  obtain ⟨φm⟩ : Nonempty (EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * m))) :=
    ⟨((stdOrthonormalBasis ℝ _).reindex (finCongr hm)).repr⟩
  obtain ⟨ψ, hψ, hψG⟩ := exists_graph_isometry e φ φm
  obtain ⟨F', hF'⟩ : ∃ F' : EuclideanSpace ℝ (Fin (2 * d)) → EuclideanSpace ℝ (Fin (2 * m)),
      F' = fun y => φm (F (φ.symm y)) := ⟨_, rfl⟩
  have hU : IsOpen (φ '' Ω) := φ.toHomeomorph.isOpenMap Ω hΩ
  have hA' : MeasurableSet (φ '' A) := φ.toHomeomorph.measurableEmbedding.measurableSet_image.2 hA
  have hF'c : ContDiffOn ℝ 1 F' (φ '' Ω) := by
    rw [hF']
    exact φm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (hFc.comp φ.symm.toContinuousLinearEquiv.contDiff.contDiffOn
        (by rintro _ ⟨y, hy, rfl⟩; simpa using hy))
  have hmp : MeasurePreserving φ μH[((2 * d : ℕ) : ℝ)] μH[((2 * d : ℕ) : ℝ)] :=
    φ.toIsometryEquiv.measurePreserving_hausdorffMeasure _
  have himg : (fun x => ψ (graphPt e F x)) '' A = realGraphPt F' '' (φ '' A) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [hψG, hF']
    simp [realGraphPt]
  rw [← hψ.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg _)) (graphPt e F '' A), Set.image_image,
    himg, h (2 * d) (2 * m) (φ '' Ω) F' hU hF'c (φ '' A) (Set.image_mono hAΩ) hA',
    ← hmp.setLIntegral_comp_emb φ.toHomeomorph.measurableEmbedding]
  refine setLIntegral_congr_fun hA fun x hx => ?_
  have hFx : HasFDerivAt F (fderiv ℝ F x) x :=
    ((hF.differentiableAt (hΩ.mem_nhds (hAΩ hx))).restrictScalars ℝ).hasFDerivAt
  have hG : HasFDerivAt (graphPt e F) (fderiv ℝ (graphPt e F) x) x :=
    (differentiableAt_graphPt_real e hFx.differentiableAt).hasFDerivAt
  set K : EuclideanSpace ℝ (Fin (2 * d)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * m)) :=
    (φm.toContinuousLinearEquiv : EuclideanSpace ℂ (Fin m) →L[ℝ] _).comp
      ((fderiv ℝ F x).comp (φ.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin (2 * d)) →L[ℝ] _))
    with hK
  have hF'x : HasFDerivAt F' K (φ x) := by
    rw [hF']
    exact φm.toContinuousLinearEquiv.hasFDerivAt.comp _
      ((by simpa using hFx : HasFDerivAt F (fderiv ℝ F x) (φ.symm (φ x))).comp _
        φ.symm.toContinuousLinearEquiv.hasFDerivAt)
  simp only [hF'x.fderiv, areaJacobian]
  congr 2
  rw [adjoint_comp_self_of_norm _
    ((K : EuclideanSpace ℝ (Fin (2 * d)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * m))) ∘ₗ φ.toLinearMap),
    det_one_add_comp]
  intro v
  simp only [ContinuousLinearMap.coe_coe]
  rw [hasFDerivAt_graphPt_apply e hFx hG v, norm_sq_sumElim]
  simp [hK]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermRegularConnected
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem IrreducibleGermRegularConnected.proof (hpar : LocalParametrisation.Statement)
    (hsheets : ParametrisationSheetsConnected.Statement) :
    IrreducibleGermRegularConnected.Statement := by
  intro σ _ X w hX hirr U hU
  obtain ⟨d, A, B, D, δ, N, hBU, hP⟩ := hpar σ X w hX hirr U hU
  have hS := hsheets σ X w B d A D δ N hP hirr
  obtain ⟨hBo, hwXB, -, -, -, -, -, -, -, -, hchart, hdense⟩ := hP

  have hSreg : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ regLocus (X ∩ B) := by
    rintro x ⟨hxXB, hx⟩
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hchart x hxXB hx
    exact ⟨hxXB, d, A, O, V, g, hO, hV, hxV, hg, hAg, hXV⟩
  exact ⟨B, hBo, hwXB.2, hBU, hS.subset_closure hSreg ((regLocus_subset _).trans hdense)⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCompletionNormalDescent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def CompletionNormalDescent.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (J : Ideal R), IsNoetherianRing R → J ≤ (⊥ : Ideal R).jacobson →
    IsDomain (AdicCompletion J R) → IsIntegrallyClosed (AdicCompletion J R) →
      IsDomain R ∧ IsIntegrallyClosed R

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

