module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CauchyRiemannIffDifferentiableOnComplex
section
open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

private lemma pi_single_eq_re_smul_add_im_smul {g : ℕ} (a : Fin g) (w : ℂ) :
    (Pi.single a w : Fin g → ℂ) =
      (w.re : ℝ) • (Pi.single a 1 : Fin g → ℂ) + (w.im : ℝ) • (I • (Pi.single a 1 : Fin g → ℂ)) := by
  ext j
  by_cases hj : j = a
  · subst hj
    apply Complex.ext <;> simp
  · simp [hj]

theorem map_I_smul_of_cauchyRiemann {g : ℕ} (L : (Fin g → ℂ) →L[ℝ] ℂ)
    (h : ∀ a, L (Pi.single a 1 : Fin g → ℂ) + I * L (I • (Pi.single a 1 : Fin g → ℂ)) = 0)
    (c : ℂ) (v : Fin g → ℂ) : L (c • v) = c • L v := by

  have hI : ∀ a, L (I • (Pi.single a 1 : Fin g → ℂ)) = I * L (Pi.single a 1) := by
    intro a
    linear_combination (-I) * h a + L (I • (Pi.single a 1 : Fin g → ℂ)) * I_sq
  have hline : ∀ a (w : ℂ), L (Pi.single a w : Fin g → ℂ) = w * L (Pi.single a 1) := by
    intro a w
    rw [pi_single_eq_re_smul_add_im_smul a w, map_add (f := _), map_smul, map_smul, hI a]
    conv_rhs => rw [← Complex.re_add_im w]
    simp only [Complex.real_smul]
    ring
  have hsum : ∀ u : Fin g → ℂ, L u = ∑ a, u a * L (Pi.single a 1) := by
    intro u
    conv_lhs => rw [← Finset.univ_sum_single u]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl (fun a _ => hline a (u a))
  rw [hsum, hsum v, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem cauchyRiemann_iff_differentiableOn_complex :
    ∀ (g : ℕ) (U : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℂ), IsOpen U → (DifferentiableOn ℝ f U → ((∀ a, ∀ z ∈ U, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = 0) ↔ DifferentiableOn ℂ f U)) ∧ (DifferentiableOn ℂ f U → ContDiffOn ℝ ∞ f U ∧ ∀ v, DifferentiableOn ℂ (fun z => fderiv ℂ f z v) U) := by
  intro g U f hU
  refine ⟨fun hR => ⟨fun hCR => ?_, fun hC => ?_⟩, fun hC => ?_⟩
  ·
    intro z hz
    have hzR : DifferentiableAt ℝ f z := hR.differentiableAt (hU.mem_nhds hz)
    set L := fderiv ℝ f z with hL
    have hlin : ∀ (c : ℂ) (v : Fin g → ℂ), L (c • v) = c • L v :=
      map_I_smul_of_cauchyRiemann L (fun a => hCR a z hz)
    let L' : (Fin g → ℂ) →L[ℂ] ℂ :=
      { toFun := L
        map_add' := L.map_add
        map_smul' := hlin
        cont := L.continuous }
    have hres : L'.restrictScalars ℝ = L := by
      ext v; rfl
    exact (hasFDerivAt_of_restrictScalars ℝ hzR.hasFDerivAt hres).differentiableAt.differentiableWithinAt
  · intro a z hz
    have hzC : DifferentiableAt ℂ f z := hC.differentiableAt (hU.mem_nhds hz)
    rw [hzC.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
    rw [← mul_assoc, I_mul_I]
    ring
  · refine ⟨?_, fun v => SCV.differentiableOn_fderiv_apply hU hC v⟩
    exact (SCV.contDiffOn_of_differentiableOn hU hC ∞).restrict_scalars ℝ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetNotMemSpanMulVecOfSocle
section
open scoped TensorProduct

namespace GlobalTheory

theorem det_notMem_span_mulVec_of_socle {T : Type} [CommRing T] {g N : ℕ} (x : Fin g → T)
    (hsyz : ∀ r : Fin g → T, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) T,
      s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x)
    (hsoc : ∏ i, x i ^ N ∉ Ideal.span (Set.range fun i => x i ^ (N + 1)))
    (a : Matrix (Fin g) (Fin g) T)
    (h : ∀ i, x i ^ (N + 1) ∈ Ideal.span (Set.range (a.mulVec x))) :
    a.det ∉ Ideal.span (Set.range (a.mulVec x)) := by
  intro hdet
  have h' : ∀ i, ∃ c : Fin g → T, ∑ j, c j * a.mulVec x j = x i ^ (N + 1) := fun i =>
    Ideal.mem_span_range_iff_exists_fun.mp (h i)
  choose b hb using h'
  let B : Matrix (Fin g) (Fin g) T := Matrix.of b
  have hB : B.mulVec (a.mulVec x) = fun i => x i ^ (N + 1) := by
    funext i
    exact hb i
  set J : Ideal T := Ideal.span (Set.range fun i => x i ^ (N + 1)) with hJ
  have hf : ∀ i, B.det * a.mulVec x i ∈ J := by
    intro i
    have e : B.adjugate.mulVec (B.mulVec (a.mulVec x)) = B.det • a.mulVec x := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have e' := congrFun e i
    rw [hB, Pi.smul_apply, smul_eq_mul] at e'
    rw [← e']
    exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun j => B.adjugate i j, rfl⟩
  have hBa : (B * a).det ∈ J := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hdet
    rw [Matrix.det_mul, ← hc, Finset.mul_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [mul_left_comm]
    exact Ideal.mul_mem_left _ _ (hf j)
  have hBx : (B * a).mulVec x = fun i => x i ^ (N + 1) := by
    rw [← Matrix.mulVec_mulVec, hB]
  have hD : (Matrix.diagonal fun i => x i ^ N).mulVec x = fun i => x i ^ (N + 1) := by
    funext i
    rw [Matrix.mulVec_diagonal, pow_succ]
  have key := GlobalTheory.det_sub_det_mem_span_of_mulVec_eq T g x hsyz (B * a)
    (Matrix.diagonal fun i => x i ^ N) (hBx.trans hD.symm)
  rw [hBx, Matrix.det_diagonal] at key
  have := J.sub_mem hBa key
  rw [sub_sub_cancel] at this
  exact hsoc this

theorem det_notMem_span_mulVec_X : ∀ (k : Type) [Field k] (g N : ℕ) (a : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k)), (∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin g) k) ^ N ∈ Ideal.span (Set.range (a.mulVec MvPowerSeries.X))) → a.det ∉ Ideal.span (Set.range (a.mulVec MvPowerSeries.X)) := by
  intro k _ g N a h
  obtain ⟨hsyz, hsoc⟩ := GlobalTheory.mvPowerSeries_variables_syzygy_socle k g MvPowerSeries.X (fun _ => rfl)
  refine det_notMem_span_mulVec_of_socle MvPowerSeries.X hsyz (hsoc N) a fun i => ?_
  rw [pow_succ]
  exact Ideal.mul_mem_right _ _ (h i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnQuotientOfDifferentiableOnSlice
section
open Filter Metric Set
open scoped Topology

namespace GlobalTheory

theorem exists_circle_ne_zero_of_frequently_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {S : Set E} {g : E → ℂ} {z₀ : E} (hS : S ∈ 𝓝 z₀)
    (hg : DifferentiableOn ℂ g S) (hfr : ∃ᶠ z in 𝓝 z₀, g z ≠ 0) :
    ∃ (v : E) (r : ℝ), 0 < r ∧ (∀ t ∈ closedBall (0 : ℂ) r, z₀ + t • v ∈ S) ∧
      ∀ t ∈ sphere (0 : ℂ) r, g (z₀ + t • v) ≠ 0 := by
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.1 hS
  obtain ⟨z₁, hz₁, hz₁b⟩ := (hfr.and_eventually (ball_mem_nhds z₀ (half_pos hε))).exists
  have hv : ‖z₁ - z₀‖ < ε / 2 := by simpa [dist_eq_norm] using hz₁b
  have hmem : ∀ t ∈ ball (0 : ℂ) 2, z₀ + t • (z₁ - z₀) ∈ S := by
    intro t ht
    apply hεS
    rw [mem_ball_zero_iff] at ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    nlinarith [norm_nonneg t, norm_nonneg (z₁ - z₀)]
  have hd : DifferentiableOn ℂ (fun t : ℂ => g (z₀ + t • (z₁ - z₀))) (ball 0 2) :=
    hg.comp (f := fun t : ℂ => z₀ + t • (z₁ - z₀)) (by fun_prop) hmem
  have han := hd.analyticOnNhd isOpen_ball
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 2 := by simp
  rcases (han 0 h0).eventually_eq_zero_or_eventually_ne_zero with h | h
  · have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 2).isPreconnected
      h0 h (show (1 : ℂ) ∈ ball (0 : ℂ) 2 by simp)
    exact absurd (by simpa using this) hz₁
  · rw [eventually_nhdsWithin_iff] at h
    obtain ⟨r, hr, hrs⟩ := nhds_basis_closedBall.mem_iff.1
      (h.and (ball_mem_nhds (0 : ℂ) two_pos))
    refine ⟨z₁ - z₀, r, hr, fun t ht => hmem t (hrs ht).2, fun t ht => ?_⟩
    refine (hrs (sphere_subset_closedBall ht)).1 ?_
    rintro rfl
    simp at ht
    exact hr.ne ht

theorem differentiableOn_quotient_of_differentiableOn_slice :
    ∀ (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
      [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] (W : Set (V × V'))
      (f θ F : V × V' → ℂ), IsOpen W → DifferentiableOn ℂ f W → DifferentiableOn ℂ θ W →
      (∀ w ∈ W, F w * θ w = f w) →
      (∀ b, DifferentiableOn ℂ (fun z => F (b, z)) {z | (b, z) ∈ W}) →
      (∀ w ∈ W, ∃ᶠ z in nhds w.2, θ (w.1, z) ≠ 0) → DifferentiableOn ℂ F W := by
  intro V V' _ _ _ _ _ _ W f θ F hW hf hθ hF hsl hfr w hw
  obtain ⟨v, r, hr, hin, hne⟩ := exists_circle_ne_zero_of_frequently_ne_zero
    (S := {z | (w.1, z) ∈ W}) (g := fun z => θ (w.1, z)) (z₀ := w.2)
    ((hW.preimage (f := fun z => (w.1, z)) (by fun_prop)).mem_nhds hw)
    (hθ.comp (f := fun z => (w.1, z)) (by fun_prop) fun z hz => hz) (hfr w hw)
  let p : V × V' → ℂ → V × V' := fun y t => (y.1, y.2 + t • v)
  have hp : Continuous fun q : (V × V') × ℂ => p q.1 q.2 := by fun_prop
  have h1 : ∀ᶠ y in 𝓝 w, ∀ t ∈ closedBall (0 : ℂ) r, p y t ∈ W :=
    (isCompact_closedBall (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht =>
      hp.continuousAt.eventually (hW.mem_nhds (hin t ht))
  have h2 : ∀ᶠ y in 𝓝 w, ∀ t ∈ sphere (0 : ℂ) r, θ (p y t) ≠ 0 :=
    (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht => by
      have hc : ContinuousAt θ (p w t) :=
        (hθ.differentiableAt (hW.mem_nhds (hin t (sphere_subset_closedBall ht)))).continuousAt
      exact (ContinuousAt.comp (g := θ) (f := fun q : (V × V') × ℂ => p q.1 q.2) (x := (w, t))
        hc hp.continuousAt).eventually_ne (hne t ht)
  obtain ⟨U, hU, hUo, hwU⟩ := _root_.eventually_nhds_iff.1 (h1.and h2)
  have hcm : ∀ s : ℝ, circleMap 0 r s ∈ sphere (0 : ℂ) r := fun s =>
    circleMap_mem_sphere 0 hr.le s
  have hG := (differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
    (F := fun (s : ℝ) (y : V × V') => f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)))
    (a := 0) (b := 2 * Real.pi) hUo ?_ ?_).1
  · have hEq : ∀ y ∈ U, F y = (2 * Real.pi)⁻¹ • ∫ s in (0 : ℝ)..2 * Real.pi,
        f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)) := by
      intro y hy
      have hd : DifferentiableOn ℂ (fun t : ℂ => F (p y t)) (closedBall 0 r) :=
        (hsl y.1).comp (f := fun t : ℂ => y.2 + t • v) (by fun_prop) fun t ht => (hU y hy).1 t ht
      have hdc : DiffContOnCl ℂ (fun t : ℂ => F (p y t)) (ball 0 |r|) := by
        apply DifferentiableOn.diffContOnCl
        rwa [abs_of_pos hr, closure_ball _ hr.ne']
      have hav := hdc.circleAverage
      rw [Real.circleAverage_def] at hav
      have : F y = F (p y 0) := by simp [p]
      rw [this, ← hav]
      congr 1
      refine intervalIntegral.integral_congr fun s _ => ?_
      have hs := hcm s
      rw [eq_div_iff ((hU y hy).2 _ hs), hF _ ((hU y hy).1 _ (sphere_subset_closedBall hs))]
    have hFU : DifferentiableOn ℂ F U := (hG.const_smul ((2 * Real.pi)⁻¹ : ℝ)).congr hEq
    exact (hFU.differentiableAt (hUo.mem_nhds hwU)).differentiableWithinAt
  · have hq : Continuous fun q : ℝ × (V × V') => p q.2 (circleMap 0 r q.1) :=
      hp.comp (f := fun q : ℝ × (V × V') => (q.2, circleMap 0 r q.1)) (by fun_prop)
    have hm : ∀ q : ℝ × (V × V'), q ∈ uIcc 0 (2 * Real.pi) ×ˢ U →
        p q.2 (circleMap 0 r q.1) ∈ W := fun q hq =>
      (hU _ hq.2).1 _ (sphere_subset_closedBall (hcm _))
    exact (hf.continuousOn.comp hq.continuousOn hm).div
      (hθ.continuousOn.comp hq.continuousOn hm) fun q hq => (hU _ hq.2).2 _ (hcm _)
  · intro s _
    have hq : Differentiable ℂ fun y : V × V' => p y (circleMap 0 r s) := by fun_prop
    have hm : ∀ y ∈ U, p y (circleMap 0 r s) ∈ W := fun y hy =>
      (hU _ hy).1 _ (sphere_subset_closedBall (hcm _))
    simp only [div_eq_mul_inv]
    exact (hf.comp hq.differentiableOn hm).mul
      ((hθ.comp hq.differentiableOn hm).inv fun y hy => (hU _ hy).2 _ (hcm _))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgClosedJoinOfTwoFieldExtensions
section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_algClosed_join_of_two_field_extensions
    (K₀ K K' : Type) [Field K₀] [Field K] [Field K'] (i : K₀ →+* K) (i' : K₀ →+* K') :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (j : K →+* Ω) (j' : K' →+* Ω),
      j.comp i = j'.comp i' := by
  first
  | exact @_root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension
  | exact _root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension
  | (apply _root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalUnramifiedOfIsIndEtale
section
open CategoryTheory IsLocalRing

namespace GlobalTheory.LocalIndEtaleUnramified

theorem exists_local_of_algHom {A S B : Type} [CommRing A] [IsLocalRing A] [CommRing S]
    [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)] [CommRing B] [Algebra A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] (g : B →ₐ[A] S) (b : B) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : Algebra A L)
      (_ : IsLocalHom (algebraMap A L)) (_ : Algebra.FormallyUnramified A L)
      (_ : Algebra.EssFiniteType A L) (φ : L →ₐ[A] S) (_ : IsLocalHom φ) (x : L),
      φ x = g b := by
  let P : Ideal B := (maximalIdeal S).comap (g : B →+* S)
  haveI hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hu : ∀ y : P.primeCompl, IsUnit (g y) := by
    intro y
    by_contra h
    exact y.2 (show (g : B →+* S) y ∈ maximalIdeal S from h)
  let φ : Localization.AtPrime P →ₐ[A] S := IsLocalization.liftAlgHom (M := P.primeCompl) hu
  have hφ : ∀ y : B, φ (algebraMap B (Localization.AtPrime P) y) = g y := fun y =>
    IsLocalization.lift_eq (M := P.primeCompl) (g := (g : B →+* S)) hu y
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl a
    refine (IsLocalization.AtPrime.isUnit_mk'_iff _ P y s).2 ?_
    have h1 : φ (IsLocalization.mk' (Localization.AtPrime P) y s) * g s = g y := by
      rw [← hφ, ← map_mul, IsLocalization.mk'_spec, hφ]
    have h2 : IsUnit (g y) := h1 ▸ ha.mul (hu s)
    intro hy
    exact (show (g : B →+* S) y ∈ maximalIdeal S from hy) h2
  have hA : IsLocalHom (algebraMap A (Localization.AtPrime P)) := by
    refine ⟨fun a ha => ?_⟩
    have := ha.map φ
    rw [AlgHom.commutes] at this
    exact IsLocalHom.map_nonunit a this
  haveI : Algebra.FormallyUnramified B (Localization.AtPrime P) :=
    Algebra.FormallyUnramified.of_isLocalization P.primeCompl
  haveI : Algebra.EssFiniteType B (Localization.AtPrime P) :=
    Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
  exact ⟨Localization.AtPrime P, inferInstance, inferInstance, inferInstance, hA,
    Algebra.FormallyUnramified.comp A B _, Algebra.EssFiniteType.comp A B _, φ, hloc,
    algebraMap B _ b, hφ b⟩

theorem exists_local_unramified_of_isIndEtale {A S : Type} [CommRing A] [IsLocalRing A]
    [CommRing S] [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) (s : S) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : Algebra A L)
      (_ : IsLocalHom (algebraMap A L)) (_ : Algebra.FormallyUnramified A L)
      (_ : Algebra.EssFiniteType A L) (φ : L →ₐ[A] S) (_ : IsLocalHom φ) (x : L),
      φ x = s := by
  obtain ⟨J, _, _, D, t, c, hc, H⟩ := h
  obtain ⟨j, b, hb⟩ := Limits.Concrete.isColimit_exists_rep D hc s
  obtain ⟨hE, hcomp⟩ := H j
  let f : A →+* D.obj j := (t.app j).hom
  let g₀ : D.obj j →+* S := (c.app j).hom
  letI : Algebra A (D.obj j) := f.toAlgebra
  haveI : Algebra.Etale A (D.obj j) := hE
  have hg : ∀ a : A, g₀ (f a) = algebraMap A S a := fun a =>
    congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of S => k.hom a) hcomp
  let g : D.obj j →ₐ[A] S := { g₀ with commutes' := hg }
  have hb' : g b = s := hb
  rw [← hb']
  exact exists_local_of_algHom g b

end GlobalTheory.LocalIndEtaleUnramified
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolynomialFinrankHomogeneousSubmodule
section
namespace GlobalTheory

private lemma finite_setOf_finsupp_degree_eq (σ : Type) [Finite σ] [Nonempty σ] (e : ℕ) :
    Finite ↑{d : σ →₀ ℕ | d.degree = e} := by
  have := Fintype.ofFinite σ
  have h : Nat.card {d : σ →₀ ℕ // d.degree = e} ≠ 0 := by
    rw [_root_.GlobalTheory.natCard_degree_eq]
    have := Fintype.card_pos (α := σ)
    exact (Nat.choose_pos (by omega)).ne'
  exact Nat.finite_of_card_ne_zero h

private lemma finrank_homogeneousSubmodule_eq_choose (σ : Type) [Fintype σ] [Nonempty σ] (K : Type)
    [Field K] (e : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule σ K e) =
      (e + Fintype.card σ - 1).choose e := by
  have := finite_setOf_finsupp_degree_eq σ e
  have := Fintype.ofFinite ↑{d : σ →₀ ℕ | d.degree = e}
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K)
      {d : σ →₀ ℕ | d.degree = e}).finrank_eq,
    ← _root_.GlobalTheory.natCard_degree_eq σ e, Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]
  rfl

private lemma cast_choose_eq_eval_descPochhammer (m e : ℕ) (hm : 1 ≤ m) :
    (((e + m - 1).choose e : ℕ) : ℚ) = (Polynomial.C (1 / ((m - 1).factorial : ℚ)) *
      (descPochhammer ℚ (m - 1)).comp (Polynomial.X + Polynomial.C ((m - 1 : ℕ) : ℚ))).eval
        (e : ℚ) := by
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  have h1 : (e : ℚ) + ((m - 1 : ℕ) : ℚ) = ((e + (m - 1) : ℕ) : ℚ) := by push_cast; ring
  rw [h1, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
    show e + m - 1 = e + (m - 1) by omega, Nat.choose_symm_add]
  have : ((m - 1).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem _root_.GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule :
    ∀ (σ : Type) [Finite σ] [Nonempty σ], ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] (e : ℕ),
      ((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) : ℕ) : ℚ) =
        Q.eval (e : ℚ) := by
  intro σ _ _
  have := Fintype.ofFinite σ
  refine ⟨Polynomial.C (1 / ((Fintype.card σ - 1).factorial : ℚ)) *
    (descPochhammer ℚ (Fintype.card σ - 1)).comp
      (Polynomial.X + Polynomial.C ((Fintype.card σ - 1 : ℕ) : ℚ)), fun K _ e => ?_⟩
  rw [finrank_homogeneousSubmodule_eq_choose σ K e]
  exact cast_choose_eq_eval_descPochhammer _ e Fintype.card_pos

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FourierCoeffEqZeroOfTsumEqZeroFin
section
open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

open Complex Matrix in
open scoped ContDiff BigOperators Real in
private lemma integral_Ioc_cexp_two_pi_I_int_mul (j : ℤ) :
    ∫ t, cexp (2 * π * I * (j : ℂ) * (t : ℂ)) ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) =
      if j = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hj
  · subst hj; simp
  · have hc : (2 * π * I * (j : ℂ)) ≠ 0 := by
      have : (j : ℂ) ≠ 0 := by exact_mod_cast hj
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hπ, this, I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have h1 : cexp (2 * π * I * (j : ℂ)) = 1 := by
      rw [show 2 * π * I * (j : ℂ) = j * (2 * π * I) by ring]
      exact exp_int_mul_two_pi_mul_I j
    simp [h1]


open Complex Matrix in
open scoped ContDiff BigOperators Real in
theorem _root_.GlobalTheory.fourier_coeff_eq_zero_of_tsum_eq_zero_fin :
    ∀ (n : ℕ) (c : (Fin n → ℤ) → ℂ), Summable (fun ν => ‖c ν‖) →
      (∀ x : Fin n → ℝ, ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) = 0) →
      ∀ ν, c ν = 0 := by
  intro n c hc h μ
  set m : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1) with hm
  haveI : MeasureTheory.IsProbabilityMeasure m := ⟨by simp [m]⟩
  set P : MeasureTheory.Measure (Fin n → ℝ) := MeasureTheory.Measure.pi fun _ => m
  set G : (Fin n → ℤ) → (Fin n → ℝ) → ℂ := fun ν x =>
    c ν * ∏ k, cexp (2 * π * I * (((ν k - μ k : ℤ)) : ℂ) * (x k : ℂ)) with hG
  have hnorm : ∀ ν x, ‖G ν x‖ = ‖c ν‖ := by
    intro ν x
    simp only [G, norm_mul, norm_prod, Complex.norm_exp]
    simp [Complex.mul_re]
  have hint : ∀ ν, MeasureTheory.Integrable (G ν) P := by
    intro ν
    refine MeasureTheory.Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop))
      ‖c ν‖ (MeasureTheory.ae_of_all _ fun x => (hnorm ν x).le)
  have hval : ∀ ν, ∫ x, G ν x ∂P = if ν = μ then c ν else 0 := by
    intro ν
    simp only [G]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_fintype_prod_eq_prod (E := fun _ => ℝ)
      (μ := fun _ => m) (fun k (t : ℝ) => cexp (2 * π * I * (((ν k - μ k : ℤ)) : ℂ) * (t : ℂ)))]
    simp only [hm, integral_Ioc_cexp_two_pi_I_int_mul]
    by_cases hνμ : ν = μ
    · subst hνμ; simp
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp hνμ
      rw [if_neg hνμ, Finset.prod_eq_zero (Finset.mem_univ k) (by simp [sub_eq_zero, hk]), mul_zero]
  have hsum : ∀ x, ∑' ν, G ν x = 0 := by
    intro x
    have hx := h x
    have : ∀ ν, G ν x = c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) *
        cexp (-(2 * π * I * ∑ k, (μ k : ℂ) * (x k : ℂ))) := by
      intro ν
      simp only [G, mul_assoc]
      congr 1
      rw [← Complex.exp_add, ← Complex.exp_sum]
      congr 1
      push_cast
      simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [this]
    rw [tsum_mul_right, hx, zero_mul]
  have key := MeasureTheory.integral_tsum_of_summable_integral_norm hint
    (by simpa [hnorm] using hc)
  simp only [hval, hsum, MeasureTheory.integral_zero] at key
  rwa [tsum_ite_eq] at key

end GlobalTheory
end

