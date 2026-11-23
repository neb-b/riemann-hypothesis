module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SchOfClosed
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.schOfClosed :
    UpperTheory.V.Af.Smo.SchOfClosed := by
  intro X _ _ _ A hA
  have b : Module.Basis (Fin (Module.finrank ℝ X)) ℝ X := Module.finBasis ℝ X
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℝ X) → (X →L[ℝ] ℝ), ∀ i x, c i x = b.repr x i :=
    ⟨fun i => LinearMap.toContinuousLinearMap (b.coord i), fun i x => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Fin (Module.finrank ℝ X) → (ℂ →L[ℝ] (X →L[ℝ] ℂ)),
      ∀ i z v, L i z v = c i v • z :=
    ⟨fun i => ContinuousLinearMap.smulRightL ℝ X ℂ (c i), fun i z v => rfl⟩
  have hsm : ∀ n : ℕ, ∀ f ∈ A, ContDiff ℝ n f := by
    intro n
    induction n with
    | zero => intro f hf; exact contDiff_zero.2 (hA f hf).2.1.continuous
    | succ n ih =>
      intro f hf
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      refine ⟨(hA f hf).2.1, by simp, ?_⟩
      rw [contDiff_clm_apply_iff]
      intro v
      exact ih _ ((hA f hf).2.2.1 v)
  have hinf : ∀ f ∈ A, ContDiff ℝ ∞ f := fun f hf => contDiff_infty.2 fun n => hsm n f hf
  have hx : ∀ x : X, ‖x‖ ≤ ∑ i, ‖b i‖ * ‖c i x‖ := by
    intro x
    calc ‖x‖ = ‖∑ i, b.repr x i • b i‖ := by rw [b.sum_repr]
      _ ≤ ∑ i, ‖b.repr x i • b i‖ := norm_sum_le _ _
      _ = ∑ i, ‖b i‖ * ‖c i x‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, hc, mul_comm]
  have h0 : ∀ k : ℕ, ∀ f ∈ A, ∃ C, ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ C := by
    intro k
    induction k with
    | zero =>
      intro f hf
      obtain ⟨C, hC⟩ := (hA f hf).1
      exact ⟨C, fun x => by simpa using hC x⟩
    | succ k ih =>
      intro f hf
      choose C hC using fun i => ih _ ((hA f hf).2.2.2 (c i))
      refine ⟨∑ i, ‖b i‖ * C i, fun x => ?_⟩
      calc ‖x‖ ^ (k + 1) * ‖f x‖ = ‖x‖ * (‖x‖ ^ k * ‖f x‖) := by ring
        _ ≤ (∑ i, ‖b i‖ * ‖c i x‖) * (‖x‖ ^ k * ‖f x‖) := by gcongr; exact hx x
        _ = ∑ i, ‖b i‖ * (‖x‖ ^ k * ‖(↑(c i x) : ℂ) * f x‖) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [norm_mul, Complex.norm_real]
            ring
        _ ≤ ∑ i, ‖b i‖ * C i := by
            gcongr with i
            exact hC i x
  have hd : ∀ n k : ℕ, ∀ f ∈ A, ∃ C, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
    intro n
    induction n with
    | zero =>
      intro k f hf
      obtain ⟨C, hC⟩ := h0 k f hf
      exact ⟨C, fun x => by rw [norm_iteratedFDeriv_zero]; exact hC x⟩
    | succ n ih =>
      intro k f hf
      obtain ⟨g, hg⟩ : ∃ g : Fin (Module.finrank ℝ X) → X → ℂ, ∀ i x, g i x = fderiv ℝ f x (b i) :=
        ⟨fun i x => fderiv ℝ f x (b i), fun _ _ => rfl⟩
      have hgA : ∀ i, g i ∈ A := by
        intro i
        have : g i = fun x => fderiv ℝ f x (b i) := funext (hg i)
        rw [this]
        exact (hA f hf).2.2.1 (b i)
      have hfd : fderiv ℝ f = fun x => ∑ i, L i (g i x) := by
        funext x
        ext v
        rw [ContinuousLinearMap.sum_apply]
        simp only [hL, hg, hc]
        conv_lhs => rw [← b.sum_repr v]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [map_smul]
      have hsum : iteratedFDeriv ℝ n (fun x => ∑ i, L i (g i x))
          = ∑ i, iteratedFDeriv ℝ n (fun y => L i (g i y)) :=
        iteratedFDeriv_sum (f := fun i y => L i (g i y)) (u := Finset.univ)
          (fun i _ => (L i).contDiff.comp (hsm n _ (hgA i)))
      choose C hC using fun i => ih k (g i) (hgA i)
      refine ⟨∑ i, ‖L i‖ * C i, fun x => ?_⟩
      rw [← norm_iteratedFDeriv_fderiv, hfd, hsum, Finset.sum_apply]
      calc ‖x‖ ^ k * ‖∑ i, iteratedFDeriv ℝ n (fun y => L i (g i y)) x‖
          ≤ ‖x‖ ^ k * ∑ i, ‖iteratedFDeriv ℝ n (fun y => L i (g i y)) x‖ := by
            gcongr
            exact norm_sum_le _ _
        _ ≤ ‖x‖ ^ k * ∑ i, ‖L i‖ * ‖iteratedFDeriv ℝ n (g i) x‖ := by
            gcongr with i
            exact (L i).norm_iteratedFDeriv_comp_left (hsm n _ (hgA i)).contDiffAt le_rfl
        _ = ∑ i, ‖L i‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (g i) x‖) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ ≤ ∑ i, ‖L i‖ * C i := by
            gcongr with i
            exact hC i x
  intro f hf
  exact ⟨⟨f, hinf f hf, fun k n => hd n k f hf⟩, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SchTensor
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.schTensor :
    UpperTheory.V.Af.Smo.SchOfClosed → UpperTheory.V.Af.Smo.SchTensor := by
  intro hS V M _ _ _ _ _ _ h hh hhc α
  classical
  let S : Set (V × M → ℂ) := {F | ∃ (f : V → ℂ) (β : 𝓢(M, ℂ)), ContDiff ℝ ∞ f ∧
    HasCompactSupport f ∧ F = fun p => f p.1 * β p.2}
  let A : Set (V × M → ℂ) := (Submodule.span ℂ S : Set (V × M → ℂ))
  have hgen : ∀ F ∈ S, (∃ C, ∀ x, ‖F x‖ ≤ C) ∧ Differentiable ℝ F ∧
      (∀ v : V × M, (fun x => fderiv ℝ F x v) ∈ A) ∧
      ∀ l : V × M →L[ℝ] ℝ, (fun x => (l x : ℂ) * F x) ∈ A := by
    rintro F ⟨f, β, hf, hfc, rfl⟩
    have hfd : Differentiable ℝ f := hf.differentiable (by simp)
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨Cf, hCf⟩ := hfc.exists_bound_of_continuous hf.continuous
      obtain ⟨Cb, hCb⟩ : ∃ C, ∀ y, ‖β y‖ ≤ C :=
        ⟨‖β.toBoundedContinuousFunction‖, fun y => by
          simpa using β.toBoundedContinuousFunction.norm_coe_le_norm y⟩
      refine ⟨Cf * Cb, fun p => ?_⟩
      rw [norm_mul]
      exact mul_le_mul (hCf _) (hCb _) (norm_nonneg _) (le_trans (norm_nonneg _) (hCf p.1))
    · exact (hfd.comp differentiable_fst).mul (β.differentiable.comp differentiable_snd)
    · intro v
      have hder : ∀ p : V × M, fderiv ℝ (fun p : V × M => f p.1 * β p.2) p v =
          fderiv ℝ f p.1 v.1 * β p.2 + f p.1 * (LineDeriv.lineDerivOp v.2 β : 𝓢(M, ℂ)) p.2 := by
        intro p
        have h1 : HasFDerivAt (fun p : V × M => f p.1)
            ((fderiv ℝ f p.1).comp (ContinuousLinearMap.fst ℝ V M)) p :=
          (hfd p.1).hasFDerivAt.comp p hasFDerivAt_fst
        have h2 : HasFDerivAt (fun p : V × M => β p.2)
            ((fderiv ℝ β p.2).comp (ContinuousLinearMap.snd ℝ V M)) p :=
          (β.differentiableAt).hasFDerivAt.comp p hasFDerivAt_snd
        rw [show (fun p : V × M => f p.1 * β p.2) = (fun p => f p.1) * (fun p => β p.2) from rfl,
          (h1.mul h2).fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
          smul_eq_mul]
        ring
      have hfe : (fun x => fderiv ℝ (fun p : V × M => f p.1 * β p.2) x v) =
          (fun p : V × M => (fun ξ => fderiv ℝ f ξ v.1) p.1 * β p.2) +
          (fun p : V × M => f p.1 * (LineDeriv.lineDerivOp v.2 β : 𝓢(M, ℂ)) p.2) := by
        ext p
        rw [hder]
        rfl
      rw [hfe]
      refine (Submodule.span ℂ S).add_mem
        (Submodule.subset_span ⟨fun ξ => fderiv ℝ f ξ v.1, β, ?_, ?_, rfl⟩)
        (Submodule.subset_span ⟨f, LineDeriv.lineDerivOp v.2 β, hf, hfc, rfl⟩)
      · exact ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const
      · exact (hfc.fderiv ℝ).comp_left (g := fun L : V →L[ℝ] ℂ => L v.1) (by simp)
    · intro l
      let l1 : V →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inl ℝ V M)
      let l2 : M →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inr ℝ V M)
      have hl : ∀ p : V × M, l p = l1 p.1 + l2 p.2 := by
        intro p
        simp only [l1, l2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
          ContinuousLinearMap.inr_apply]
        rw [← map_add (f := _)]
        congr 1
        ext <;> simp
      have htg : Function.HasTemperateGrowth (fun y : M => ((l2 y : ℝ) : ℂ)) := by
        fun_prop
      have hfe : (fun x : V × M => (l x : ℂ) * (f x.1 * β x.2)) =
          (fun p : V × M => (fun ξ => ((l1 ξ : ℝ) : ℂ) * f ξ) p.1 * β p.2) +
          (fun p : V × M => f p.1 *
            (SchwartzMap.smulLeftCLM ℂ (fun y : M => ((l2 y : ℝ) : ℂ)) β) p.2) := by
        ext p
        simp only [Pi.add_apply, SchwartzMap.smulLeftCLM_apply_apply htg, smul_eq_mul, hl p]
        push_cast
        ring
      rw [hfe]
      refine (Submodule.span ℂ S).add_mem
        (Submodule.subset_span ⟨fun ξ => ((l1 ξ : ℝ) : ℂ) * f ξ, β, ?_, ?_, rfl⟩)
        (Submodule.subset_span ⟨f, SchwartzMap.smulLeftCLM ℂ (fun y : M => ((l2 y : ℝ) : ℂ)) β,
          hf, hfc, rfl⟩)
      · exact (Complex.ofRealCLM.contDiff.comp l1.contDiff).mul hf
      · exact hfc.mul_left
  have hclosed : ∀ F ∈ A, (∃ C, ∀ x, ‖F x‖ ≤ C) ∧ Differentiable ℝ F ∧
      (∀ v : V × M, (fun x => fderiv ℝ F x v) ∈ A) ∧
      ∀ l : V × M →L[ℝ] ℝ, (fun x => (l x : ℂ) * F x) ∈ A := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF => exact hgen F hF
    | zero =>
      refine ⟨⟨0, fun x => by simp⟩, differentiable_const 0, fun v => ?_, fun l => ?_⟩
      · have h0 : (fun x => fderiv ℝ (0 : V × M → ℂ) x v) = 0 := by
          ext x
          simp
        rw [h0]
        exact (Submodule.span ℂ S).zero_mem
      · have h0 : (fun x => (l x : ℂ) * (0 : V × M → ℂ) x) = 0 := by
          ext x
          simp
        rw [h0]
        exact (Submodule.span ℂ S).zero_mem
    | add F G _ _ hF hG =>
      obtain ⟨⟨C1, hC1⟩, hd1, hv1, hl1⟩ := hF
      obtain ⟨⟨C2, hC2⟩, hd2, hv2, hl2⟩ := hG
      refine ⟨⟨C1 + C2, fun x => (norm_add_le _ _).trans (add_le_add (hC1 x) (hC2 x))⟩,
        hd1.add hd2, fun v => ?_, fun l => ?_⟩
      · have he : (fun x => fderiv ℝ (F + G) x v) =
            (fun x => fderiv ℝ F x v) + (fun x => fderiv ℝ G x v) := by
          ext x
          rw [fderiv_add (hd1 x) (hd2 x)]
          rfl
        rw [he]
        exact (Submodule.span ℂ S).add_mem (hv1 v) (hv2 v)
      · have he : (fun x => (l x : ℂ) * (F + G) x) =
            (fun x => (l x : ℂ) * F x) + (fun x => (l x : ℂ) * G x) := by
          ext x
          simp [mul_add]
        rw [he]
        exact (Submodule.span ℂ S).add_mem (hl1 l) (hl2 l)
    | smul c F _ hF =>
      obtain ⟨⟨C1, hC1⟩, hd1, hv1, hl1⟩ := hF
      refine ⟨⟨‖c‖ * C1, fun x => ?_⟩, hd1.const_smul c, fun v => ?_, fun l => ?_⟩
      · rw [Pi.smul_apply, norm_smul]
        exact mul_le_mul_of_nonneg_left (hC1 x) (norm_nonneg _)
      · have he : (fun x => fderiv ℝ (c • F) x v) = c • (fun x => fderiv ℝ F x v) := by
          ext x
          rw [fderiv_const_smul (hd1 x) c]
          rfl
        rw [he]
        exact (Submodule.span ℂ S).smul_mem c (hv1 v)
      · have he : (fun x => (l x : ℂ) * (c • F) x) = c • (fun x => (l x : ℂ) * F x) := by
          ext x
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
        rw [he]
        exact (Submodule.span ℂ S).smul_mem c (hl1 l)
  obtain ⟨G, hG⟩ := hS (V × M) A hclosed _ (Submodule.subset_span ⟨h, α, hh, hhc, rfl⟩)
  exact ⟨G, fun ξ y => by rw [hG]⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphAll
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem comm_loc {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : GA E n) (hg : cmp w (GeneralLinearGroup.map (pFin E) g) = 1) (y : GL (Fin n) (w.adicCompletion E)) :
    g * finGL E n (locGL E n w y) = finGL E n (locGL E n w y) * g := by
  refine TR.ga_ext ?_ ?_
  · rw [map_mul, map_mul, TR.pInf_finGL, mul_one, one_mul]
  · rw [map_mul, map_mul, GlobalTheory.CuspRep.pFin_finGL]
    refine cmp_ext fun v => ?_
    rw [map_mul, map_mul]
    by_cases h : v = w
    · subst h
      rw [hg, mul_one, one_mul]
    · have : cmp v (locGL E n w y) = 1 := GlobalTheory.CuspRep.pLoc_locGL_of_ne h y
      rw [this, mul_one, one_mul]

theorem UpperTheory.V.Af.Smo.sphAll :
    UpperTheory.V.Af.Smo.AwayInd → UpperTheory.V.Af.Smo.SphZero → UpperTheory.V.Af.Smo.EmbY → UpperTheory.V.Af.Smo.SphAll := by
  intro hA hZ hE E _ _ _ n S B W hW hS hK p hp h0
  refine hA E n S (fun k => W (p * finGL E n k) = 0) (fun k hk => (hK p k hk).trans h0) ?_
  intro w hw k _ hk hP y
  have hc : cmp w (GeneralLinearGroup.map (pFin E) (p * finGL E n k)) = 1 := by
    rw [map_mul, map_mul, GlobalTheory.CuspRep.pFin_finGL, hp w hw, hk, mul_one]
  obtain ⟨e1, e2, -, -⟩ := hE E n 0
  have hz := hZ E n w (psiL w) (hS w hw).1 (B w) _ ?_ ((hS w hw).2 (p * finGL E n k)) (by simpa using hP)
  · have := congrFun hz y
    simpa [mul_assoc] using this
  · intro ν hν g
    obtain ⟨a1, a2⟩ := e1 w ν hν
    obtain ⟨b1, b2⟩ := e2 _ a1
    have := hW _ b1 (p * finGL E n k * finGL E n (locGL E n w g))
    rw [b2, a2] at this
    show W _ = _
    rw [map_mul, map_mul, ← mul_assoc, comm_loc w _ hc ν, mul_assoc, this]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.TwistRed
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.twistRed :
    UpperTheory.V.Af.Smo.TwistRed := by
  intro E _ _ _ n π π' χ
  refine ⟨fun hs => ?_, fun h => ?_⟩
  · filter_upwards [hs, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ)] with w ⟨B, h1, h2⟩ hu
    exact ⟨_, h1.twist hu, h2.twist hu⟩
  · have h' := h.twist χ⁻¹
    rwa [← CuspSub.twist_mul, ← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one, CuspSub.twist_one] at h'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Vanish
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem isY_map {R T : Type} [CommRing R] [CommRing T] {n m : ℕ} (φ : R →+* T) {p : GL (Fin n) R}
    (h : IsY m p.val) : IsY m (GeneralLinearGroup.map φ p).val := fun i hi =>
  ⟨by change φ (p.val i i) = 1; rw [(h i hi).1, map_one],
    fun j hj => by change φ (p.val i j) = 0; rw [(h i hi).2 j hj, map_zero]⟩

private theorem isY_one {R : Type} [CommRing R] {n m : ℕ} : IsY m (1 : GL (Fin n) R).val := fun i _ =>
  ⟨by simp, fun j hj => by simp [Matrix.one_apply_ne hj.ne']⟩

private theorem isY_mul {R : Type} [CommRing R] {n m : ℕ} {p q : GL (Fin n) R}
    (hp : IsY m p.val) (hq : IsY m q.val) : IsY m (p * q).val := by
  intro i hi
  have key : ∀ j, j ≤ i → (p * q).val i j = q.val i j := by
    intro j hj
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, (hp i hi).1, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hp i hi).2 k h, zero_mul]
      · rw [(hq k (hi.trans h.le)).2 j (hj.trans_lt h), mul_zero]
    · simp
  exact ⟨by rw [key i le_rfl, (hq i hi).1], fun j hj => by rw [key j hj.le, (hq i hi).2 j hj]⟩

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem exists_part (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (Af E)) :
    ∃ s : GL (Fin n) (Af E), SuppIn S s ∧ ∀ w ∈ S, cmp w s = cmp w g := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun w _ => map_one _, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert v S hv ih =>
    obtain ⟨s, h1, h2⟩ := ih
    refine ⟨s * locGL E n v (cmp v g), fun w hw => ?_, fun w hw => ?_⟩
    · rw [Finset.mem_insert, not_or] at hw
      rw [map_mul, h1 w hw.2, one_mul]
      exact GlobalTheory.CuspRep.pLoc_locGL_of_ne hw.1 _
    · rw [map_mul]
      rcases Finset.mem_insert.1 hw with rfl | h
      · rw [h1 w hv, one_mul]
        exact GlobalTheory.CuspRep.pLoc_locGL _ _
      · rw [h2 w h, show cmp w (locGL E n v (cmp v g)) = 1 from
          GlobalTheory.CuspRep.pLoc_locGL_of_ne (fun e : w = v => hv (e ▸ h)) _, mul_one]

private theorem af_ext {x y : Af E} (h : ∀ w, pLoc E w x = pLoc E w y) : x = y :=
  DFunLike.ext _ _ h

private theorem isY_af {m : ℕ} {s : GL (Fin n) (Af E)} (h : ∀ w, IsY m (cmp w s).val) : IsY m s.val := fun i hi =>
  ⟨af_ext fun w => by rw [map_one]; exact (h w i hi).1,
    fun j hj => af_ext fun w => by rw [map_zero]; exact (h w i hi).2 j hj⟩

private theorem pFin_finGL (k : GL (Fin n) (Af E)) : GeneralLinearGroup.map (pFin E) (finGL E n k) = k := by
  rw [finGL, GlobalTheory.CuspRep.map_cornerGL_of_hom _ _ (RingHom.id _) fun x => rfl]
  rfl

variable [IsTotallyReal E]

private theorem isY_ad {m : ℕ} {g : GA E n} (h1 : IsY m (GeneralLinearGroup.map (pInf E) g).val)
    (h2 : IsY m (GeneralLinearGroup.map (pFin E) g).val) : IsY m g.val := fun i hi =>
  ⟨TR.ad_ext (by rw [map_one]; exact (h1 i hi).1) (by rw [map_one]; exact (h2 i hi).1),
    fun j hj => TR.ad_ext (by rw [map_zero]; exact (h1 i hi).2 j hj) (by rw [map_zero]; exact (h2 i hi).2 j hj)⟩

private theorem exists_dec (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E n)
    (h1 : IsY (n - 1) (GeneralLinearGroup.map (pInf E) g).val)
    (h2 : ∀ w ∈ S, IsY (n - 1) (cmp w (GeneralLinearGroup.map (pFin E) g)).val) :
    ∃ p k, InPS S p ∧ Away S k ∧ g = p * finGL E n k := by
  obtain ⟨s, hs, hg⟩ := exists_part S (GeneralLinearGroup.map (pFin E) g)
  have e : GeneralLinearGroup.map (pFin E) (infGL E n (GeneralLinearGroup.map (pInf E) g) * finGL E n s) = s := by
    rw [map_mul, TR.pFin_infGL, pFin_finGL, one_mul]
  refine ⟨infGL E n (GeneralLinearGroup.map (pInf E) g) * finGL E n s, s⁻¹ * GeneralLinearGroup.map (pFin E) g,
    ⟨isY_ad ?_ ?_, ?_⟩, fun w hw => ?_, ?_⟩
  · rw [map_mul, TR.pInf_infGL, TR.pInf_finGL, mul_one]
    exact h1
  · rw [e]
    refine isY_af fun w => ?_
    by_cases hw : w ∈ S
    · rw [hg w hw]; exact h2 w hw
    · rw [hs w hw]; exact isY_one
  · rw [e]; exact hs
  · rw [map_mul, map_inv, hg w hw, inv_mul_cancel]
  · rw [mul_assoc, ← map_mul, mul_inv_cancel_left, TR.infGL_mul_finGL]

end

theorem UpperTheory.V.Af.Smo.vanish :
    UpperTheory.V.Af.Smo.SphAll → UpperTheory.V.Af.Smo.InjP → UpperTheory.V.Af.Smo.DenseAway → UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.Smo.EigMap → UpperTheory.V.Af.Smo.Vanish := by
  intro hSA hI hD hWB hEM E _ _ _ n hn S B f hf hS hK h0
  have hW : ∀ p, InPS S p → ∀ k, Away S k → whittaker f (p * finGL E n k) = 0 := fun p hp =>
    hSA E n S B (whittaker f) (hWB E n f hf).2.2
      (fun w hw => ⟨(hS w hw).1, (hEM E n w (B w) f (hS w hw).2).1 hf⟩)
      (fun g k hk => by
        unfold whittaker
        simp only [← mul_assoc, hK _ k hk]) p hp.2 (h0 p hp)
  have hX := hI E n hn f hf {g | IsY (n - 1) (GeneralLinearGroup.map (pInf E) g).val ∧
      ∀ w ∈ S, IsY (n - 1) (cmp w (GeneralLinearGroup.map (pFin E) g)).val}
    (fun γ hγ g hg => by
      have h : IsY (n - 1) (ratGL E n γ).val := isY_map _ hγ
      refine ⟨?_, fun w hw => ?_⟩
      · rw [map_mul]; exact isY_mul (isY_map _ h) hg.1
      · rw [map_mul, map_mul]; exact isY_mul (isY_map _ (isY_map _ h)) (hg.2 w hw))
    (fun g hg => by
      obtain ⟨p, k, hp, hk, rfl⟩ := exists_dec S g hg.1 hg.2
      exact hW p hp k hk)
  refine Continuous.ext_on (hD E n S) hf.cont continuous_const ?_
  rintro _ ⟨γ, k, hk, rfl⟩
  have h : f (finGL E n k) = 0 := hX _ ⟨by rw [TR.pInf_finGL]; exact isY_one, fun w hw => by
    rw [pFin_finGL, hk w hw]; exact isY_one⟩
  exact (hf.left γ _).trans h
end

