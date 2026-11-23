module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Bundle0001
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistUnitary

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LactSpec
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.lactSpec :
    UpperTheory.ConvolutionTheory.Dp.LactSpec := by
  intro K _ _ n u β hβ
  obtain ⟨h, hl, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β hβ
  exact ⟨h, hl u⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.OrthOrIso
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem le_or_iso {M I : Type} [AddCommGroup M] [Module ℂ M] (A : I → M →ₗ[ℂ] M) (U U' C : Submodule ℂ M)
    (hU : ∀ i, ∀ x ∈ U, A i x ∈ U) (hU' : ∀ i, ∀ x ∈ U', A i x ∈ U') (hC : ∀ i, ∀ x ∈ C, A i x ∈ C)
    (hi : ∀ W ≤ U, (∀ i, ∀ x ∈ W, A i x ∈ W) → W = ⊥ ∨ W = U) (hi' : ∀ W ≤ U', (∀ i, ∀ x ∈ W, A i x ∈ W) → W = ⊥ ∨ W = U')
    (hd : U' ⊓ C = ⊥) (hle : U ≤ U' ⊔ C) :
    U ≤ C ∨ ∃ T : U ≃ₗ[ℂ] U', ∀ i (φ ψ : U), ψ.1 = A i φ.1 → (T ψ).1 = A i (T φ).1 := by
  have uniq : ∀ (x : M) (a b : U'), x - a ∈ C → x - b ∈ C → a = b := fun x a b ha hb => by
    have h1 : (a : M) - b ∈ U' ⊓ C := ⟨U'.sub_mem a.2 b.2, by simpa using C.sub_mem hb ha⟩
    rw [hd, Submodule.mem_bot, sub_eq_zero] at h1
    exact Subtype.ext h1
  have ex : ∀ x : U, ∃ a : U', (x : M) - a ∈ C := fun x => by
    obtain ⟨a, ha, c, hc, e⟩ := Submodule.mem_sup.1 (hle x.2)
    exact ⟨⟨a, ha⟩, by rw [← e]; simpa using hc⟩
  choose p hp using ex
  let P : U →ₗ[ℂ] U' :=
    { toFun := p
      map_add' := fun x y => uniq _ _ _ (hp _) (by
        have := C.add_mem (hp x) (hp y)
        rwa [sub_add_sub_comm] at this)
      map_smul' := fun c x => uniq _ _ _ (hp _) (by
        have := C.smul_mem c (hp x)
        rwa [smul_sub] at this) }
  have hP : ∀ i (φ ψ : U), ψ.1 = A i φ.1 → (P ψ).1 = A i (P φ).1 := fun i φ ψ e =>
    congrArg Subtype.val (uniq ψ.1 (p ψ) ⟨_, hU' i _ (p φ).2⟩ (hp ψ) (by rw [e, ← map_sub]; exact hC i _ (hp φ)))
  rcases hi (U ⊓ C) inf_le_left fun i x hx => ⟨hU i x hx.1, hC i x hx.2⟩ with h0 | h0
  · have hinj : Function.Injective P := (injective_iff_map_eq_zero P).2 fun x hx => by
      have h1 := hp x
      rw [show p x = 0 from hx] at h1
      have h2 : x.1 ∈ U ⊓ C := ⟨x.2, by simpa using h1⟩
      rw [h0] at h2
      exact Subtype.ext h2
    rcases hi' ((LinearMap.range P).map U'.subtype) (Submodule.map_subtype_le _ _) (by
      rintro i _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, ⟨⟨_, hU i _ x.2⟩, rfl⟩, hP i x _ rfl⟩) with h1 | h1
    · refine Or.inl fun x hx => ?_
      have h2 : (P ⟨x, hx⟩).1 ∈ (LinearMap.range P).map U'.subtype := ⟨_, ⟨_, rfl⟩, rfl⟩
      rw [h1, Submodule.mem_bot] at h2
      have h3 := hp ⟨x, hx⟩
      rw [show (p ⟨x, hx⟩).1 = 0 from h2] at h3
      simpa using h3
    · refine Or.inr ⟨LinearEquiv.ofBijective P ⟨hinj, fun y => ?_⟩, hP⟩
      obtain ⟨_, ⟨x, rfl⟩, e⟩ := h1.ge y.2
      exact ⟨x, Subtype.ext e⟩
  · exact Or.inl (inf_eq_left.1 h0)

theorem UpperTheory.ConvolutionTheory.Dp.orthOrIso :
    UpperTheory.ConvolutionTheory.Dp.OrthOrIso := by
  intro K _ _ n μ _ U U' l l' hs hs' hi hi'
  obtain ⟨C, hC, hsup, horth⟩ := UpperTheory.V.Af.StrongMultiplicityOne.compl K n μ U' l' hs'
  have hinf : U' ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨ha, haC⟩
    have hzero := horth a ha a haC
    rw [inner_self_eq_zero] at hzero
    exact (Submodule.mem_bot ℂ).2 (CuspidalSpectrum.eq_zero_of_cuspVecL_eq_zero (μ := μ) (l' ha) hzero)
  let A : ((isExpLieAlgebra K n).lieSubalgebra ⊕ archCompact K n ⊕ AdelicGLn.FiniteAdelicGL K n) → cuspForms K n →ₗ[ℂ] cuspForms K n :=
    Sum.elim (fun X => (gkModuleCusp K n).ρ X) (Sum.elim (fun k => (gkModuleCusp K n).σ k) fun g => finRepCusp K n g)
  have hA : ∀ W, Fb.Stab W ↔ ∀ i, ∀ x ∈ W, A i x ∈ W := fun W =>
    ⟨fun h i => by
      rcases i with X | k | g
      exacts [h.ρ X, h.σ k, h.τ g], fun h => ⟨fun X => h (.inl X), fun k => h (.inr (.inl k)), fun g => h (.inr (.inr g))⟩⟩
  rcases le_or_iso A U U' C ((hA _).1 hs) ((hA _).1 hs') ((hA _).1 hC) (fun W h1 h2 => hi W h1 ((hA _).2 h2))
    (fun W h1 h2 => hi' W h1 ((hA _).2 h2)) hinf (l.trans hsup.ge) with h | ⟨T, hT⟩
  · refine Or.inl (Submodule.IsOrtho.symm ?_)
    rw [Submodule.isOrtho_iff_inner_eq]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact horth a ha b (h hb)
  · exact Or.inr ⟨T, fun X => hT (.inl X), fun k => hT (.inr (.inl k)), fun g => hT (.inr (.inr g))⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.RhoLoc
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem localEmbedding_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) (w.adicCompletion K)) :
    AdelicGLn.localEmbedding w g = locGL K n w g := by
  classical
  refine Units.ext <| Matrix.ext fun a b => FiniteAdeleRing.ext K fun v => ?_
  change ((AdelicGLn.finiteRestrictedEquiv K n).symm _ : AdelicGLn.FiniteAdelicGL K n) a b v = _
  rw [AdelicGLn.finiteRestrictedEquiv_symm_apply, RestrictedProduct.coe_mulSingle_apply]
  by_cases h : v = w
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (GlobalTheory.CuspRep.pLoc_locGL v g)).symm
  · rw [Pi.mulSingle_eq_of_ne h]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (GlobalTheory.CuspRep.pLoc_locGL_of_ne h g)).symm

private theorem finProj_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (u : AdelicGLn.FiniteAdelicGL K n) :
    MultiplicityOne.finProj K n u = retractOne (finGL K n u) := by
  rw [← Fb.finEmb_eq]
  exact Subtype.ext rfl

theorem UpperTheory.ConvolutionTheory.Dp.rhoLoc :
    UpperTheory.ConvolutionTheory.Dp.RhoLoc := by
  intro K _ _ n μ _ w g v
  change rightRegularRep (rationalGLOne (K := K) (n := n)) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) v =
    rightRegularRep (rationalGLOne (K := K) (n := n)) μ (retractOne (finGL K n (locGL K n w g))) v
  rw [finProj_eq, localEmbedding_eq]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatUnit
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem eq_of_esymm {n : ℕ} {B B' : Multiset ℂ} (hB : B.card = n) (hB' : B'.card = n)
    (h : ∀ i : Fin n, B.esymm (i + 1) = B'.esymm (i + 1)) : B = B' := by
  have h2 : (B.map fun r => Polynomial.X - Polynomial.C r).prod = (B'.map fun r => Polynomial.X - Polynomial.C r).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hB, hB']
    refine Finset.sum_congr rfl fun j hj => ?_
    rcases j with _ | j
    · simp [Multiset.esymm]
    · rw [h ⟨j, by simpa using hj⟩]
  simpa using congrArg Polynomial.roots h2

open UpperTheory.ConvolutionTheory in
theorem UpperTheory.ConvolutionTheory.Dp.sSatUnit :
    UpperTheory.ConvolutionTheory.Dp.SSatUnit := by
  intro K _ _ n μ _ w V B hB
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hB.2.1
  refine ⟨?_, fun B₁ h₁ => eq_of_esymm h₁.1 hB.1 fun i =>
    smul_left_injective ℂ h0 ((h₁.2.2 i v hv).symm.trans (hB.2.2 i v hv))⟩
  have hne : ∀ b ∈ B, b ≠ 0 := by
    intro b hb e
    subst e
    have hn : 0 < n := hB.1 ▸ Multiset.card_pos_iff_exists_mem.2 ⟨_, hb⟩
    have h1 := hB.2.2 ⟨n - 1, by omega⟩ v hv
    have h2 : B.esymm (n - 1 + 1) = 0 := by
      rw [Nat.sub_add_cancel hn, ← hB.1, Multiset.esymm, Multiset.powersetCard_self]
      simpa using hb
    set J := GLnLocal.integralGL (w.adicCompletion K) n
    set x := Cartan.diagPow (w.adicCompletion K) n fun _ => 1 with hx
    have hxc : x ∈ Subgroup.center _ :=
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2 ⟨_, by rw [Matrix.scalar_apply, hx, Cartan.coe_diagPow]⟩
    have e1 : (fun a : Fin n => if a ≤ (⟨n - 1, by omega⟩ : Fin n) then (1 : ℤ) else 0) = fun _ => 1 :=
      funext fun a => if_pos (Fin.le_def.2 (by have := a.2; simp only; omega))
    have e2 : {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} = {QuotientGroup.mk x} := by
      ext c
      constructor
      · rintro ⟨k, hk, rfl⟩
        rw [Subgroup.mem_center_iff.1 hxc k]
        exact QuotientGroup.mk_mul_of_mem x hk
      · rintro rfl
        exact ⟨1, J.one_mem, by rw [one_mul]⟩
    have e3 : prj (fixL μ w J) v = v :=
      Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure _ hv.2)
    have e4 : Hop μ w J x v = rhoL μ w (QuotientGroup.mk x : _ ⧸ J).out v := by
      rw [Hop, e2, finsum_mem_singleton, ContinuousLinearMap.comp_apply, e3]
    rw [h2, zero_smul, Tsph, e1, ContinuousLinearMap.smul_apply, e4] at h1
    rcases smul_eq_zero.1 h1 with h | h
    · refine (Real.rpow_pos_of_pos ?_ _).ne' (Complex.ofReal_eq_zero.1 h)
      exact Nat.cast_pos.2 (Nat.pos_of_ne_zero fun e => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 e))
    · refine h0 (norm_eq_zero.1 ?_)
      have h3 : ∀ g, ‖rhoF μ g v‖ = ‖v‖ := fun g => by
        unfold rhoF
        exact UnitaryRep.norm_map _ _ v
      rw [← h3, ← rhoL, h, norm_zero]
  refine ⟨B.attach.map fun b => Units.mk0 b.1 (hne b.1 b.2), ?_⟩
  rw [Multiset.map_map]
  exact (Multiset.attach_map_val B).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TwCls
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.twCls :
    UpperTheory.ConvolutionTheory.Dp.TwCls := by
  intro K _ _ n μ _ θ φ hφ ψ hψ
  have hmemS : ∀ g, θ.e.symm g ∈ rationalGLOne (K := K) (n := n) ↔ g ∈ rationalGLOne (K := K) (n := n) := fun g => by
    have h := θ.mem_gam (θ.e.symm g)
    rw [ContinuousMulEquiv.apply_symm_apply] at h
    exact h.symm
  have hpresS : MeasurePreserving θ.e.symm μ μ :=
    MeasurePreserving.symm θ.e.toHomeomorph.toMeasurableEquiv θ.pres
  obtain ⟨hmk, hT⟩ := UpperTheory.ConvolutionTheory.K.qmapPres (rationalGLOne (K := K) (n := n)) μ θ.e.symm hmemS hpresS
  let T : RightCosetSpace (rationalGLOne (K := K) (n := n)) → RightCosetSpace (rationalGLOne (K := K) (n := n)) :=
    fun y => mk _ (θ.e.symm (Quotient.out y))
  have hTmk : ∀ x, T (mk _ x) = mk _ (θ.e.symm x) := hmk
  have hTc : Continuous T := by
    refine (isOpenQuotientMap_mk (rationalGLOne (K := K) (n := n))).isQuotientMap.continuous_iff.2 ?_
    have h : T ∘ mk _ = mk _ ∘ θ.e.symm := funext hTmk
    rw [h]
    exact (continuous_mk _).comp θ.e.symm.continuous
  let Φ := cuspQuot φ.2.1.isLeftInvariant
  let Ψ := cuspQuot ψ.2.1.isLeftInvariant
  have hΦc : Continuous Φ := continuous_cuspQuot _ φ.2.1.continuous
  have hΨc : Continuous Ψ := continuous_cuspQuot _ ψ.2.1.continuous
  have hb := (UpperTheory.ConvolutionTheory.Dp.clsBasic K n μ).2.2.2
  have hout : ∀ (χ : cuspForms K n) (y : RightCosetSpace (rationalGLOne (K := K) (n := n))),
      χ.1 ((Quotient.out y : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) =
        cuspQuot χ.2.1.isLeftInvariant y := fun χ y => by
    have h : mk (rationalGLOne (K := K) (n := n)) (Quotient.out y) = y := Quotient.out_eq y
    conv_rhs => rw [← h]
    rw [cuspQuot_mk]
  have hφa : (clsL μ φ : RightCosetSpace (rationalGLOne (K := K) (n := n)) → ℂ)
      =ᵐ[quotientMeasure (rationalGLOne (K := K) (n := n)) μ] Φ :=
    (hb φ hφ).trans (Filter.Eventually.of_forall (hout φ))
  have hψa : (clsL μ ψ : RightCosetSpace (rationalGLOne (K := K) (n := n)) → ℂ)
      =ᵐ[quotientMeasure (rationalGLOne (K := K) (n := n)) μ] Ψ :=
    (hb ψ hψ).trans (Filter.Eventually.of_forall (hout ψ))
  have hU : (θ.U (clsL μ ψ) : RightCosetSpace (rationalGLOne (K := K) (n := n)) → ℂ)
      =ᵐ[quotientMeasure (rationalGLOne (K := K) (n := n)) μ] Ψ ∘ T :=
    (θ.U_spec _).trans (hT.quasiMeasurePreserving.ae_eq_comp hψa)
  constructor
  · intro h x
    have h1 : Ψ ∘ T =ᵐ[quotientMeasure (rationalGLOne (K := K) (n := n)) μ] Φ := by
      rw [h] at hU
      exact hU.symm.trans hφa
    have h2 : Ψ ∘ T = Φ := (Continuous.ae_eq_iff_eq _ (hΨc.comp hTc) hΦc).1 h1
    have h3 := congrFun h2 (mk _ (θ.e x))
    simp only [Function.comp_apply, hTmk, ContinuousMulEquiv.symm_apply_apply] at h3
    simpa only [Ψ, Φ, cuspQuot_mk] using h3
  · intro h
    have h2 : Ψ ∘ T = Φ := by
      funext y
      obtain ⟨x, rfl⟩ := mk_surjective _ y
      simp only [Function.comp_apply, hTmk, Ψ, Φ, cuspQuot_mk]
      rw [h, ContinuousMulEquiv.apply_symm_apply]
    rw [h2] at hU
    exact Lp.ext (hU.trans hφa.symm)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TwUnitary
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.twUnitary :
    UpperTheory.ConvolutionTheory.Dp.TwUnitary := by
  intro K _ _ n μ _ θ
  obtain ⟨U, hU, hint, -⟩ := UpperTheory.ConvolutionTheory.C.twistUnitary K n μ θ
  have h : ∀ v, θ.U v = U v := fun v => by rw [← hU]; rfl
  refine ⟨fun v => ?_, fun w => ?_, fun g v => ?_⟩
  · rw [h]; exact U.norm_map v
  · obtain ⟨v, hv⟩ := U.surjective w
    exact ⟨v, (h v).trans hv⟩
  · rw [h, h]; exact hint g v
end

