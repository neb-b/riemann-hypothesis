module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0003
public import GroundTheory.IdeleRoots.TorusPowers.SatakeBoundAdic
public import GroundTheory.GlobalFields.LocalFieldAtPlace

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CapZcMemOfE
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem UpperTheory.ConvolutionTheory.Dp.capZc_mem_of_e {n : ℕ} (S : Subalgebra ℂ (HarishChandra.U n))
    (h : ∀ a b, HarishChandra.e (a, b) ∈ S) (x : HarishChandra.U n) : x ∈ S := by
  induction x using HarishChandra.U.induction with
  | halg r => exact S.algebraMap_mem r
  | hι X =>
    rw [HarishChandra.ι_eq_sum_e]
    exact S.sum_mem fun a _ => S.smul_mem (h a.1 a.2) _
  | hmul a b ha hb => exact S.mul_mem ha hb
  | hadd a b ha hb => exact S.add_mem ha hb

private theorem UpperTheory.ConvolutionTheory.Dp.capZc_prod (n : ℕ) (u : ℂ) :
    (∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k) : MvPolynomial (Fin n) ℂ) =
      u ^ n • (1 : MvPolynomial (Fin n) ℂ) +
        ∑ i : Fin n, u ^ (n - (i + 1)) • MvPolynomial.esymm (Fin n) ℂ (i + 1) := by
  have h := congrArg (Polynomial.eval (MvPolynomial.C u : MvPolynomial (Fin n) ℂ))
    (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n))
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, Fintype.card_fin] at h
  rw [h, Finset.sum_range_succ', add_comm, ← Fin.sum_univ_eq_sum_range
    (fun i => MvPolynomial.esymm (Fin n) ℂ (i + 1) * MvPolynomial.C u ^ (n - (i + 1))) n]
  congr 1
  · rw [MvPolynomial.esymm_zero, MvPolynomial.smul_eq_C_mul, map_pow, Nat.sub_zero, mul_comm]
  · exact Finset.sum_congr rfl fun i _ => by rw [MvPolynomial.smul_eq_C_mul, map_pow, mul_comm]

private theorem UpperTheory.ConvolutionTheory.Dp.capZc_center {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}
    {z : Cm.UC E n} (h : ∀ τ i j, Cm.genC τ i j * z = z * Cm.genC τ i j) :
    z ∈ Subalgebra.center ℂ (Cm.UC E n) := by
  have : Algebra.adjoin ℂ {x : Cm.UC E n | ∃ τ i j, x = Cm.genC τ i j} ≤ Subalgebra.centralizer ℂ {z} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, i, j, rfl⟩ _ rfl
    exact (h τ i j).symm
  exact Subalgebra.mem_center_iff.2 fun x =>
    (this (Cm.adjoin_genC (E := E) (a := n) ▸ Algebra.mem_top) z rfl).symm

theorem UpperTheory.ConvolutionTheory.Dp.capZc :
    UpperTheory.ConvolutionTheory.Dp.CapZc := by
  intro E _ _ _ n τ
  obtain ⟨⟨j, hj⟩, hiff⟩ := UpperTheory.ConvolutionTheory.Dp.jGen E n τ
  have hg := (hiff j).1 hj
  set w : Fin n → Subalgebra.center ℂ (HarishChandra.U n) := fun i =>
    (HarishChandra.harishChandraEquiv (n := n)).symm
      ⟨MvPolynomial.esymm (Fin n) ℂ (i + 1), MvPolynomial.esymm_isSymmetric (Fin n) ℂ (i + 1)⟩ with hw
  have hzc : ∀ i : Fin n, UpperTheory.ConvolutionTheory.zc τ i = j (w i) := fun i => by
    obtain ⟨j', hj', e⟩ := Classical.epsilon_spec
      (p := fun z => ∃ j, UpperTheory.ConvolutionTheory.IsJ τ j ∧ z = j (w i : HarishChandra.U n)) ⟨_, j, hj, rfl⟩
    refine e.trans ?_
    exact capZc_mem_of_e (AlgHom.equalizer j' j) (fun a b => ((hiff j').1 hj' a b).trans (hg a b).symm) _
  have hwH : ∀ i, HarishChandra.harishChandraHom (w i) = MvPolynomial.esymm (Fin n) ℂ (i + 1) := fun i => by
    rw [← HarishChandra.harishChandraEquiv_apply, hw, AlgEquiv.apply_symm_apply]
  refine ⟨fun i => ?_, fun u => ?_⟩
  · rw [hzc]
    refine capZc_center fun σ a b => ?_
    by_cases e : σ = τ
    · subst e
      rw [← hg]
      exact (map_mul j _ _).symm.trans
        ((congrArg j (Subalgebra.mem_center_iff.1 (w i).2 _)).trans (map_mul j _ _))
    · have := capZc_mem_of_e ((Subalgebra.centralizer ℂ {Cm.genC σ a b}).comap j) (fun c d => by
        rintro _ rfl
        rw [RingHom.coe_coe, hg]
        exact Cm.commute_genC e a b c d) (w i)
      exact this _ rfl
  · obtain ⟨z, hz, hH⟩ := UpperTheory.ConvolutionTheory.Dp.capHC n u
    have e : z = u ^ n • 1 + ∑ i : Fin n, u ^ (n - (i + 1)) • w i := by
      apply HarishChandra.harishChandraHom_injective
      rw [hH, capZc_prod]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_smul, map_one, map_sum, hwH]
    have e2 := congrArg (j.comp (Subalgebra.center ℂ (HarishChandra.U n)).val) e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_smul, map_one, map_sum] at e2
    simp only [hzc]
    refine Eq.trans ?_ e2
    change _ = j (z : HarishChandra.U n)
    rw [hz, Fb.map_qdet]
    simp only [hg]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.exCusp :
    UpperTheory.ConvolutionTheory.Dp.ExCusp := by
  intro E _ _ _ n μ _ V hV
  obtain ⟨hs, hne, hirr, -⟩ := formsIrr E n μ V hV
  refine ⟨Cm.ofIrr _ hs (hs.isIrreducible_iff.2 ⟨hne, hirr⟩), ⟨hV, Cm.carrier_ofIrr _ _ _⟩, fun π h => ?_⟩
  refine GlobalTheory.CuspRep.CuspSub.ext ?_
  rw [← Cm.map_carrier π, h.carrier_eq]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExSummand
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.exSummand :
    UpperTheory.ConvolutionTheory.Dp.ExSummand := by
  intro E _ _ _ n μ _ π V
  constructor
  · intro h
    refine ⟨h.carrier_eq ▸ inf_le_left, ?_⟩
    rw [h.carrier_eq, (formsIrr E n μ V h.summand).2.2.2]
  · rintro ⟨hc, rfl⟩
    obtain ⟨hne, hirr⟩ := (Cm.stab_carrier π).isIrreducible_iff.1 (Cm.isIrreducible_toModule π)
    exact ⟨closureSummand E n μ _ hc (Cm.stab_carrier π) hne hirr, (formsClosure E n μ _ hc (Cm.stab_carrier π)).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LactCenGen
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.Dp

theorem oinf_toLp {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : TI K n) (w : CuspL2 μ) :
    Oinf μ ν β (toLp μ w) = toLp μ ((archRepT μ).integrated ν β w) := by
  refine Eq.trans ?_ (toLp_integrated_archRepT μ ν (γ := β) β.continuous β.hasCompactSupport w).symm
  rw [Oinf, UnitaryRep.integrated_ccToL1_apply]
  rfl

theorem rUC_tmul {K : Type} [Field K] [NumberField K] {n : ℕ} (c : ℂ) (p : UEnv K n) (f : (isExpLieAlgebra K n).smoothFuns (F := ℂ))
    (g : archGroup K n) : (rUC (c ⊗ₜ p) f).1 g = c * ((isExpLieAlgebra K n).rightUAction p f).1 g := by
  have h : rUC (c ⊗ₜ p) = algebraMap ℂ _ c * (isExpLieAlgebra K n).rightUAction (F := ℂ) p :=
    Algebra.TensorProduct.lift_tmul _ _ _ c p
  rw [h]
  rfl

set_option maxHeartbeats 800000 in
theorem lactCen_of_gen (K : Type) [Field K] [NumberField K] (n : ℕ)
    (hG : Subgroup.closure (Set.range (isExpLieAlgebra K n).expG) = ⊤) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : TI K n) (hβ : SmoothT β) :
    ∀ p ∈ (isExpLieAlgebra K n).centerU, ∀ q ∈ (isExpLieAlgebra K n).centerU, ∀ φ ∈ centralCuspForms K n,
      Oinf μ ν (lact ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) β) (clsL μ φ) =
        Oinf μ ν β (clsL μ (uActionCusp K n p φ + Complex.I • uActionCusp K n q φ)) := by
  intro p hp q hq φ hφ
  obtain ⟨h, hl⟩ := lactSpec K n ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) β hβ
  have hT : (isExpLieAlgebra K n).IsTestFunction β := ⟨hβ, β.hasCompactSupport⟩
  let f : (isExpLieAlgebra K n).smoothFuns (F := ℂ) := ⟨fun g => β g⁻¹, h⟩
  have e : (fun g => f.1 g⁻¹) = β := funext fun g => by simp only [f, inv_inv]
  have hf : (isExpLieAlgebra K n).IsTestFunction fun g => f.1 g⁻¹ := e ▸ hT
  have hπ : ∀ g, ‖archRepT μ g‖ ≤ 1 := fun g => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [one_mul]
    exact ((archURepT μ).norm_map g v).le
  have key : ∀ z ∈ (isExpLieAlgebra K n).centerU,
      (archRepT μ).integrated ν (fun g => ((isExpLieAlgebra K n).rightUAction z f).1 g⁻¹) (cuspVecL μ φ) =
        (archRepT μ).integrated ν β (cuspVecL μ (uActionCusp K n z φ)) := fun z hz => by
    rw [← (kernel_uAction _ ν (archRepT μ) z f hf).2, central_integrated _ ν (archRepT μ) hπ hG hz hf (isSmoothVector_cuspToL2 μ hφ),
      uAction_cuspToL2 μ hφ, e]
  have e2 : (lact ((1 : ℂ) ⊗ₜ p + Complex.I ⊗ₜ q) β : archGroup K n → ℂ) = fun g =>
      ((isExpLieAlgebra K n).rightUAction p f).1 g⁻¹ + Complex.I * ((isExpLieAlgebra K n).rightUAction q f).1 g⁻¹ := by
    funext g
    have h3 := rUC_tmul 1 p f g⁻¹
    rw [one_mul] at h3
    rw [hl g, map_add (f := _), ← h3, ← rUC_tmul Complex.I q f g⁻¹]
    rfl
  have h1 := (kernel_uAction _ ν (archRepT μ) p f hf).1
  have h2 := (kernel_uAction _ ν (archRepT μ) q f hf).1
  have h4 : ∀ (γ : TI K n) ψ, Oinf μ ν γ (clsL μ ψ) = toLp μ ((archRepT μ).integrated ν γ (cuspVecL μ ψ)) :=
    fun γ ψ => oinf_toLp μ ν γ _
  have h5 : Oinf μ ν β (clsL μ (uActionCusp K n p φ + Complex.I • uActionCusp K n q φ)) =
      Oinf μ ν β (clsL μ (uActionCusp K n p φ)) + Complex.I • Oinf μ ν β (clsL μ (uActionCusp K n q φ)) := by
    rw [(clsL μ).map_add, (clsL μ).map_smul, (Oinf μ ν β).map_add, (Oinf μ ν β).map_smul]
  rw [h5, h4, h4, h4, e2, (isExpLieAlgebra K n).integrated_add_kernel ν _ h1 (h2.const_mul _),
    IsExpLieAlgebra.integrated_const_mul_kernel, key p hp, key q hq, (toLp μ).map_add, (toLp μ).map_smul]

end UpperTheory.ConvolutionTheory.Dp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocEmb
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.locEmb :
    UpperTheory.ConvolutionTheory.Dp.LocEmb := by
  intro E _ _ _ n μ _ π V h
  have hcar := h.carrier_eq
  have hcen : ∀ ψ : Cm.carrier π, ψ.1 ∈ centralCuspForms E n := fun ψ => (hcar.le ψ.2).1
  have hV : ∀ ψ : Cm.carrier π, clsL μ ψ.1 ∈ V := fun ψ => (hcar.le ψ.2).2
  obtain ⟨hinj, -, heq, -⟩ := UpperTheory.ConvolutionTheory.Dp.clsBasic E n μ
  obtain ⟨-, -, -, hdense⟩ := UpperTheory.ConvolutionTheory.Dp.formsIrr E n μ V h.summand
  let J0 : Cm.carrier π →ₗ[ℂ] V := ((clsL μ).comp (Cm.carrier π).subtype).codRestrict V hV
  have hJ0 : ∀ ψ, (J0 ψ).1 = clsL μ ψ.1 := fun _ => rfl
  refine ⟨J0 ∘ₗ (Cm.carrierEq π).symm.toLinearMap, ?_, ?_, ?_, ?_⟩
  · have hi : Function.Injective J0 := fun a b hab => by
      have h0 : clsL μ (a.1 - b.1) = 0 := by
        rw [map_sub, ← hJ0, ← hJ0, hab, sub_self]
      exact Subtype.ext (sub_eq_zero.1 (hinj _ (Submodule.sub_mem _ (hcen a) (hcen b)) h0))
    exact hi.comp (Cm.carrierEq π).symm.injective
  · intro v
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    have himg : (Subtype.val '' Set.range (J0 ∘ₗ (Cm.carrierEq π).symm.toLinearMap) : Set (LL μ)) =
        ((formsIn μ V).map (clsL μ) : Submodule ℂ (LL μ)) := by
      ext x
      constructor
      · rintro ⟨_, ⟨φ, rfl⟩, rfl⟩
        exact ⟨_, hcar ▸ ((Cm.carrierEq π).symm φ).2, rfl⟩
      · rintro ⟨ψ, hψ, rfl⟩
        have hψ' : ψ ∈ Cm.carrier π := hcar ▸ hψ
        refine ⟨_, ⟨Cm.carrierEq π ⟨ψ, hψ'⟩, rfl⟩, ?_⟩
        simp [hJ0]
    have hc : (v : LL μ) ∈ closure (((formsIn μ V).map (clsL μ) : Submodule ℂ (LL μ)) : Set (LL μ)) :=
      hdense.ge v.2
    rw [← himg] at hc
    exact hc
  · intro ψ
    simp [hJ0]
  · intro w g φ
    obtain ⟨ψ, rfl⟩ := (Cm.carrierEq π).surjective φ
    apply Subtype.ext
    set ψ' := (Cm.carrierEq π).symm (π.locRep w g (Cm.carrierEq π ψ)) with hψ'
    have hx : ∀ x, ψ'.1.1 x = ψ.1.1 (x * finGL E n (locGL E n w g)) := fun x => by
      have h1 : Cm.carrierEq π ψ' = π.locRep w g (Cm.carrierEq π ψ) := (Cm.carrierEq π).apply_symm_apply _
      exact congrArg (fun f : π.V => f.1.1 x) h1
    have h2 := heq ψ.1 (hcen ψ) ψ'.1 (finGL E n (locGL E n w g)) hx
    show clsL μ ψ'.1 = RG μ (finGL E n (locGL E n w g)) (clsL μ ((Cm.carrierEq π).symm (Cm.carrierEq π ψ)).1)
    rw [LinearEquiv.symm_apply_apply]
    exact h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TsphVec
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

section SlopeTestRemainingChoices

open UpperTheory.ConvolutionTheory GlobalTheory.LFun Formalism.UG

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem kgl_eq (w : Pl K) : GLnLocal.integralGL (w.adicCompletion K) n = KGL w (n := n) := by
  have h : ∀ O : Subring (w.adicCompletion K), O = (ValuativeRel.valuation (w.adicCompletion K)).integer →
      GLnLocal.integralGL (w.adicCompletion K) n = GLint (Fin n) O := by
    rintro _ rfl
    rfl
  exact h _ (Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm)

private theorem diagJ_mul {L : Type} [Field L] (a b : L) (j : ℕ) : diagJ n a j * diagJ n b j = diagJ n (a * b) j := by
  rw [diagJ, diagJ, diagJ, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

private theorem diagJ_one {L : Type} [Field L] (j : ℕ) : diagJ n (1 : L) j = 1 := by
  simp [diagJ]

private theorem exists_unit (w : Pl K) {u : w.adicCompletion K} (hu : Valued.v u = 1) (j : ℕ) :
    ∃ k ∈ KGL w (n := n), (k : Matrix (Fin n) (Fin n) (w.adicCompletion K)) = diagJ n u j := by
  have h0 : u ≠ 0 := by rintro rfl; simp at hu
  have hm : ∀ x : w.adicCompletion K, Valued.v x = 1 → ∀ a b,
      diagJ n x j a b ∈ (ValuativeRel.valuation (w.adicCompletion K)).integer := fun x hx a b => by
    rw [diagJ, Matrix.diagonal_apply]
    split_ifs
    · exact (GroundTheory.Global.mem_valuationInteger_iff w x).2 hx.le
    · exact one_mem _
    · exact zero_mem _
  refine ⟨⟨diagJ n u j, diagJ n u⁻¹ j, by rw [diagJ_mul, mul_inv_cancel₀ h0, diagJ_one],
    by rw [diagJ_mul, inv_mul_cancel₀ h0, diagJ_one]⟩, ?_, rfl⟩
  rw [← kgl_eq]
  exact (GLnLocal.mem_integralGL_iff _ n).2 ⟨hm u hu, hm u⁻¹ (by rw [map_inv₀, hu, inv_one])⟩

private theorem tj_eq (w : Pl K) {ϖ ϖ₀ : w.adicCompletion K} (h : IsUnifV K w ϖ) (h₀ : IsUnifV K w ϖ₀) (j : ℕ)
    (x : GL (Fin n) (w.adicCompletion K)) (hx : (x : Matrix (Fin n) (Fin n) (w.adicCompletion K)) = diagJ n ϖ₀ j) :
    Tj ℂ n (Ov K w) ϖ j = dosetInd ℂ (KGL w (n := n)) x := by
  have h0 : ϖ₀ ≠ 0 := fun e => by simp [IsUnifV, e] at h₀
  obtain ⟨k, hk, hk'⟩ := exists_unit (n := n) w (u := ϖ₀⁻¹ * ϖ) (by
    rw [map_mul, map_inv₀, h, h₀]; exact inv_mul_cancel₀ WithZero.coe_ne_zero) j
  have e : diagJ n ϖ j = ((x * k : GL (Fin n) (w.adicCompletion K)) : Matrix (Fin n) (Fin n) (w.adicCompletion K)) := by
    rw [Units.val_mul, hx, hk', diagJ_mul, mul_inv_cancel_left₀ h0]
  unfold Tj dosetInd
  congr 1
  ext g
  rw [DoubleCoset.mem_doubleCoset, Set.mem_setOf_eq, e]
  constructor
  · rintro ⟨a, ha, b, hb, hg⟩
    refine ⟨a, ha, k * b, mul_mem hk hb, Units.ext ?_⟩
    rw [hg]; simp only [Units.val_mul, mul_assoc]
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, k⁻¹ * b, mul_mem (inv_mem hk) hb, ?_⟩
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group

private theorem out_mem_iff {G : Type} [Group G] (J : Subgroup G) (x : G) (c : G ⧸ J) :
    c.out ∈ DoubleCoset.doubleCoset x (J : Set G) J ↔ ∃ k ∈ J, c = QuotientGroup.mk (k * x) := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    exact ⟨a, ha, by rw [← c.out_eq', e]; exact QuotientGroup.mk_mul_of_mem _ hb⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul J (k * x)
    exact ⟨k, hk, b, b.2, hb⟩

variable (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K)

private theorem hop_apply (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (x : GL (Fin n) (w.adicCompletion K))
    (hJ : IsCommensurated J) {v : LL μ} (hv : v ∈ fixL μ w J) :
    Hop μ w J x v = heckeVec (localRepresentationL2 μ w) J (dosetInd ℂ J x) v := by
  classical
  have hp : prj (fixL μ w J) v = v :=
    Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure _ hv)
  have hS : {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}.Finite := by
    refine (Formalism.UG.P.finite_support_cosets (f := dosetInd ℂ J x) hJ ⟨{x}, fun g hg => ?_⟩).subset fun c hc => ?_
    · obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 (Set.mem_of_indicator_ne_zero hg)
      exact ⟨x, Finset.mem_singleton_self x, ⟨a, ha⟩, ⟨b, hb⟩, e⟩
    · simp [dosetInd, (out_mem_iff J x c).2 hc]
  rw [Hop, ContinuousLinearMap.comp_apply, hp, finsum_mem_eq_finite_toFinset_sum _ hS,
    ContinuousLinearMap.sum_apply, ← finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_def, heckeVec]
  refine finsum_congr fun c => ?_
  by_cases hc : ∃ k ∈ J, c = QuotientGroup.mk (k * x)
  · rw [Set.indicator_of_mem (by exact hc), dosetInd, Set.indicator_of_mem ((out_mem_iff J x c).2 hc), rhoLoc]
    simp
  · rw [Set.indicator_of_notMem (by exact hc), dosetInd, Set.indicator_of_notMem (mt (out_mem_iff J x c).1 hc),
      zero_smul]

private theorem mem_fixL (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (v : LL μ) :
    v ∈ fixL μ w J ↔ ∀ k ∈ J, localRepresentationL2 μ w k v = v := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, Subgroup.mem_map]
  constructor
  · intro h k hk
    rw [← rhoLoc]
    exact h _ ⟨k, hk, rfl⟩
  · rintro h _ ⟨k, hk, rfl⟩
    exact (rhoLoc K n μ w k v).trans (h k hk)

private theorem scal (B : Multiset ℂˣ) (i : Fin n) (y v : LL μ) :
    (((Ideal.absNorm w.asIdeal : ℝ) ^ (-((((i : ℕ) + 1) * (n - ((i : ℕ) + 1)) : ℕ) : ℝ) / 2) : ℝ) : ℂ) • y =
      (B.map fun b : ℂˣ => (b : ℂ)).esymm (i + 1) • v ↔ y = satEig (qV K w) n B (i + 1) • v := by
  have hq : (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (qV_ne_zero w))
  have he : (qV K w : ℂ) ^ (((((i : ℕ) + 1 : ℕ) : ℂ) * ((n : ℂ) - (((i : ℕ) + 1 : ℕ) : ℂ))) / 2) =
      ((((Ideal.absNorm w.asIdeal : ℝ) ^ (-((((i : ℕ) + 1) * (n - ((i : ℕ) + 1)) : ℕ) : ℝ) / 2) : ℝ) : ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv, ← Real.rpow_neg hq.le, Complex.ofReal_cpow hq.le, qV]
    congr 1
    push_cast [Nat.cast_sub (Nat.succ_le_of_lt i.2)]
    ring
  rw [satEig, he, mul_smul, eq_inv_smul_iff₀ (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne')]

private theorem tsph_iff {V : Submodule ℂ (LL μ)} (hV : IsSummand μ V) (B : Multiset ℂˣ) (v : V)
    (hv : (v : LL μ) ∈ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n)) {ϖ : w.adicCompletion K}
    (h : IsUnifV K w ϖ) (i : Fin n) :
    Tsph μ w i v = (B.map fun b : ℂˣ => (b : ℂ)).esymm (i + 1) • (v : LL μ) ↔
      heckeVec (locOn hV w) (KGL w (n := n)) (Tj ℂ n (Ov K w) ϖ (i + 1)) v = satEig (qV K w) n B (i + 1) • v := by
  have e := map_heckeVec (ρ := locOn hV w) (ρ' := localRepresentationL2 μ w) (Final.GLintComm K w n) (Tj_mem_hecke h (i + 1))
    V.subtype (fun _ _ => rfl) v
  have ht := tj_eq w h (GroundTheory.BlockD.SatakeBound.valued_uniformizer_eq w) (i + 1)
    (Cartan.diagPow (w.adicCompletion K) n fun a => if a ≤ i then 1 else 0) (by
      rw [Cartan.coe_diagPow, diagJ]
      congr 1
      funext a
      by_cases ha : a ≤ i
      · rw [if_pos ha, if_pos (Nat.lt_succ_of_le ha), zpow_one]
      · rw [if_neg ha, if_neg (fun h' => ha (Nat.le_of_lt_succ h')), zpow_zero])
  rw [kgl_eq] at hv
  rw [Tsph, ContinuousLinearMap.smul_apply, scal, kgl_eq, hop_apply μ w _ _ (Final.GLintComm K w n) hv, ← ht]
  exact ⟨fun h' => Subtype.ext (e.trans h'), fun h' => e.symm.trans (congrArg Subtype.val h')⟩

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.Dp.tsphVec :
    UpperTheory.ConvolutionTheory.Dp.TsphVec := by
  intro K _ _ n μ _ w V hV B
  have hf : ∀ v : V, v ∈ GlobalTheory.PRep.fixed (locOn hV w) (GlobalTheory.LFun.KGL w (n := n)) ↔
      (v : LL μ) ∈ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n) := fun v => by
    rw [GlobalTheory.LGrp.mem_fixed, mem_fixL, kgl_eq]
    exact forall₂_congr fun k _ => Subtype.ext_iff
  obtain ⟨ϖ₀, h₀⟩ := GlobalTheory.LFun.exists_isUnifV w
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.exists_vec
    refine ⟨by rw [Multiset.card_map, h.card], (Submodule.ne_bot_iff _).2
      ⟨x, ⟨x.2, (hf x).1 hx.2.1⟩, fun e => hx.1 (Subtype.ext e)⟩, fun i v hv => ?_⟩
    by_cases h0 : v = 0
    · simp [h0]
    · exact (tsph_iff μ w hV B ⟨v, hv.1⟩ hv.2 h₀ i).2
        ((h.2 ⟨v, hv.1⟩ ((hf _).2 hv.2) fun e => h0 (congrArg Subtype.val e)).2.2.2 ϖ₀ h₀ _ i.2)
  · rintro ⟨hc, hne, h⟩
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hne
    refine ⟨(Submodule.ne_bot_iff _).2 ⟨⟨v, hv.1⟩, (hf _).2 hv.2, fun e => h0 (congrArg Subtype.val e)⟩,
      fun x hx hx0 => ⟨hx0, hx, by rwa [Multiset.card_map] at hc, fun ϖ hϖ j hj => ?_⟩⟩
    rcases j with _ | j
    · rw [tj_eq w hϖ hϖ 0 1 (by simp [Formalism.UG.diagJ]),
        GlobalTheory.LFun.heckeVec_dosetInd (R := {1}) hx (by simpa using DoubleCoset.mem_doubleCoset_self _ _ _) ?_]
      · simp [GlobalTheory.LFun.satEig, Multiset.esymm]
      · intro g hg
        obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
        exact ⟨1, ⟨Finset.mem_singleton_self _, by simpa using mul_mem ha hb⟩,
          fun y hy => Finset.mem_singleton.1 hy.1⟩
    · exact (tsph_iff μ w hV B x ((hf x).1 hx) hϖ ⟨j, hj⟩).1 (h ⟨j, hj⟩ x ⟨x.2, (hf x).1 hx⟩)
end

