module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LineRank
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0005
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LactTens
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Fx
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

namespace UpperTheory.ConvolutionTheory.L1

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {m : ℕ} {D : InfD σ m} {n : ℕ}

private theorem prod_upd (φ : Fin (m + 1) → TI F n) (k : Fin (m + 1)) (x : TI F n)
    (c : Fin (m + 1) → archGroup F n) :
    ∏ i, (Function.update φ k x i) (c i) = x (c k) * ∏ i ∈ Finset.univ.erase k, φ i (c i) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

private theorem tens_lin {φ : Fin (m + 1) → TI F n} {k : Fin (m + 1)} {x y : TI F n} {b c : TI E n}
    (r s : ℂ) (hx : IsTens D (Function.update φ k x) b) (hy : IsTens D (Function.update φ k y) c) :
    IsTens D (Function.update φ k (r • x + s • y)) (r • b + s • c) := by
  intro g
  have h1 := hx g
  have h2 := hy g
  rw [prod_upd] at h1 h2 ⊢
  simp only [CompactlySupportedContinuousMap.add_apply, CompactlySupportedContinuousMap.smul_apply,
    smul_eq_mul, h1, h2]
  ring

end

private theorem zc_eq {K : Type} [Field K] [NumberField K] {n : ℕ} {τ : K →+* ℂ}
    {j : HarishChandra.U n →ₐ[ℂ] UC K n} (hj : IsJ τ j)
    (hu : ∀ j', IsJ τ j' → j' = j) (i : Fin n) :
    zc τ i = j ((HarishChandra.harishChandraEquiv (n := n)).symm
      ⟨MvPolynomial.esymm (Fin n) ℂ (i + 1), MvPolynomial.esymm_isSymmetric (Fin n) ℂ (i + 1)⟩ :
        Subalgebra.center ℂ (HarishChandra.U n)) := by
  obtain ⟨j', hj', h⟩ := Classical.epsilon_spec (p := fun z : UC K n => ∃ j, IsJ τ j ∧
    z = j ((HarishChandra.harishChandraEquiv (n := n)).symm
      ⟨MvPolynomial.esymm (Fin n) ℂ (i + 1), MvPolynomial.esymm_isSymmetric (Fin n) ℂ (i + 1)⟩ :
        Subalgebra.center ℂ (HarishChandra.U n))) ⟨_, j, hj, rfl⟩
  rw [hu j' hj'] at h
  exact h

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.lactTens :
    UpperTheory.ConvolutionTheory.L1.LactTens := by
  intro F E _ _ _ _ _ _ _ σ m D n τ k hk φ₀ β₀ hs₀ ht₀ i
  obtain ⟨⟨jE, hjE, uE⟩, -⟩ := UpperTheory.ConvolutionTheory.L1.jUnique E n τ
  obtain ⟨⟨jF, hjF, uF⟩, -⟩ := UpperTheory.ConvolutionTheory.L1.jUnique F n (τ.comp (algebraMap F E))
  have key : ∀ u : HarishChandra.U n, ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
      IsTens D (Function.update φ k (lact (jF u) (φ k))) (lact (jE u) β) := by
    have sm : ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β → SmoothT β :=
      fun φ β hs ht => (UpperTheory.ConvolutionTheory.L1.tensSmooth F E σ m D n φ β ht).1 hs
    have halg : ∀ r : ℂ, ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
        IsTens D (Function.update φ k (lact (jF (algebraMap ℂ _ r)) (φ k))) (lact (jE (algebraMap ℂ _ r)) β) := by
      intro r φ β hs ht
      obtain ⟨-, h1, -, -, hc⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws E n β (sm φ β hs ht)
      obtain ⟨-, h1', -, -, hc'⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws F n (φ k) (hs k)
      rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hc, hc', h1, h1']
      intro g
      have h := ht g
      rw [prod_upd, CompactlySupportedContinuousMap.smul_apply, CompactlySupportedContinuousMap.smul_apply, h,
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), smul_eq_mul, smul_eq_mul, mul_assoc]
    have hadd : ∀ a b : HarishChandra.U n,
        (∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
          IsTens D (Function.update φ k (lact (jF a) (φ k))) (lact (jE a) β)) →
        (∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
          IsTens D (Function.update φ k (lact (jF b) (φ k))) (lact (jE b) β)) →
        ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
          IsTens D (Function.update φ k (lact (jF (a + b)) (φ k))) (lact (jE (a + b)) β) := by
      intro a b ha hb φ β hs ht
      obtain ⟨-, -, -, hp, -⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws E n β (sm φ β hs ht)
      obtain ⟨-, -, -, hp', -⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws F n (φ k) (hs k)
      rw [map_add (f := _), map_add (f := _), hp, hp']
      simpa using tens_lin (D := D) 1 1 (ha φ β hs ht) (hb φ β hs ht)
    have hmul : ∀ a b : HarishChandra.U n,
        (∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
          IsTens D (Function.update φ k (lact (jF a) (φ k))) (lact (jE a) β)) →
        (∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
          IsTens D (Function.update φ k (lact (jF b) (φ k))) (lact (jE b) β)) →
        ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
          IsTens D (Function.update φ k (lact (jF (a * b)) (φ k))) (lact (jE (a * b)) β) := by
      intro a b ha hb φ β hs ht
      obtain ⟨-, -, hm, -, -⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws E n β (sm φ β hs ht)
      obtain ⟨hsu, -, hm', -, -⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws F n (φ k) (hs k)
      have hs' : ∀ i, SmoothT (Function.update φ k (lact (jF b) (φ k)) i) := by
        intro i
        by_cases h : i = k
        · subst h; rw [Function.update_self]; exact hsu _
        · rw [Function.update_of_ne h]; exact hs i
      have := ha _ _ hs' (hb φ β hs ht)
      rw [Function.update_self, Function.update_idem] at this
      rw [map_mul, map_mul, hm, hm']
      exact this
    have hgen : ∀ (p : Fin n × Fin n) (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
        IsTens D (Function.update φ k (lact (jF (HarishChandra.e p)) (φ k))) (lact (jE (HarishChandra.e p)) β) := by
      rintro ⟨a, b⟩ φ β hs ht
      obtain ⟨-, -, -, hp, hc⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws E n β (sm φ β hs ht)
      obtain ⟨-, -, -, hp', hc'⟩ := UpperTheory.ConvolutionTheory.L1.lactLaws F n (φ k) (hs k)
      have form : ∀ {K : Type} [Field K] [NumberField K] (t : K →+* ℂ),
          (2⁻¹ : ℂ) ⊗ₜ[ℝ] elem t a b 1 - (2⁻¹ * Complex.I) ⊗ₜ[ℝ] elem t a b Complex.I =
            (2⁻¹ : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] elem t a b 1) + (-(2⁻¹ * Complex.I)) • ((1 : ℂ) ⊗ₜ[ℝ] elem t a b Complex.I) := by
        intro K _ _ t
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one,
          TensorProduct.neg_tmul, sub_eq_add_neg]
      rw [hjE a b, hjF a b, form, form, hp, hp', hc, hc, hc', hc']
      exact tens_lin (D := D) _ _ (UpperTheory.ConvolutionTheory.L1.lactGen F E σ m D n τ k hk φ β hs ht a b 1)
        (UpperTheory.ConvolutionTheory.L1.lactGen F E σ m D n τ k hk φ β hs ht a b Complex.I)
    intro u
    refine HarishChandra.U.induction halg ?_ hmul hadd u
    intro x
    rw [HarishChandra.ι_eq_sum_e]
    refine Finset.sum_induction _ (fun v => ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β →
      IsTens D (Function.update φ k (lact (jF v) (φ k))) (lact (jE v) β)) hadd ?_ ?_
    · simpa using halg 0
    · intro p _
      rw [Algebra.smul_def]
      exact hmul _ _ (halg _) (hgen p)
  rw [UpperTheory.ConvolutionTheory.L1.zc_eq hjE uE i, UpperTheory.ConvolutionTheory.L1.zc_eq hjF uF i]
  exact key _ φ₀ β₀ hs₀ ht₀
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SphRank
section
open MeasureTheory GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C

theorem UpperTheory.ConvolutionTheory.L1.sphRank :
    UpperTheory.ConvolutionTheory.L1.SphRank := by
  intro K _ _ n μ _ V hV w
  letI : MeasurableSpace (Gw n w) := borel _
  haveI : BorelSpace (Gw n w) := ⟨rfl⟩
  obtain ⟨⟨σ, hσ⟩, -, -⟩ := UpperTheory.ConvolutionTheory.C.occursBasics K n μ V w Measure.haar hV
  have hmem : ∀ x : σ.V, (∀ g ∈ GLnLocal.integralGL (w.adicCompletion K) n,
      σ.ρ g x = (1 : Gw n w → ℂ) g • x) → x ∈ fixedVectors σ.ρ (GLnLocal.integralGL (w.adicCompletion K) n) := by
    intro x hx
    exact fun g hg => by simpa using hx g hg
  refine UpperTheory.ConvolutionTheory.L1.lineRank K n μ V hV w σ hσ _ 1
    ⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩
    ⟨IsLocallyConstant.const 1, fun _ _ => by simp, fun _ _ _ _ => by simp⟩ ?_
  by_cases h : fixedVectors σ.ρ (GLnLocal.integralGL (w.adicCompletion K) n) = ⊥
  · refine ⟨0, fun x hx => ⟨0, ?_⟩⟩
    have hx' := hmem x hx
    rw [h] at hx'
    simpa using hx'
  · haveI := σ.irred
    obtain ⟨e, -, hall⟩ := finrank_eq_one_iff'.1 (Spherical.finrank_fixedVectors_eq_one σ.smooth h)
    refine ⟨e, fun x hx => ?_⟩
    obtain ⟨c, hc⟩ := hall ⟨x, hmem x hx⟩
    exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ZBasic
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped ComplexConjugate Classical

namespace UpperTheory.ConvolutionTheory.L1

private theorem list_prod_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (L : List (H →L[ℂ] H)) (v : H) (c : ℂ)
    (h : ∀ A ∈ L, A v = c • v) : L.prod v = c ^ L.length • v := by
  induction L with
  | nil => simp
  | cons A L ih =>
    have h1 := ih fun B hB => h B (List.mem_cons_of_mem _ hB)
    rw [List.prod_cons, ContinuousLinearMap.mul_apply, h1, map_smul, h A List.mem_cons_self, smul_smul, List.length_cons,
      pow_succ]

section One
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

private theorem mem_eigL' (w : Pl K) (J : Subgroup (Gw n w)) (χ : Gw n w → ℂ) (v : LL μ) :
    v ∈ eigL μ w J χ ↔ ∀ x ∈ J, rhoL μ w x v = χ x • v := by
  simp only [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
    LinearMap.id_apply]

private theorem mem_fixL' (w : Pl K) (J : Subgroup (Gw n w)) (v : LL μ) :
    v ∈ fixL μ w J ↔ ∀ x ∈ J, rhoL μ w x v = v := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply,
    Subgroup.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, rhoL]

private theorem rhoL_comm {w w' : Pl K} (hne : w' ≠ w) (g : Gw n w) (x : Gw n w') (v : LL μ) :
    rhoL μ w' x (rhoL μ w g v) = rhoL μ w g (rhoL μ w' x v) := by
  have h := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' hne g x
  simp only [rhoL, rhoF]
  rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, ← map_mul, ← map_mul, h]

private theorem archP_finProj_comm (a : archGroup K n) (h : AdelicGLn.FiniteAdelicGL K n) :
    archP K n a * MultiplicityOne.finProj K n h = MultiplicityOne.finProj K n h * archP K n a :=
  (MultiplicityOne.finProj_mul_archProj_comm h a).symm

end One

section Grp
variable {G : Type} [Group G] [TopologicalSpace G]

private theorem chr_one {J : Subgroup G} {χ : G → ℂ} (h : IsChr J χ) : χ 1 = 1 := by
  have h1 := h.2.2 1 J.one_mem 1 J.one_mem
  have h2 : χ 1 ≠ 0 := fun h0 => by
    have := h.2.1 1 J.one_mem
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  rw [mul_one] at h1
  exact mul_left_cancel₀ h2 (by rw [← h1, mul_one])

private def kerS (J : Subgroup G) (χ : G → ℂ) (h : IsChr J χ) : Subgroup G where
  carrier := {x | x ∈ J ∧ χ x = 1}
  one_mem' := ⟨J.one_mem, chr_one h⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨J.mul_mem ha hb, by rw [h.2.2 a ha b hb, ha', hb', one_mul]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨J.inv_mem ha, ?_⟩
    have h1 := h.2.2 a ha a⁻¹ (J.inv_mem ha)
    rwa [mul_inv_cancel, chr_one h, ha', one_mul, eq_comm] at h1

private theorem kerS_co {J : Subgroup G} {χ : G → ℂ} (hJ : CO J) (h : IsChr J χ) : CO (kerS J χ h) := by
  have e : (kerS J χ h : Set G) = (J : Set G) ∩ χ ⁻¹' {1} := rfl
  have ho : IsOpen (χ ⁻¹' {(1 : ℂ)}) := h.1.isOpen_fiber 1
  have hc : IsClosed (χ ⁻¹' {(1 : ℂ)}) := isClosed_singleton.preimage h.1.continuous
  rw [CO, e]
  exact ⟨hJ.1.inter_right hc, hJ.2.inter ho⟩

end Grp

section Two
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {n m : ℕ} {q : Pl F} {w₀ : PlacesOver E q}
variable (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]

private theorem under_of_over {v : Pl F} (u : PlacesOver E v) : u.1.under (𝓞 F) = v := by
  ext1
  exact (Ideal.over_def u.1.asIdeal v.asIdeal).symm

private theorem finite_over (v : Pl F) : {w : Pl E | w.under (𝓞 F) = v}.Finite := by
  refine (Set.finite_range fun u : PlacesOver E v => u.1).subset fun w hw => ?_
  subst hw
  exact ⟨⟨w, ⟨rfl⟩⟩, rfl⟩

private theorem mem_Z (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (O : Fin (m + 1) → LL μ →L[ℂ] LL μ) (y : ℝ) (v : LL μ) :
    v ∈ T.Z μ V O y ↔ v ∈ V ∧ (∀ i, O i v = (y : ℂ) • v) ∧ ∀ w ∉ T.marked, v ∈ eigL μ w (T.J w) (T.χ w) := by
  simp only [Ty.Z, archEig, eigIn, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_top, true_and,
    Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, and_assoc]

private theorem mem_Y (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (O : Fin (m + 1) → LL μ →L[ℂ] LL μ) (y : ℝ) (v : LL μ) :
    v ∈ T.Y μ V O y ↔ v ∈ V ∧ (∀ i, O i v = (y : ℂ) • v) ∧ ∀ w, v ∈ eigL μ w (T.J w) (T.χ w) := by
  simp only [Ty.Y, Ty.typed, archEig, eigIn, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_top, true_and,
    Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, and_assoc]

private theorem marked_chi (hq : GM.Split E q) (T : Ty σ n q w₀) {w : Pl E} (hw : w ∈ T.marked) : T.χ w = 1 := by
  rcases hw with rfl | ⟨v, hv, rfl⟩
  · exact T.triv q hq w₀
  · exact T.triv v (Finset.mem_filter.1 hv).2 (T.mk' v)

private theorem marked_under (T : Ty σ n q w₀) {w : Pl E} (hw : w ∈ T.marked) : w.under (𝓞 F) ∈ insert q T.S := by
  rcases hw with rfl | ⟨v, hv, rfl⟩
  · rw [under_of_over]
    exact Finset.mem_insert_self _ _
  · rw [under_of_over]
    exact Finset.mem_insert_of_mem (Finset.mem_filter.1 hv).1

private theorem operatorAt_comm (s : archGroup F n →* archGroup E n) (hs : Continuous s) (ν : Measure (archGroup F n)) [ν.IsHaarMeasure]
    (a : TI F n) (h : AdelicGLn.FiniteAdelicGL E n) (v : LL μ) :
    OComponent μ s hs ν a (rhoF μ h v) = rhoF μ h (OComponent μ s hs ν a v) := by
  have key : (rhoF μ h) ∘L OComponent μ s hs ν a = OComponent μ s hs ν a ∘L (rhoF μ h) := by
    refine UnitaryRep.comp_integrated_of_mem_intertwiners _ _ ?_ _
    intro x u
    simp only [UnitaryRep.compHom_apply, rhoF]
    rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, archP_finProj_comm]
  exact (DFunLike.congr_fun key v).symm

private theorem Z_closed (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (hV : IsClosed (V : Set (LL μ)))
    (O : Fin (m + 1) → LL μ →L[ℂ] LL μ) (y : ℝ) : IsClosed (T.Z μ V O y : Set (LL μ)) := by
  have e : (T.Z μ V O y : Set (LL μ)) = (V : Set (LL μ)) ∩ ((⋂ i, {v | O i v = (y : ℂ) • v}) ∩
      ⋂ w, ⋂ (_ : w ∉ T.marked), (eigL μ w (T.J w) (T.χ w) : Set (LL μ))) := by
    ext v
    simp only [SetLike.mem_coe, mem_Z, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [e]
  refine hV.inter (IsClosed.inter (isClosed_iInter fun i => isClosed_eq (O i).continuous (continuous_const_smul _)) ?_)
  exact isClosed_iInter fun w => isClosed_iInter fun _ =>
    (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) (T.χ w) (T.co w) (T.chr w)).1

private theorem Z_stable (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V)
    (s : Fin (m + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)) (νF : Measure (archGroup F n)) [νF.IsHaarMeasure]
    (a : TI F n) (y : ℝ) (w : Pl E) (hw : w ∈ T.marked) (g : Gw n w) (v : LL μ)
    (hv : v ∈ T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y) :
    rhoL μ w g v ∈ T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y := by
  obtain ⟨h1, h2, h3⟩ := (mem_Z μ T V _ y v).1 hv
  refine (mem_Z μ T V _ y _).2 ⟨hV.inv _ _ h1, fun i => ?_, fun w' hw' => ?_⟩
  · have := operatorAt_comm μ (s i) (hs i) νF a (AdelicGLn.localEmbedding w g) v
    refine this.trans ?_
    rw [h2 i, map_smul]
    rfl
  · refine (mem_eigL' μ _ _ _ _).2 fun x hx => ?_
    have hne : w' ≠ w := fun h => hw' (h ▸ hw)
    rw [rhoL_comm μ hne, (mem_eigL' μ _ _ _ _).1 (h3 w' hw') x hx, map_smul]

private theorem Y_eq (hq : GM.Split E q) (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (O : Fin (m + 1) → LL μ →L[ℂ] LL μ) (y : ℝ) :
    T.Y μ V O y = T.Z μ V O y ⊓ ⨅ w ∈ T.marked, fixL μ w (T.J w) := by
  have hfix : ∀ w ∈ T.marked, eigL μ w (T.J w) (T.χ w) = fixL μ w (T.J w) := fun w hw => by
    rw [marked_chi hq T hw]
    exact (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) 1 (T.co w) (marked_chi hq T hw ▸ T.chr w)).2.1
  ext v
  simp only [Submodule.mem_inf, Submodule.mem_iInf, mem_Y, mem_Z]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2, fun w _ => h3 w⟩, fun w hw => hfix w hw ▸ h3 w⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨h1, h2, fun w => ?_⟩
    by_cases hw : w ∈ T.marked
    · exact (hfix w hw).symm ▸ h4 w hw
    · exact h3 w hw

end Two

section Three
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {n m : ℕ} {q : Pl F} {w₀ : PlacesOver E q}

private theorem Z_fin (hn : 0 < n) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (D : InfD σ m)
    (s : Fin (m + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)) (hposition : IsBlockElement D n s)
    (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (a : TI F n) (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V)
    (y : ℝ) (hy : 0 < y) (U : ∀ w : Pl E, Subgroup (Gw n w)) (hU : ∀ w ∈ T.marked, CO (U w)) :
    FiniteDimensional ℂ ↥(T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y ⊓ ⨅ w ∈ T.marked, fixL μ w (U w)) := by
  obtain ⟨-, -, -, -, -, -, hH, hβ⟩ := UpperTheory.ConvolutionTheory.L1.archBasic F E σ m D n
  haveI := hH νF
  obtain ⟨β, hβ⟩ := hβ fun _ => a
  have hop : Oinf μ (Measure.map (glueA D n) (Measure.pi fun _ => νF)) β =
      (List.ofFn fun i => OComponent μ (s i) (hs i) νF a).prod :=
    UpperTheory.ConvolutionTheory.L1.tensOp F E σ m D n (Measure.map (glueA D n) (Measure.pi fun _ => νF)) νF rfl s hs hposition (LL μ) _ (fun _ => a) β hβ
  have hfin : {w : Pl E | w.under (𝓞 F) ∈ insert q T.S}.Finite := by
    have : {w : Pl E | w.under (𝓞 F) ∈ insert q T.S} = ⋃ v ∈ insert q T.S, {w : Pl E | w.under (𝓞 F) = v} := by
      ext w
      simp
    rw [this]
    exact (Finset.finite_toSet _).biUnion fun v _ => finite_over v
  set P : Finset (Pl E) := hfin.toFinset with hP
  have hPm : ∀ w, w ∈ P ↔ w.under (𝓞 F) ∈ insert q T.S := fun w => by simp [hP]
  let U' : ∀ w : Pl E, Subgroup (Gw n w) := fun w =>
    if w ∈ T.marked then U w else kerS (T.J w) (T.χ w) (T.chr w)
  have hU' : ∀ w ∈ P, CO (U' w) := fun w _ => by
    by_cases hw : w ∈ T.marked
    · simpa only [U', if_pos hw] using hU w hw
    · simpa only [U', if_neg hw] using kerS_co (T.co w) (T.chr w)
  haveI := UpperTheory.ConvolutionTheory.C.eigAdm E n hn μ (Measure.map (glueA D n) (Measure.pi fun _ => νF)) β (y ^ (m + 1)) (pow_ne_zero _ hy.ne') P U' hU'
  refine Submodule.finiteDimensional_of_le (fun v hv => ?_)
    (S₂ := eigIn (cuspidalL2 μ) (Oinf μ (Measure.map (glueA D n) (Measure.pi fun _ => νF)) β) (y ^ (m + 1)) ⊓ sphOff μ P ⊓
      ⨅ w ∈ P, fixL μ w (U' w))
  obtain ⟨hZ, hf⟩ := Submodule.mem_inf.1 hv
  obtain ⟨h1, h2, h3⟩ := (mem_Z μ T V _ y v).1 hZ
  have hf' : ∀ w ∈ T.marked, v ∈ fixL μ w (U w) := fun w hw => by
    simpa only [Submodule.mem_iInf] using (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf w) hw
  refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hV.le h1, ?_⟩, ?_⟩, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, hop, list_prod_apply _ v (y : ℂ)]
    · simp
    · intro A hA
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hA
      exact h2 i
  · refine (Submodule.mem_iInf _).2 fun w => (Submodule.mem_iInf _).2 fun hw => ?_
    have hmk : w ∉ T.marked := fun h => hw ((hPm w).2 (marked_under T h))
    have hu : w.under (𝓞 F) ∉ insert q T.S := fun h => hw ((hPm w).2 h)
    obtain ⟨e1, e2⟩ := T.off w (fun h => hu (Finset.mem_insert_of_mem h)) (fun h => hu (by rw [h]; exact Finset.mem_insert_self _ _))
    refine (mem_fixL' μ _ _ _).2 fun x hx => ?_
    rw [(mem_eigL' μ _ _ _ _).1 (h3 w hmk) x (e1 ▸ hx), e2]
    simp
  · refine (Submodule.mem_iInf _).2 fun w => (Submodule.mem_iInf _).2 fun _ => ?_
    by_cases hw : w ∈ T.marked
    · simpa only [U', if_pos hw] using hf' w hw
    · simp only [U', if_neg hw]
      refine (mem_fixL' μ _ _ _).2 fun x hx => ?_
      rw [(mem_eigL' μ _ _ _ _).1 (h3 w hw) x hx.1, hx.2, one_smul]

end Three

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.zBasic :
    UpperTheory.ConvolutionTheory.L1.ZBasic := by
  intro F E _ _ _ _ _ σ m n hn μ _ D s hs hposition νF _ a q w₀ hq T V hV y hy
  exact ⟨UpperTheory.ConvolutionTheory.L1.Z_closed μ T V hV.closed _ y, fun w hw g v hv => UpperTheory.ConvolutionTheory.L1.Z_stable μ T V hV s hs νF a y w hw g v hv,
    fun U hU => UpperTheory.ConvolutionTheory.L1.Z_fin hn μ D s hs hposition νF a T V hV y hy U hU, UpperTheory.ConvolutionTheory.L1.Y_eq μ hq T V _ y⟩
end
end

