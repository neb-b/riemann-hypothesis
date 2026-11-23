module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.UnitsTrace
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0002
public import GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdeleTopology

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.AlgTrace
section
private theorem factor_alg {A B C : Type} [Ring A] [Ring B] [Ring C] [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]
    (p : A →ₐ[ℂ] B) (hp : Function.Surjective p) (g : A →ₐ[ℂ] C) (h : ∀ a, p a = 0 → g a = 0) :
    ∃ r : B →ₐ[ℂ] C, ∀ a, r (p a) = g a := by
  have key : ∀ a, g (Function.surjInv hp (p a)) = g a := by
    intro a
    rw [← sub_eq_zero, ← map_sub]
    apply h
    rw [map_sub, Function.surjInv_eq hp, sub_self]
  refine ⟨{ toFun := fun b => g (Function.surjInv hp b)
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_, commutes' := ?_ }, key⟩
  · rw [← map_one p, key, map_one]
  · intro x y
    obtain ⟨x, rfl⟩ := hp x
    obtain ⟨y, rfl⟩ := hp y
    simp only [← map_mul p, key, map_mul g]
  · rw [← map_zero p, key, map_zero]
  · intro x y
    obtain ⟨x, rfl⟩ := hp x
    obtain ⟨y, rfl⟩ := hp y
    simp only [← map_add p, key, map_add g]
  · intro c
    simp only [← p.commutes c, key, g.commutes]

private theorem comm_lift {X E : Type} [Ring E] [Algebra ℂ E] (T : X → E) (S : E) (h : ∀ x, Commute S (T x))
    (a : FreeAlgebra ℂ X) : Commute S (FreeAlgebra.lift ℂ T a) := by
  induction a using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact (Algebra.commutes r S).symm
  | grade1 x => rw [FreeAlgebra.lift_ι_apply]; exact h x
  | mul a b ha hb => rw [map_mul]; exact ha.mul_right hb
  | add a b ha hb => rw [map_add (f := _)]; exact ha.add_right hb

theorem UpperTheory.ConvolutionTheory.L1.algTrace :
    UpperTheory.ConvolutionTheory.L1.AlgTrace := by
  intro W X _ _ _ m T hcomm hirr U hU
  rcases subsingleton_or_nontrivial W with hW | hW
  · refine ⟨1, one_ne_zero, fun i₀ S _ => ?_⟩
    rw [one_mul]
    congr 1
    ext w
    exact Subsingleton.elim _ _
  let ρ : Fin (m + 1) → (FreeAlgebra ℂ X →ₐ[ℂ] Module.End ℂ W) := fun i => FreeAlgebra.lift ℂ (T i)
  have hρι : ∀ i x, ρ i (FreeAlgebra.ι ℂ x) = T i x := fun i x => FreeAlgebra.lift_ι_apply _ _
  have hρT : ∀ i j, i ≠ j → ∀ a y, Commute (ρ i a) (T j y) := fun i j hij a y =>
    (comm_lift (T i) (T j y) (fun x => (hcomm i j hij x y).symm) a).symm
  have hρρ : ∀ i j, i ≠ j → ∀ a b, Commute (ρ i a) (ρ j b) := fun i j hij a b =>
    comm_lift (T j) (ρ i a) (hρT i j hij a) b
  have hρU : ∀ i a w, U (ρ (i + 1) a w) = ρ i a (U w) := by
    intro i a
    induction a using FreeAlgebra.induction with
    | grade0 r => intro w; simp [Algebra.algebraMap_eq_smul_one]
    | grade1 x => intro w; rw [hρι, hρι, hU]
    | mul a b ha hb => intro w; simp only [map_mul, Module.End.mul_apply, ha, hb]
    | add a b ha hb => intro w; simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
  have hker : ∀ a, ρ 0 a = 0 → ∀ i, ρ i a = 0 := by
    intro a ha i
    induction i using Fin.induction with
    | zero => exact ha
    | succ i ih =>
      rw [← Fin.coeSucc_eq_succ]
      ext w
      apply U.injective
      rw [hρU, ih]
      simp
  obtain ⟨d, -, ⟨e⟩⟩ := UpperTheory.ConvolutionTheory.L1.matImage (FreeAlgebra ℂ X) W (ρ 0) {b | ∃ j, j ≠ 0 ∧ ∃ x, b = T j x}
    (by
      rintro a b ⟨j, hj, x, rfl⟩
      exact hρT 0 j hj.symm a x)
    (by
      intro P h1 h2
      apply hirr P
      intro i x w hw
      by_cases hi : i = 0
      · subst hi
        rw [← hρι]
        exact h1 _ w hw
      · exact h2 _ ⟨i, hi, x, rfl⟩ w hw)
  let p : FreeAlgebra ℂ X →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ := (e : (ρ 0).range →ₐ[ℂ] _).comp (ρ 0).rangeRestrict
  have hp : Function.Surjective p := e.surjective.comp (ρ 0).rangeRestrict_surjective
  have hp0 : ∀ a, p a = 0 → ρ 0 a = 0 := by
    intro a ha
    have h1 : e ((ρ 0).rangeRestrict a) = 0 := ha
    have h2 : (ρ 0).rangeRestrict a = 0 := (map_eq_zero_iff e e.injective).1 h1
    exact congrArg Subtype.val h2
  choose r hr using fun i => factor_alg p hp (ρ i) (fun a ha => hker a (hp0 a ha) i)
  obtain ⟨c, hc, H⟩ := UpperTheory.ConvolutionTheory.L1.unitsTrace W m d r
    (by
      intro i j hij a b
      obtain ⟨a, rfl⟩ := hp a
      obtain ⟨b, rfl⟩ := hp b
      rw [hr, hr]
      exact hρρ i j hij a b)
    (by
      intro P h
      apply hirr P
      intro i x w hw
      rw [← hρι, ← hr]
      exact h _ _ w hw)
    U
    (by
      intro i a w
      obtain ⟨a, rfl⟩ := hp a
      rw [hr, hr, hρU])
  refine ⟨c, hc, fun i₀ S hS => H i₀ S ?_⟩
  intro j hj a
  obtain ⟨a, rfl⟩ := hp a
  rw [hr]
  exact comm_lift (T j) S (hS j hj) a
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo

theorem UpperTheory.ConvolutionTheory.L1.archBasic :
    UpperTheory.ConvolutionTheory.L1.ArchBasic := by
  intro F E _ _ _ _ _ σ m D n
  obtain ⟨h1, h2, h3, h4, h5, -⟩ :=
    UpperTheory.ConvolutionTheory.L1.glueBasic (InfiniteAdeleRing F) (InfiniteAdeleRing E) _ _ m D n
  have compA_apply : ∀ i x, UpperTheory.ConvolutionTheory.L1.compA D n i x =
      archEquiv F n (D.comp n i ((archEquiv E n).symm x)) := fun _ _ => rfl
  have glueA_apply : ∀ g, UpperTheory.ConvolutionTheory.L1.glueA D n g =
      archEquiv E n (D.glue n fun i => (archEquiv F n).symm (g i)) := fun _ => rfl
  have c1 : ∀ g i, UpperTheory.ConvolutionTheory.L1.compA D n i (UpperTheory.ConvolutionTheory.L1.glueA D n g) = g i := by
    intro g i
    rw [compA_apply, glueA_apply, ContinuousMulEquiv.symm_apply_apply, h1,
      ContinuousMulEquiv.apply_symm_apply]
  have c2 : ∀ x, UpperTheory.ConvolutionTheory.L1.glueA D n (fun i => UpperTheory.ConvolutionTheory.L1.compA D n i x) = x := by
    intro x
    rw [glueA_apply]
    simp only [compA_apply, ContinuousMulEquiv.symm_apply_apply]
    rw [h2, ContinuousMulEquiv.apply_symm_apply]
  have c3 : ∀ g h, UpperTheory.ConvolutionTheory.L1.glueA D n (g * h) =
      UpperTheory.ConvolutionTheory.L1.glueA D n g * UpperTheory.ConvolutionTheory.L1.glueA D n h := by
    intro g h
    simp only [glueA_apply]
    rw [← map_mul, ← h3]
    congr 2
    funext i
    exact map_mul (archEquiv F n).symm (g i) (h i)
  have c4 : Continuous (UpperTheory.ConvolutionTheory.L1.glueA D n) := by
    have : Continuous fun g : Fin (m + 1) → archGroup F n =>
        archEquiv E n (D.glue n fun i => (archEquiv F n).symm (g i)) :=
      (archEquiv E n).continuous.comp
        (h4.comp (continuous_pi fun i => (archEquiv F n).symm.continuous.comp (continuous_apply i)))
    exact this
  have c5 : ∀ i, Continuous (UpperTheory.ConvolutionTheory.L1.compA D n i) := by
    intro i
    have : Continuous fun x : archGroup E n =>
        archEquiv F n (D.comp n i ((archEquiv E n).symm x)) :=
      (archEquiv F n).continuous.comp ((h5 i).comp (archEquiv E n).symm.continuous)
    exact this
  let e : (Fin (m + 1) → archGroup F n) ≃ₜ* archGroup E n :=
    { toFun := UpperTheory.ConvolutionTheory.L1.glueA D n
      invFun := fun x i => UpperTheory.ConvolutionTheory.L1.compA D n i x
      left_inv := fun g => funext (c1 g)
      right_inv := c2
      map_mul' := c3
      continuous_toFun := c4
      continuous_invFun := continuous_pi c5 }
  refine ⟨c1, c2, c3, c4, c5, ?_, ?_, ?_⟩
  · refine ⟨fun i => (e.toMulEquiv.toMonoidHom).comp (MonoidHom.mulSingle (fun _ : Fin (m + 1) => archGroup F n) i), ?_, ?_⟩
    · intro i g
      rfl
    · intro i
      have hm : Continuous fun g : archGroup F n => (Pi.mulSingle i g : Fin (m + 1) → archGroup F n) :=
        by
          refine continuous_pi fun j => ?_
          by_cases hj : j = i
          · subst hj
            simpa using (continuous_id' : Continuous fun a : archGroup F n => a)
          · simpa [Pi.mulSingle_eq_of_ne hj] using continuous_const
      exact c4.comp hm
  · intro νF _
    exact e.isHaarMeasure_map (Measure.pi fun _ => νF)
  · intro φ
    have hc : Continuous fun g : archGroup E n => ∏ i, φ i (UpperTheory.ConvolutionTheory.L1.compA D n i g) :=
      continuous_finsetProd _ fun i _ => (φ i).continuous.comp (c5 i)
    have hK : IsCompact (UpperTheory.ConvolutionTheory.L1.glueA D n '' Set.pi Set.univ fun i => tsupport (φ i)) :=
      (isCompact_univ_pi fun i => (φ i).hasCompactSupport).image c4
    have hs : HasCompactSupport fun g : archGroup E n => ∏ i, φ i (UpperTheory.ConvolutionTheory.L1.compA D n i g) := by
      refine HasCompactSupport.of_support_subset_isCompact hK ?_
      intro x hx
      refine ⟨fun i => UpperTheory.ConvolutionTheory.L1.compA D n i x, ?_, c2 x⟩
      intro i _
      apply subset_tsupport
      intro h0
      exact hx (Finset.prod_eq_zero (Finset.mem_univ i) h0)
    exact ⟨⟨⟨_, hc⟩, hs⟩, fun g => rfl⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CvPowers
section
open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

private theorem cvP_test {a b : G → ℂ} (ha : Continuous a ∧ HasCompactSupport a)
    (hb : Continuous b ∧ HasCompactSupport b) : Continuous (cv μ a b) ∧ HasCompactSupport (cv μ a b) := by
  have h := cvBasic G μ a b b ha.1 ha.2 hb.1 hb.2 hb.1 hb.2
  exact ⟨h.1, h.2.1⟩

private theorem cvP_assoc {a b c : G → ℂ} (ha : Continuous a ∧ HasCompactSupport a)
    (hb : Continuous b ∧ HasCompactSupport b) (hc : Continuous c ∧ HasCompactSupport c) :
    cv μ (cv μ a b) c = cv μ a (cv μ b c) :=
  (cvBasic G μ a b c ha.1 ha.2 hb.1 hb.2 hc.1 hc.2).2.2.2.1

private theorem cvP_pow_test {a : G → ℂ} (ha : Continuous a ∧ HasCompactSupport a) (k : ℕ) :
    Continuous (cvPow μ a k) ∧ HasCompactSupport (cvPow μ a k) := by
  induction k with
  | zero => exact ha
  | succ k ih => exact cvP_test μ ha ih

private theorem cvP_add {a : G → ℂ} (ha : Continuous a ∧ HasCompactSupport a) (j k : ℕ) :
    cv μ (cvPow μ a j) (cvPow μ a k) = cvPow μ a (j + k + 1) := by
  induction j with
  | zero => rw [Nat.zero_add]; rfl
  | succ j ih =>
    change cv μ (cv μ a (cvPow μ a j)) (cvPow μ a k) = _
    rw [cvP_assoc μ ha (cvP_pow_test μ ha j) (cvP_pow_test μ ha k), ih,
      show j + 1 + k + 1 = (j + k + 1) + 1 by omega]
    rfl

private theorem cvP_pow_pow {a : G → ℂ} (ha : Continuous a ∧ HasCompactSupport a) (k m : ℕ) :
    cvPow μ (cvPow μ a k) m = cvPow μ a (m * k + m + k) := by
  induction m with
  | zero => simp only [Nat.zero_mul, Nat.zero_add]; rfl
  | succ m ih =>
    change cv μ (cvPow μ a k) (cvPow μ (cvPow μ a k) m) = _
    rw [ih, cvP_add μ ha]
    congr 1
    ring

private theorem cvP_update {b ψ : G → ℂ} (hb : Continuous b ∧ HasCompactSupport b)
    (hψ : Continuous ψ ∧ HasCompactSupport ψ) (m : ℕ) :
    cvAll μ m (Function.update (fun _ => b) (Fin.last m) (cv μ b ψ)) = cv μ (cvPow μ b m) ψ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : Fin.tail (Function.update (fun _ : Fin (m + 1 + 1) => b) (Fin.last (m + 1)) (cv μ b ψ)) =
        Function.update (fun _ => b) (Fin.last m) (cv μ b ψ) := by
      rw [← Fin.succ_last, Fin.tail_update_succ]
      rfl
    have h0 : Function.update (fun _ : Fin (m + 1 + 1) => b) (Fin.last (m + 1)) (cv μ b ψ) 0 = b := by
      rw [Function.update_of_ne]
      exact (Fin.last_pos).ne
    rw [cvAll, h1, h0, ih, ← cvP_assoc μ hb (cvP_pow_test μ hb m) hψ]
    rfl

end

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.cvPowers :
    UpperTheory.ConvolutionTheory.L1.CvPowers := by
  intro G _ _ _ _ _ _ _ _ μ _ m a ψ ha ha' hψ hψ' k
  have h1 : cvPow μ (cvPow μ a k) m = cvPow μ (cvPow μ a m) k := by
    rw [cvP_pow_pow μ ⟨ha, ha'⟩, cvP_pow_pow μ ⟨ha, ha'⟩]
    congr 1
    ring
  refine ⟨h1, ?_, ?_⟩
  · rw [cvP_update μ (cvP_pow_test μ ⟨ha, ha'⟩ k) ⟨hψ, hψ'⟩, h1]
  · intro φ φ' _ _
    funext g
    simp only [cv]
    rw [← integral_fintype_prod_eq_prod (fun i y => φ i y * φ' i (y⁻¹ * g i))]
    congr 1
    funext y
    rw [← Finset.prod_mul_distrib]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.FinSplit
section
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.L1

private theorem pi_factor {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ι → Type*} [∀ i, Field (k i)]
    {K : Type*} [Field K] (φ : (∀ i, k i) →+* K) : ∃ w, ∀ b : ∀ i, k i, b w = 0 → φ b = 0 := by
  have h1 : ∑ i, φ (Pi.single i 1) = 1 := by
    have h : (∑ x, Pi.single x 1 : ∀ i, k i) = 1 := Finset.univ_sum_single (1 : ∀ i, k i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, h, map_one]
  obtain ⟨w, hw⟩ : ∃ w, φ (Pi.single w 1) ≠ 0 := by
    by_contra! h
    simp [h] at h1
  refine ⟨w, fun b hb => ?_⟩
  have h0 : b * Pi.single w 1 = 0 := by
    ext i
    by_cases h : i = w
    · subst h
      simp [hb]
    · simp [Pi.single_eq_of_ne h]
  have h2 := congrArg φ h0
  rw [map_mul, map_zero] at h2
  exact (mul_eq_zero.1 h2).resolve_right hw

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem comp_eq (v : HeightOneSpectrum (𝓞 F)) (φ : CompletionsOver E v →+* v.adicCompletion F)
    (hφ : ∀ a, φ (incFin E v a) = a)
    (hs : ∀ w : PlacesOver E v, Function.Surjective (completionMap v w.1)) :
    ∃ w : PlacesOver E v, ∀ b, completionMap v w.1 (φ b) = b w := by
  classical
  obtain ⟨w, hw⟩ := pi_factor φ
  refine ⟨w, fun b => ?_⟩
  obtain ⟨a, ha⟩ := hs w (b w)
  have h : φ (b - incFin E v a) = 0 := hw _ (by
    change b w - completionMap v w.1 a = 0
    rw [ha, sub_self])
  rw [map_sub, hφ, sub_eq_zero] at h
  rw [h, ha]

private noncomputable def pt (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v)
    (hs : Function.Surjective (completionMap v w.1)) : E →ₐ[F] v.adicCompletion F where
  toRingHom := (RingEquiv.ofBijective (completionMap v w.1)
    ⟨(completionMap v w.1).injective, hs⟩).symm.toRingHom.comp (algebraMap E (w.1.adicCompletion E))
  commutes' r := by
    change (RingEquiv.ofBijective (completionMap v w.1) _).symm _ = _
    rw [RingEquiv.symm_apply_eq]
    change _ = completionMap v w.1 _
    rw [completionMap_algebraMap, ← IsScalarTower.algebraMap_apply]

private theorem completionMap_pt (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v)
    (hs : Function.Surjective (completionMap v w.1)) (x : E) :
    completionMap v w.1 (pt v w hs x) = algebraMap E (w.1.adicCompletion E) x :=
  (RingEquiv.ofBijective (completionMap v w.1) ⟨(completionMap v w.1).injective, hs⟩).apply_symm_apply _

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.finSplit :
    UpperTheory.ConvolutionTheory.L1.FinSplit := by
  intro F E _ _ _ _ _ _ σ hσ m hm v w₀ hs
  classical
  obtain ⟨e, he, hshift⟩ := UpperTheory.ConvolutionTheory.L1.galSplit F E σ hσ m hm (v.adicCompletion F)
    (CompletionsOver E v) (tensorEquiv' E v) (pt v w₀ (hs w₀))
  have hinc : ∀ r, incFin E v r = tensorEquiv' E v (1 ⊗ₜ r) := fun r => by
    rw [tensorEquiv'_tmul, map_one, one_mul]
    rfl
  have hdiag : ∀ r i, e (incFin E v r) i = r := fun r i => by
    rw [hinc, he, map_one, map_one, one_mul]
  have hsmul : ∀ (a : v.adicCompletion F) (b : CompletionsOver E v), e (a • b) = a • e b := by
    intro a b
    funext i
    rw [Algebra.smul_def, map_mul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    exact congrArg (· * e b i) (hdiag a i)
  let L : CompletionsOver E v ≃ₗ[v.adicCompletion F] (Fin (m + 1) → v.adicCompletion F) :=
    { e.toAddEquiv with map_smul' := hsmul }
  let D : Split (incFin E v) (galFin σ v) m :=
    { e := e
      cont := IsModuleTopology.continuous_of_linearMap L.toLinearMap
      cont_symm := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap
      map_diag := hdiag
      map_shift := hshift }
  have hcomp : ∀ i, ∃ w : PlacesOver E v, ∀ b, completionMap v w.1 (e b i) = b w := fun i =>
    comp_eq v ((Pi.evalRingHom _ i).comp e.toRingHom) (fun a => hdiag a i) hs
  choose w hw using hcomp
  have hne : ∀ i u, e (Pi.single u 1) i ≠ 0 → w i = u := by
    intro i u h
    by_contra hu
    apply h
    apply (completionMap v (w i).1).injective
    rw [hw, map_zero, Pi.single_eq_of_ne hu]
  have hinj : Function.Injective w := by
    intro i j h
    by_contra hij
    have key : ∀ u, u = w j → ∀ b, completionMap v u.1 (e b i) = b u → e b i = e b j := by
      intro u hu b h3
      subst hu
      exact (completionMap v (w j).1).injective (h3.trans (hw j b).symm)
    have h4 := key _ h (e.symm (Pi.single i 1)) (hw i _)
    rw [RingEquiv.apply_symm_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)] at h4
    exact one_ne_zero h4
  have hsurj : Function.Surjective w := by
    intro u
    have h1 : e (Pi.single u 1) ≠ 0 := fun h => by
      have h2 := congrFun ((map_eq_zero_iff e e.injective).1 h) u
      rw [Pi.single_eq_same] at h2
      exact one_ne_zero h2
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h1
    exact ⟨i, hne i u hi⟩
  have h0 : ∀ b : CompletionsOver E v, completionMap v w₀.1 (e b 0) = b w₀ := by
    intro b
    obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective b
    induction t with
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), Pi.add_apply, map_add (f := _), hx, hy, Pi.add_apply]
    | tmul x a =>
      rw [he, map_mul]
      simp only [Fin.val_zero, pow_zero]
      rw [show ((1 : E ≃ₐ[F] E) x) = x from rfl, completionMap_pt, tensorEquiv'_tmul]
      rfl
  have hw0 : w 0 = w₀ := by
    refine hne 0 w₀ fun h => ?_
    have h1 := h0 (Pi.single w₀ 1)
    rw [h, map_zero, Pi.single_eq_same] at h1
    exact zero_ne_one h1
  exact ⟨D, Equiv.ofBijective w ⟨hinj, hsurj⟩, hw0, fun b i => hw i b⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.InfSplit
section
open NumberField GroundTheory.Global.InfinitePlace
open scoped TensorProduct

theorem UpperTheory.ConvolutionTheory.L1.infSplit :
    UpperTheory.ConvolutionTheory.L1.InfSplit := by
  intro F E _ _ _ _ _ _ σ hσ m hm
  refine ⟨fun hF => ?_, fun p => ?_⟩
  · have h : ∀ v : InfinitePlace F, Nonempty (E →ₐ[F] v.Completion) := fun v => by
      haveI : IsAlgClosed v.Completion :=
        IsAlgClosed.of_ringEquiv ℂ _
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex (hF.isComplex v)).symm
      exact ⟨IsAlgClosed.lift⟩
    exact ⟨Pi.algHom F (fun v : InfinitePlace F => v.Completion) fun v => (h v).some⟩
  · obtain ⟨e, he, hs⟩ := UpperTheory.ConvolutionTheory.L1.galSplit F E σ hσ m hm (InfiniteAdeleRing F) (InfiniteAdeleRing E)
      (tensorInfiniteAdeleRingEquiv (K := F) (L := E)) p
    have hd : ∀ r i, e (infiniteAdeleRingMap (K := F) (L := E) r) i = r := fun r i => by
      have := he 1 r i
      rwa [tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul, map_one, map_one, one_mul] at this
    have hx : ∀ (x : E) i, e (algebraMap E (InfiniteAdeleRing E) x) i = p ((σ ^ (i : ℕ)) x) := fun x i => by
      have := he x 1 i
      rwa [tensorInfiniteAdeleRingEquiv_tmul', map_one, mul_one, mul_one] at this
    refine ⟨⟨e, ?_, ?_, hd, hs⟩, hx⟩
    · let b := Module.finBasis F E
      have h : ∀ y i, e y i = ∑ j, p ((σ ^ (i : ℕ)) (b j)) * adeleCoord b j y := fun y i => by
        conv_lhs => rw [← tensorInfiniteAdeleRingEquiv_sum_adeleCoord b y]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_sum, Finset.sum_apply]
        exact Finset.sum_congr rfl fun j _ => he _ _ _
      refine continuous_pi fun i => ?_
      simp_rw [h]
      exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_adeleCoord b j)
    · have h : ∀ a, e.symm a =
          ∑ i, infiniteAdeleRingMap (K := F) (L := E) (a i) * e.symm (Pi.single i 1) := fun a => by
        apply e.injective
        funext k
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_apply, RingEquiv.apply_symm_apply]
        simp_rw [map_mul, RingEquiv.apply_symm_apply, Pi.mul_apply, hd]
        rw [Finset.sum_eq_single k]
        · simp
        · intro j _ hj
          rw [Pi.single_eq_of_ne hj.symm, mul_zero]
        · simp
      have h' : (e.symm : _ → _) = fun a => ∑ i, infiniteAdeleRingMap (K := F) (L := E) (a i) * e.symm (Pi.single i 1) :=
        funext h
      rw [h']
      exact continuous_finsetSum _ fun i _ =>
        (continuous_infiniteAdeleRingMap.comp (continuous_apply i)).mul continuous_const
end

