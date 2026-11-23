module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.AnalyticAtDet
section
noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw.LVs

def H (N : ℕ) (t : ℤ) (T : Matrix (Fin N) (Fin N) ℂ) : ℂ := (1 + T).det ^ t

theorem analyticAt_det {ι : Type} [Fintype ι] [DecidableEq ι] (M0 : Matrix ι ι ℂ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T.det) M0 := by
  have he : ∀ a b : ι, AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T a b) M0 := fun a b =>
    ((ContinuousLinearMap.proj b).comp
      (ContinuousLinearMap.proj a : (ι → ι → ℂ) →L[ℂ] (ι → ℂ))).analyticAt M0
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => he (σ i) i)

theorem analyticAt_H (N : ℕ) (t : ℤ) (T0 : Matrix (Fin N) (Fin N) ℂ) (h : (1 + T0).det ≠ 0) :
    AnalyticAt ℂ (H N t) T0 := by
  have hd : AnalyticAt ℂ (fun T : Matrix (Fin N) (Fin N) ℂ => (1 + T).det) T0 :=
    (analyticAt_det (1 + T0)).comp (analyticAt_const.add analyticAt_id)
  exact hd.zpow h

end PositivityTheory.Rg.Sw.LVs.CK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyEq
section
noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CEq

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem iteratedFDeriv_comp_clm (F : Matrix κ κ ℂ → ℂ) (hF : AnalyticAt ℂ F 0)
    (L : Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) (n : ℕ) (v : Fin n → Matrix ι ι ℂ) :
    iteratedFDeriv ℂ n (F ∘ L) 0 v = iteratedFDeriv ℂ n F 0 (fun i => L (v i)) := by
  obtain ⟨s, hs0, hAs⟩ := hF.exists_mem_nhds_analyticOnNhd
  have ht : IsOpen (interior s) := isOpen_interior
  have h0t : (0 : Matrix κ κ ℂ) ∈ interior s := mem_interior_iff_mem_nhds.mpr hs0
  have hcd : ContDiffOn ℂ ω F (interior s) := (hAs.mono interior_subset).contDiffOn ht.uniqueDiffOn
  have hpre : IsOpen (L ⁻¹' interior s) := ht.preimage L.continuous
  have hL0 : L 0 ∈ interior s := by simpa using h0t
  have h0pre : (0 : Matrix ι ι ℂ) ∈ L ⁻¹' interior s := hL0
  have key := L.iteratedFDerivWithin_comp_right hcd ht.uniqueDiffOn hpre.uniqueDiffOn hL0
    (i := n) le_top
  have e1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℂ) (f := F ∘ L) n hpre h0pre
  have e2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℂ) (f := F) n ht h0t
  have hz : L 0 = 0 := L.map_zero
  rw [← e1, ← e2]
  erw [key]
  exact congrArg (fun y => iteratedFDerivWithin ℂ n F (interior s) y (fun i => L (v i))) hz

omit [DecidableEq κ] in
theorem symm_perm (F : Matrix κ κ ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n : ℕ} (v : Fin n → Matrix κ κ ℂ)
    (π : Equiv.Perm (Fin n)) : iteratedFDeriv ℂ n F 0 (v ∘ π) = iteratedFDeriv ℂ n F 0 v :=
  (hF.contDiffAt).iteratedFDeriv_comp_perm v π

def Dg {n : ℕ} (f : κ ≃ Fin n) (F : Matrix κ κ ℂ → ℂ) : ℂ :=
  ∑ σ : Equiv.Perm κ, (Equiv.Perm.sign σ : ℂ) *
    iteratedFDeriv ℂ n F 0 (fun i => Matrix.single (f.symm i) (σ (f.symm i)) 1)

omit [DecidableEq ι] in
theorem detD_eq_Dg (F : Matrix κ κ ℂ → ℂ) : detD F = Dg (Fintype.equivFin κ) F := rfl

theorem Dg_indep (F : Matrix κ κ ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n m : ℕ} (f : κ ≃ Fin n) (g : κ ≃ Fin m) :
    Dg f F = Dg g F := by
  have hnm : n = m := by simpa using Fintype.card_congr (f.symm.trans g)
  subst hnm
  unfold Dg
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have hv : (fun i => Matrix.single (f.symm i) (σ (f.symm i)) (1 : ℂ)) =
      (fun i => Matrix.single (g.symm i) (σ (g.symm i)) (1 : ℂ)) ∘ (f.symm.trans g) := by
    funext i
    simp
  rw [hv]
  exact symm_perm F hF _ _

omit [DecidableEq ι] [DecidableEq κ] in
theorem reindex_single [DecidableEq ι] [DecidableEq κ] (e' : ι ≃ κ) (a b : ι) :
    (Matrix.single a b (1 : ℂ)).reindex e' e' = Matrix.single (e' a) (e' b) 1 := by
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.single_apply, Equiv.eq_symm_apply]

theorem reindex_thm : Reindex := by
  intro ι κ _ _ _ _ e F hF
  rw [detD_eq_Dg, detD_eq_Dg,
    ← Dg_indep F hF (e.symm.trans (Fintype.equivFin ι)) (Fintype.equivFin κ)]
  unfold Dg
  refine Fintype.sum_equiv (Equiv.permCongr e) _ _ fun σ => ?_
  rw [Equiv.Perm.sign_permCongr]
  congr 1
  have h1 : iteratedFDeriv ℂ (Fintype.card ι) (fun T => F (Matrix.reindex e e T)) 0
      (fun i => Matrix.single ((Fintype.equivFin ι).symm i) (σ ((Fintype.equivFin ι).symm i)) (1 : ℂ)) =
      iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i =>
        Matrix.reindex e e (Matrix.single ((Fintype.equivFin ι).symm i)
          (σ ((Fintype.equivFin ι).symm i)) (1 : ℂ))) :=
    iteratedFDeriv_comp_clm F hF
      (LinearMap.toContinuousLinearMap (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap) _ _
  rw [h1]
  congr 1
  funext i
  rw [reindex_single]
  simp

omit [Fintype ι] in
theorem mul_single_eq [Fintype ι] (A : Matrix ι ι ℂ) (a b : ι) :
    A * Matrix.single a b (1 : ℂ) = ∑ c, A c a • Matrix.single c b (1 : ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]

private theorem sum_sign_iteratedFDeriv_single_eq_zero_of_not_inj (F : Matrix ι ι ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n : ℕ}
    (a : Fin n ≃ ι) (r : Fin n → ι) (hr : ¬ Function.Injective r) :
    ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, r i = r j ∧ i ≠ j := by
    simp only [Function.Injective, not_forall] at hr
    obtain ⟨i, j, h, hne⟩ := hr
    exact ⟨i, j, h, hne⟩
  have hane : a i ≠ a j := fun h => hne (a.injective h)
  have key : ∀ σ : Equiv.Perm ι, iteratedFDeriv ℂ n F 0
      (fun k => Matrix.single (r k) ((σ * Equiv.swap (a i) (a j)) (a k)) (1 : ℂ)) =
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) := by
    intro σ
    rw [← symm_perm F hF (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) (Equiv.swap i j)]
    congr 1
    funext k
    simp only [Equiv.Perm.mul_apply, Function.comp_apply]
    by_cases hki : k = i
    · subst hki
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left, hij]
    · by_cases hkj : k = j
      · subst hkj
        rw [Equiv.swap_apply_right, Equiv.swap_apply_right, hij]
      · have h1 : a k ≠ a i := fun h => hki (a.injective h)
        have h2 : a k ≠ a j := fun h => hkj (a.injective h)
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hS := (Equiv.sum_comp (Equiv.mulRight (Equiv.swap (a i) (a j)))
    (fun σ : Equiv.Perm ι => ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)))).symm
  have hg : ∀ σ : Equiv.Perm ι, ((Equiv.Perm.sign (σ * Equiv.swap (a i) (a j)) : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0
        (fun k => Matrix.single (r k) ((σ * Equiv.swap (a i) (a j)) (a k)) (1 : ℂ)) =
      -(((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ))) := by
    intro σ
    rw [key σ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hane]
    push_cast
    ring
  simp only [Equiv.coe_mulRight] at hS
  rw [Finset.sum_congr rfl (fun σ _ => hg σ), Finset.sum_neg_distrib] at hS
  have h2 : (2 : ℂ) * ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) = 0 := by
    linear_combination hS
  simpa using h2

private theorem sum_sign_iteratedFDeriv_single_perm_eq_sign_mul (F : Matrix ι ι ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n : ℕ}
    (a : Fin n ≃ ι) (ρ : Equiv.Perm ι) :
    ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (ρ (a k)) (σ (a k)) (1 : ℂ)) =
    ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) (σ (a k)) (1 : ℂ)) := by
  have hterm : ∀ σ : Equiv.Perm ι,
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (ρ (a k)) (σ (a k)) (1 : ℂ)) =
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ)) := by
    intro σ
    rw [← symm_perm F hF (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ))
      ((a.trans ρ).trans a.symm)]
    congr 1
    funext k
    simp [Equiv.Perm.mul_apply]
  calc ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (ρ (a k)) (σ (a k)) (1 : ℂ))
      = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ)) :=
        Finset.sum_congr rfl fun σ _ => by rw [hterm σ]
    _ = ∑ τ : Equiv.Perm ι, ((Equiv.Perm.sign (τ * ρ) : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) ((τ * ρ * ρ⁻¹) (a k)) (1 : ℂ)) :=
        (Equiv.sum_comp (Equiv.mulRight ρ) (fun σ : Equiv.Perm ι => ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          iteratedFDeriv ℂ n F 0
            (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ)))).symm
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [mul_inv_cancel_right, Equiv.Perm.sign_mul]
        push_cast
        ring

theorem equivar_thm : Equivar := by
  intro ι _ _ F A hF
  let a : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let L : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ A)
  have hΦ : ∀ σ : Equiv.Perm ι,
      iteratedFDeriv ℂ (Fintype.card ι) (fun T => F (A * T)) 0
        (fun i => Matrix.single (a i) (σ (a i)) (1 : ℂ)) =
      ∑ r : Fin (Fintype.card ι) → ι, (∏ i, A (r i) (a i)) *
        iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i => Matrix.single (r i) (σ (a i)) (1 : ℂ)) := by
    intro σ
    have h1 : iteratedFDeriv ℂ (Fintype.card ι) (fun T => F (A * T)) 0
        (fun i => Matrix.single (a i) (σ (a i)) (1 : ℂ)) =
        iteratedFDeriv ℂ (Fintype.card ι) F 0
          (fun i => A * Matrix.single (a i) (σ (a i)) (1 : ℂ)) :=
      iteratedFDeriv_comp_clm F hF L _ _
    rw [h1]
    simp_rw [mul_single_eq]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  have hswap : detD (fun T => F (A * T)) = ∑ r : Fin (Fintype.card ι) → ι,
      (∏ i, A (r i) (a i)) * ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i => Matrix.single (r i) (σ (a i)) (1 : ℂ)) := by
    unfold detD
    rw [Finset.sum_congr rfl fun σ _ => by rw [hΦ σ]]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [hswap]
  have hinj : ∀ ρ ∈ (Finset.univ : Finset (Equiv.Perm ι)), ∀ ρ' ∈ (Finset.univ : Finset (Equiv.Perm ι)),
      (fun i => ρ (a i)) = (fun i => ρ' (a i)) → ρ = ρ' := by
    intro ρ _ ρ' _ h
    ext x
    simpa [a] using congrFun h (Fintype.equivFin ι x)
  rw [← Finset.sum_subset (Finset.subset_univ
      ((Finset.univ : Finset (Equiv.Perm ι)).image fun ρ => (fun i => ρ (a i)))),
    Finset.sum_image hinj]
  · have hD : detD F = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun k => Matrix.single (a k) (σ (a k)) (1 : ℂ)) := rfl
    simp_rw [sum_sign_iteratedFDeriv_single_perm_eq_sign_mul F hF a, ← hD]
    rw [Matrix.det_apply', Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [show (∏ i, A (ρ (a i)) (a i)) = ∏ x, A (ρ x) x from Equiv.prod_comp a (fun x => A (ρ x) x)]
    ring
  · intro r _ hr
    rw [sum_sign_iteratedFDeriv_single_eq_zero_of_not_inj F hF a r ?_, mul_zero]
    intro hr'
    apply hr
    rw [Finset.mem_image]
    refine ⟨Equiv.ofBijective (fun x => r (a.symm x))
      ((hr'.comp a.symm.injective).bijective_of_finite), Finset.mem_univ _, ?_⟩
    funext i
    simp

end PositivityTheory.Rg.Sw.LVs.CEq

namespace PositivityTheory.Rg.Sw.LVs

theorem equivar : Equivar := CEq.equivar_thm

theorem reindex : Reindex := CEq.reindex_thm

end PositivityTheory.Rg.Sw.LVs
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyG
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem analyticAt_det {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T.det) X := by
  have he : ∀ a b : ι, AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T a b) X := fun a b =>
    ((ContinuousLinearMap.proj b).comp
      (ContinuousLinearMap.proj a : (ι → ι → ℂ) →L[ℂ] (ι → ℂ))).analyticAt X
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => he (σ i) i)

theorem analyticAt_det_one_add_zpow {ι : Type} [Fintype ι] [DecidableEq ι] (t : ℤ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det ^ t) 0 := by
  have h1 : AnalyticAt ℂ (fun T : Matrix ι ι ℂ => (1 + T).det) 0 :=
    (analyticAt_det (1 + 0)).comp (analyticAt_const.add analyticAt_id)
  exact h1.zpow (by simp)

theorem cayley_of (hE : Equivar) (hR : Reindex) (hK : KappaFin) : Cayley := by
  intro ι _ _ A t
  set e := Fintype.equivFin ι
  have h1 := hE ι (fun T : Matrix ι ι ℂ => (1 + T).det ^ t) A (analyticAt_det_one_add_zpow t)
  have h2 := hR ι (Fin (Fintype.card ι)) e
    (fun S : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ => (1 + S).det ^ t)
    (analyticAt_det_one_add_zpow t)
  have h3 : (fun T : Matrix ι ι ℂ => (1 + Matrix.reindex e e T).det ^ t) =
      fun T => (1 + T).det ^ t := by
    funext T
    have h4 : 1 + Matrix.reindex e e T = Matrix.reindex e e (1 + T) := by
      ext i j
      simp [Matrix.one_apply]
    rw [h4, Matrix.det_reindex_self]
  rw [h3, hK] at h2
  rw [h1, h2, mul_comm]

end PositivityTheory.Rg.Sw.LVs
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffB
section
noncomputable section

open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace STD

variable {n : ℕ}

theorem contDiffOn_dc {U : Set (Vr n)} (hU : IsOpen U) {f : Vr n → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    (a : Fin n × Fin n) : ContDiffOn ℝ ∞ (dc a f) U := by
  have h1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x) U := hf.fderiv_of_isOpen hU (by simp)
  exact (h1.clm_apply contDiffOn_const).add (contDiffOn_const.mul (h1.clm_apply contDiffOn_const))

theorem contDiffOn_dList {U : Set (Vr n)} (hU : IsOpen U) {f : Vr n → ℂ} (hf : ContDiffOn ℝ ∞ f U) :
    ∀ l : List (Fin n × Fin n), ContDiffOn ℝ ∞ (dList l f) U
  | [] => hf
  | a :: l => contDiffOn_dc hU (contDiffOn_dList hU hf l) a

structure IsT (U : Set (Vr n)) (φ : Vr n → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  cpt : HasCompactSupport φ
  sub : tsupport φ ⊆ U

theorem support_dc_subset (f : Vr n → ℂ) (a : Fin n × Fin n) : support (dc a f) ⊆ tsupport f := by
  intro x hx
  by_contra h
  apply hx
  have : fderiv ℝ f x = 0 := by
    by_contra h'
    exact h (support_fderiv_subset (𝕜 := ℝ) h')
  simp [dc, this]

theorem isT_dc {U : Set (Vr n)} {φ : Vr n → ℂ} (h : IsT U φ) (a : Fin n × Fin n) : IsT U (dc a φ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact contDiffOn_univ.mp (contDiffOn_dc isOpen_univ (contDiffOn_univ.mpr h.smooth) a)
  · exact h.cpt.mono' (support_dc_subset φ a)
  · exact (closure_minimal (support_dc_subset φ a) (isClosed_tsupport φ)).trans h.sub

theorem isT_dList {U : Set (Vr n)} {φ : Vr n → ℂ} (h : IsT U φ) : ∀ l : List (Fin n × Fin n), IsT U (dList l φ)
  | [] => h
  | a :: l => isT_dc (isT_dList h l) a

theorem tsupport_dList_subset (φ : Vr n → ℂ) : ∀ l : List (Fin n × Fin n), tsupport (dList l φ) ⊆ tsupport φ
  | [] => le_rfl
  | a :: l => (closure_minimal ((support_dc_subset _ a).trans (tsupport_dList_subset φ l))
      (isClosed_tsupport φ))

theorem integrable_mul_of_contOn {U : Set (Vr n)} (hU : IsOpen U) {h φ : Vr n → ℂ} (hh : ContinuousOn h U)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    Integrable (fun x => h x * φ x) := by
  have hc' : Continuous (fun x => h x * φ x) :=
    (hh.mul hφ.continuousOn).continuous_of_tsupport_subset hU ((tsupport_mul_subset_right).trans hs)
  exact hc'.integrable_of_hasCompactSupport hc.mul_left

theorem ibp_dc {U : Set (Vr n)} (hU : IsOpen U) {F φ : Vr n → ℂ} (hF : ContDiffOn ℝ ∞ F U)
    (hφ : IsT U φ) (a : Fin n × Fin n) :
    ∫ x, F x * dc a φ x = - ∫ x, dc a F x * φ x := by
  have hFd : ∀ x ∈ tsupport φ, DifferentiableAt ℝ F x := fun x hx =>
    (hF.contDiffAt (hU.mem_nhds (hφ.sub hx))).differentiableAt (by simp)
  have hφd : ∀ x ∈ tsupport F, DifferentiableAt ℝ φ x := fun x _ =>
    (hφ.smooth.differentiable (by simp)) x
  have hFc : ContinuousOn (fun x => fderiv ℝ F x) U := hF.continuousOn_fderiv_of_isOpen hU (by simp)
  have hφc : Continuous (fun x => fderiv ℝ φ x) := hφ.smooth.continuous_fderiv (by simp)
  have hA : ∀ v : Vr n, Integrable (fun x => fderiv ℝ F x v * φ x) := fun v =>
    integrable_mul_of_contOn hU (hFc.clm_apply continuousOn_const) hφ.smooth.continuous hφ.cpt hφ.sub
  have hB : ∀ v : Vr n, Integrable (fun x => F x * fderiv ℝ φ x v) := fun v =>
    integrable_mul_of_contOn hU hF.continuousOn (hφc.clm_apply continuous_const)
      (hφ.cpt.fderiv_apply ℝ v)
      ((closure_minimal (fun x hx => support_fderiv_subset ℝ
        (fun h0 => (Function.mem_support.mp hx) (by simp [h0])))
        (isClosed_tsupport φ)).trans hφ.sub)
  have key : ∀ v : Vr n, ∫ x, F x * fderiv ℝ φ x v = - ∫ x, fderiv ℝ F x v * φ x := fun v =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hA v) (hB v)
      (integrable_mul_of_contOn hU hF.continuousOn hφ.smooth.continuous hφ.cpt hφ.sub) hFd hφd
  have e1 : ∫ x, F x * dc a φ x
      = (∫ x, F x * fderiv ℝ φ x (v1 a.1 a.2)) + Complex.I * ∫ x, F x * fderiv ℝ φ x (v2 a.1 a.2) := by
    rw [← integral_const_mul, ← integral_add (hB _) ((hB _).const_mul _)]
    congr 1
    funext x
    simp only [dc]
    ring
  have e2 : ∫ x, dc a F x * φ x
      = (∫ x, fderiv ℝ F x (v1 a.1 a.2) * φ x) + Complex.I * ∫ x, fderiv ℝ F x (v2 a.1 a.2) * φ x := by
    rw [← integral_const_mul, ← integral_add (hA _) ((hA _).const_mul _)]
    congr 1
    funext x
    simp only [dc]
    ring
  rw [e1, e2, key, key]
  ring

theorem ibp_dList {U : Set (Vr n)} (hU : IsOpen U) :
    ∀ (l : List (Fin n × Fin n)) {F φ : Vr n → ℂ}, ContDiffOn ℝ ∞ F U → IsT U φ →
      ∫ x, F x * dList l φ x = (-1) ^ l.length * ∫ x, dList l.reverse F x * φ x := by
  intro l
  match l with
  | [] => intro F φ _ _; simp [dList]
  | a :: l =>
    intro F φ hF hφ
    have happ : ∀ (l m : List (Fin n × Fin n)) (f : Vr n → ℂ), dList (l ++ m) f = dList l (dList m f) := by
      intro l m f
      induction l with
      | nil => simp [dList]
      | cons b l ih => simp [dList, ih]
    have h1 := ibp_dc hU hF (isT_dList hφ l) a
    have h2 := ibp_dList hU l (contDiffOn_dc hU hF a) hφ
    rw [dList, h1, h2, List.reverse_cons, happ]
    simp only [dList, List.length_cons, pow_succ]
    ring

end STD

end PositivityTheory.Rg.Sw.LVs
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatA
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem cm_mul_cmI : Cm n * CmI n = 1 := by
  rw [Cm, CmI, Matrix.mul_smul, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj]
  simp [smul_smul]
  have h : -(Complex.I * 2⁻¹ * Complex.I + Complex.I * 2⁻¹ * Complex.I) = 1 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← neg_add, ← add_smul, ← neg_smul, h, one_smul]

theorem cmI_mul_cm : CmI n * Cm n = 1 := by
  rw [Cm, CmI, Matrix.smul_mul, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj]
  simp [smul_smul]
  have h : -(Complex.I * 2⁻¹ * Complex.I + Complex.I * 2⁻¹ * Complex.I) = 1 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← neg_add, ← add_smul, ← neg_smul, h, one_smul]

theorem cm_inv : (Cm n)⁻¹ = CmI n := Matrix.inv_eq_right_inv cm_mul_cmI

theorem cmH_JJ_cm : (Cm n)ᴴ * JJ n * Cm n = fromBlocks ((-(2 * Complex.I)) • 1) 0 0 ((2 * Complex.I) • 1) := by
  rw [Cm, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  simp [smul_smul]
  refine ⟨?_, ?_⟩
  · rw [← neg_add, ← add_smul, two_mul]
  · rw [← add_smul, two_mul]

end PositivityTheory.Rg.Sw.LVs.TC
end
end

