module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.FixOfPerp
section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ}

def sigI (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgnI (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem sigI_val (i : Fin (2 * r + k + 1)) :
    (sigI k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl

theorem hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sigI k r i then sgnI k r i else 0 := by
  unfold Hpk sgnI
  simp only [Fin.ext_iff, sigI_val]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem sig_sig (i : Fin (2 * r + k + 1)) : sigI k r (sigI k r i) = i := by
  apply Fin.ext; rw [sigI_val, sigI_val]; split_ifs <;> omega

theorem sgn_sig (i : Fin (2 * r + k + 1)) : sgnI k r (sigI k r i) = sgnI k r i := by
  unfold sgnI; rw [sigI_val]; split_ifs <;> first | rfl | (exfalso; omega)

theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgnI k r i * sgnI k r i = 1 := by
  unfold sgnI; split_ifs <;> norm_num

theorem star_sgn (i : Fin (2 * r + k + 1)) : star (sgnI k r i) = sgnI k r i := by
  unfold sgnI; split_ifs <;> simp

theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = sgnI k r i * v (sigI k r i) := by
  simp only [mulVec, dotProduct, hpk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem hpk_invol (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i; rw [hpk_mulVec, hpk_mulVec, sig_sig, sgn_sig, ← mul_assoc, sgn_mul_self, one_mul]

abbrev EE (k r : ℕ) := EuclideanSpace ℂ (Fin (2 * r + k + 1))

def HE (k r : ℕ) : EE k r →ₗ[ℂ] EE k r := Matrix.toEuclideanLin (Hpk k r)

theorem HE_apply (x : EE k r) : HE k r x = WithLp.toLp 2 (Hpk k r *ᵥ x.ofLp) :=
  Matrix.toLpLin_apply 2 2 (Hpk k r) x

theorem HE_HE (x : EE k r) : HE k r (HE k r x) = x := by
  rw [HE_apply, HE_apply, WithLp.ofLp_toLp, hpk_invol]

def sigE (k r : ℕ) : Fin (2 * r + k + 1) ≃ Fin (2 * r + k + 1) := ⟨sigI k r, sigI k r, sig_sig, sig_sig⟩

theorem HE_adj (x y : EE k r) : inner ℂ (HE k r x) y = inner ℂ x (HE k r y) := by
  simp only [HE_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, hpk_mulVec, Pi.star_apply]
  refine Fintype.sum_equiv (sigE k r) _ _ (fun i => ?_)
  simp only [sigE, Equiv.coe_fn_mk, sig_sig, sgn_sig, star_mul', star_sgn]; ring

theorem herm_eq (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = inner ℂ (WithLp.toLp 2 w : EE k r) (HE k r (WithLp.toLp 2 v)) := by
  rw [HE_apply, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, WithLp.ofLp_toLp, herm,
    dotProduct_comm]

theorem fix_of_perp (c : Fin (r + 1) → EE k r) (hc : Orthonormal ℂ c)
    (hiso : ∀ a b, inner ℂ (c a) (HE k r (c b)) = 0) (x : EE k r)
    (hx1 : ∀ a, inner ℂ (c a) x = 0) (hx2 : ∀ a, inner ℂ (HE k r (c a)) x = 0) : HE k r x = x := by
  set Vm : Submodule ℂ (EE k r) := LinearMap.ker (HE k r + LinearMap.id) with hVm
  set d : Fin (r + 1) → EE k r := fun a => c a - HE k r (c a) with hd
  have hdV : ∀ a, d a ∈ Vm := fun a => by
    simp only [hVm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, hd, map_sub, HE_HE]; abel
  have hdd : ∀ a b, inner ℂ (d a) (d b) = if a = b then 2 else 0 := by
    intro a b
    simp only [hd, inner_sub_left, inner_sub_right, HE_adj, HE_HE, hiso, orthonormal_iff_ite.1 hc]
    split_ifs <;> norm_num
  have hind : LinearIndependent ℂ d := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun a h => ?_) (fun a b hab => ?_)
    · have := hdd a a; rw [h, inner_zero_left, if_pos rfl] at this; norm_num at this
    · show inner ℂ (d a) (d b) = 0
      rw [hdd, if_neg hab]
  have hfin : Module.finrank ℂ Vm ≤ r + 1 := by
    let idx : Fin (r + 1) → Fin (2 * r + k + 1) := fun a =>
      ⟨if a.val < r then a.val else r + k, by split_ifs <;> omega⟩
    let π : Vm →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
      { toFun := fun v a => (v : EE k r).ofLp (idx a)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective π := by
      refine (injective_iff_map_eq_zero π).2 fun v hv => ?_
      have hx : ∀ i, sgnI k r i * (v : EE k r).ofLp (sigI k r i) = -(v : EE k r).ofLp i := by
        intro i
        have h1 := v.2
        simp only [hVm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply] at h1
        have h2 := congrArg (fun z : EE k r => z.ofLp i) h1
        simp only [HE_apply, WithLp.ofLp_add, WithLp.ofLp_toLp, Pi.add_apply, hpk_mulVec, WithLp.ofLp_zero,
          Pi.zero_apply] at h2
        linear_combination h2
      have h0 : ∀ i : Fin (2 * r + k + 1), i.val < r → (v : EE k r).ofLp i = 0 := by
        intro i hi
        have := congrFun hv ⟨i.val, by omega⟩
        have e : idx ⟨i.val, by omega⟩ = i := Fin.ext (by simp [idx, hi])
        change (v : EE k r).ofLp (idx ⟨i.val, by omega⟩) = 0 at this
        rwa [e] at this
      have hrk : ∀ i : Fin (2 * r + k + 1), i.val = r + k → (v : EE k r).ofLp i = 0 := by
        intro i hi
        have := congrFun hv ⟨r, by omega⟩
        have e : idx ⟨r, by omega⟩ = i := Fin.ext (by simp [idx, hi])
        change (v : EE k r).ofLp (idx ⟨r, by omega⟩) = 0 at this
        rwa [e] at this
      have hall : ∀ i, (v : EE k r).ofLp i = 0 := by
        intro i
        by_cases h1 : i.val < r
        · exact h0 i h1
        by_cases h2 : i.val = r + k
        · exact hrk i h2
        have hs := hx i
        by_cases h3 : i.val < r + k
        · have e1 : sigI k r i = i := Fin.ext (by rw [sigI_val]; split_ifs <;> omega)
          have e2 : sgnI k r i = 1 := by unfold sgnI; rw [if_neg h2]
          rw [e1, e2, one_mul] at hs
          have h4 : (2 : ℂ) * (v : EE k r).ofLp i = 0 := by linear_combination hs
          simpa using h4
        · have e3 : (sigI k r i).val < r := by rw [sigI_val]; split_ifs <;> omega
          rw [h0 _ e3, mul_zero] at hs
          exact neg_eq_zero.1 hs.symm
      apply Subtype.ext
      show (v : EE k r) = 0
      ext i
      simpa using hall i
    simpa using LinearMap.finrank_le_finrank_of_injective hinj
  have hspan : Submodule.span ℂ (Set.range d) = Vm := by
    apply Submodule.eq_of_le_of_finrank_le
    · rw [Submodule.span_le]; rintro _ ⟨a, rfl⟩; exact hdV a
    · rw [finrank_span_eq_card hind, Fintype.card_fin]; exact hfin
  have heV : x - HE k r x ∈ Vm := by
    simp only [hVm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, map_sub, HE_HE]; abel
  rw [← hspan] at heV
  obtain ⟨coef, hcoef⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 heV
  have hxd : ∀ a, inner ℂ x (d a) = 0 := fun a => by
    rw [hd, inner_sub_right, inner_eq_zero_symm.1 (hx1 a), inner_eq_zero_symm.1 (hx2 a), sub_zero]
  have hxe : inner ℂ x (x - HE k r x) = 0 := by
    rw [← hcoef, inner_sum]; exact Finset.sum_eq_zero fun a _ => by rw [inner_smul_right, hxd, mul_zero]
  have h1 : inner ℂ (HE k r x) (x - HE k r x) = -inner ℂ x (x - HE k r x) := by
    simp only [HE_adj, map_sub, HE_HE, inner_sub_right]; ring
  have hee : inner ℂ (x - HE k r x) (x - HE k r x) = 0 := by
    rw [inner_sub_left, h1, hxe]; ring
  have := inner_self_eq_zero.1 hee
  rw [sub_eq_zero] at this; exact this.symm

end ReciprocityTheory.ChartRestriction.DS.Xi.GS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.GramReDetLe
section
noncomputable section

open Matrix InnerProductSpace
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GSB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS

variable {n m : ℕ}

theorem gram_det_zero (w : Fin m → EuclideanSpace ℂ (Fin n)) (hw : ¬ LinearIndependent ℂ w) :
    (GS.gram w).det = 0 := by
  rw [Fintype.not_linearIndependent_iff] at hw
  obtain ⟨g, hg, i, hi⟩ := hw
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨g, fun h => hi (congrFun h i), ?_⟩
  funext a
  simp only [mulVec, dotProduct, GS.gram, Matrix.of_apply, Pi.zero_apply]
  have hs : ∑ b, inner ℂ (w a) (w b) * g b = inner ℂ (w a) (∑ b, g b • w b) := by
    rw [inner_sum]
    congr 1
    funext b
    rw [inner_smul_right]
    ring
  rw [hs, hg, inner_zero_right]

theorem gram_re_det_le (v : Fin m → EuclideanSpace ℂ (Fin n)) (M : ℝ) (hM : ∀ j, ‖v j‖ ≤ M) :
    (GS.gram v).det.re ≤ (M ^ 2) ^ m := by
  by_cases hv : LinearIndependent ℂ v
  · obtain ⟨u, τ, hu, hτ, -, hwe, -⟩ := gs_fac v hv
    rw [det_gram_of v u τ hu hτ hwe, Complex.ofReal_re]
    have hτj : ∀ j, ‖τ j j‖ ≤ M := by
      intro j
      have h1 : inner ℂ (u j) (v j) = τ j j := by
        rw [hwe j]; exact hu.inner_right_fintype (fun b => τ b j) j
      rw [← h1]
      calc ‖inner ℂ (u j) (v j)‖ ≤ ‖u j‖ * ‖v j‖ := norm_inner_le_norm _ _
        _ = ‖v j‖ := by rw [hu.1 j, one_mul]
        _ ≤ M := hM j
    calc ∏ j, ‖τ j j‖ ^ 2 ≤ ∏ _j : Fin m, M ^ 2 :=
          Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hτj j) 2
      _ = (M ^ 2) ^ m := by simp
  · rw [gram_det_zero v hv, Complex.zero_re]
    by_cases hm : m = 0
    · subst hm; simp
    · exact pow_nonneg (sq_nonneg M) m

end ReciprocityTheory.ChartRestriction.DS.Xi.GSB

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GSB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS

def linA {k r : ℕ} (A : Mat k r) :
    EuclideanSpace ℂ (Fin (2 * r + k + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
  (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap ∘ₗ Matrix.toLin' A ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).toLinearMap

theorem linA_apply {k r : ℕ} (A : Mat k r) (x : EuclideanSpace ℂ (Fin (2 * r + k + 1))) :
    linA A x = WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) := rfl

theorem gram_one {m n : ℕ} (u : Fin m → EuclideanSpace ℂ (Fin n)) (hu : Orthonormal ℂ u) : GS.gram u = 1 := by
  ext a b
  simp only [GS.gram, Matrix.of_apply, Matrix.one_apply]
  exact orthonormal_iff_ite.mp hu a b

theorem ga_mul_le (k r : ℕ) (A : Mat k r) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => A *ᵥ Y a) ≤ (gN A ^ 2) ^ (l.val + 1) * Ga k r l Y := by
  rw [ga_eq, ga_eq]
  set w : Fin (l.val + 1) → EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    fun a => WithLp.toLp 2 (Y (Fin.castLE (by omega) a)) with hwdef
  have hAw : (fun a : Fin (l.val + 1) =>
      (WithLp.toLp 2 (A *ᵥ Y (Fin.castLE (by omega) a)) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) =
      fun a => linA A (w a) := by
    funext a; rw [linA_apply]
  rw [hAw]
  by_cases hw : LinearIndependent ℂ w
  · obtain ⟨u, τ, hu, hτ, -, hwe, -⟩ := gs_fac w hw
    have h1 : (fun a => linA A (w a)) = fun a => ∑ b, τ b a • linA A (u b) := by
      funext a; rw [hwe a, map_sum]; simp only [map_smul]
    have hgw : (GS.gram w).det = (τᴴ).det * τ.det := by
      rw [show w = (fun a => ∑ b, τ b a • u b) from funext hwe, gram_comb, gram_one u hu, Matrix.mul_one, det_mul]
    have hv : ∀ b, ‖linA A (u b)‖ ≤ gN A := by
      intro b
      have := norm_mulVec_le A (WithLp.ofLp (u b))
      rw [WithLp.toLp_ofLp, hu.1 b, mul_one] at this
      rw [linA_apply]; exact this
    have hle := gram_re_det_le (fun b => linA A (u b)) (gN A) hv
    have hX := det_gram_of w u τ hu hτ hwe
    rw [h1, gram_comb, det_mul, det_mul]
    have e1 : (τᴴ).det * (GS.gram fun b => linA A (u b)).det * τ.det =
        (GS.gram w).det * (GS.gram fun b => linA A (u b)).det := by rw [hgw]; ring
    rw [e1, hX, Complex.re_ofReal_mul]
    have hnn : (0 : ℝ) ≤ ∏ j, ‖τ j j‖ ^ 2 := Finset.prod_nonneg fun j _ => by positivity
    rw [Complex.ofReal_re, mul_comm]
    exact mul_le_mul_of_nonneg_right hle hnn
  · have hw' : ¬ LinearIndependent ℂ (fun a => linA A (w a)) := fun h => hw (h.of_comp (linA A))
    rw [gram_det_zero _ hw', gram_det_zero _ hw, Complex.zero_re, mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Xi.GSB
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergMapContinuous
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem pt_bound {N a u v p q : ℝ} (ha : 0 < a) (hu : 0 ≤ u) (hv : 0 ≤ v) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h1 : a ≤ N) (h2 : u ≤ N) (h3 : v ≤ N) :
    N ^ (-(p + q)) ≤ 2 ^ (p + q) * ((a + u) ^ (-p) * (a + v) ^ (-q)) := by
  have hN : 0 < N := lt_of_lt_of_le ha h1
  have hau : 0 < a + u := by linarith
  have hav : 0 < a + v := by linarith
  have hmono : ∀ {x e : ℝ}, 0 < x → x ≤ 2 * N → 0 ≤ e → (2 * N) ^ (-e) ≤ x ^ (-e) := by
    intro x e hx hxN he
    rw [Real.rpow_neg (by linarith), Real.rpow_neg hx.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hx e) (Real.rpow_le_rpow hx.le hxN he)
  have e1 : (2 * N) ^ (-p) ≤ (a + u) ^ (-p) := hmono hau (by linarith) hp
  have e2 : (2 * N) ^ (-q) ≤ (a + v) ^ (-q) := hmono hav (by linarith) hq
  have key : 2 ^ (p + q) * ((2 * N) ^ (-p) * (2 * N) ^ (-q)) = N ^ (-(p + q)) := by
    rw [← Real.rpow_add (by positivity : (0:ℝ) < 2 * N), Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hN.le,
      ← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2), show p + q + (-p + -q) = (0:ℝ) by ring,
      Real.rpow_zero, one_mul, neg_add]
  rw [← key]
  exact mul_le_mul_of_nonneg_left (mul_le_mul e1 e2 (by positivity) (by positivity)) (by positivity)

theorem liftVec_cont (k r' : ℕ) : Continuous fun y : Fin (2 * r' + k + 1) → ℂ => liftVec k 1 r' y := by
  apply continuous_pi
  intro p
  simp only [liftVec]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

def heisM (k r' : ℕ) : HPar k r' → Mt k (1 + r') := fun x => heis0 k r' x

theorem heisenberg_map_continuous (k r' : ℕ) : Continuous (heisM k r') := by
  have hl := liftVec_cont k r'
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [heisM, heis0, heisG, hb, herm, Matrix.add_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Matrix.mulVec, Pi.star_apply]
  fun_prop

theorem heisenberg_at_zero (k r' : ℕ) : heis0 k r' (0, 0) = 1 := by
  have hz : liftVec k 1 r' 0 = 0 := by
    funext p
    simp only [liftVec, Pi.zero_apply]
    split_ifs <;> rfl
  ext i j
  simp [heis0, heisG, hb, herm, hz, Matrix.vecMulVec]

theorem ιLev_inv_mul (hCL : HeisConjLev) (k r' : ℕ) (g : Mat k r') (hg : g ∈ GV k r') :
    (ιLev k 1 r' g)⁻¹ * ιLev k 1 r' g = 1 := by
  have h := hCL k r' g hg (0, 0)
  simp only [heisenberg_at_zero, mul_one, Matrix.mulVec_zero] at h
  first
  | exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse h)
  | exact mul_eq_one_comm.mp h
  | exact (Matrix.mul_eq_one_comm).1 h

theorem gN_cont (k n : ℕ) : Continuous fun M : Mat k n => gN M := by
  simp only [gN]
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

theorem int_conj (hCL : HeisConjLev) (hCM : HeisConjLevMeas) (k r' : ℕ) (A : ℝ) (c : ℂ) (g : Mat k r')
    (hg : g ∈ GV k r') :
    ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A)) =
      ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ^ (-A)) := by
  have hinv : (ιLev k 1 r' g)⁻¹ * ιLev k 1 r' g = 1 := ιLev_inv_mul hCL k r' g hg
  have hgN := gN_cont k (1 + r')
  have hcm : Continuous fun M : Mt k (1 + r') => w0 k r' c * Matrix.of M * ιLev k 1 r' g :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hH : Measurable fun M : Mt k (1 + r') =>
      ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)) :=
    ((hgN.comp hcm).measurable.pow_const _).ennreal_ofReal
  have hcc : Continuous (conjM (ιLev k 1 r' g) : Mt k (1 + r') → Mt k (1 + r')) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hconj : Measurable (conjM (ιLev k 1 r' g) : Mt k (1 + r') → Mt k (1 + r')) := hcc.measurable
  have hheis : Measurable (heisM k r') := (heisenberg_map_continuous k r').measurable
  have hL : ∀ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A)) =
      (fun M : Mt k (1 + r') => ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)))
        (conjM (ιLev k 1 r' g) (heis0 k r' x)) := by
    intro x
    have e : w0 k r' c * Matrix.of (conjM (ιLev k 1 r' g) (heis0 k r' x)) * ιLev k 1 r' g =
        w0 k r' c * ιLev k 1 r' g * heis0 k r' x := by
      change w0 k r' c * (ιLev k 1 r' g * heis0 k r' x * (ιLev k 1 r' g)⁻¹) * ιLev k 1 r' g =
        w0 k r' c * ιLev k 1 r' g * heis0 k r' x
      simp only [mul_assoc, hinv, mul_one]
    simp only [e]
  calc ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A))
      = ∫⁻ x : HPar k r', (fun M : Mt k (1 + r') =>
          ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)))
            (conjM (ιLev k 1 r' g) (heis0 k r' x)) := lintegral_congr fun x => hL x
    _ = ∫⁻ M, (fun M : Mt k (1 + r') =>
          ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)))
            (conjM (ιLev k 1 r' g) M) ∂(μHeis k r') := (lintegral_map (hH.comp hconj) hheis).symm
    _ = ∫⁻ M, ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A))
          ∂((μHeis k r').map (conjM (ιLev k 1 r' g))) := (lintegral_map hH hconj).symm
    _ = ∫⁻ M, ENNReal.ofReal (gN (w0 k r' c * Matrix.of M * ιLev k 1 r' g) ^ (-A)) ∂(μHeis k r') := by
          rw [hCM k r' g hg]
    _ = ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * Matrix.of (heis0 k r' x : Mt k (1 + r')) * ιLev k 1 r' g) ^ (-A)) :=
          lintegral_map hH hheis
    _ = _ := rfl

theorem int_prod (k r' : ℕ) {A p q K₁ K₂ e₁ e₂ : ℝ} (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hK₁ : ∀ a b : ℝ, 0 < a → 0 < b → ∫⁻ y : Fin (2 * r' + k + 1) → ℂ, ENNReal.ofReal ((a + b * ‖y‖) ^ (-p)) ≤
      ENNReal.ofReal (K₁ * a ^ (-p) * (a / b) ^ e₁))
    (hK₂ : ∀ a b : ℝ, 0 < a → 0 < b → ∫⁻ s : ℝ, ENNReal.ofReal ((a + b * ‖s‖) ^ (-q)) ≤
      ENNReal.ofReal (K₂ * a ^ (-q) * (a / b) ^ e₂))
    (F : HPar k r' → ℝ≥0∞) {a b₁ b₂ : ℝ} (ha : 0 < a) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hF : ∀ x : HPar k r', F x ≤
      ENNReal.ofReal (2 ^ A * ((a + b₁ * ‖x.1‖) ^ (-p) * (a + b₂ * ‖x.2‖) ^ (-q)))) :
    ∫⁻ x, F x ≤ ENNReal.ofReal (2 ^ A * (K₁ * a ^ (-p) * (a / b₁) ^ e₁) * (K₂ * a ^ (-q) * (a / b₂) ^ e₂)) := by
  have hf₁ : Measurable fun y : Fin (2 * r' + k + 1) → ℂ => ENNReal.ofReal ((a + b₁ * ‖y‖) ^ (-p)) :=
    ((measurable_const.add (measurable_const.mul measurable_norm)).pow_const _).ennreal_ofReal
  have hf₂ : Measurable fun s : ℝ => ENNReal.ofReal ((a + b₂ * ‖s‖) ^ (-q)) :=
    ((measurable_const.add (measurable_const.mul measurable_norm)).pow_const _).ennreal_ofReal
  have hX : 0 ≤ K₁ * a ^ (-p) * (a / b₁) ^ e₁ :=
    mul_nonneg (mul_nonneg hK₁0 (Real.rpow_nonneg ha.le _)) (Real.rpow_nonneg (div_pos ha hb₁).le _)
  have h2A : (0 : ℝ) ≤ 2 ^ A := by positivity
  calc ∫⁻ x, F x ≤ ∫⁻ x : HPar k r', ENNReal.ofReal (2 ^ A) *
        (ENNReal.ofReal ((a + b₁ * ‖x.1‖) ^ (-p)) * ENNReal.ofReal ((a + b₂ * ‖x.2‖) ^ (-q))) := by
        refine lintegral_mono fun x => (hF x).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul h2A, ENNReal.ofReal_mul (Real.rpow_nonneg
          (add_nonneg ha.le (mul_nonneg hb₁.le (norm_nonneg _))) _)]
    _ = ENNReal.ofReal (2 ^ A) * ((∫⁻ y : Fin (2 * r' + k + 1) → ℂ, ENNReal.ofReal ((a + b₁ * ‖y‖) ^ (-p))) *
          ∫⁻ s : ℝ, ENNReal.ofReal ((a + b₂ * ‖s‖) ^ (-q))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_prod_mul (μ := (volume : Measure (Fin (2 * r' + k + 1) → ℂ)))
          (ν := (volume : Measure ℝ)) hf₁.aemeasurable hf₂.aemeasurable
    _ ≤ ENNReal.ofReal (2 ^ A) * (ENNReal.ofReal (K₁ * a ^ (-p) * (a / b₁) ^ e₁) *
          ENNReal.ofReal (K₂ * a ^ (-q) * (a / b₂) ^ e₂)) := by
        gcongr
        · exact hK₁ a b₁ ha hb₁
        · exact hK₂ a b₂ ha hb₂
    _ = _ := by
        rw [← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_mul h2A]
        congr 1
        ring

theorem eInt_bound' (hGL : GNLower) (hHA : HeisAct) (hCL : HeisConjLev) (hCM : HeisConjLevMeas)
    (k r' : ℕ) (A : ℝ) (hA : ((4 * r' + 2 * k + 3 : ℕ) : ℝ) < A) :
    ∃ C : ℝ, ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r',
      ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A)) ≤
        ENNReal.ofReal (C * min (‖c‖ ^ (-((4 * r' + 2 * k + 3 : ℕ) : ℝ))) ‖c‖⁻¹ *
          gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)) := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = ((4 * r' + 2 * k + 3 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hd] at hA ⊢
  have hd3 : (3 : ℝ) ≤ d := by rw [hd]; norm_cast; omega
  have hE : (Module.finrank ℝ (Fin (2 * r' + k + 1) → ℂ) : ℝ) = d - 1 := by
    rw [Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    rw [hd]; push_cast; ring
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = d - 1 + (A - d) / 2 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 + (A - d) / 2 := ⟨_, rfl⟩
  have hpq : p + q = A := by rw [hp, hq]; ring
  have hp0 : 0 ≤ p := by rw [hp]; linarith
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  obtain ⟨K₁, hK₁0, hK₁⟩ := scale_int (volume : Measure (Fin (2 * r' + k + 1) → ℂ)) (r := p)
    (by rw [hE, hp]; linarith)
  obtain ⟨K₂, hK₂0, hK₂⟩ := scale_int (volume : Measure ℝ) (r := q)
    (by simp only [Module.finrank_self, Nat.cast_one]; rw [hq]; linarith)
  rw [hE] at hK₁
  simp only [Module.finrank_self, Nat.cast_one] at hK₂
  refine ⟨2 ^ A * K₁ * K₂, fun c hc g hg => ?_⟩
  have ha : 0 < gN g := lt_of_lt_of_le zero_lt_one (hGL k r' g hg)
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  have B1 := int_prod k r' hK₁0 hK₂0 hK₁ hK₂
    (fun x => ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A))) ha hc0 hc0
    (fun x => by
      obtain ⟨h1, h2, h3⟩ := pt_un k r' c g x hHA
      rw [← Real.norm_eq_abs] at h3
      have := pt_bound ha (mul_nonneg hc0.le (norm_nonneg _)) (mul_nonneg hc0.le (norm_nonneg _))
        hp0 hq0 h1 h2 h3
      rw [hpq] at this
      exact ENNReal.ofReal_le_ofReal this)
  have B2 := int_prod k r' hK₁0 hK₂0 hK₁ hK₂
    (fun x => ENNReal.ofReal (gN (w0 k r' c * heis0 k r' x * ιLev k 1 r' g) ^ (-A))) ha one_pos hc0
    (fun x => by
      obtain ⟨h1, h2, h3⟩ := pt_conj k r' c g x hHA
      rw [← Real.norm_eq_abs] at h3
      rw [← one_mul ‖x.1‖] at h2
      have := pt_bound ha (by positivity) (mul_nonneg hc0.le (norm_nonneg _)) hp0 hq0 h1 h2 h3
      rw [hpq] at this
      exact ENNReal.ofReal_le_ofReal this)
  rw [← int_conj hCL hCM k r' A c g hg] at B2
  have ea : gN g ^ (d - A) = gN g ^ (-p) * gN g ^ (d - 1) * gN g ^ (-q) * gN g ^ (1 : ℝ) := by
    rw [← Real.rpow_add ha, ← Real.rpow_add ha, ← Real.rpow_add ha]
    congr 1
    linarith
  have E1 : 2 ^ A * (K₁ * gN g ^ (-p) * (gN g / ‖c‖) ^ (d - 1)) * (K₂ * gN g ^ (-q) * (gN g / ‖c‖) ^ (1 : ℝ)) =
      2 ^ A * K₁ * K₂ * ‖c‖ ^ (-d) * gN g ^ (d - A) := by
    have ec : ‖c‖ ^ (-d) = ‖c‖ ^ (-(d - 1)) * ‖c‖ ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; ring
    rw [Real.div_rpow ha.le hc0.le, Real.div_rpow ha.le hc0.le, ea, ec, Real.rpow_neg hc0.le,
      Real.rpow_neg hc0.le]
    ring
  have E2 : 2 ^ A * (K₁ * gN g ^ (-p) * (gN g / 1) ^ (d - 1)) * (K₂ * gN g ^ (-q) * (gN g / ‖c‖) ^ (1 : ℝ)) =
      2 ^ A * K₁ * K₂ * ‖c‖⁻¹ * gN g ^ (d - A) := by
    rw [div_one, Real.div_rpow ha.le hc0.le, ea, Real.rpow_one, Real.rpow_one]
    ring
  rcases le_total (‖c‖ ^ (-d)) ‖c‖⁻¹ with h | h
  · rw [min_eq_left h, ← E1]; exact B1
  · rw [min_eq_right h, ← E2]; exact B2

end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
end
end

