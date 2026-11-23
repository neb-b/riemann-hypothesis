module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0078
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0076
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0077

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace VeroneseTop

theorem sum_le_weighted {n : ℕ} (f : Fin n × Fin n → ℝ) (hf : ∀ i j, f (i, j) = f (j, i)) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2), (if p.1 = p.2 then (1 : ℝ) else 2) * f p =
      ∑ p, f p := by
  have h1 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1), f p =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), f p := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simpa using hp
    · intro p hp
      simpa using hp
    · intro p _
      rfl
    · intro p _
      rfl
    · intro p _
      exact hf p.1 p.2
  have h2 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), f p =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2), (if p.1 = p.2 then 0 else f p) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_filter]
    congr 1
    ext p
    simp [lt_iff_le_and_ne]
  have h3 : Finset.univ.filter (fun p : Fin n × Fin n => ¬ p.1 ≤ p.2) =
      Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1) := by
    ext p
    simp
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Fin n × Fin n => p.1 ≤ p.2), h3, h1, h2,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> ring

theorem sum_wt_mul {D : ℕ} (a : Fin (D + 1) → ℝ) :
    ∑ q : Ix (Veronese.Idx D), Veronese.wt q * (a q.2.1.1 * a q.2.1.2) = (∑ i, a i) ^ 2 := by
  rw [Fintype.sum_sigma, Fintype.sum_unique]
  calc ∑ y : Veronese.Idx D, Veronese.wt (⟨default, y⟩ : Ix (Veronese.Idx D)) * (a y.1.1 * a y.1.2)
      = ∑ y : Veronese.Idx D, (if y.1.1 = y.1.2 then (1 : ℝ) else 2) * (a y.1.1 * a y.1.2) := rfl
    _ = ∑ p ∈ Finset.univ.filter (fun p : Fin (D + 1) × Fin (D + 1) => p.1 ≤ p.2),
          (if p.1 = p.2 then (1 : ℝ) else 2) * (a p.1 * a p.2) := by
      rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
    _ = ∑ p : Fin (D + 1) × Fin (D + 1), a p.1 * a p.2 :=
      sum_le_weighted (fun p => a p.1 * a p.2) (fun i j => mul_comm _ _)
    _ = (∑ i, a i) ^ 2 := by
      rw [sq, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]

theorem fs_sq {J : Type} [Fintype J] (z : J → ℂ) :
    (fsMetric (ι := J)).ρ z ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  show ‖WithLp.toLp 2 z‖ ^ 2 = _
  rw [EuclideanSpace.norm_sq_eq]

theorem fs_nonneg {J : Type} [Fintype J] (z : J → ℂ) : 0 ≤ (fsMetric (ι := J)).ρ z :=
  norm_nonneg (WithLp.toLp 2 z)

theorem metric_nonneg (D : ℕ) (u : Ix (Veronese.Idx D) → ℂ) : 0 ≤ (Veronese.metric D).ρ u :=
  fs_nonneg (Veronese.scale D u)

theorem metric_sq (D : ℕ) (u : Ix (Veronese.Idx D) → ℂ) :
    (Veronese.metric D).ρ u ^ 2 = ∑ q, Veronese.wt q * ‖u q‖ ^ 2 := by
  show (fsMetric (ι := Ix (Veronese.Idx D))).ρ (Veronese.scale D u) ^ 2 = _
  rw [fs_sq]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hw : 0 ≤ Veronese.wt q := (Veronese.wt_pos q).le
  rw [Veronese.scale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hw]

theorem formApply_forms (D : ℕ) (w : Ix (Fin (D + 1)) → ℂ) (q : Ix (Veronese.Idx D)) :
    formApply (Veronese.forms D) w q = w ⟨(), q.2.1.1⟩ * w ⟨(), q.2.1.2⟩ := by
  simp [formApply, Veronese.forms]

theorem metric_forms (D : ℕ) (w : Ix (Fin (D + 1)) → ℂ) :
    (Veronese.metric D).ρ (formApply (Veronese.forms D) w) =
      (fsMetric (ι := Ix (Fin (D + 1)))).ρ w * (fsMetric (ι := Ix (Fin (D + 1)))).ρ w := by
  have h0 : 0 ≤ (Veronese.metric D).ρ (formApply (Veronese.forms D) w) :=
    metric_nonneg D _
  have h1 : 0 ≤ (fsMetric (ι := Ix (Fin (D + 1)))).ρ w * (fsMetric (ι := Ix (Fin (D + 1)))).ρ w :=
    mul_nonneg (fs_nonneg w) (fs_nonneg w)
  refine (sq_eq_sq₀ h0 h1).1 ?_
  have hw : (fsMetric (ι := Ix (Fin (D + 1)))).ρ w * (fsMetric (ι := Ix (Fin (D + 1)))).ρ w =
      ∑ i : Fin (D + 1), ‖w ⟨(), i⟩‖ ^ 2 := by
    rw [← sq, fs_sq, Fintype.sum_sigma, Fintype.sum_unique]
  rw [hw, metric_sq, ← sum_wt_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [formApply_forms, norm_mul, mul_pow]

theorem isMultiHomog_forms (D : ℕ) (q : Ix (Veronese.Idx D)) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (Veronese.forms D q) ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) := by
  have h := Inter.AvoidRing.isMultiHomog_mul
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.1)
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.2)
  have e : ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) = Pi.single () 1 + Pi.single () 1 := by
    funext k
    cases k
    simp
  rw [e]
  exact h

theorem isBasePtFree_forms (D : ℕ) : IsBasePtFree (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (Veronese.forms D) := by
  intro k₂ i
  refine ⟨2, Ideal.mem_sup_right (Ideal.subset_span ⟨⟨(i (), i ()), le_rfl⟩, ?_⟩)⟩
  cases k₂
  simp [Veronese.forms, pow_two]

theorem tensor_self {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {F : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ} (hF : IsIntersectionFamily F)
    {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n) {T : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hT : IsSmoothHerm T) :
    F P n (fun _ => T.tensor T) = 2 ^ n * F P n (fun _ => T) := by
  have hTT : IsSmoothHerm (T.tensor T) := hT.mul hT
  have intersection_update_fsHerm_neg_one : ∀ L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (∀ i, IsSmoothHerm (L i)) → ∀ j : Fin n,
      F P n (Function.update L j (T.tensor T)) = 2 * F P n (Function.update L j T) := by
    intro L hL j
    cases n with
    | zero => exact j.elim0
    | succ m =>
      have e : ∀ X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, IsSmoothHerm X →
          F P (m + 1) (Function.update L j X) =
            F P (m + 1) (Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X) := by
        intro X hX
        rw [← Inter.ThmIMultilin.update_comp_swap]
        exact (hF.1 P (m + 1) _ _ hP (Inter.ThmIMultilin.smooth_update hL j hX)).symm
      rw [e _ hTT, e T hT, hF.2.1 P m _ T T hP (fun i => hL _) hT hT]
      ring
  have step : ∀ k, k ≤ n →
      F P n (fun i => if (i : ℕ) < k then T.tensor T else T) = 2 ^ k * F P n (fun _ => T) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      have hL : ∀ i : Fin n, IsSmoothHerm (if (i : ℕ) < k then T.tensor T else T) := by
        intro i
        split_ifs
        · exact hTT
        · exact hT
      have h1 : (fun i : Fin n => if (i : ℕ) < k + 1 then T.tensor T else T) =
          Function.update (fun i : Fin n => if (i : ℕ) < k then T.tensor T else T) ⟨k, hk⟩ (T.tensor T) := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp
        · have h' : (i : ℕ) ≠ k := fun e => h (Fin.ext e)
          rw [Function.update_of_ne h]
          by_cases hi : (i : ℕ) < k
          · simp [hi, show (i : ℕ) < k + 1 by omega]
          · simp [hi, show ¬ (i : ℕ) < k + 1 by omega]
      have h2 : Function.update (fun i : Fin n => if (i : ℕ) < k then T.tensor T else T) ⟨k, hk⟩ T =
          fun i : Fin n => if (i : ℕ) < k then T.tensor T else T := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp
        · rw [Function.update_of_ne h]
      rw [h1, intersection_update_fsHerm_neg_one _ hL, h2, ih (by omega), pow_succ]
      ring
  have hn := step n le_rfl
  simp only [Fin.is_lt, ite_true] at hn
  exact hn

end VeroneseTop


open VeroneseTop in
theorem VeroneseTop.proof (hCM : GraphChangeOfModel.Statement) (hA : VeroneseArith.Statement)
    (hIm : VeroneseGraphImage.Statement) (hDeg : VeroneseGraphDeg.Statement) : VeroneseTop.Statement := by
  intro D hD I hI
  obtain ⟨G, J, hJ, hJ1⟩ := hDeg D hD
  have hfs : IsSmoothHerm (HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))) :=
    BlockImageTop.isSmoothHerm_ofCone ProjLine.isSmoothMetric_fs
  have hP : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (D + 1) := IndefiniteRowSideFullHecke.Inter.isArithVar_bot D
  have key := hCM I hI Unit (GlobalTheory (Fin (D + 1))) Unit (GlobalTheory (Veronese.Idx D)) ⊥ (D + 1) (Veronese.forms D)
    (fun _ _ => 2) G J (fun _ => HermLine.ofCone (Veronese.metric D))
    (fun _ => (HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))).tensor
      (HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))))
    hP (isMultiHomog_forms D) (isBasePtFree_forms D) (by rw [hIm D]; exact hA D hD) hJ
    (fun _ => BlockImageTop.isSmoothHerm_ofCone (Veronese.isSmoothMetric_metric D)) (fun _ => hfs.mul hfs)
    (fun _ k => by cases k; simp [HermLine.tensor, HermLine.ofCone])
    (fun _ z _ => (metric_forms D z).symm)
  rw [hIm D, hJ1] at key
  have h2 := tensor_self (hI Unit (GlobalTheory (Fin (D + 1)))) hP hfs
  rw [Int.cast_one, one_mul] at key
  rw [top, hhOf, ← key, ← h2]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombExpand
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open GroundTheory.Heights₂.Heights.Inter (famExt famExt_apply famExt_basis famExt_symm)

noncomputable section

set_option linter.unusedSectionVars false

namespace ZCombExpand

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {J : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem famExt_symm_of (e : Fin 2 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (he : ∀ i, IsSmoothHerm (e i))
    (hJ : ∀ (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (σ : Equiv.Perm (Fin n)), (∀ j, IsSmoothHerm (L j)) →
      J P n (L ∘ σ) = J P n L) :
    IsSymmForm (famExt J P n e) := by
  intro σ v
  rw [famExt_apply, famExt_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin 2))) _ _ fun s => ?_
  have h1 : e ∘ (Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) = (e ∘ s) ∘ σ.symm := rfl
  have h2 : ∏ j, v j ((Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) j) = ∏ j, (v ∘ σ) j (s j) := by
    refine (Equiv.prod_comp σ fun j => v j (s (σ.symm j))).symm.trans ?_
    simp
  rw [h1, h2, hJ (e ∘ s) σ.symm fun j => he _]

theorem famExt_expand (e : Fin 2 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hs : IsSymmForm (famExt J P n e)) (q p : ℝ) :
    famExt J P n e (fun _ => ![q, p]) =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * q ^ (n - i) * p ^ i *
        J P n (fun j : Fin n => if (j : ℕ) < n - i then e 0 else e 1) := by
  classical
  have hw : (fun _ : Fin n => (![q, p] : Fin 2 → ℝ)) =
      fun _ => p • (Pi.single 1 1 : Fin 2 → ℝ) + q • (Pi.single 0 1 : Fin 2 → ℝ) := by
    funext j i
    fin_cases i <;> simp
  rw [hw, symm_expand _ hs, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [show n + 1 - 1 - i = n - i by omega]
  have hmix : (mix (n - i) (Pi.single 0 1) (p • Pi.single 1 1) : Fin n → Fin 2 → ℝ) =
      (Finset.univ.filter fun j : Fin n => ¬ (j : ℕ) < n - i).piecewise
        (fun j => p • (mix (n - i) (Pi.single 0 1) (Pi.single 1 1) : Fin n → Fin 2 → ℝ) j)
        (mix (n - i) (Pi.single 0 1) (Pi.single 1 1)) := by
    funext j
    by_cases h : (j : ℕ) < n - i
    · rw [Finset.piecewise_eq_of_notMem _ _ _ (by simp; omega)]
      simp [mix, h]
    · rw [Finset.piecewise_eq_of_mem _ _ _ (by simp; omega)]
      simp [mix, h]
  have hcard : (Finset.univ.filter fun j : Fin n => ¬ (j : ℕ) < n - i).card = i := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
      Fintype.card_fin, Fin.card_filter_val_lt]
    omega
  have hbasis : (mix (n - i) (Pi.single 0 1) (Pi.single 1 1) : Fin n → Fin 2 → ℝ) =
      fun j => Pi.single ((fun j : Fin n => if (j : ℕ) < n - i then (0 : Fin 2) else 1) j) 1 := by
    funext j
    simp only [mix]
    split_ifs <;> rfl
  have hlist : (e ∘ fun j : Fin n => if (j : ℕ) < n - i then (0 : Fin 2) else 1) =
      fun j : Fin n => if (j : ℕ) < n - i then e 0 else e 1 := by
    funext j
    simp only [Function.comp]
    split_ifs <;> rfl
  rw [hmix, MultilinearMap.map_piecewise_smul, Finset.prod_const, hcard, hbasis, famExt_basis, hlist,
    smul_eq_mul, Nat.choose_symm hin]
  simp only [RingHom.id_apply]
  ring

end ZCombExpand

theorem ZCombExpand.proof : ZCombExpand.Statement := by
  intro K _ ι _ I hI P d M H q p hP hM hH
  set e : Fin 2 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := ![M, H] with he_def
  have he : ∀ i, IsSmoothHerm (e i) := by
    intro i
    fin_cases i
    · exact hM
    · exact hH
  set Z := HermLine.zcomb M H (q : ℤ) (p : ℤ) with hZ_def
  have hZ : IsSmoothHerm Z := ZCombLimit.isSmoothHerm_zcomb_int hM hH _ _
  refine ⟨?_, ?_⟩
  · have hposition : ∀ (L : Fin d → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a : Fin d), (∀ j, IsSmoothHerm (L j)) →
        I P d (Function.update L a Z) =
          (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 0 * I P d (Function.update L a (e 0)) +
            (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 1 * I P d (Function.update L a (e 1)) := by
      intro L a hL
      cases d with
      | zero => exact a.elim0
      | succ m =>
        have h := ZCombLimit.fam_update_zcomb_int hI hP L hL a hM hH (q : ℤ) (p : ℤ)
        simpa [e] using h
    have key := ZCombLimit.eq_famExt_of_position (J := I) (P := P) IsSmoothHerm e Z ![(q : ℝ), (p : ℝ)] he hZ
      hposition Finset.univ (fun _ => 0)
    simp only [Finset.mem_univ, if_true] at key
    rw [key, ZCombExpand.famExt_expand e (famExt_symm hI hP e he)]
    rfl
  · intro hd
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    let J : Ideal (MRing ι) → (m : ℕ) → (Fin m → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ :=
      fun P' m L => I P' (m + 1) (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M L)
    have hcons : ∀ L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (∀ j, IsSmoothHerm (L j)) →
        ∀ j, IsSmoothHerm (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M L j) := by
      intro L hL j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hM
      · simpa using hL j
    have hsymm : ∀ (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (σ : Equiv.Perm (Fin n)), (∀ j, IsSmoothHerm (L j)) →
        J P n (L ∘ σ) = J P n L := by
      intro L σ hL
      have hc : (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M (L ∘ σ) : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) =
          (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M L) ∘ (Equiv.Perm.decomposeFin.symm (0, σ)) := by
        funext j
        refine Fin.cases ?_ (fun j => ?_) j
        · simp [Equiv.Perm.decomposeFin_symm_apply_zero]
        · simp [Equiv.Perm.decomposeFin_symm_apply_succ]
      show I P (n + 1) _ = I P (n + 1) _
      rw [hc, hI.1 P (n + 1) _ _ hP (hcons L hL)]
    have hposition : ∀ (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a : Fin n), (∀ j, IsSmoothHerm (L j)) →
        J P n (Function.update L a Z) =
          (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 0 * J P n (Function.update L a (e 0)) +
            (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 1 * J P n (Function.update L a (e 1)) := by
      intro L a hL
      show I P (n + 1) _ = _ * I P (n + 1) _ + _ * I P (n + 1) _
      rw [Fin.cons_update, Fin.cons_update, Fin.cons_update]
      have h := ZCombLimit.fam_update_zcomb_int hI hP _ (hcons L hL) a.succ hM hH (q : ℤ) (p : ℤ)
      simpa [e] using h
    have key := ZCombLimit.eq_famExt_of_position (J := J) (P := P) IsSmoothHerm e Z ![(q : ℝ), (p : ℝ)] he hZ
      hposition Finset.univ (fun _ => 0)
    simp only [Finset.mem_univ, if_true] at key
    have hl : (fun j : Fin (n + 1) => if (j : ℕ) = 0 then M else Z) =
        Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M (fun _ : Fin n => Z) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp
    rw [hl, show I P (n + 1) (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M (fun _ : Fin n => Z)) =
      J P n (fun _ => Z) from rfl, key,
      ZCombExpand.famExt_expand e (ZCombExpand.famExt_symm_of e he hsymm), Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hl2 : (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M
        (fun j : Fin n => if (j : ℕ) < n - i then e 0 else e 1) : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) =
        fun j : Fin (n + 1) => if (j : ℕ) < n + 1 - i then M else H := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero]
        exact (if_pos (show ((0 : Fin (n + 1)) : ℕ) < n + 1 - i by simp; omega)).symm
      · simp only [Fin.cons_succ, Fin.val_succ]
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd (by omega) h2
        · exact absurd (by omega) h1
        · rfl
    show _ * I P (n + 1) _ = _
    rw [hl2]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDehomNormPIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def DehomNormPIntegral.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ (p : ℕ), p.Prime → ∀ M : ℕ, ¬ p ∣ M → ∀ (j : Fin (D + 1)) (m : ℕ) (u : Ω),
      u ∈ integralClosure (Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => l i / l j))) Ω →
      ∀ c : ℕ → MvPolynomial (Fin (D + 1)) ℚ,
        (c (Module.finrank P Ω)).IsHomogeneous (Module.finrank P Ω * m) →
        (LinearMap.charpoly (Algebra.lmul P Ω u)).map (algebraMap P Ω) =
          ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
            Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) →
        ∀ μ : Fin (D + 1) →₀ ℕ, 0 ≤ padicValRat p ((c (Module.finrank P Ω)).coeff μ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormBadPrimesFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def HasCommonZeroModP (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∃ z : (Σ k, ι k) → AlgebraicClosure (ZMod p), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧
    (∀ f ∈ mCoordIdeal y, eval z (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f) = 0) ∧
    ∀ j, eval z (map (Int.castRingHom (AlgebraicClosure (ZMod p))) (L j)) = 0

end Defs

def FibreNormBadPrimesFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    {p : ℕ | ∃ hp : p.Prime, HasCommonZeroModP y L p hp}.Finite

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormDehomRoots
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormDehomRoots.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ (j : Fin (D + 1))
      (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ), IsDehomNormForms y L j (q * τ) s c →
        ∀ ζ : Fin (D + 1) → ℂ, ζ ≠ 0 → ∀ w : ℂ,
          ∑ i ∈ Finset.range (Module.finrank (pullField y L) Ω + 1),
            eval ζ (map (algebraMap ℚ ℂ) (c i)) * w ^ (Module.finrank (pullField y L) Ω - i) = 0 →
          ∃ z ∈ mcPts (mCoordIdeal y), ∃ t : ℂ, t ≠ 0 ∧
            (∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) ∧
            ∀ (dg dh : K → ℕ) (g h : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g dg → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h dh →
              (∀ k, dg k = dh k + τ * (q * e k)) → aeval y g = s * aeval y h →
              eval z (map (Int.castRingHom ℂ) h) ≠ 0 →
              eval z (map (Int.castRingHom ℂ) g) = w * t ^ (q * τ) * eval z (map (Int.castRingHom ℂ) h)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

