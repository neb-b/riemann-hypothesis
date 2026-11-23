module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PLemmaB
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem antisymmetrize_C_mul (f N : ℕ) (k : ℚ) (H : RootRing f N) :
    antisymmetrize f N (C k * H) = C k * antisymmetrize f N H := by
  unfold antisymmetrize
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [blockPermute]

theorem blockVandermonde_ne_zero (f N : ℕ) : blockVandermonde f N ≠ 0 := by
  unfold blockVandermonde vandermondeOf
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ =>
    Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr ?_
  intro h
  have h' := X_injective h
  simp only [Prod.mk.injEq, true_and] at h'
  exact (ne_of_lt (Finset.mem_Ioi.mp hj)) h'

theorem LemmaB.proof (h1 : SchAevalSignedRename.Statement) (h2 : SchAntisymmetrizePlace.Statement)
    (h3 : SchSmallBlockProduct.Statement) (h4 : SchConcatAlternant.Statement)
    (h5 : SchConcatAlternantZero.Statement) (h6 : SchBlockVandermondeOne.Statement)
    (h7 : SchSchurHomogeneous.Statement) : LemmaB.Statement := by
  intro r a c
  obtain ⟨s, hs, hconc⟩ := h4 r a c
  have hsgn : ∀ n : ℕ, c.sign ^ n = 1 ∨ c.sign ^ n = -1 := by
    intro n
    cases c <;> simp [SmallBlock.sign, neg_one_pow_eq_or]
  refine ⟨s * ((r.factorial : ℚ) * a.factorial) * c.sign ^ (r * (r - 1) / 2 + r * a), ?_, ?_⟩
  · rcases hs with rfl | rfl <;> rcases hsgn (r * (r - 1) / 2 + r * a) with h | h <;>
      rw [h] <;> first | (left; ring1) | (right; ring1)
  intro lam hlam
  have hV : algebraMap (RootRing 1 (r + a)) (FractionRing (RootRing 1 (r + a)))
      (blockVandermonde 1 (r + a)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (blockVandermonde_ne_zero 1 (r + a))
  unfold dividedDifference
  rw [h3, antisymmetrize_C_mul, h2, KAlt.antisym_rename_mul_rename, map_smul]
  split_ifs with hcont
  · rw [hconc lam hcont, div_eq_iff hV, ← map_mul]
    congr 1
    have hA := h1 (Fin (r + a)) (Fin 1 × Fin (r + a)) c.sign (fun i => ((0 : Fin 1), i))
      (∑ i, (lam i - a)) (schur (Fin (r + a)) (fun i : Fin r => lam i - a))
      (h7 (Fin (r + a)) r (fun i : Fin r => lam i - a))
    have hsum : ∑ i, lam i = ∑ i, (lam i - a) + r * a := by
      rw [show r * a = ∑ _i : Fin r, a by simp, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (Nat.sub_add_cancel (hcont i)).symm
    rw [hA, h6, map_mul, hsum, smul_eq_C_mul]
    simp only [map_mul, map_pow, map_natCast]
    ring
  · rw [h5 r a lam hlam hcont, map_zero, smul_zero, mul_zero, map_zero, zero_div]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestBoundOfPrimeBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset Elem

noncomputable section

theorem RestBoundOfPrimeBound.proof : RestBoundOfPrimeBound.Statement := by
  classical
  intro f r a c B₀ hf hr ha hB Q s e hp P
  set R : ℕ → ℝ := fun p => restPrimeModel f r a c Q s e p with hR
  set C : ℝ := ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| with hC
  set X : ℝ := (restX r a : ℝ) with hXdef
  have hN2 : 2 ≤ r + a := by omega
  have hNR : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast hN2
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hB0 : 0 < B₀ := by nlinarith
  have hC0 : 0 ≤ C := by positivity
  have hX0 : 0 ≤ X := by
    simp only [hXdef, restX]; push_cast; positivity
  set K : ℝ := 1.5 * f * X * C with hK
  have hK0 : 0 ≤ K := by positivity
  set S : Set ℕ := {p | p ∈ P ∧ p.Prime ∧ B₀ < p} with hS
  set g : ℕ → ℝ := fun i => if i ∈ P ∧ i.Prime ∧ B₀ < i then |R i| else 0 with hg
  have hind : S.indicator (fun p => |R p|) = g := by
    funext i
    by_cases h : i ∈ P ∧ i.Prime ∧ B₀ < i
    · simp [hS, hg, Set.indicator_of_mem, h]
    · rw [Set.indicator_of_notMem (show i ∉ S from h)]
      simp [hg, h]
  have hg0 : ∀ i, 0 ≤ g i := fun i => by
    simp only [hg]; split_ifs <;> positivity
  have hgle : ∀ i, g i ≤ K * (primeWeight B₀ i / (i : ℝ) ^ 2) := fun i => by
    simp only [hg]
    split_ifs with h
    · have hw : primeWeight B₀ i = Real.log i := by simp [primeWeight, h.2.1, h.2.2]
      rw [hw]
      calc |R i| ≤ 1.5 * f * X * (Real.log i / (i : ℝ) ^ 2) * ((f * (r * a) + 1 : ℕ) : ℝ) *
            |(fibreDegree f r a c : ℝ)| := hp i h.2.1 h.2.2
        _ = K * (Real.log i / (i : ℝ) ^ 2) := by rw [hK, hC]; ring
    · exact mul_nonneg hK0 (div_nonneg (primeWeight_nonneg B₀ i) (by positivity))
  have hpart : ∀ n, ∑ i ∈ range n, g i ≤ K * (2 * Real.log 4 / B₀) := fun n => by
    calc ∑ i ∈ range n, g i ≤ ∑ i ∈ range n, K * (primeWeight B₀ i / (i : ℝ) ^ 2) :=
          Finset.sum_le_sum fun i _ => hgle i
      _ = K * ∑ i ∈ range n, primeWeight B₀ i / (i : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ K * (2 * Real.log 4 / B₀) :=
          mul_le_mul_of_nonneg_left (prime_partial_le B₀ hB0 n) hK0
  have hgs : Summable g := summable_of_sum_range_le hg0 hpart
  have hsub : Summable (fun p : S => |R p|) :=
    (summable_subtype_iff_indicator (f := fun p : ℕ => |R p|) (s := S)).mpr (by rw [hind]; exact hgs)
  refine ⟨hsub, ?_⟩
  have htsum : ∑' p : S, |R p| ≤ K * (2 * Real.log 4 / B₀) := by
    rw [tsum_subtype S (fun p : ℕ => |R p|), hind]
    exact Real.tsum_le_of_sum_range_le hg0 hpart
  have habs : |∑' p : S, R p| ≤ ∑' p : S, |R p| := by
    have := norm_tsum_le_tsum_norm (f := fun p : S => R p)
      (by simpa [Real.norm_eq_abs] using hsub)
    simpa [Real.norm_eq_abs] using this

  have hXle : X ≤ 3 / 2 * ((r + a : ℕ) : ℝ) ^ 2 := by
    have h := XBound.intersectionNumber_baseChange r a hN2
    simp only [hXdef] at h ⊢
    linarith [h.1, h.2]
  have hNpos : (0 : ℝ) < ((r + a : ℕ) : ℝ) := by linarith
  have hD : (0 : ℝ) < 4 * f * ((r + a : ℕ) : ℝ) ^ 2 := by positivity
  have hlog : 2 * Real.log 4 / B₀ ≤ 2.78 / (4 * f * ((r + a : ℕ) : ℝ) ^ 2) := by
    calc 2 * Real.log 4 / B₀ ≤ 2.78 / B₀ :=
          div_le_div_of_nonneg_right two_log_four_le hB0.le
      _ ≤ 2.78 / (4 * f * ((r + a : ℕ) : ℝ) ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) hD hB
  have hconst := RestConstants.intersectionNumber_baseChange.2 f (r + a) hf hN2
  have hfin : K * (2 * Real.log 4 / B₀) ≤ 1.6 * C := by
    have hl0 : 0 ≤ 2 * Real.log 4 / B₀ :=
      div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) hB0.le
    calc K * (2 * Real.log 4 / B₀)
        = (1.5 * f * X) * (2 * Real.log 4 / B₀) * C := by rw [hK]; ring
      _ ≤ (1.5 * f * (3 / 2 * ((r + a : ℕ) : ℝ) ^ 2)) * (2.78 / (4 * f * ((r + a : ℕ) : ℝ) ^ 2)) * C := by
          apply mul_le_mul_of_nonneg_right _ hC0
          apply mul_le_mul _ hlog hl0 (by positivity)
          exact mul_le_mul_of_nonneg_left hXle (by positivity)
      _ ≤ 1.6 * C := mul_le_mul_of_nonneg_right hconst hC0
  calc |∑' p : S, R p| ≤ ∑' p : S, |R p| := habs
    _ ≤ K * (2 * Real.log 4 / B₀) := htsum
    _ ≤ 1.6 * C := hfin
    _ = 1.6 * ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| := by rw [hC]; ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAevalSignedRename
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchAevalSignedRename.proof : SchAevalSignedRename.Statement := by
  intro ι κ _ _ _ _ s g d P hP
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hd : (∑ i ∈ e.support, e i) = d := by
    have h := hP (mem_support_iff.mp he)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  rw [rename_monomial, aeval_monomial, monomial_eq, Finsupp.prod_mapDomain_index
    (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [algebraMap_eq, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    ← C_pow]
  rw [← map_prod, Finset.prod_pow_eq_pow_sum, hd]
  ring

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAltPartitionExpansion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchAltPartitionExpansion.alt_partition_add_stair_eq {r : ℕ} (lam : Fin r → ℕ) :
    Comb.alt (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) =
      vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) * schur (Fin r) lam := by
  unfold Comb.alt
  rw [← Matrix.det_transpose, mul_comm]
  exact Schur.det_pow_add_staircase_eq lam

theorem SchAltPartitionExpansion.strictAnti_partition_add_stair {r n : ℕ} {lam : Fin r → ℕ} (hlam : lam ∈ partitionsOf r n) :
    StrictAnti (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) := by
  unfold partitionsOf at hlam
  rw [Finset.mem_filter] at hlam
  intro i j hij
  have h1 := hlam.2 i j hij.le
  have hj := j.isLt
  have hij' : (i : ℕ) < j := hij
  simp only
  omega

theorem SchAltPartitionExpansion.proof (h1 : SchStrictAntiSplit.Statement) :
    SchAltPartitionExpansion.Statement := by
  intro r n P hP hhom
  set e : (Fin r → ℕ) → (Fin r →₀ ℕ) := fun lam =>
    Finsupp.equivFunOnFinite.symm fun i : Fin r => lam i + (r - 1 - (i : ℕ)) with he
  have e_inj : Set.InjOn e (partitionsOf r n : Set (Fin r → ℕ)) := by
    intro a _ b _ hab
    funext i
    have := congrArg (fun f : Fin r →₀ ℕ => f i) hab
    simp only [he, Finsupp.coe_equivFunOnFinite_symm] at this
    omega

  have hR : ∑ lam ∈ partitionsOf r n,
      C (AddMonoidAlgebra.coeff P (e lam)) *
        (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) * schur (Fin r) lam) =
      ∑ d ∈ (partitionsOf r n).image e, AddMonoidAlgebra.coeff P d • Comb.alt (⇑d) := by
    rw [Finset.sum_image e_inj]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [C_mul', ← SchAltPartitionExpansion.alt_partition_add_stair_eq]
    simp [he]
  rw [hR]
  conv_lhs => rw [Comb.IsAlt.eq_sum_alt hP]
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hsum : ∑ i, d i = r * (r - 1) / 2 + n := by
      have := hhom (mem_support_iff.mp hd.1)
      rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
      exact this
    obtain ⟨hge, hmem⟩ := h1 r n (⇑d) hd.2 hsum
    refine Finset.mem_image.mpr ⟨_, hmem, ?_⟩
    ext i
    simp only [he, Finsupp.coe_equivFunOnFinite_symm]
    have := hge i
    omega
  · intro d hd hnot
    obtain ⟨lam, hlam, rfl⟩ := Finset.mem_image.mp hd
    have hz : AddMonoidAlgebra.coeff P (e lam) = 0 := by
      by_contra hne
      apply hnot
      rw [Finset.mem_filter]
      refine ⟨mem_support_iff.mpr hne, ?_⟩
      simpa [he] using SchAltPartitionExpansion.strictAnti_partition_add_stair hlam
    rw [hz, zero_smul]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAlternantHomogeneous
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

theorem SchAlternantHomogeneous.proof : SchAlternantHomogeneous.Statement := by
  intro ι _ _ e
  unfold alternant
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro σ _
  have h : IsHomogeneous (∏ i, (X (σ i) : MvPolynomial ι ℚ) ^ e i) (∑ i, e i) :=
    IsHomogeneous.prod _ _ _ (fun i _ => isHomogeneous_X_pow _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
    simp only [hs, Matrix.of_apply, one_smul, Units.neg_smul]
  · exact h
  · exact h.neg

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAlternantRenamePlace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial

noncomputable section

theorem rename_alternant_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (v : ι → ℕ) :
    rename e (alternant v) = alternant (v ∘ e.symm) := by
  unfold alternant
  rw [AlgHom.map_det, ← Matrix.det_submatrix_equiv_self e
    (Matrix.of fun p p' : κ => (X p : MvPolynomial κ ℚ) ^ (v ∘ e.symm) p')]
  congr 1
  ext i i'
  simp [Matrix.map_apply, Matrix.submatrix_apply]

def smallBlockEquiv (r a : ℕ) (c : SmallBlock) : Fin r ⊕ Fin a ≃ Fin (r + a) where
  toFun x := (smallBlockPlace r a c x).2
  invFun := smallBlockOf r a c
  left_inv := by
    intro x
    cases c <;> rcases x with i | j <;> simp [smallBlockPlace, smallBlockOf, yIndex, zIndex]
  right_inv := by
    intro p
    cases c <;> simp only [smallBlockOf] <;> split_ifs with h <;>
      apply Fin.ext <;> simp [smallBlockPlace, yIndex, zIndex] <;> omega

theorem SchAlternantRenamePlace.proof : SchAlternantRenamePlace.Statement := by
  intro r a c v
  have hg : smallBlockPlace r a c =
      (fun p : Fin (r + a) => ((0 : Fin 1), p)) ∘ smallBlockEquiv r a c := by
    funext x
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have hs : (smallBlockEquiv r a c).symm = smallBlockOf r a c := rfl
  rw [hg, ← rename_rename]
  congr 1
  rw [rename_alternant_equiv, hs]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAntisymmetrizePlace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def smallBlockPlaceEquiv (r a : ℕ) (c : SmallBlock) : Fin r ⊕ Fin a ≃ Fin (r + a) where
  toFun x := (smallBlockPlace r a c x).2
  invFun := smallBlockOf r a c
  left_inv x := by
    cases c <;> rcases x with i | j <;>
      simp [smallBlockPlace, smallBlockOf, yIndex, zIndex]
  right_inv p := by
    cases c
    · by_cases h : (p : ℕ) < a
      · simp [smallBlockPlace, smallBlockOf, zIndex, h]
      · simp only [smallBlockOf, h, dite_false, smallBlockPlace, Sum.elim_inl, yIndex]
        ext; simp; omega
    · by_cases h : (p : ℕ) < r
      · simp [smallBlockPlace, smallBlockOf, yIndex, h]
      · simp only [smallBlockOf, h, dite_false, smallBlockPlace, Sum.elim_inr, zIndex]
        ext; simp; omega

theorem smallBlockPlace_eq (r a : ℕ) (c : SmallBlock) (x : Fin r ⊕ Fin a) :
    smallBlockPlace r a c x = (0, smallBlockPlaceEquiv r a c x) := by
  exact Prod.ext (Subsingleton.elim _ _) rfl

theorem SchAntisymmetrizePlace.proof : SchAntisymmetrizePlace.Statement := by
  intro r a c Q
  set e := smallBlockPlaceEquiv r a c with he
  unfold antisymmetrize antisym
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Fintype.sum_equiv ((Equiv.funUnique (Fin 1) _).trans e.symm.permCongr) _ _ ?_
  intro w
  simp only [Equiv.trans_apply, Equiv.funUnique_apply]
  rw [AlgHom.map_smul_of_tower, blockPermute, rename_rename, rename_rename]
  have hs : blockSign 1 (r + a) w = ((Equiv.Perm.sign (e.symm.permCongr (w 0)) : ℤ) : ℚ) := by
    rw [Equiv.Perm.sign_permCongr, blockSign, Fintype.prod_unique]
    rfl
  rw [hs]
  congr 3
  funext x
  simp [smallBlockPlace_eq, ← he]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchBlockVandermondeOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem SchBlockVandermondeOne.proof : SchBlockVandermondeOne.Statement := by
  intro N
  simp only [blockVandermonde, vandermondeOf, Fin.prod_univ_one, map_prod, map_sub, rename_X]

end GroundTheory.Heights₂.Heights.RestTerms
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchConcatAlternantZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchConcatAlternantZero.proof : SchConcatAlternantZero.Statement := by
  intro r a lam hanti hnot
  have hex : ∃ i, lam i < a := by
    by_contra h
    exact hnot fun i => not_lt.mp fun hi => h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let k : Fin r := ⟨r - 1, by omega⟩
  have hkv : (k : ℕ) = r - 1 := rfl
  have hik : i ≤ k := by
    rw [Fin.le_def, hkv]; omega
  have hka : lam k < a := lt_of_le_of_lt (hanti hik) hi
  let j : Fin a := ⟨a - 1 - lam k, by omega⟩
  have hjv : (j : ℕ) = a - 1 - lam k := rfl
  have hexp : lam k + (r - 1 - (k : ℕ)) = a - 1 - (j : ℕ) := by
    rw [hkv, hjv]; omega
  unfold alternant
  apply Matrix.det_zero_of_column_eq (i := Sum.inl k) (j := Sum.inr j) Sum.inl_ne_inr
  intro p
  simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
  rw [hexp]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

