module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange
public import Formalism.SharpRestriction.Divisibility.Bundle0001
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0006
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GramLocallyUnimodular
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.GramLoc

theorem exists_common_denom {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (p : Ideal R) [p.IsPrime] (L M : Submodule R W) (hM : M.FG) (h : M ≤ Formalism.HermitianLatticesTheory.localization₂ p L) :
    ∃ s : R, s ∉ p ∧ ∀ y ∈ M, s • y ∈ L := by
  obtain ⟨T, rfl⟩ := hM
  have h1 : ∀ y : T, ∃ s : R, s ∈ p.primeCompl ∧ s • (y : W) ∈ L := fun y =>
    h (Submodule.subset_span y.2)
  choose f hf hf' using h1
  refine ⟨∏ y, f y, Submonoid.prod_mem p.primeCompl (fun y _ => hf y), ?_⟩
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    classical
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx⟩ : T)), mul_smul]
    exact L.smul_mem _ (hf' ⟨x, hx⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact L.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact L.smul_mem _ hx

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def locRing (w : HeightOneSpectrum (𝓞 K)) : Subring K where
  carrier := {a | ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ r : 𝓞 K, (s : K) * a = r}
  mul_mem' := by
    rintro a b ⟨s, hs, r, hr⟩ ⟨t, ht, u, hu⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, r * u, ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_add (f := _), map_neg] at *
    rw [← hr, ← hu]; ring
  one_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, 1, by simp⟩
  add_mem' := by
    rintro a b ⟨s, hs, r, hr⟩ ⟨t, ht, u, hu⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, t * r + s * u, ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_add (f := _), map_neg] at *
    rw [← hr, ← hu]; ring
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, 0, by simp⟩
  neg_mem' := by
    rintro a ⟨s, hs, r, hr⟩
    refine ⟨s, hs, -r, ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_add (f := _), map_neg] at *
    rw [← hr]; ring

theorem det_mem_subring (S : Subring K) (P : Matrix (Fin n) (Fin n) K) (h : ∀ a b, P a b ∈ S) :
    P.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

theorem col_mem_colLat (B : GL (Fin n) K) (j : Fin n) :
    (fun a => (B : Matrix (Fin n) (Fin n) K) a j) ∈ colLat B :=
  Submodule.subset_span ⟨j, rfl⟩

theorem coord_of_mem_colLat (B : GL (Fin n) K) (x : Fin n → K) (hx : x ∈ colLat B) (j : Fin n) :
    ∃ r : 𝓞 K, (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) j = r := by
  unfold colLat at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have h : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) = 1 :=
      Units.inv_mul B
    have h2 := congrFun (congrFun h j) i
    refine ⟨if j = i then 1 else 0, ?_⟩
    change (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) j i = _
    rw [h2, Matrix.one_apply]
    split_ifs <;> simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr⟩ := hx
    obtain ⟨u, hu⟩ := hy
    exact ⟨r + u, by rw [Matrix.mulVec_add, Pi.add_apply, hr, hu]; simp⟩
  | smul a x _ hx =>
    obtain ⟨r, hr⟩ := hx
    refine ⟨a * r, ?_⟩
    rw [Matrix.mulVec_smul, Pi.smul_apply, hr, Algebra.smul_def]
    simp

variable [StarRing K]

theorem vw_nonneg_of_mem (w : HeightOneSpectrum (𝓞 K)) (a : K) (ha : a ∈ locRing w) :
    0 ≤ vw w a := by
  obtain ⟨s, hs, r, hr⟩ := ha
  by_cases h0 : a = 0
  · rw [h0, ValuationRepresentative.vw_zero]
  have hs0 : (s : K) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  have h1 := ValuationRepresentative.vw_mul w _ _ hs0 h0
  have h2 : vw w (s : K) = 0 := idxChange_cnt_unit (K := K) w hs
  have h3 := ValuationRepresentative.vw_int_nonneg w r
  rw [hr, h2] at h1
  omega

theorem cO_notMem (w : HeightOneSpectrum (𝓞 K)) (t : 𝓞 K) (ht : t ∉ (conjPl w).asIdeal) :
    cO K t ∉ w.asIdeal := by
  intro h
  apply ht
  have := Ideal.mem_map_of_mem (cO K) h
  rwa [ValuationRepresentative.cO_cO] at this

theorem mem_localization_of_mem {w : HeightOneSpectrum (𝓞 K)} (M : Submodule (𝓞 K) (Fin n → K)) :
    M ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := fun x hx =>
  ⟨1, one_mem _, by simpa using hx⟩

theorem gram_mem (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hM : hdualFr G M = M) (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K)
    (hB : IsBasisAt (conjPl w) M B) (hB' : IsBasisAt w M B') (a b : Fin n) :
    ((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)) a b ∈ locRing w := by
  unfold IsBasisAt at hB hB'
  have h1 := mem_localization_of_mem (w := conjPl w) _ (col_mem_colLat B a)
  have h2 := mem_localization_of_mem (w := w) _ (col_mem_colLat B' b)
  rw [← hB] at h1
  rw [← hB'] at h2
  obtain ⟨t, ht, h1⟩ := h1
  obtain ⟨u, hu, h2⟩ := h2
  rw [← hM] at h2
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (h2 _ h1)
  refine ⟨cO K t * u, fun h => (w.isPrime.mem_or_mem h).elim (cO_notMem w t ht) hu, r, ?_⟩
  change _ = algebraMap (𝓞 K) K r
  rw [hr, Matrix.mul_assoc]
  have hc : ((cO K t * u : 𝓞 K) : K) = star (t : K) * (u : K) := by
    rw [← ValuationRepresentative.cO_apply]; exact map_mul (algebraMap (𝓞 K) K) _ _
  rw [hc]
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Pi.smul_apply,
    Algebra.smul_def, Matrix.conjTranspose_apply, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change star (t : K) * (u : K) * _ = star (t : K) * _ * (_ * ((u : K) * _))
  ring

theorem gram_inv_mem (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hG : IsUnit G.det) (hfg : M.FG)
    (hM : hdualFr G M = M) (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K)
    (hB : IsBasisAt (conjPl w) M B) (hB' : IsBasisAt w M B') (a b : Fin n) :
    (((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (G⁻¹ * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ)) a b ∈ locRing w := by
  unfold IsBasisAt at hB hB'
  obtain ⟨t, ht, h1⟩ := exists_common_denom (conjPl w).asIdeal (colLat B) M hfg
    (hB ▸ mem_localization_of_mem M)
  set C : Matrix (Fin n) (Fin n) K := ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hC
  set x : Fin n → K := fun i => (G⁻¹ * Cᴴ) i b with hx
  have hGx : G *ᵥ x = fun i => star (C b i) := by
    funext i
    change (G * (G⁻¹ * Cᴴ)) i b = _
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hG, Matrix.conjTranspose_apply]
  have hxM : cO K t • x ∈ hdualFr G M := by
    intro y hy
    obtain ⟨r, hr⟩ := coord_of_mem_colLat B _ (h1 y hy) b
    refine Submodule.mem_one.2 ⟨cO K r, ?_⟩
    change ((cO K r : 𝓞 K) : K) = _
    rw [ValuationRepresentative.cO_apply, ← hr, Matrix.mulVec_smul, Matrix.mulVec_smul, hGx]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.smul_apply,
      Algebra.smul_def, star_mul', Finset.mul_sum, star_sum, ← hC]
    refine Finset.sum_congr rfl fun i _ => ?_
    change star (t : K) * _ = _ * (star (t : K) * _)
    ring
  rw [hM] at hxM
  have h3 := mem_localization_of_mem (w := w) M hxM
  rw [hB'] at h3
  obtain ⟨u, hu, h3⟩ := h3
  obtain ⟨r, hr⟩ := coord_of_mem_colLat B' _ h3 a
  refine ⟨u * cO K t, fun h => (w.isPrime.mem_or_mem h).elim hu (cO_notMem w t ht), r, ?_⟩
  rw [← hr, ← mul_smul, Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
  rfl

theorem gram_locally_unimodular : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)), Gᴴ = G → IsUnit G.det → IsSelfDualK G M → ∀ (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K), IsBasisAt (conjPl w) M B → IsBasisAt w M B' → (∀ a b, 0 ≤ vw w (((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)) a b)) ∧ vw w ((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)).det = 0 := by
  intro K _ _ _ n G M _ hG hM w B B' hB hB'
  have hfg : M.FG := hM.1.fg
  have h1 := gram_mem G M hM.2 w B B' hB hB'
  have h2 := gram_inv_mem G M hG hfg hM.2 w B B' hB hB'
  refine ⟨fun a b => vw_nonneg_of_mem w _ (h1 a b), ?_⟩
  have d1 := vw_nonneg_of_mem w _ (det_mem_subring _ _ h1)
  have d2 := vw_nonneg_of_mem w _ (det_mem_subring _ _ h2)
  have e : ((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)) *
      (((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (G⁻¹ * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ)) = 1 := by
    have e1 : (B' : Matrix (Fin n) (Fin n) K) * ((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
      Units.mul_inv B'
    have e2 : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) = 1 :=
      Units.inv_mul B
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B' : Matrix (Fin n) (Fin n) K), e1, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hG, ← Matrix.conjTranspose_mul, e2,
      Matrix.conjTranspose_one]
  have e' := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_one] at e'
  have e3 := ValuationRepresentative.vw_mul w _ _ (left_ne_zero_of_mul_eq_one e') (right_ne_zero_of_mul_eq_one e')
  rw [e', ValuationRepresentative.vw_one] at e3
  omega

end GlobalTheory.GramLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HookREqHookProd
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.LiftSizeCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

theorem telescope (a k b : ℕ) (hb : b ≤ a) :
    (∏ c ∈ Finset.range b, (a - c - 1 + (k + 1) + 1)) * (a - b + k + 1) =
      (∏ c ∈ Finset.range b, (a - c - 1 + k + 1)) * (a + k + 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have h1 : a - b - 1 + (k + 1) + 1 = a - b + k + 1 := by omega
    have h2 : a - (b + 1) + k + 1 = a - b - 1 + k + 1 := by omega
    rw [h1, h2, ih (by omega)]
    ring

theorem row_hook (ν : ℕ → ℕ) (r k : ℕ) (hν : ∀ x y, x ≤ y → y < r + 1 + k → ν y ≤ ν x) :
    (∏ c ∈ Finset.range (ν r),
        ((ν r - c - 1) + ((Finset.Ioo r (r + 1 + k)).filter (fun r' => c < ν r')).card + 1)) *
      ∏ l ∈ Finset.Ioo r (r + 1 + k), (ν r - ν l + (l - r)) = (ν r + k).factorial := by
  induction k with
  | zero =>
    have he : Finset.Ioo r (r + 1 + 0) = ∅ := by
      ext x
      simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
      omega
    rw [he, Finset.prod_empty, mul_one, Nat.add_zero]
    simp only [Finset.filter_empty, Finset.card_empty, add_zero]
    rw [← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    omega
  | succ k ih =>
    have hν' : ∀ x y, x ≤ y → y < r + 1 + k → ν y ≤ ν x := fun x y hxy hy => hν x y hxy (by omega)
    have IH := ih hν'
    set m := r + 1 + k with hm
    have hIns : Finset.Ioo r (r + 1 + (k + 1)) = insert m (Finset.Ioo r m) := by
      ext x
      simp only [Finset.mem_Ioo, Finset.mem_insert]
      omega
    have hmn : m ∉ Finset.Ioo r m := by simp
    have hba : ν m ≤ ν r := hν r m (by omega) (by omega)
    have hcardIoo : (Finset.Ioo r m).card = k := by rw [Nat.card_Ioo]; omega
    rw [hIns, Finset.prod_insert hmn]
    rw [← Finset.prod_range_mul_prod_Ico _ hba] at IH ⊢
    have hlow : ∀ c ∈ Finset.range (ν m),
        ν r - c - 1 + ((insert m (Finset.Ioo r m)).filter (fun r' => c < ν r')).card + 1 =
          ν r - c - 1 + (k + 1) + 1 := by
      intro c hc
      rw [Finset.mem_range] at hc
      rw [Finset.filter_insert, if_pos hc, Finset.card_insert_of_notMem (by simp),
        Finset.filter_true_of_mem (fun l hl => ?_), hcardIoo]
      rw [Finset.mem_Ioo] at hl
      exact lt_of_lt_of_le hc (hν l m hl.2.le (by omega))
    have hlow' : ∀ c ∈ Finset.range (ν m),
        ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1 =
          ν r - c - 1 + k + 1 := by
      intro c hc
      rw [Finset.mem_range] at hc
      rw [Finset.filter_true_of_mem (fun l hl => ?_), hcardIoo]
      rw [Finset.mem_Ioo] at hl
      exact lt_of_lt_of_le hc (hν l m hl.2.le (by omega))
    have hhigh : ∀ c ∈ Finset.Ico (ν m) (ν r),
        ν r - c - 1 + ((insert m (Finset.Ioo r m)).filter (fun r' => c < ν r')).card + 1 =
          ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1 := by
      intro c hc
      rw [Finset.mem_Ico] at hc
      rw [Finset.filter_insert, if_neg (by omega)]
    rw [Finset.prod_congr rfl hlow, Finset.prod_congr rfl hhigh]
    rw [Finset.prod_congr rfl hlow'] at IH
    have hT := telescope (ν r) k (ν m) hba
    have hd : ν r - ν m + (m - r) = ν r - ν m + k + 1 := by omega
    rw [hd, show ν r + (k + 1) = (ν r + k) + 1 by ring, Nat.factorial_succ, ← IH]
    calc (∏ c ∈ Finset.range (ν m), (ν r - c - 1 + (k + 1) + 1)) *
          (∏ c ∈ Finset.Ico (ν m) (ν r),
            (ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1)) *
          ((ν r - ν m + k + 1) * ∏ l ∈ Finset.Ioo r m, (ν r - ν l + (l - r)))
        = ((∏ c ∈ Finset.range (ν m), (ν r - c - 1 + (k + 1) + 1)) * (ν r - ν m + k + 1)) *
          (∏ c ∈ Finset.Ico (ν m) (ν r),
            (ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1)) *
          ∏ l ∈ Finset.Ioo r m, (ν r - ν l + (l - r)) := by ring
      _ = _ := by rw [hT]; ring

theorem hookProd_mul (n : ℕ) (ν : ℕ → ℕ) (hν : ∀ x y, x ≤ y → y < n → ν y ≤ ν x) :
    hookProd n ν * ∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (ν r - ν l + (l - r)) =
      ∏ r ∈ Finset.range n, (ν r + n - 1 - r).factorial := by
  unfold hookProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.1 hr
  have e : r + 1 + (n - 1 - r) = n := by omega
  have h := row_hook ν r (n - 1 - r) (fun x y hxy hy => hν x y hxy (by omega))
  rw [e] at h
  rw [h]
  congr 1
  omega

variable (D : D7) (L : SizeData₂ D)

variable {eps : ℝ} (Fm : FamP eps)

end GlobalTheory.LiftSizeCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IndexAtLevelIffOuterClausesAnd
section
noncomputable section

namespace GlobalTheory.LevelIndexCompare

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.IndefiniteRowSideFullHecke.IndexAtLevelRanks

section General

end General

variable (D : D7) (u : D.what₂.Word)

def incl (w : D.what₂.places.Pl) : LT.Sram D u w →ₗ[LT.Ow D w] (D.fm u).ramSub where
  toFun x := ⟨x.1, x.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def URamStable (v : (D.mem u).A.vT) : Prop :=
  ∀ x ∈ (D.fm u).ramSub, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x)

theorem T_ne_zero : ((D.mem u).A.T : ℂ) ≠ 0 := by exact_mod_cast (D.mem u).A.T_prime.ne_zero

theorem emb_zpow_smul (n : ℤ) (x : LT.Vl D u 0) :
    (D.fm u).emb 0 ((((D.mem u).A.T : D.what₂.LL) ^ n) • x) = (((D.mem u).A.T : ℂ) ^ n) • (D.fm u).emb 0 x := by
  rw [LinearMap.map_smulₛₗ, map_zpow₀, map_natCast]

theorem exists_isScaledU_iff (w : D.what₂.places.Pl) (v : (D.mem u).A.vT) :
    (∃ g, IsScaledU D u w v g) ↔ URamStable D u v := by
  constructor
  · rintro ⟨g, hg⟩ x hx
    refine ⟨(((D.mem u).A.T : D.what₂.LL) ^ (-(D.fm u).bTop ((D.fm u).tauOf w v))) • (g ⟨x, hx⟩ : LT.Vl D u 0),
      (D.fm u).ramSub.smul_mem _ (g ⟨x, hx⟩).2, ?_⟩
    rw [emb_zpow_smul, hg, smul_smul, ← zpow_add₀ (T_ne_zero D u), neg_add_cancel, zpow_zero, one_smul]
  · intro h
    let e : (D.fm u).ramSub →ₛₗ[D.what₂.embLL] LT.Fn D u 0 := ((D.fm u).emb 0).comp (D.fm u).ramSub.subtype
    have he : Function.Injective e := ((D.fm u).emb_inj 0).comp Subtype.val_injective
    let f : LT.Fn D u 0 →ₗ[ℂ] LT.Fn D u 0 :=
      (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) • LT.Uop D u 0 v
    have hf : ∀ x, ∃ y, e y = f (e x) := by
      intro x
      obtain ⟨y, hy, hxy⟩ := h x.1 x.2
      refine ⟨⟨(((D.mem u).A.T : D.what₂.LL) ^ ((D.fm u).bTop ((D.fm u).tauOf w v))) • y,
        (D.fm u).ramSub.smul_mem _ hy⟩, ?_⟩
      exact (emb_zpow_smul D u _ y).trans (by rw [hxy]; rfl)
    exact ⟨descend e e he f hf, fun x => descend_spec e e he f hf x⟩

theorem emb_list_prod (w : D.what₂.places.Pl) (g : (D.mem u).A.vT → Module.End D.what₂.LL (D.fm u).ramSub)
    (l : List (D.mem u).A.vT) (hg : ∀ v ∈ l, IsScaledU D u w v (g v)) (x : (D.fm u).ramSub) :
    (D.fm u).emb 0 ((l.map g).prod x : LT.Vl D u 0) =
      (((D.mem u).A.T : ℂ) ^ (l.map fun v => (D.fm u).bTop ((D.fm u).tauOf w v)).sum) •
        (l.foldr (fun v f => (LT.Uop D u 0 v).comp f) LinearMap.id) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, hg v List.mem_cons_self,
      ih (fun v' hv' => hg v' (List.mem_cons_of_mem _ hv')), map_smul, smul_smul, List.map_cons, List.sum_cons,
      zpow_add₀ (T_ne_zero D u)]
    rfl

theorem emb_pow (G : Module.End D.what₂.LL (D.fm u).ramSub) (c : ℂ) (U : Module.End ℂ (LT.Fn D u 0))
    (h : ∀ x : (D.fm u).ramSub, (D.fm u).emb 0 (G x : LT.Vl D u 0) = c • U ((D.fm u).emb 0 (x : LT.Vl D u 0)))
    (n : ℕ) (x : (D.fm u).ramSub) :
    (D.fm u).emb 0 ((G ^ n) x : LT.Vl D u 0) = c ^ n • (U ^ n) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, h, ih, map_smul, smul_smul, pow_succ' c, pow_succ' U, Module.End.mul_apply]

theorem mem_Nlam_iff (w : D.what₂.places.Pl) (g : (D.mem u).A.vT → Module.End D.what₂.LL (D.fm u).ramSub)
    (hg : ∀ v ∈ LT.VVT D u w, IsScaledU D u w v (g v)) (y : LT.Vl D u 0) :
    y ∈ LT.Nlam D u w ↔ ∃ x : LT.Sram D u w,
      y = ((((LT.VVT D u w).toList.map g).prod ^ D.R.m) (incl D u w x) : (D.fm u).ramSub) := by
  have key : ∀ x : (D.fm u).ramSub,
      (D.fm u).emb 0 ((((LT.VVT D u w).toList.map g).prod ^ D.R.m) x : (D.fm u).ramSub) =
        ((((D.mem u).A.T : ℂ) ^ LT.expT D u w) • (LT.Uprod D u 0 w) ^ D.R.m) ((D.fm u).emb 0 (x : LT.Vl D u 0)) := by
    intro x
    rw [emb_pow D u _ _ (LT.Uprod D u 0 w)
      (emb_list_prod D u w g _ (fun v hv => hg v (Finset.mem_toList.1 hv))), Finset.sum_map_toList,
      ← zpow_natCast, ← zpow_mul, mul_comm]
    rfl
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, (D.fm u).emb_inj 0 (hxy.trans (key (incl D u w ⟨x, hx⟩)).symm)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, key _⟩

end GlobalTheory.LevelIndexCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwiningGlOfUnitary
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem zpow_mul_eq_iff_toNat (d x y : ℂ) (hd : d ≠ 0) (a b : ℤ) :
    d ^ a * x = d ^ b * y ↔ d ^ (a - b).toNat * x = d ^ (b - a).toNat * y := by
  have ha : d ^ a = d ^ (min a b) * d ^ (a - b).toNat := by
    rw [← zpow_natCast, ← zpow_add₀ hd]; congr 1; omega
  have hb : d ^ b = d ^ (min a b) * d ^ (b - a).toNat := by
    rw [← zpow_natCast, ← zpow_add₀ hd]; congr 1; omega
  rw [ha, hb, mul_assoc, mul_assoc, mul_right_inj' (zpow_ne_zero _ hd)]

theorem exists_coef_sqRep (n : ℕ) (mu : DomWeight n) (f : nablaSq ℂ n mu)
    (l : Module.Dual ℂ (nablaSq ℂ n mu)) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : GL (Fin n) ℂ,
      l (sqRep ℂ n mu g f) = (g : Matrix (Fin n) (Fin n) ℂ).det ^ mu.detShift *
        eval (fun x => (g : Matrix (Fin n) (Fin n) ℂ) x.1 x.2) P := by
  obtain ⟨L, hL⟩ := LinearMap.exists_extend l
  obtain ⟨P, hP⟩ := GlobalTheory.Branching.rowAct_coef_poly_and_unitary_dense.1 n n f L
  refine ⟨rename Prod.swap P, fun g => ?_⟩
  rw [← hL, LinearMap.comp_apply, Submodule.subtype_apply, sqRep_coe, sqAct, map_smul, hP, eval_rename]
  simp only [detPow, smul_eq_mul, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem intertwining_gl_of_unitary (n : ℕ) (mu nu : DomWeight n)
    (φ : (smallRep (unitaryIncl n) mu).IntertwiningMap (smallRep (unitaryIncl n) nu))
    (g : GL (Fin n) ℂ) (f : nablaSq ℂ n mu) :
    φ (sqRep ℂ n mu g f) = sqRep ℂ n nu g (φ f) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, sub_eq_zero]
  obtain ⟨P, hP⟩ := exists_coef_sqRep n mu f (l ∘ₗ φ.toLinearMap)
  obtain ⟨Q, hQ⟩ := exists_coef_sqRep n nu (φ f) l
  let D : MvPolynomial (Fin n × Fin n) ℂ := (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det
  have hD : ∀ m : Matrix (Fin n) (Fin n) ℂ, eval (fun x => m x.1 x.2) D = m.det := by
    intro m
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
  have key : ∀ g : GL (Fin n) ℂ, l (φ (sqRep ℂ n mu g f)) = l (sqRep ℂ n nu g (φ f)) ↔
      eval (fun x => (g : Matrix (Fin n) (Fin n) ℂ) x.1 x.2)
        (D ^ (mu.detShift - nu.detShift).toNat * P - D ^ (nu.detShift - mu.detShift).toNat * Q) = 0 := by
    intro g
    have h1 : l (φ (sqRep ℂ n mu g f)) = _ := hP g
    rw [h1, hQ, zpow_mul_eq_iff_toNat _ _ _ (Matrix.GeneralLinearGroup.det_ne_zero g)]
    simp only [map_sub, map_mul, map_pow, hD, sub_eq_zero]
  have hz := GlobalTheory.Branching.rowAct_coef_poly_and_unitary_dense.2 n _ fun u hu =>
    (key (unitaryIncl n ⟨u, hu⟩)).1 (congrArg l (φ.isIntertwining _ _ ⟨u, hu⟩ f))
  rw [key, hz, map_zero]

end GlobalTheory.Branching
end

