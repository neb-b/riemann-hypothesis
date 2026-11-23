module

public import ReciprocityTheory.SemistableReduction.Bundle0022
public import ReciprocityTheory.SemistableReduction.Bundle0014
public import ReciprocityTheory.SemistableReduction.SemiDegCE
public import ReciprocityTheory.SemistableReduction.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.IndependentSectionsUpperCount

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegA
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Module

theorem wa_witt_ker {K : Type} [Field K] (r m : ℕ) (g : Fin r → K)
    (hg : ∀ k : Fin r, m ≤ (k : ℕ) → (k : ℕ) + m < r → g k ≠ 0) (v : Fin r → K)
    (hv : ∀ p : Fin r, ∑ i, v i * wittMat r m g p i = 0) : v = 0 := by
  funext j
  have hj := j.isLt
  by_cases hmid : m ≤ (j : ℕ) ∧ (j : ℕ) + m < r
  · have h := hv j
    rw [Finset.sum_eq_single j] at h
    · simp only [wittMat, Matrix.of_apply] at h
      rw [if_neg (by omega), if_pos ⟨trivial, hmid.1, hmid.2⟩] at h
      exact (mul_eq_zero.1 h).resolve_right (hg j hmid.1 hmid.2)
    · intro i _ hij
      have hi := i.isLt
      simp only [wittMat, Matrix.of_apply]
      rw [if_neg, if_neg, mul_zero]
      · rintro ⟨h1, -⟩
        exact hij h1.symm
      · rintro ⟨h1, h2⟩
        rcases h2 with h2 | h2 <;> omega
    · intro h
      exact absurd (Finset.mem_univ j) h
  · set p : Fin r := ⟨r - 1 - j, by omega⟩ with hp
    have hpv : (p : ℕ) = r - 1 - j := rfl
    have h := hv p
    rw [Finset.sum_eq_single j] at h
    · simp only [wittMat, Matrix.of_apply] at h
      have hc : (p : ℕ) + j + 1 = r ∧ ((p : ℕ) < m ∨ (j : ℕ) < m) := by
        rw [hpv]
        omega
      rw [if_pos hc, mul_one] at h
      exact h
    · intro i _ hij
      have hi := i.isLt
      simp only [wittMat, Matrix.of_apply]
      rw [if_neg, if_neg, mul_zero]
      · rintro ⟨-, h2, h3⟩
        rw [hpv] at h2 h3
        omega
      · rintro ⟨h1, -⟩
        apply hij
        ext
        rw [hpv] at h1
        omega
    · intro h
      exact absurd (Finset.mem_univ j) h

theorem wittBasis_holds : WittBasisStatement := by
  intro K _ _ r S hdet
  have hnd : ∀ x ∈ (⊤ : Submodule K (Fin r → K)),
      (∀ y ∈ (⊤ : Submodule K (Fin r → K)), S.h x y = 0) → x = 0 := by
    intro x _ hx
    have hrow : Matrix.vecMul (fun a => S.c (x a)) S.G = 0 := by
      funext b'
      have h1 := hx (Pi.single b' 1) Submodule.mem_top
      simpa [HermForm.h, Pi.single_apply, Matrix.vecMul, dotProduct] using h1
    have h2 : (fun a => S.c (x a)) = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hrow
    funext a
    have h3 := congrFun h2 a
    simp only [Pi.zero_apply, map_eq_zero] at h3
    exact h3
  obtain ⟨m, bb, g, -, hm, hW, hg⟩ := wa_main S r ⊤ (by rw [finrank_top, Module.finrank_fin_fun]) hnd
  have hgmid : ∀ k : Fin r, m ≤ (k : ℕ) → (k : ℕ) + m < r → g k ≠ 0 := by
    intro k hk1 hk2 hgk
    have ht := hg (Pi.single k 1) (fun i hi => by
      rw [Pi.single_apply, if_neg]
      rintro rfl
      omega) (by
      rw [Finset.sum_eq_single k]
      · simp [hgk]
      · intro i _ hik
        simp [Pi.single_eq_of_ne hik]
      · intro h
        exact absurd (Finset.mem_univ k) h)
    have := congrFun ht k
    simp at this
  have hlin : ∀ (x v : Fin r → K), S.h x (fun a => ∑ i, bb i a * v i) = ∑ i, v i * S.h x (bb i) := by
    intro x v
    simp only [HermForm.h, Finset.mul_sum]
    calc ∑ a, ∑ b', ∑ i, S.c (x a) * S.G a b' * (bb i b' * v i)
        = ∑ a, ∑ i, ∑ b', S.c (x a) * S.G a b' * (bb i b' * v i) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b', S.c (x a) * S.G a b' * (bb i b' * v i) := Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b', v i * (S.c (x a) * S.G a b' * bb i b') :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b' _ => by ring
  refine ⟨Matrix.of fun a i => bb i a, m, g, ?_, hm, ?_, hg⟩
  · intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    apply hv0
    have hPv : Matrix.mulVec (Matrix.of fun a i => bb i a) v = fun a => ∑ i, bb i a * v i := by
      funext a
      simp [Matrix.mulVec, dotProduct]
    refine wa_witt_ker r m g hgmid v fun p => ?_
    have h1 : S.h (bb p) (fun a => ∑ i, bb i a * v i) = 0 := by
      rw [← hPv, hv]
      simp [HermForm.h]
    rw [hlin] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun i _ => by rw [hW p i]
  · ext i j
    rw [← hW i j]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, HermForm.h,
      Finset.sum_mul]
    exact Finset.sum_comm

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegB
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField

theorem latDegBasis_holds : LatDegBasisStatement := by
  intro K _ _ r k H B b b' hH hB hb hb'
  obtain ⟨hbB, hbli, hbsp⟩ := hb
  obtain ⟨hb'B, hb'li, hb'sp⟩ := hb'
  set P := Submodule.span (𝓞 K) (Set.range b) with hP
  set P' := Submodule.span (𝓞 K) (Set.range b') with hP'
  obtain ⟨D, hD, hDB⟩ := exists_smul_le_span b B hB hbsp
  have hcoef : ∀ j, ∃ c : Fin k → 𝓞 K, ∑ i, c i • b i = D • b' j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp (hDB _ (hb'B j))
  choose m hm using hcoef
  set M : Matrix (Fin k) (Fin k) (𝓞 K) := Matrix.of fun i j => m j i with hMdef
  set Dm : Matrix (Fin k) (Fin k) (𝓞 K) := Matrix.diagonal fun _ => D with hDm
  have hcM : (fun j => ∑ i, M i j • b i) = fun j => D • b' j := by
    funext j
    exact hm j
  have hcD : (fun j => ∑ i, Dm i j • b' i) = fun j => D • b' j := comb_diagonal b' D
  set NK := M.map (algebraMap (𝓞 K) K) with hNK
  set DK := Dm.map (algebraMap (𝓞 K) K) with hDK
  have hcMK : (fun j => ∑ i, NK i j • b i) = fun j => D • b' j := by
    rw [← hcM]
    funext j
    simp [NK, algebraMap_smul]
  have hcDK : (fun j => ∑ i, DK i j • b' i) = fun j => D • b' j := by
    rw [← hcD]
    funext j
    simp [DK, algebraMap_smul]
  have hNKdet : NK.det = algebraMap (𝓞 K) K M.det := (RingHom.map_det _ M).symm
  have hDKdet : DK.det = algebraMap (𝓞 K) K Dm.det := (RingHom.map_det _ Dm).symm
  have hgc : ∀ σ : K →+* ℂ, (gramC (H σ) σ (fun j => D • b' j)).det =
      ((Complex.normSq (σ NK.det) : ℝ) : ℂ) * (gramC (H σ) σ b).det := fun σ => by
    rw [← hcMK]
    exact det_gramC_comb _ _ _ _
  have hgc' : ∀ σ : K →+* ℂ, (gramC (H σ) σ (fun j => D • b' j)).det =
      ((Complex.normSq (σ DK.det) : ℝ) : ℂ) * (gramC (H σ) σ b').det := fun σ => by
    rw [← hcDK]
    exact det_gramC_comb _ _ _ _
  have hpos : ∀ σ : K →+* ℂ, 0 < (gramC (H σ) σ b).det.re := fun σ =>
    gramC_det_re_pos (H σ) σ b (hH σ) hbli
  have hpos' : ∀ σ : K →+* ℂ, 0 < (gramC (H σ) σ b').det.re := fun σ =>
    gramC_det_re_pos (H σ) σ b' (hH σ) hb'li
  have hDmdet : Dm.det ≠ 0 := by
    simp [Dm, Matrix.det_diagonal, hD]
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have hDKne : DK.det ≠ 0 := by
    rw [hDKdet, ← map_zero (algebraMap (𝓞 K) K)]
    exact hinj.ne hDmdet
  have hre : ∀ σ : K →+* ℂ, Complex.normSq (σ NK.det) * (gramC (H σ) σ b).det.re =
      Complex.normSq (σ DK.det) * (gramC (H σ) σ b').det.re := fun σ => by
    have := congrArg Complex.re ((hgc σ).symm.trans (hgc' σ))
    simpa [Complex.re_ofReal_mul] using this
  have hNKne : NK.det ≠ 0 := by
    intro h0
    have h := hre (Classical.arbitrary (K →+* ℂ))
    rw [h0, map_zero, map_zero, zero_mul] at h
    have h1 : 0 < Complex.normSq ((Classical.arbitrary (K →+* ℂ)) DK.det) :=
      Complex.normSq_pos.mpr (by simpa using hDKne)
    have h2 := hpos' (Classical.arbitrary (K →+* ℂ))
    nlinarith
  have hMdet : M.det ≠ 0 := by
    intro h0
    apply hNKne
    rw [hNKdet, h0, map_zero]
  set C := Submodule.span (𝓞 K) (Set.range (fun j => D • b' j)) with hC
  have hIdx1 := relIndex_span_comb b hbli M hMdet
  rw [hcM] at hIdx1
  have hIdx2 := relIndex_span_comb b' hb'li Dm hDmdet
  rw [hcD] at hIdx2
  have hPB : P ≤ B := Submodule.span_le.mpr (Set.range_subset_iff.mpr hbB)
  have hP'B : P' ≤ B := Submodule.span_le.mpr (Set.range_subset_iff.mpr hb'B)
  have hCP : C ≤ P := Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => hDB _ (hb'B j))
  have hCP' : C ≤ P' := Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j =>
    Submodule.smul_mem _ D (Submodule.subset_span ⟨j, rfl⟩))
  have mul1 := AddSubgroup.relIndex_mul_relIndex C.toAddSubgroup P.toAddSubgroup B.toAddSubgroup
    hCP hPB
  have mul2 := AddSubgroup.relIndex_mul_relIndex C.toAddSubgroup P'.toAddSubgroup B.toAddSubgroup
    hCP' hP'B
  have hI := relIndex_span_ne_zero b hbli B hbB D hD hDB
  have e1 : ((Algebra.norm ℤ M.det : ℤ) : ℝ) = ((Algebra.norm ℚ NK.det : ℚ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) (Algebra.coe_norm_int M.det)
    simp only [Rat.cast_intCast] at this
    rw [hNKdet]
    convert this using 3
  have e2 : ((Algebra.norm ℤ Dm.det : ℤ) : ℝ) = ((Algebra.norm ℚ DK.det : ℚ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) (Algebra.coe_norm_int Dm.det)
    simp only [Rat.cast_intCast] at this
    rw [hDKdet]
    convert this using 3
  have hcP : ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) =
      |((Algebra.norm ℚ NK.det : ℚ) : ℝ)| := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hIdx1
    simp only [Int.cast_natCast, Int.cast_abs] at this
    rw [this, e1]
  have hcP' : ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) =
      |((Algebra.norm ℚ DK.det : ℚ) : ℝ)| := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hIdx2
    simp only [Int.cast_natCast, Int.cast_abs] at this
    rw [this, e2]
  have hnM : ((Algebra.norm ℚ NK.det : ℚ) : ℝ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hNKne)
  have hnD : ((Algebra.norm ℚ DK.det : ℚ) : ℝ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hDKne)
  have hmulR : ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) *
      ((P.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) =
      ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) *
      ((P'.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) := by
    exact_mod_cast mul1.trans mul2.symm
  have hcPne : ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) ≠ 0 := by
    rw [hcP]
    exact abs_ne_zero.mpr hnM
  have hcP'ne : ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) ≠ 0 := by
    rw [hcP']
    exact abs_ne_zero.mpr hnD
  have hIne : ((P.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hI
  have hI'ne : ((P'.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmulR
    exact mul_ne_zero hcPne hIne hmulR
  have hlog : Real.log ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) +
      Real.log ((P.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) =
      Real.log ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) +
      Real.log ((P'.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) := by
    rw [← Real.log_mul hcPne hIne, ← Real.log_mul hcP'ne hI'ne, hmulR]
  rw [hcP, hcP'] at hlog
  have hsum : ∑ σ : K →+* ℂ, (Real.log (Complex.normSq (σ NK.det)) +
      Real.log (gramC (H σ) σ b).det.re) = ∑ σ : K →+* ℂ, (Real.log (Complex.normSq (σ DK.det)) +
      Real.log (gramC (H σ) σ b').det.re) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h1 : Complex.normSq (σ NK.det) ≠ 0 := (Complex.normSq_pos.mpr (by simpa using hNKne)).ne'
    have h2 : Complex.normSq (σ DK.det) ≠ 0 := (Complex.normSq_pos.mpr (by simpa using hDKne)).ne'
    rw [← Real.log_mul h1 (hpos σ).ne', ← Real.log_mul h2 (hpos' σ).ne', hre σ]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_log_normSq _ hNKne,
    sum_log_normSq _ hDKne] at hsum
  simp only [latDeg]
  linarith

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegC
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField Matrix
open scoped nonZeroDivisors

theorem hermForm_sum_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {ι : Type} (s : Finset ι) (u : Fin r → K) (w : ι → Fin r → K) :
    S.h u (∑ i ∈ s, w i) = ∑ i ∈ s, S.h u (w i) := by
  classical
  refine Finset.induction_on s (by simp [HermForm.h]) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  simp only [HermForm.h, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hermForm_smul_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (u w : Fin r → K) : S.h u (a • w) = a * S.h u w := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def coordForm {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) : HermForm K k where
  c := S.c
  c_invol := S.c_invol
  c_emb := S.c_emb
  G := hGram S b
  G_herm i j := hermForm_conj S (b i) (b j)

def combMap {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) :
    (Fin k → K) →ₗ[K] (Fin r → K) where
  toFun t := ∑ i, t i • b i
  map_add' s t := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a t := by simp [Finset.smul_sum, smul_smul]

theorem combMap_apply {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) (t : Fin k → K) :
    combMap b t = ∑ i, t i • b i := rfl

theorem coordForm_h {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) (s t : Fin k → K) :
    S.h (combMap b s) (combMap b t) = (coordForm S b).h s t := by
  have key : ∀ j, S.h (combMap b s) (b j) = ∑ i, S.c (s i) * S.h (b i) (b j) := by
    intro j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hermForm_conj S (b j), combMap_apply, hermForm_sum_right, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hermForm_smul_right, map_mul, hermForm_conj]
  show _ = ∑ i, ∑ j, S.c (s i) * S.h (b i) (b j) * t j
  rw [combMap_apply b t, hermForm_sum_right]
  simp only [hermForm_smul_right, key, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem combMap_injective {K : Type} [Field K] {r k : ℕ} {b : Fin k → Fin r → K}
    (hb : LinearIndependent K b) : Function.Injective (combMap b) := by
  rw [Fintype.linearIndependent_iff] at hb
  refine (injective_iff_map_eq_zero (combMap b)).2 fun t ht => funext fun i => ?_
  exact hb t (by simpa only [combMap_apply] using ht) i

def coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : Submodule (𝓞 K) (Fin k → K) := B.comap ((combMap b).restrictScalars (𝓞 K))

theorem mem_coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} {t : Fin k → K} : t ∈ coordLat B b ↔ combMap b t ∈ B := Iff.rfl

theorem exists_coord {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) {y : Fin r → K} (hy : y ∈ B) :
    ∃ t ∈ coordLat B b, combMap b t = y := by
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hb.2.2 y hy)
  exact ⟨t, mem_coordLat.2 (by rw [combMap_apply, ht]; exact hy), by rw [combMap_apply, ht]⟩

theorem map_coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) :
    (coordLat B b).map ((combMap b).restrictScalars (𝓞 K)) = B := by
  ext y
  refine ⟨fun h => ?_, fun hy => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.1 h
    exact mem_coordLat.1 ht
  · obtain ⟨t, ht, rfl⟩ := exists_coord hb hy
    exact Submodule.mem_map.2 ⟨t, ht, rfl⟩

theorem coordLat_fg {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hB : B.FG) (hb : IsKBasisIn B b) : (coordLat B b).FG := Submodule.fg_of_fg_map_injective ((combMap b).restrictScalars (𝓞 K)) (combMap_injective hb.2.1) (by rw [map_coordLat hb]; exact hB)

theorem combMap_intVec {K : Type} [Field K] [NumberField K] {r k : ℕ}
    {b : Fin k → Fin r → K} {t : Fin k → K} (ht : t ∈ intVec K k)
    (P : Submodule (𝓞 K) (Fin r → K)) (hP : ∀ i, b i ∈ P) : combMap b t ∈ P := by
  rw [combMap_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨x, hx⟩ := Submodule.mem_one.1 ((Submodule.mem_pi).1 ht i (Set.mem_univ i))
  rw [← hx, algebraMap_smul]
  exact P.smul_mem x (hP i)

theorem intVec_le_coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) : intVec K k ≤ coordLat B b := fun t ht => mem_coordLat.2 (combMap_intVec ht B hb.1)

theorem spanIdx_eq_vecIdx {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) : spanIdx B b = vecIdx (coordLat B b) := by
  have hinj := combMap_injective hb.2.1
  have hspan : (intVec K k).map ((combMap b).restrictScalars (𝓞 K)) = Submodule.span (𝓞 K) (Set.range b) := by
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro _ ⟨t, ht, rfl⟩
      exact combMap_intVec ht _ fun i => Submodule.subset_span ⟨i, rfl⟩
    · rintro _ ⟨i, rfl⟩
      refine ⟨Pi.single i 1, (Submodule.mem_pi).2 fun j _ => ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · rw [Pi.single_apply, if_pos rfl]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
        · rw [Pi.single_apply, if_neg hj]; exact zero_mem _
      · show combMap b (Pi.single i 1) = b i
        simp [combMap_apply, Pi.single_apply, ite_smul]
  have e1 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup =
      (intVec K k).toAddSubgroup.map ((combMap b).restrictScalars (𝓞 K)).toAddMonoidHom := by
    rw [← hspan]; exact AddSubgroup.ext fun _ => Iff.rfl
  have e2 : B.toAddSubgroup =
      (coordLat B b).toAddSubgroup.map ((combMap b).restrictScalars (𝓞 K)).toAddMonoidHom := by
    conv_lhs => rw [← map_coordLat hb]
    exact AddSubgroup.ext fun _ => Iff.rfl
  unfold spanIdx vecIdx
  rw [e1, e2, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]

theorem coordLat_integral {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} {S : HermForm K r} (hint : IsIntegralOn S B) :
    IsIntegralOn (coordForm S b) (coordLat B b) := by
  intro s hs t ht
  rw [← coordForm_h]
  exact hint _ (mem_coordLat.1 hs) _ (mem_coordLat.1 ht)

theorem coordLat_selfDual {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} {S : HermForm K r} (hb : IsKBasisIn B b)
    (hsd : IsSelfDual S B) : IsSelfDual (coordForm S b) (coordLat B b) := by
  refine ⟨coordLat_integral hsd.1, fun s hs => mem_coordLat.2 (hsd.2 _ fun y hy => ?_)⟩
  obtain ⟨t, ht, rfl⟩ := exists_coord hb hy
  rw [coordForm_h]
  exact hs t ht

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

namespace ReciprocityTheory.MultiplicativeHeights

open SemiDegIdx

theorem integralIndex_holds : IntegralIndexStatement := by
  intro K _ _ r k S B b hB hb hint hdet
  have key : ((vecIdx (coordLat B b) : ℕ) : ℚ) ^ 2 ≤ |Algebra.norm ℚ (hGram S b).det| :=
    vec_integral_bound (coordForm S b) _ (coordLat_fg hB hb) (intVec_le_coordLat hb)
      (coordLat_integral hint) hdet
  rw [spanIdx_eq_vecIdx hb]
  exact_mod_cast key

theorem selfDualIndex_holds : SelfDualIndexStatement := by
  intro K _ _ r S L b hL hsd hb
  have key : |Algebra.norm ℚ (hGram S b).det| ≤ ((vecIdx (coordLat L b) : ℕ) : ℚ) ^ 2 :=
    vec_selfDual_bound (coordForm S b) _ (coordLat_fg hL.1 hb) (intVec_le_coordLat hb)
      (coordLat_selfDual hb hsd)
  rw [spanIdx_eq_vecIdx hb]
  exact_mod_cast key

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.ShareSt
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate Module
open scoped ComplexOrder

def ballRatio (r : ℕ) : ℝ := (1 + 1 / (7 * (r : ℝ))) / (1 - 1 / (7 * (r : ℝ)))

def signMat (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun k : Fin r => sgn p k

def BoundedBallStatement : Prop :=
  ∀ (r p : ℕ) (H : Matrix (Fin r) (Fin r) ℂ) (s : ℝ),
    H.PosDef → H * signMat p r * H = signMat p r → 0 ≤ s → s < 1 →
    (∀ u : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ u) = u → negSq p u ≤ s ^ 2 * posSq p u) →
    ∀ u : Fin r → ℂ, hq H u ≤ (1 + s) / (1 - s) * normSq u ∧
      normSq u ≤ (1 + s) / (1 - s) * hq H u

def NoContraction {K : Type} [Field K] [NumberField K] {r : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  ∀ N : Matrix (Fin r) (Fin r) K, (∀ x ∈ L, N *ᵥ x ∈ L) →
    (∀ (σ : K →+* ℂ) (u : Fin r → ℂ), u ≠ 0 → hq (H σ) (N.map σ *ᵥ u) < hq (H σ) u) → N = 0

end ReciprocityTheory.MultiplicativeHeights
end
end

