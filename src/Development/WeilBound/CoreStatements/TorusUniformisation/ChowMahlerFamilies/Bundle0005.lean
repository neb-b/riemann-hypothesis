module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0008

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.DualBasisReverseTriangular
section
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace PositivityTheory.Xgn.DualReverseTriangular

theorem repr_eq_dot {Ω : Type} [Field Ω] {r : ℕ} (w v : Module.Basis (Fin r) Ω (Fin r → Ω))
    (h : ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) (z : Fin r → Ω) (j : Fin r) :
    v.repr z j = w j.rev ⬝ᵥ z := by
  conv_rhs => rw [← v.sum_repr z]
  rw [dotProduct_sum]
  simp only [dotProduct_smul, h, Fin.rev_inj, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

theorem repr_eq_dot' {Ω : Type} [Field Ω] {r : ℕ} (w v : Module.Basis (Fin r) Ω (Fin r → Ω))
    (h : ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) (z : Fin r → Ω) (j : Fin r) :
    w.repr z j.rev = z ⬝ᵥ v j := by
  conv_rhs => rw [← w.sum_repr z]
  rw [sum_dotProduct]
  simp only [smul_dotProduct, h, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

theorem tri_inv {Ω : Type} [Field Ω] {r : ℕ} (w w' : Module.Basis (Fin r) Ω (Fin r → Ω))
    (h : ∀ i j, i < j → w.repr (w' i) j = 0) :
    (∀ i j, i < j → w'.repr (w i) j = 0) ∧ ∀ i, w'.repr (w i) i * w.repr (w' i) i = 1 := by
  have hAB := w.toMatrix_mul_toMatrix_flip w'
  have hBA := w'.toMatrix_mul_toMatrix_flip w
  letI : Invertible (w.toMatrix w') := ⟨w'.toMatrix w, hBA, hAB⟩
  have hA : (w.toMatrix w').BlockTriangular id := by
    intro i j hji
    rw [Module.Basis.toMatrix_apply]
    exact h j i hji
  have hB : (w'.toMatrix w).BlockTriangular id := by
    have hinv := Matrix.blockTriangular_inv_of_blockTriangular hA
    rwa [Matrix.inv_eq_right_inv hAB] at hinv
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · simpa [Module.Basis.toMatrix_apply] using hB hij
  · have e := congrFun (congrFun hBA i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at e
    · simpa [Module.Basis.toMatrix_apply] using e
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · rw [hB hlt, zero_mul]
      · rw [hA hlt, mul_zero]
    · simp

end PositivityTheory.Xgn.DualReverseTriangular

theorem PositivityTheory.Xgn.dual_basis_reverse_triangular : ∀ (Ω : Type) [Field Ω] (r : ℕ) (w w' v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
    (∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) → (∀ i j, w' i ⬝ᵥ v' j = if i = j.rev then 1 else 0) →
    (∀ i j, i < j → w.repr (w' i) j = 0) →
    (∀ i j, i < j → v.repr (v' i) j = 0) ∧ ∀ i, v.repr (v' i) i * w.repr (w' i.rev) i.rev = 1 := by
  intro Ω _ r w w' v v' h h' ht
  obtain ⟨h1, h2⟩ := PositivityTheory.Xgn.DualReverseTriangular.tri_inv w w' ht
  have key : ∀ i j, v.repr (v' i) j = w'.repr (w j.rev) i.rev := fun i j => by
    rw [PositivityTheory.Xgn.DualReverseTriangular.repr_eq_dot w v h,
      PositivityTheory.Xgn.DualReverseTriangular.repr_eq_dot' w' v' h']
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key]
    exact h1 _ _ (Fin.rev_lt_rev.mpr hij)
  · rw [key]
    exact h2 _
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HodgeDualFrameExists
section
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace PositivityTheory.Xgn.HodgeDualFrame

theorem mem_dotDual {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) {r : ℕ}
    (L : AddSubgroup (Fin r → Ω)) (e : Fin r → Ω) :
    e ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ e ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem pow_mul_mem {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {R : Subalgebra O Ω} {f a : Ω}
    (hf : f ∈ R) {m n : ℕ} (hmn : m ≤ n) (h : f ^ m * a ∈ R) : f ^ n * a ∈ R := by
  have key : f ^ n * a = f ^ (n - m) * (f ^ m * a) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hmn]
  rw [key]
  exact R.mul_mem (R.pow_mem hf _) h

theorem exists_unif {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {R : Subalgebra O Ω} {f : Ω}
    (hf : f ∈ R) {m : ℕ} (a : Fin m → Ω) (h : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) :
    ∃ n : ℕ, ∀ q, f ^ n * a q ∈ R := by
  choose n hn using h
  refine ⟨Finset.univ.sup n, fun q => ?_⟩
  exact pow_mul_mem hf (Finset.le_sup (Finset.mem_univ q)) (hn q)

theorem exists_dual {Ω : Type} [Field Ω] {r : ℕ} (b : Fin r → Fin r → Ω)
    (hli : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = ⊤) :
    ∃ d : Fin r → Fin r → Ω, (∀ (a : Fin r → Ω) (q : Fin r), (∑ p, a p • b p) ⬝ᵥ d q = a q) ∧
      ∀ e : Fin r → Ω, e = ∑ q, (b q ⬝ᵥ e) • d q := by
  classical
  let M : Matrix (Fin r) (Fin r) Ω := Matrix.of b
  have hu : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.mp hli
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hu
  have hrow : ∀ p q, b p ⬝ᵥ (fun i => M⁻¹ i q) = if p = q then 1 else 0 := by
    intro p q
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv M hdet) p) q
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  refine ⟨fun q i => M⁻¹ i q, ?_, ?_⟩
  · intro a q
    rw [sum_dotProduct]
    simp_rw [smul_dotProduct, hrow]
    simp
  · intro e
    have h := Matrix.mulVec_mulVec e M⁻¹ M
    rw [Matrix.nonsing_inv_mul M hdet, Matrix.one_mulVec] at h
    funext i
    calc e i = Matrix.mulVec M⁻¹ (Matrix.mulVec M e) i := by rw [h]
      _ = _ := by
        simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro q _
        rw [mul_comm]
        rfl

theorem main {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) {r : ℕ}
    (L : AddSubgroup (Fin r → Ω)) {m : ℕ} (s : Fin m → Fin r → Ω) (hs : ∀ k, s k ∈ L)
    (hgen : ∀ e ∈ L, ∃ a : Fin m → Ω, (∀ k, a k ∈ R) ∧ e = ∑ k, a k • s k)
    {f : Ω} (hf : f ∈ R) (b : Fin r → Fin r → Ω)
    (hli : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = ⊤)
    (hfr : ∀ e : Fin r → Ω, (∃ n : ℕ, f ^ n • e ∈ L) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q) :
    ∃ d : Fin r → Fin r → Ω, LinearIndependent Ω d ∧
      Submodule.span Ω (Set.range d) = ⊤ ∧ ∀ e : Fin r → Ω,
        ((∃ n : ℕ, f ^ n • e ∈ dotDual R L) ↔
          ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) ∧ e = ∑ q, a q • d q) := by
  classical
  obtain ⟨d, hd1, hd2⟩ := exists_dual b hli hsp
  have hδ : ∀ p q, b p ⬝ᵥ d q = if p = q then 1 else 0 := by
    intro p q
    have h := hd1 (Pi.single p 1) q
    have hs : (∑ p', (Pi.single p (1 : Ω) : Fin r → Ω) p' • b p') = b p := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro p' _ hp'
        simp [Pi.single_eq_of_ne hp']
      · simp
    rw [hs] at h
    rw [h]
    by_cases hpq : p = q
    · subst hpq
      simp
    · simp [hpq, Pi.single_eq_of_ne (Ne.symm hpq)]
  have hcoord : ∀ (a : Fin r → Ω) q, b q ⬝ᵥ (∑ p, a p • d p) = a q := by
    intro a q
    rw [dotProduct_sum]
    simp_rw [dotProduct_smul, hδ]
    simp
  have hli' : LinearIndependent Ω d := by
    rw [Fintype.linearIndependent_iff]
    intro g hg q
    have h := hcoord g q
    rw [hg, dotProduct_zero] at h
    exact h.symm
  have hsp' : Submodule.span Ω (Set.range d) = ⊤ := by
    rw [eq_top_iff]
    intro e _
    rw [hd2 e]
    exact Submodule.sum_mem _ (fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩))
  choose c hc hce using fun k => (hfr (s k)).mp ⟨0, by simpa using hs k⟩
  refine ⟨d, hli', hsp', fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨n, hn⟩
    refine ⟨fun q => b q ⬝ᵥ e, fun q => ?_, hd2 e⟩
    have hbq : ∃ N : ℕ, f ^ N • b q ∈ L := by
      apply (hfr (b q)).mpr
      refine ⟨Pi.single q 1, fun p => ⟨0, ?_⟩, ?_⟩
      · by_cases hpq : p = q
        · subst hpq
          simp
        · simp [Pi.single_eq_of_ne hpq]
      · rw [Finset.sum_eq_single q]
        · simp
        · intro p _ hp
          simp [Pi.single_eq_of_ne hp]
        · simp
    obtain ⟨N, hN⟩ := hbq
    refine ⟨N + n, ?_⟩
    have h := (mem_dotDual R L _).mp hn _ hN
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h
    show f ^ (N + n) * (b q ⬝ᵥ e) ∈ R
    rw [pow_add, mul_assoc]
    exact h
  · rintro ⟨a, ha, rfl⟩
    have hsk : ∀ k, s k ⬝ᵥ (∑ p, a p • d p) = ∑ p, c k p * a p := by
      intro k
      rw [hce k, sum_dotProduct]
      simp_rw [smul_dotProduct, hcoord, smul_eq_mul]
    have hk : ∀ k, ∃ n : ℕ, f ^ n * (s k ⬝ᵥ (∑ p, a p • d p)) ∈ R := by
      intro k
      obtain ⟨n, hn⟩ := exists_unif hf (fun p => c k p * a p) (fun p => by
        obtain ⟨n1, h1⟩ := hc k p
        obtain ⟨n2, h2⟩ := ha p
        refine ⟨n1 + n2, ?_⟩
        have hm : f ^ (n1 + n2) * (c k p * a p) = (f ^ n1 * c k p) * (f ^ n2 * a p) := by ring
        rw [hm]
        exact R.mul_mem h1 h2)
      refine ⟨n, ?_⟩
      rw [hsk k, Finset.mul_sum]
      exact sum_mem (fun p _ => hn p)
    obtain ⟨N, hN⟩ := exists_unif hf (fun k => s k ⬝ᵥ (∑ p, a p • d p)) hk
    refine ⟨N, (mem_dotDual R L _).mpr fun l hl => ?_⟩
    obtain ⟨g, hg, rfl⟩ := hgen l hl
    rw [sum_dotProduct]
    refine sum_mem (fun k _ => ?_)
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    exact R.mul_mem (hg k) (hN k)

end PositivityTheory.Xgn.HodgeDualFrame

theorem PositivityTheory.Xgn.hodge_dual_frame_exists : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)),
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i, x i ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing O x i) ∧ (∀ l, c l ∈ chartRing O x i) ∧
      ∑ l, c l * f l = 1 ∧ ∀ l, ∃ b : Fin r → Fin r → Ω, LinearIndependent Ω b ∧
        Submodule.span Ω (Set.range b) = ⊤ ∧ ∀ e : Fin r → Ω,
          ((∃ n : ℕ, f l ^ n • e ∈ dotDual (chartRing O x i) (B.lat i)) ↔
            ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing O x i) ∧ e = ∑ q, a q • b q) := by
  intro O _ Ω _ _ ι x r B hB i hi
  obtain ⟨k, f, c, hf, hc, hsum, hfr⟩ := B.frame i hi
  refine ⟨k, f, c, hf, hc, hsum, fun l => ?_⟩
  obtain ⟨b, hli, hsp, hb⟩ := hfr l
  obtain ⟨m, s, hs, hgen⟩ := hB i hi
  exact PositivityTheory.Xgn.HodgeDualFrame.main (chartRing O x i) (B.lat i) s hs hgen
    (hf l) b hli hsp hb
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HodgeDualLatticeOverlap
section
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace PositivityTheory.Xgn.HodgeDualOverlap

theorem mem_dotDual {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) {r : ℕ}
    (L : AddSubgroup (Fin r → Ω)) (e : Fin r → Ω) :
    e ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ e ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

end PositivityTheory.Xgn.HodgeDualOverlap

private theorem exists_div_pow_mul_mem_chartRing {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {ι : Type}
    (x : ι → Ω) (i j : ι) (hi : x i ≠ 0) (y : Ω) (hy : y ∈ chartRing O x i) :
    ∃ d : ℕ, (x i / x j) ^ d * y ∈ chartRing O x j := by
  have hq : x i / x j ∈ chartRing O x j := Algebra.subset_adjoin ⟨i, rfl⟩
  have mono : ∀ z : Ω, ∀ d n : ℕ, d ≤ n → (x i / x j) ^ d * z ∈ chartRing O x j →
      (x i / x j) ^ n * z ∈ chartRing O x j := by
    intro z d n hdn hz
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdn
    rw [pow_add, mul_comm ((x i / x j) ^ d), mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hq _) hz
  induction hy using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨t, rfl⟩ := hz
    refine ⟨1, ?_⟩
    have h : (x i / x j) ^ 1 * (x t / x i) = x t / x j := by
      rw [pow_one, div_mul_div_comm, mul_comm (x i), mul_div_mul_right _ _ hi]
    rw [h]
    exact Algebra.subset_adjoin ⟨t, rfl⟩
  | algebraMap r => exact ⟨0, by simpa using Subalgebra.algebraMap_mem _ r⟩
  | add a b _ _ ha hb =>
    obtain ⟨d, hd⟩ := ha
    obtain ⟨e, he⟩ := hb
    refine ⟨d + e, ?_⟩
    rw [mul_add]
    exact Subalgebra.add_mem _ (mono _ d _ (by omega) hd) (mono _ e _ (by omega) he)
  | mul a b _ _ ha hb =>
    obtain ⟨d, hd⟩ := ha
    obtain ⟨e, he⟩ := hb
    refine ⟨d + e, ?_⟩
    have h : (x i / x j) ^ (d + e) * (a * b) = ((x i / x j) ^ d * a) * ((x i / x j) ^ e * b) := by
      ring
    rw [h]
    exact Subalgebra.mul_mem _ hd he

open PositivityTheory.Xgn.HodgeDualOverlap in
theorem PositivityTheory.Xgn.hodge_dual_lattice_overlap : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (L : ι → AddSubgroup (Fin r → Ω)),
    (∀ c, ∀ a ∈ chartRing O x c, ∀ e ∈ L c, a • e ∈ L c) →
    (∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ L i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ L j) →
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ L c) ∧
      ∀ e ∈ L c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ dotDual (chartRing O x i) (L i),
      ∃ m : ℕ, (x i / x j) ^ m • e ∈ dotDual (chartRing O x j) (L j) := by
  intro O _ Ω _ _ ι x r L _ h2 h3 i j hi hj e he
  rw [mem_dotDual] at he
  have hq : x i / x j ∈ chartRing O x j := Algebra.subset_adjoin ⟨i, rfl⟩
  obtain ⟨n, s, hs, hgen⟩ := h3 j hj
  have hk : ∀ k, ∃ m : ℕ, (x i / x j) ^ m * (s k ⬝ᵥ e) ∈ chartRing O x j := by
    intro k
    obtain ⟨a, ha⟩ := h2 j i hj hi (s k) (hs k)
    have hmem := he _ ha
    rw [smul_dotProduct, smul_eq_mul] at hmem
    obtain ⟨d, hd⟩ := exists_div_pow_mul_mem_chartRing x i j hi _ hmem
    refine ⟨d, ?_⟩
    have hc1 : x i / x j * (x j / x i) = 1 := by field_simp
    have hc : (x i / x j) ^ a * (x j / x i) ^ a = 1 := by rw [← mul_pow, hc1, one_pow]
    have h : (x i / x j) ^ d * (s k ⬝ᵥ e) =
        (x i / x j) ^ a * ((x i / x j) ^ d * ((x j / x i) ^ a * (s k ⬝ᵥ e))) := by
      linear_combination (-((x i / x j) ^ d * (s k ⬝ᵥ e))) * hc
    rw [h]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hq _) hd
  choose m hm using hk
  refine ⟨∑ k, m k, ?_⟩
  rw [mem_dotDual]
  intro l hl
  obtain ⟨c, hc, rfl⟩ := hgen l hl
  rw [sum_dotProduct]
  refine Subalgebra.sum_mem _ (fun k _ => ?_)
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  refine Subalgebra.mul_mem _ (hc k) ?_
  have hle : m k ≤ ∑ k, m k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
  rw [ht, pow_add, mul_comm ((x i / x j) ^ m k), mul_assoc]
  exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hq _) (hm k)
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XDotdualBc
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.A_dotdual_bc

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (w : Fin m → Ω) :
    w ∈ dotDual R L ↔ ∀ v ∈ L, v ⬝ᵥ w ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

theorem dot_bij (m : ℕ) : Function.Bijective (dotProductBilin Ω Ω (m := Fin m) (A := Ω)).flip := by
  have h : ⇑(dotProductBilin Ω Ω (m := Fin m) (A := Ω)).flip = ⇑(dotProductEquiv Ω (Fin m)) := by
    funext w
    ext j
    simp [dotProductBilin, dotProductEquiv]
  rw [h]
  exact (dotProductEquiv Ω (Fin m)).bijective

theorem exists_system (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω))
    (h : LocFree R m L) : ∃ (k : ℕ) (v l : Fin k × Fin m → Fin m → Ω), (∀ i, v i ∈ L) ∧
      (∀ i, l i ∈ dotDual R L) ∧ ∀ j j', ∑ i, l i j * v i j' = if j' = j then 1 else 0 := by
  let L' : Submodule R (Fin m → Ω) :=
    { L with smul_mem' := fun a e he => h.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L') (r := m) h
  refine ⟨k, fun i => v i, fun i j => φ i (Pi.single j 1), fun i => (v i).2, fun i => ?_,
    fun j j' => ?_⟩
  · rw [mem_dotDual]
    intro e he
    have h1 : e ⬝ᵥ (fun j => φ i (Pi.single j 1)) = φ i e := by
      rw [LinearMap.pi_apply_eq_sum_univ (φ i) e, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul]
      congr 2
      funext j'
      simp [Pi.single_apply, eq_comm]
    rw [h1]
    exact hφ i e he
  · have := congrFun (hv (Pi.single j 1)) j'
    simpa [Finset.sum_apply, Pi.single_apply] using this

theorem bc_dot {C : Type} [Field C] [Algebra Ω C] {m : ℕ} (a b : Fin m → Ω) :
    bcMap Ω C (Fin m) a ⬝ᵥ bcMap Ω C (Fin m) b = algebraMap Ω C (a ⬝ᵥ b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, bcMap, map_sum]

end PositivityTheory.Xgn.A_dotdual_bc

open PositivityTheory.Xgn.A_dotdual_bc in
theorem PositivityTheory.Xgn.t_dotdual_bc : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ (m : ℕ) (L : AddSubgroup (Fin m → Ω)), LocFree R m L → LocFree R m (dotDual R L) ∧ dotDual R (dotDual R L) = L ∧ dotDual RC (spanOver RC (bcMap Ω C (Fin m) '' L)) = spanOver RC (bcMap Ω C (Fin m) '' (dotDual R L : AddSubgroup (Fin m → Ω))) := by
  intro o Ω C _ _ _ _ _ _ _ R RC hR m L h
  obtain ⟨h1, h2⟩ := DualLattice.locFree_dual R (dotProductBilin Ω Ω (m := Fin m) (A := Ω))
    (dot_bij m) m L (dotDual R L) h (fun w => mem_dotDual R L w)
  refine ⟨h1, ?_, ?_⟩
  · ext v
    rw [mem_dotDual, h2]
    refine forall₂_congr fun w _ => ?_
    rw [dotProduct_comm]
    rfl
  obtain ⟨k, v, l, hv, hl, hs⟩ := exists_system R L h
  apply le_antisymm
  · intro u hu
    rw [mem_dotDual] at hu
    have key : u = ∑ i, (bcMap Ω C (Fin m) (v i) ⬝ᵥ u) • bcMap Ω C (Fin m) (l i) := by
      funext j
      have h3 : ∀ j', ∑ i, algebraMap Ω C (l i j) * algebraMap Ω C (v i j')
          = if j' = j then 1 else 0 := fun j' => by
        have := congrArg (algebraMap Ω C) (hs j j')
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum] at this
        simp only [map_mul] at this
        rw [this]
        split_ifs <;> simp
      have h4 : ∀ (x : Fin m → Ω) j, bcMap Ω C (Fin m) x j = algebraMap Ω C (x j) := fun _ _ => rfl
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, h4, Finset.sum_mul]
      rw [Finset.sum_comm]
      calc u j = ∑ j', (if j' = j then 1 else 0) * u j' := by simp
        _ = _ := Finset.sum_congr rfl fun j' _ => by
          rw [← h3, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
    rw [key]
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
    refine ⟨_, hu _ (AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨v i, hv i, rfl⟩, ?_⟩), _,
      ⟨l i, hl i, rfl⟩, rfl⟩
    rw [one_smul]
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, _, ⟨w, hw, rfl⟩, rfl⟩
    refine (mem_dotDual _ _ _).2 fun x hx => ?_
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, _, ⟨e, he, rfl⟩, rfl⟩ := hx
      rw [smul_dotProduct, dotProduct_smul, bc_dot, smul_eq_mul, smul_eq_mul]
      exact RC.mul_mem hb (RC.mul_mem ha (hR _ ((mem_dotDual R L w).1 hw e he)))
    | zero => rw [zero_dotProduct]; exact RC.zero_mem
    | add x y _ _ hx hy => rw [add_dotProduct]; exact RC.add_mem hx hy
    | neg x _ hx => rw [neg_dotProduct]; exact RC.neg_mem hx
end

