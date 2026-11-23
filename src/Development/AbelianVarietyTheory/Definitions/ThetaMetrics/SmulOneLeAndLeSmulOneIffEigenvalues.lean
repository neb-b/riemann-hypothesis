module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.StarInvMulVecDotProductMulVecInvMulVec
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005

@[expose] public section

open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology

namespace GlobalTheory

section Weight

variable {κ X : Type*}

noncomputable def lwP₂ (S : Finset κ) (z : κ → ℂ) : ℝ :=
  1 + ∑ j ∈ S, |Real.log ‖z j‖|

def coordDivisor (S : Finset κ) (w : X → κ → ℂ) : Set X :=
  {x | ∃ j ∈ S, w x j = 0}

theorem notMem_coordDivisor {S : Finset κ} {w : X → κ → ℂ} {x : X} :
    x ∉ coordDivisor S w ↔ ∀ j ∈ S, w x j ≠ 0 := by
  simp [coordDivisor]

theorem mem_coordDivisor_iff_prod_eq_zero {S : Finset κ} {w : X → κ → ℂ} {x : X} :
    x ∈ coordDivisor S w ↔ ∏ j ∈ S, w x j = 0 := by
  simp [coordDivisor, Finset.prod_eq_zero_iff]

theorem isClosed_coordDivisor [TopologicalSpace X] (S : Finset κ) {w : X → κ → ℂ}
    (hw : ∀ j ∈ S, Continuous fun x => w x j) : IsClosed (coordDivisor S w) := by
  have : coordDivisor S w = {x | ∏ j ∈ S, w x j = 0} :=
    Set.ext fun _ => mem_coordDivisor_iff_prod_eq_zero
  rw [this]
  exact isClosed_eq (continuous_finsetProd S hw) continuous_const

theorem one_le_logWeight (S : Finset κ) (z : κ → ℂ) : 1 ≤ lwP₂ S z :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem logWeight_pos (S : Finset κ) (z : κ → ℂ) : 0 < lwP₂ S z :=
  one_pos.trans_le (one_le_logWeight S z)

theorem abs_log_norm_le_logWeight {S : Finset κ} (z : κ → ℂ) {j : κ} (hj : j ∈ S) :
    |Real.log ‖z j‖| ≤ lwP₂ S z :=
  (Finset.single_le_sum (f := fun j => |Real.log ‖z j‖|) (fun _ _ => abs_nonneg _) hj).trans
    (le_add_of_nonneg_left zero_le_one)

theorem mul_logWeight_pow_le (S : Finset κ) (z : κ → ℂ) {C C' : ℝ} {N N' : ℕ} (hC : C ≤ C')
    (hC' : 0 ≤ C') (hN : N ≤ N') : C * lwP₂ S z ^ N ≤ C' * lwP₂ S z ^ N' :=
  mul_le_mul hC (pow_le_pow_right₀ (one_le_logWeight S z) hN)
    (pow_nonneg (logWeight_pos S z).le _) hC'

end Weight

section Polydisc

variable {ι : Type*}

end Polydisc

section Growth

variable {κ κ' X X' E F : Type*} [TopologicalSpace X] [TopologicalSpace X']
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

def HasLogGrowth (S : Finset κ) (w : X → κ → ℂ) (U : Set X) (f : X → E) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ x ∈ K, x ∉ coordDivisor S w →
    ‖f x‖ ≤ C * lwP₂ S (w x) ^ N

variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}

namespace HasLogGrowth

theorem exists_one_le {f : X → E} (hf : HasLogGrowth S w U f) {K : Set X} (hKU : K ⊆ U)
    (hK : IsCompact K) : ∃ (C : ℝ) (N : ℕ), 1 ≤ C ∧ ∀ x ∈ K, x ∉ coordDivisor S w →
      ‖f x‖ ≤ C * lwP₂ S (w x) ^ N := by
  obtain ⟨C, N, h⟩ := hf K hKU hK
  exact ⟨max C 1, N, le_max_right _ _, fun x hx hB => (h x hx hB).trans
    (mul_logWeight_pow_le _ _ (le_max_left _ _) (zero_le_one.trans (le_max_right _ _)) le_rfl)⟩

theorem mono {f : X → E} (hf : HasLogGrowth S w U f) {V : Set X} (hV : V ⊆ U) :
    HasLogGrowth S w V f :=
  fun K hK => hf K (hK.trans hV)

theorem of_norm_le {f : X → E} {g : X → F} (hg : HasLogGrowth S w U g)
    (h : ∀ x ∈ U, x ∉ coordDivisor S w → ‖f x‖ ≤ ‖g x‖) : HasLogGrowth S w U f := by
  intro K hKU hK
  obtain ⟨C, N, hC⟩ := hg K hKU hK
  exact ⟨C, N, fun x hx hB => (h x (hKU hx) hB).trans (hC x hx hB)⟩

theorem of_le {f : X → E} {g : X → ℝ} (hg : HasLogGrowth S w U g)
    (h : ∀ x ∈ U, x ∉ coordDivisor S w → ‖f x‖ ≤ g x) : HasLogGrowth S w U f :=
  hg.of_norm_le fun x hx hB => (h x hx hB).trans (le_abs_self _)

theorem congr {f g : X → E} (hg : HasLogGrowth S w U g)
    (h : ∀ x ∈ U, x ∉ coordDivisor S w → f x = g x) : HasLogGrowth S w U f :=
  hg.of_norm_le fun x hx hB => by rw [h x hx hB]

theorem norm {f : X → E} (hf : HasLogGrowth S w U f) : HasLogGrowth S w U fun x => ‖f x‖ :=
  hf.of_norm_le fun _ _ _ => (norm_norm _).le

theorem of_continuousOn {f : X → E} (hf : ContinuousOn f U) : HasLogGrowth S w U f := by
  intro K hKU hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hf.mono hKU)
  exact ⟨C, 0, fun x hx _ => by simpa using hC x hx⟩

theorem const (c : E) : HasLogGrowth S w U fun _ => c :=
  of_continuousOn continuousOn_const

theorem lwP₂ : HasLogGrowth S w U fun x => lwP₂ S (w x) :=
  fun _ _ _ => ⟨1, 1, fun x _ _ => by simp [abs_of_pos (logWeight_pos S (w x))]⟩

theorem log_norm {j : κ} (hj : j ∈ S) : HasLogGrowth S w U fun x => Real.log ‖w x j‖ :=
  lwP₂.of_le fun x _ _ => abs_log_norm_le_logWeight (w x) hj

theorem add {f g : X → E} (hf : HasLogGrowth S w U f) (hg : HasLogGrowth S w U g) :
    HasLogGrowth S w U fun x => f x + g x := by
  intro K hKU hK
  obtain ⟨C, N, hC1, hC⟩ := hf.exists_one_le hKU hK
  obtain ⟨D, M, hD1, hD⟩ := hg.exists_one_le hKU hK
  refine ⟨C + D, max N M, fun x hx hB => (norm_add_le _ _).trans ?_⟩
  rw [add_mul]
  exact add_le_add
    ((hC x hx hB).trans (mul_logWeight_pow_le _ _ le_rfl (by linarith) (le_max_left _ _)))
    ((hD x hx hB).trans (mul_logWeight_pow_le _ _ le_rfl (by linarith) (le_max_right _ _)))

theorem sum {α : Type*} {s : Finset α} {f : α → X → E} (hf : ∀ a ∈ s, HasLogGrowth S w U (f a)) :
    HasLogGrowth S w U fun x => ∑ a ∈ s, f a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

theorem mul {R : Type*} [SeminormedRing R] {f g : X → R} (hf : HasLogGrowth S w U f)
    (hg : HasLogGrowth S w U g) : HasLogGrowth S w U fun x => f x * g x := by
  intro K hKU hK
  obtain ⟨C, N, hC1, hC⟩ := hf.exists_one_le hKU hK
  obtain ⟨D, M, hD1, hD⟩ := hg.exists_one_le hKU hK
  refine ⟨C * D, N + M, fun x hx hB => (norm_mul_le _ _).trans ?_⟩
  rw [pow_add, mul_mul_mul_comm]
  exact mul_le_mul (hC x hx hB) (hD x hx hB) (norm_nonneg _) ((norm_nonneg _).trans (hC x hx hB))

theorem prod {R α : Type*} [SeminormedCommRing R] {s : Finset α} {f : α → X → R}
    (hf : ∀ a ∈ s, HasLogGrowth S w U (f a)) : HasLogGrowth S w U fun x => ∏ a ∈ s, f a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).mul
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

theorem pow {R : Type*} [SeminormedRing R] {f : X → R} (hf : HasLogGrowth S w U f) (k : ℕ) :
    HasLogGrowth S w U fun x => f x ^ k := by
  induction k with
  | zero => simpa using const 1
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem comp_of_logWeight {f : X → E} (hf : HasLogGrowth S w U f) {S' : Finset κ'}
    {w' : X' → κ' → ℂ} {U' : Set X'} {π : X' → X} (hπ : ContinuousOn π U') (hU : MapsTo π U' U)
    (hB : ∀ x ∈ U', x ∉ coordDivisor S' w' → π x ∉ coordDivisor S w)
    (hw : HasLogGrowth S' w' U' fun x => GlobalTheory.lwP₂ S (w (π x))) :
    HasLogGrowth S' w' U' fun x => f (π x) := by
  intro K hKU hK
  obtain ⟨C, N, h⟩ := hf (π '' K) (hU.mono_left hKU).image_subset
    (hK.image_of_continuousOn (hπ.mono hKU))
  exact HasLogGrowth.of_le (U := K) ((const C).mul ((hw.mono hKU).pow N))
    (fun x hx hx' => h _ (mem_image_of_mem π hx) (hB x (hKU hx) hx')) K Subset.rfl hK

end HasLogGrowth

def IsUnitMulMonomialOn (S : Finset κ) (v : X' → κ → ℂ) (S' : Finset κ') (w' : X' → κ' → ℂ)
    (U' : Set X') : Prop :=
  ∀ j ∈ S, ∃ (u : X' → ℂ) (m : κ' → ℕ), ContinuousOn u U' ∧
    ∀ x ∈ U', u x ≠ 0 ∧ v x j = u x * ∏ i ∈ S', w' x i ^ m i

namespace IsUnitMulMonomialOn

variable {S' : Finset κ'} {w' : X' → κ' → ℂ} {U' : Set X'} {v : X' → κ → ℂ}

theorem notMem (h : IsUnitMulMonomialOn S v S' w' U') {x : X'} (hx : x ∈ U')
    (hB : x ∉ coordDivisor S' w') : x ∉ coordDivisor S v := by
  rw [notMem_coordDivisor] at hB ⊢
  intro j hj
  obtain ⟨u, m, -, hu⟩ := h j hj
  rw [(hu x hx).2]
  exact mul_ne_zero (hu x hx).1 (Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ (hB i hi))

theorem hasLogGrowth_logWeight (h : IsUnitMulMonomialOn S v S' w' U') :
    HasLogGrowth S' w' U' fun x => lwP₂ S (v x) := by
  refine (HasLogGrowth.const 1).add (HasLogGrowth.sum (f := fun j x => |Real.log ‖v x j‖|)
    fun j hj => ?_)
  obtain ⟨u, m, hc, hu⟩ := h j hj
  have h1 : HasLogGrowth S' w' U' fun x => Real.log ‖u x‖ :=
    .of_continuousOn (hc.norm.log fun x hx => norm_ne_zero_iff.2 (hu x hx).1)
  have h2 : HasLogGrowth S' w' U' fun x => ∑ i ∈ S', (m i : ℝ) * Real.log ‖w' x i‖ :=
    .sum (f := fun i x => (m i : ℝ) * Real.log ‖w' x i‖)
      fun i hi => (HasLogGrowth.const _).mul (.log_norm hi)
  refine (h1.add h2).norm.congr fun x hx hB => ?_
  rw [notMem_coordDivisor] at hB
  have h3 : ∀ i ∈ S', ‖w' x i ^ m i‖ ≠ 0 := fun i hi => norm_ne_zero_iff.2 (pow_ne_zero _ (hB i hi))
  rw [(hu x hx).2, norm_mul, norm_prod, Real.log_mul (norm_ne_zero_iff.2 (hu x hx).1)
    (Finset.prod_ne_zero_iff.2 h3), Real.log_prod h3]
  simp

end IsUnitMulMonomialOn

theorem HasLogGrowth.comp {f : X → E} (hf : HasLogGrowth S w U f) {S' : Finset κ'}
    {w' : X' → κ' → ℂ} {U' : Set X'} {π : X' → X} (hπ : ContinuousOn π U') (hU : MapsTo π U' U)
    (hw : IsUnitMulMonomialOn S (fun x => w (π x)) S' w' U') :
    HasLogGrowth S' w' U' fun x => f (π x) :=
  hf.comp_of_logWeight hπ hU (fun _ hx hB => hw.notMem hx hB) hw.hasLogGrowth_logWeight

end Growth

section Scalar

variable {κ κ' X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']

def IsLogBoundedScalar (S : Finset κ) (w : X → κ → ℂ) (U : Set X) (g : X → ℝ) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ x ∈ K, x ∉ coordDivisor S w →
    (C * lwP₂ S (w x) ^ N)⁻¹ ≤ g x ∧ g x ≤ C * lwP₂ S (w x) ^ N

variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X} {g g' : X → ℝ}

namespace IsLogBoundedScalar

end IsLogBoundedScalar

end Scalar

section Entries

variable {κ X l m n : Type*} [TopologicalSpace X]

def HasLogGrowthEntries (S : Finset κ) (w : X → κ → ℂ) (U : Set X) (A : X → Matrix m n ℂ) : Prop :=
  ∀ i j, HasLogGrowth S w U fun x => A x i j

variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}

namespace HasLogGrowthEntries

end HasLogGrowthEntries

end Entries

section MatrixLemmas

variable {m n : Type*}

variable [Fintype n] [DecidableEq n]

variable [Fintype m] [DecidableEq m]

noncomputable def schurComplement₁₁ (G : Matrix (m ⊕ n) (m ⊕ n) ℂ) : Matrix n n ℂ :=
  G.toBlocks₂₂ - G.toBlocks₂₁ * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂



end MatrixLemmas

section PiKronecker

variable {α : Type*} [Fintype α] {l n o : α → Type*}

variable [DecidableEq α] [∀ a, Fintype (n a)]

variable [∀ a, DecidableEq (n a)]

end PiKronecker

section Compound

variable {l n o : Type*} [LinearOrder l] [LinearOrder n] [LinearOrder o]

noncomputable def compoundMatrix (k : ℕ) (A : Matrix l n ℂ) :
    Matrix (Set.powersetCard l k) (Set.powersetCard n k) ℂ :=
  Matrix.of fun I J => (A.submatrix (subsetEnum I) (subsetEnum J)).det

theorem compoundMatrix_mul [Fintype n] (k : ℕ) (A : Matrix l n ℂ) (A' : Matrix n o ℂ) :
    compoundMatrix k (A * A') = compoundMatrix k A * compoundMatrix k A' := by
  ext I J
  exact det_submatrix_mul_eq_sum_minors A A' _ _

theorem compoundMatrix_conjTranspose (k : ℕ) (A : Matrix l n ℂ) :
    compoundMatrix k Aᴴ = (compoundMatrix k A)ᴴ := by
  ext I J
  simp only [compoundMatrix, of_apply, conjTranspose_apply, ← det_conjTranspose,
    conjTranspose_submatrix]

theorem compoundMatrix_one (k : ℕ) : compoundMatrix k (1 : Matrix n n ℂ) = 1 := by
  ext I J
  rcases eq_or_ne I J with rfl | h
  · rw [one_apply_eq, compoundMatrix, of_apply, submatrix_one _ (subsetEnum_injective I), det_one]
  · rw [one_apply_ne h, compoundMatrix, of_apply]
    obtain ⟨x, hxI, hxJ⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne I J).mp h
    have h1 : x ∈ range (subsetEnum I) := by rw [range_subsetEnum]; exact hxI
    have h2 : x ∉ range (subsetEnum J) := by rw [range_subsetEnum]; exact hxJ
    obtain ⟨i, rfl⟩ := h1
    exact det_eq_zero_of_row_eq_zero i fun j => one_apply_ne fun e => h2 ⟨j, e.symm⟩

variable [Fintype n]

end Compound

section LogBounded

variable {κ κ' X X' m n : Type*} [TopologicalSpace X] [TopologicalSpace X']

def IsLogBounded [DecidableEq n] (S : Finset κ) (w : X → κ → ℂ) (U : Set X)
    (G : X → Matrix n n ℂ) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ x ∈ K, x ∉ coordDivisor S w →
    (C * lwP₂ S (w x) ^ N)⁻¹ • (1 : Matrix n n ℂ) ≤ G x ∧
      G x ≤ (C * lwP₂ S (w x) ^ N) • (1 : Matrix n n ℂ)

variable [DecidableEq n] [DecidableEq m] {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
  {G G' : X → Matrix n n ℂ} {H : X → Matrix m m ℂ}

namespace IsLogBounded

variable [Fintype n]

end IsLogBounded

variable [Fintype n]

namespace IsLogBounded


end IsLogBounded


namespace IsLogBounded

variable [Fintype m]


end IsLogBounded

end LogBounded

section Examples

end Examples

end GlobalTheory
