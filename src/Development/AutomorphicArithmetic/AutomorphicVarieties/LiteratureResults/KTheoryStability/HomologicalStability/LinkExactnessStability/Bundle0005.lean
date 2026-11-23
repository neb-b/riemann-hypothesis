module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsGLSplitSeqStandardOfStableRangeLe
section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory.SplitStd

variable {R : Type} [CommRing R]

def extLast (m : ℕ) : Matrix (Fin m) (Fin m) R →* Matrix (Fin (m + 1)) (Fin (m + 1)) R where
  toFun A := Matrix.of fun i j =>
    Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j) (fun i' => Fin.lastCases 0 (fun j' => A i' j') j) i
  map_one' := by
    ext i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  map_mul' A B := by
    ext i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

theorem extLast_mulVec_single_last (m : ℕ) (A : Matrix (Fin m) (Fin m) R) :
    extLast m A *ᵥ Pi.single (Fin.last m) 1 = Pi.single (Fin.last m) 1 := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    simp [extLast, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.castSucc_ne_last]

theorem single_last_vecMul_extLast (m : ℕ) (A : Matrix (Fin m) (Fin m) R) :
    Pi.single (Fin.last m) 1 ᵥ* extLast m A = Pi.single (Fin.last m) 1 := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    simp [extLast, Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc, Fin.castSucc_ne_last]

theorem extLast_mulVec (m : ℕ) (A : Matrix (Fin m) (Fin m) R) (w : Fin (m + 1) → R)
    (hw : w (Fin.last m) = 0) (a : Fin m) (h : A *ᵥ (fun i => w i.castSucc) = Pi.single a 1) :
    extLast m A *ᵥ w = Pi.single a.castSucc 1 := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [extLast, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hw, (Fin.castSucc_ne_last a).symm]
  · have := congrFun h i
    simp only [Matrix.mulVec, dotProduct] at this
    simp [extLast, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hw, this, Pi.single_apply]

theorem vecMul_extLast (m : ℕ) (A : Matrix (Fin m) (Fin m) R) (w : Fin (m + 1) → R)
    (hw : w (Fin.last m) = 0) (a : Fin m) (h : (fun i => w i.castSucc) ᵥ* A = Pi.single a 1) :
    w ᵥ* extLast m A = Pi.single a.castSucc 1 := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [extLast, Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc, hw, (Fin.castSucc_ne_last a).symm]
  · have := congrFun h i
    simp only [Matrix.vecMul, dotProduct] at this
    simp [extLast, Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc, hw, this, Pi.single_apply]

theorem dot_conj {k : ℕ} (g : GL (Fin k) R) (f v : Fin k → R) :
    (f ᵥ* ((g⁻¹ : GL (Fin k) R) : Matrix (Fin k) (Fin k) R)) ⬝ᵥ ((g : Matrix (Fin k) (Fin k) R) *ᵥ v)
      = f ⬝ᵥ v := by
  rw [← dotProduct_mulVec, mulVec_mulVec, Units.inv_mul, one_mulVec]

theorem core (s : ℕ) (hs : StableRangeLe R s) : ∀ (k m : ℕ) (v f : Fin k → Fin m → R),
    (∀ i j, f i ⬝ᵥ v j = if i = j then 1 else 0) → k + s ≤ m →
    ∃ (g : GL (Fin m) R) (σ : Fin k → Fin m), Function.Injective σ ∧ ∀ j,
      (g : Matrix (Fin m) (Fin m) R) *ᵥ v j = Pi.single (σ j) 1 ∧
      f j ᵥ* ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) = Pi.single (σ j) 1 := by
  intro k
  induction k with
  | zero => intro m v f _ _; exact ⟨1, Fin.elim0, fun a => a.elim0, fun j => j.elim0⟩
  | succ k ih =>
    intro m v f hvf hkm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨g₁, hg₁v, hg₁f⟩ := GlobalTheory.T.exists_GL_moving_unimodular_pair_to_last_basis R s hs m (by omega) (v 0) (f 0) (by simpa using hvf 0 0)
    have hvl : ∀ j : Fin k, ((g₁ : Matrix _ _ R) *ᵥ v j.succ) (Fin.last m) = 0 := by
      intro j
      have key := dot_conj g₁ (f 0) (v j.succ)
      rw [hg₁f, single_dotProduct, one_mul, hvf, if_neg (Fin.succ_ne_zero j).symm] at key
      exact key
    have hfl : ∀ j : Fin k, (f j.succ ᵥ* ((g₁⁻¹ : GL _ R) : Matrix _ _ R)) (Fin.last m) = 0 := by
      intro j
      have key := dot_conj g₁ (f j.succ) (v 0)
      rw [hg₁v, dotProduct_single, mul_one, hvf, if_neg (Fin.succ_ne_zero j)] at key
      exact key
    let v' : Fin k → Fin m → R := fun j i => ((g₁ : Matrix _ _ R) *ᵥ v j.succ) i.castSucc
    let f' : Fin k → Fin m → R := fun j i => (f j.succ ᵥ* ((g₁⁻¹ : GL _ R) : Matrix _ _ R)) i.castSucc
    have hdual : ∀ i j, f' i ⬝ᵥ v' j = if i = j then 1 else 0 := by
      intro i j
      have key := dot_conj g₁ (f i.succ) (v j.succ)
      rw [hvf, dotProduct, Fin.sum_univ_castSucc, hvl j, mul_zero, add_zero] at key
      simpa [dotProduct, v', f', Fin.succ_inj] using key
    obtain ⟨g', σ', hσ', hg'⟩ := ih m v' f' hdual (by omega)
    refine ⟨Units.map (extLast m) g' * g₁,
      (Fin.cons (Fin.last m) (fun j => (σ' j).castSucc) : Fin (k + 1) → Fin (m + 1)), ?_, ?_⟩
    · rw [Fin.cons_injective_iff]
      refine ⟨?_, (Fin.castSucc_injective _).comp hσ'⟩
      rintro ⟨j, hj⟩
      exact Fin.castSucc_ne_last _ hj
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero, _root_.mul_inv_rev, Units.val_mul, Units.coe_map, Units.coe_map_inv]
        refine ⟨?_, ?_⟩
        · rw [← mulVec_mulVec, hg₁v, extLast_mulVec_single_last]
        · rw [← vecMul_vecMul, hg₁f, single_last_vecMul_extLast]
      · simp only [Fin.cons_succ, _root_.mul_inv_rev, Units.val_mul, Units.coe_map, Units.coe_map_inv]
        refine ⟨?_, ?_⟩
        · rw [← mulVec_mulVec]
          exact extLast_mulVec m _ _ (hvl j) _ (hg' j).1
        · rw [← vecMul_vecMul]
          exact vecMul_extLast m _ _ (hfl j) _ (hg' j).2

def pmat {n : ℕ} (π : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if i = π j then 1 else 0

theorem pmat_mul_symm {n : ℕ} (π : Equiv.Perm (Fin n)) : (pmat π : Matrix (Fin n) (Fin n) R) * pmat π.symm = 1 := by
  ext i j
  simp [pmat, Matrix.mul_apply, Matrix.one_apply, Equiv.apply_eq_iff_eq_symm_apply]

def pGL {n : ℕ} (π : Equiv.Perm (Fin n)) : GL (Fin n) R :=
  ⟨pmat π, pmat π.symm, pmat_mul_symm π, by simpa using pmat_mul_symm (R := R) π.symm⟩

theorem pGL_mulVec {n : ℕ} (π : Equiv.Perm (Fin n)) (a : Fin n) :
    ((pGL π : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ Pi.single a 1 = Pi.single (π a) 1 := by
  funext i
  simp only [pGL, pmat, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_apply]
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem vecMul_pGL_inv {n : ℕ} (π : Equiv.Perm (Fin n)) (a : Fin n) :
    Pi.single a 1 ᵥ* (((pGL π)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Pi.single (π a) 1 := by
  funext i
  simp only [pGL, pmat, Matrix.vecMul, dotProduct, Matrix.of_apply, Units.inv_mk]
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_apply, Equiv.eq_symm_apply, eq_comm]
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem exists_perm {n k : ℕ} (σ ι : Fin k → Fin n) (hσ : Function.Injective σ) (hι : Function.Injective ι) :
    ∃ π : Equiv.Perm (Fin n), ∀ j, π (σ j) = ι j := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, fun j => j.elim0⟩
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq (t := (Finset.univ : Finset (Fin n)))
    (s := Finset.univ.image σ) (f := fun x => ι (Function.invFun σ x)) (by simp)
    (fun _ _ => Finset.mem_univ _) (by
      intro x hx y hy hxy
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      simp only [Function.leftInverse_invFun hσ a, Function.leftInverse_invFun hσ b] at hxy
      rw [hι hxy])
  refine ⟨g.trans (Equiv.subtypeUnivEquiv Finset.mem_univ), fun j => ?_⟩
  have := hg (σ j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  simpa [Function.leftInverse_invFun hσ j] using this

end GlobalTheory.SplitStd

open GlobalTheory.SplitStd in
theorem GlobalTheory.splitSeq_to_standard : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ) (l : List ((Fin n → R) × (Fin n → R))), l ∈ splitSeq R n → l.length + s ≤ n → ∀ ι : Fin l.length → Fin n, Function.Injective ι → ∃ g : GL (Fin n) R, ∀ j : Fin l.length, (g : Matrix (Fin n) (Fin n) R) *ᵥ (l.get j).1 = Pi.single (ι j) 1 ∧ (l.get j).2 ᵥ* ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Pi.single (ι j) 1 := by
  intro R _ s hs n l hl hlen ι hι
  obtain ⟨g, σ, hσ, hg⟩ := core s hs l.length n (fun j => (l.get j).1) (fun j => (l.get j).2) hl hlen
  obtain ⟨π, hπ⟩ := exists_perm σ ι hσ hι
  refine ⟨pGL π * g, fun j => ⟨?_, ?_⟩⟩
  · rw [Units.val_mul, ← mulVec_mulVec, (hg j).1, pGL_mulVec, hπ]
  · rw [_root_.mul_inv_rev, Units.val_mul, ← vecMul_vecMul, (hg j).2, vecMul_pGL_inv, hπ]

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exists_GL_splitSeq_standard_of_stableRangeLe : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ) (l : List ((Fin n → R) × (Fin n → R))), l ∈ splitSeq R n → l.length + s ≤ n → ∀ ι : Fin l.length → Fin n, Function.Injective ι → ∃ g : GL (Fin n) R, ∀ j : Fin l.length, (g : Matrix (Fin n) (Fin n) R) *ᵥ (l.get j).1 = Pi.single (ι j) 1 ∧ (l.get j).2 ᵥ* ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Pi.single (ι j) 1 := by
  first
  | exact @GlobalTheory.splitSeq_to_standard
  | exact @GlobalTheory.SplitStd.exists_perm
  | exact @GlobalTheory.SplitStd.vecMul_pGL_inv
  | exact @GlobalTheory.SplitStd.pGL_mulVec
  | exact @GlobalTheory.SplitStd.pmat_mul_symm
  | exact @GlobalTheory.SplitStd.core
  | exact @GlobalTheory.SplitStd.dot_conj
  | exact @GlobalTheory.SplitStd.vecMul_extLast
  | exact @GlobalTheory.SplitStd.extLast_mulVec
  | exact @GlobalTheory.SplitStd.single_last_vecMul_extLast
  | exact @GlobalTheory.SplitStd.extLast_mulVec_single_last
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsMemTranslateUnimodularPairOfStableRangeLe
section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory

theorem finsupp_coord_ideal_eq_top {R : Type} [CommRing R] (u : ℕ →₀ R) (g : (ℕ →₀ R) →ₗ[R] R)
    (hg : g u = 1) (K : Ideal R) (hK : ∀ i, u i ∈ K) : K = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← hg]
  rw [show g u = g (u.sum Finsupp.single) by rw [Finsupp.sum_single]]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← Finsupp.smul_single_one, map_smul, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (hK i)

theorem finsupp_exists_form_of_span {R : Type} [CommRing R] (u : ℕ →₀ R)
    (h : Ideal.span (Set.range fun i => u i) = ⊤) : ∃ g : (ℕ →₀ R) →ₗ[R] R, g u = 1 := by
  have h1 : (1 : R) ∈ Ideal.span (Set.range fun i => u i) := by
    rw [h]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h1
  refine ⟨∑ i ∈ c.support, c i • Finsupp.lapply i, ?_⟩
  rw [← hc]
  simp [Finsupp.sum, LinearMap.sum_apply]

private theorem linearMap_apply_mem_span_range_coeffs {R : Type} [CommRing R] (w : ℕ →₀ R)
    (g : (ℕ →₀ R) →ₗ[R] R) : g w ∈ Ideal.span (Set.range fun i => w i) := by
  have e : g w = ∑ i ∈ w.support, w i * g (Finsupp.single i 1) := by
    conv_lhs => rw [← Finsupp.sum_single w]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finsupp.smul_single_one, map_smul, smul_eq_mul]
  rw [e]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem unimodular_partner_aff : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n j : ℕ), s ≤ n →
    n ≤ j → ∀ v : ℕ →₀ R, [v] ∈ uniM R (ℕ →₀ R) → ∃ x ∈ aff R n j, [v, x] ∈ uniM R (ℕ →₀ R) := by
  intro R _ s hs n j hsn hnj v hv
  obtain ⟨f, hf⟩ := hv
  obtain ⟨f0, hf0⟩ : ∃ f0 : (ℕ →₀ R) →ₗ[R] R, f0 v = 1 :=
    ⟨f ⟨0, by simp⟩, by simpa using hf ⟨0, by simp⟩ ⟨0, by simp⟩⟩
  let a : ℕ → R := fun i => f0 (Finsupp.single i 1)
  let φ : (ℕ →₀ R) →ₗ[R] R :=
    f0 - ∑ i ∈ Finset.range n, a i • Finsupp.lapply i - a j • Finsupp.lapply j
  have hφ : ∀ w, φ w = f0 w - ∑ i ∈ Finset.range n, a i * w i - a j * w j := by
    intro w
    simp [φ, LinearMap.sum_apply]
  have hφs : ∀ k c, k < n → φ (Finsupp.single k c) = 0 := by
    intro k c hk
    have h1 : f0 (Finsupp.single k c) = c * a k := by
      rw [← Finsupp.smul_single_one, map_smul, smul_eq_mul]
    rw [hφ, h1, Finset.sum_eq_single k
      (fun b _ hb => by simp [Finsupp.single_apply, Ne.symm hb])
      (fun h => absurd (Finset.mem_range.2 hk) h)]
    simp only [Finsupp.single_eq_same, Finsupp.single_apply, if_neg (show k ≠ j by omega), mul_zero,
      sub_zero]
    ring
  have hφj : φ (Finsupp.single j 1) = 0 := by
    rw [hφ, Finset.sum_eq_zero (fun i hi => by
      have := Finset.mem_range.1 hi
      simp [Finsupp.single_apply, show j ≠ i by omega])]
    simp [a]
  let b' : R := φ v + a j * v j
  let r : Fin (n + 1) → R := fun i => if (i : ℕ) < n then v i else b'
  have hrc : ∀ i : Fin n, r i.castSucc = v i := fun i => by simp [r, i.isLt]
  have hrl : r (Fin.last n) = b' := by simp [r]
  have hr : Unimodular R r := by
    show Ideal.span (Set.range r) = ⊤
    rw [Ideal.eq_top_iff_one]
    have key : (1 : R) = ∑ i : Fin n, a i * r i.castSucc + 1 * r (Fin.last n) := by
      simp only [hrc, hrl, one_mul, b']
      rw [hφ, ← hf0, ← Finset.sum_range (fun i => a i * v i)]
      ring
    rw [key]
    exact Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩))
  obtain ⟨t, ht⟩ := hs n hsn r hr
  have ht' : Ideal.span (Set.range fun i => r i.castSucc + t i * r (Fin.last n)) = ⊤ := ht
  let y : ℕ →₀ R := ∑ i : Fin n, Finsupp.single (i : ℕ) (-(t i * a j))
  have hy0 : ∀ m, n ≤ m → y m = 0 := by
    intro m hm
    simp only [y, Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun i _ => by
      have := i.isLt
      simp [Finsupp.single_apply, show (i : ℕ) ≠ m by omega]
  have hyi : ∀ i : Fin n, y i = -(t i * a j) := by
    intro i
    simp only [y, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, Fin.val_ne_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ i) h
  let x : ℕ →₀ R := Finsupp.single j 1 + y
  have hxj : x j = 1 := by simp [x, hy0 j hnj]
  have hxaff : x ∈ aff R n j := by
    simp only [aff, low, Set.mem_setOf_eq]
    intro m hm
    simp [x, hy0 m hm]
  have hφx : φ x = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [x, map_add (f := _), hφj, zero_add, y, map_sum]
    exact Finset.sum_eq_zero fun i _ => hφs _ _ i.isLt
  let v' : ℕ →₀ R := v - v j • x
  have hv'i : ∀ i : Fin n, v' i = v i + v j * (t i * a j) := by
    intro i
    simp only [v', x, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.add_apply, hyi,
      Finsupp.single_apply, if_neg (show j ≠ (i : ℕ) by have := i.isLt; omega)]
    ring
  have hφv' : φ v' = φ v := by simp [v', hφx]
  have hspan : Ideal.span (Set.range fun i => v' i) = ⊤ := by
    rw [eq_top_iff, ← ht', Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have he : r i.castSucc + t i * r (Fin.last n) = v' i + t i * φ v' := by
      rw [hrc, hrl, hv'i, hφv']
      simp only [b']
      ring
    simp only [he]
    exact Ideal.add_mem _ (Ideal.subset_span ⟨(i : ℕ), rfl⟩)
      (Ideal.mul_mem_left _ _ (linearMap_apply_mem_span_range_coeffs v' φ))
  obtain ⟨h, hh⟩ := finsupp_exists_form_of_span v' hspan
  let f1 : (ℕ →₀ R) →ₗ[R] R := h - h x • Finsupp.lapply j
  let f2 : (ℕ →₀ R) →ₗ[R] R := Finsupp.lapply j - v j • f1
  have hvdec : v = v' + v j • x := by simp [v']
  have hhv : h v = 1 + v j * h x := by
    conv_lhs => rw [hvdec]
    rw [map_add (f := _), map_smul, hh, smul_eq_mul]
  have hf1x : f1 x = 0 := by
    simp only [f1, LinearMap.sub_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul, hxj]
    ring
  have hf1v : f1 v = 1 := by
    simp only [f1, LinearMap.sub_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul, hhv]
    ring
  have hf2x : f2 x = 1 := by
    simp only [f2, LinearMap.sub_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul, hf1x, hxj]
    ring
  have hf2v : f2 v = 0 := by
    simp only [f2, LinearMap.sub_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul, hf1v]
    ring
  refine ⟨x, hxaff, ?_⟩
  simp only [uniM, Set.mem_setOf_eq]
  refine ⟨![f1, f2], ?_⟩
  intro p q
  fin_cases p <;> fin_cases q <;> simp [hf1x, hf1v, hf2x, hf2v]

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exists_mem_translate_unimodular_pair_of_stableRangeLe : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n j : ℕ), s ≤ n → n ≤ j → ∀ v : ℕ →₀ R, [v] ∈ uniM R (ℕ →₀ R) → ∃ x ∈ aff R n j, [v, x] ∈ uniM R (ℕ →₀ R) := by
  first
  | exact @GlobalTheory.unimodular_partner_aff
  | exact @GlobalTheory.finsupp_exists_form_of_span
  | exact @GlobalTheory.finsupp_coord_ideal_eq_top
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsTransvectionPreservingLowAndAff
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.ShearLow

theorem main : ∀ (R : Type) [CommRing R] (n : ℕ) (h : (ℕ →₀ R) →ₗ[R] R) (t : ℕ →₀ R), t ∈ low R n → h t = 0 → ∃ ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R), (∀ x, ψ x = x + h x • t) ∧ (∀ x, ψ x ∈ low R n ↔ x ∈ low R n) ∧ ∀ j x, ψ x ∈ aff R n j ↔ x ∈ aff R n j := by
  intro R _ n h t ht hht
  have key : ∀ x y : ℕ →₀ R, y ∈ low R n → (x + y ∈ low R n ↔ x ∈ low R n) := by
    intro x y hy
    simp only [low, Set.mem_setOf_eq, Finsupp.add_apply] at hy ⊢
    constructor
    · intro hx i hi
      have hxi := hx i hi
      rw [hy i hi, add_zero] at hxi
      exact hxi
    · intro hx i hi
      rw [hx i hi, hy i hi, add_zero]
  have hts : ∀ c : R, c • t ∈ low R n := by
    intro c
    simp only [low, Set.mem_setOf_eq, Finsupp.smul_apply] at ht ⊢
    intro i hi
    rw [ht i hi, smul_zero]
  let ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R) :=
    { toFun := fun x => x + h x • t
      invFun := fun x => x - h x • t
      map_add' := by
        intro x y
        simp only [map_add (f := _), add_smul]
        abel
      map_smul' := by
        intro c x
        simp only [map_smul, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]
      left_inv := by
        intro x
        simp only [map_add (f := _), map_smul, hht, smul_eq_mul, mul_zero, add_zero, add_sub_cancel_right]
      right_inv := by
        intro x
        simp only [map_sub, map_smul, hht, smul_eq_mul, mul_zero, sub_zero, sub_add_cancel] }
  have hψ : ∀ x, ψ x = x + h x • t := fun x => rfl
  refine ⟨ψ, hψ, ?_, ?_⟩
  · intro x
    rw [hψ]
    exact key x _ (hts _)
  · intro j x
    rw [hψ]
    simp only [aff, Set.mem_setOf_eq]
    have e : x + h x • t - (Finsupp.single j 1) = (x - Finsupp.single j 1) + h x • t := by abel
    rw [e]
    exact key _ _ (hts _)

end GlobalTheory.ShearLow

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exists_transvection_preserving_low_and_aff : ∀ (R : Type) [CommRing R] (n : ℕ) (h : (ℕ →₀ R) →ₗ[R] R) (t : ℕ →₀ R), t ∈ low R n → h t = 0 → ∃ ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R), (∀ x, ψ x = x + h x • t) ∧ (∀ x, ψ x ∈ low R n ↔ x ∈ low R n) ∧ ∀ j x, ψ x ∈ aff R n j ↔ x ∈ aff R n j := by
  first
  | exact @GlobalTheory.ShearLow.main
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.InnerAutActsTriviallyGroupHomology
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

def conjActHom {k G : Type} [CommRing k] [Group G] (g : G) (A : Rep k G) :
    A ⟶ Rep.res (MulAut.conj g).toMonoidHom A :=
  Rep.ofHom ⟨A.ρ g, fun h => LinearMap.ext fun a => by
    change A.ρ g (A.ρ h a) = A.ρ (g * h * g⁻¹) (A.ρ g a)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]⟩

theorem conjActHom_hom_apply {k G : Type} [CommRing k] [Group G] (g : G) (A : Rep k G) (a : A) :
    (conjActHom g A).hom a = A.ρ g a := rfl

theorem conj_map_eq_id_zero (k G : Type) [CommRing k] [Group G] (g : G) (A : Rep k G)
    (u : A ⟶ Rep.res (MulAut.conj g).toMonoidHom A) (hu : ∀ a, u.hom a = A.ρ g a) :
    groupHomology.map (MulAut.conj g).toMonoidHom u 0 = 𝟙 _ := by
  rw [← cancel_epi (groupHomology.H0π A), groupHomology.H0π_comp_map, Category.comp_id]
  ext a
  have hv : (groupHomology.H0π A).hom (A.ρ g a) = (groupHomology.H0π A).hom a := by
    rw [← groupHomology.coinvariantsMk_comp_H0Iso_inv]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    congr 1
    exact Representation.Coinvariants.mk_self_apply _ _ _
  rw [← hv, ← hu]
  rfl

theorem conj_map_eq_id : ∀ (k G : Type) [CommRing k] [Group G] (g : G) (n : ℕ) (A : Rep k G)
    (u : A ⟶ Rep.res (MulAut.conj g).toMonoidHom A), (∀ a, u.hom a = A.ρ g a) →
    groupHomology.map (MulAut.conj g).toMonoidHom u n = 𝟙 _ := by
  intro k G _ _ g n
  induction n with
  | zero => exact conj_map_eq_id_zero k G g
  | succ n ih =>
    intro A u hu
    obtain ⟨ι, K, i, e, h, hS⟩ := exists_free_shortExact k G A
    have hP : IsZero (groupHomology (Rep.free k G ι) (n + 1)) :=
      GlobalTheory.T.projective_rep_groupHomology_pos_vanishes k G (Rep.free k G ι) inferInstance n
    have hmono := groupHomology.mono_δ_of_isZero hS n hP
    have hnat := (GlobalTheory.T.groupHomology_longExact_maps_natural_of_res k G G (MulAut.conj g).toMonoidHom _ _ hS hS
      (conjActHom g K) (conjActHom g (Rep.free k G ι)) u
      (fun a => by
        change (Rep.free k G ι).ρ g (i.hom a) = i.hom (K.ρ g a)
        exact (Rep.hom_comm_apply i g a).symm)
      (fun a => by
        change u.hom (e.hom a) = e.hom ((Rep.free k G ι).ρ g a)
        rw [hu]
        exact (Rep.hom_comm_apply e g a).symm) n).1
    rw [ih K (conjActHom g K) (fun _ => rfl), Category.comp_id] at hnat
    rw [← cancel_mono (groupHomology.δ hS (n + 1) n rfl), Category.id_comp]
    exact hnat.symm

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.innerAut_acts_trivially_groupHomology : ∀ (k G : Type) [CommRing k] [Group G] (g : G) (n : ℕ) (A : Rep k G) (u : A ⟶ Rep.res (MulAut.conj g).toMonoidHom A), (∀ a, u.hom a = A.ρ g a) → groupHomology.map (MulAut.conj g).toMonoidHom u n = 𝟙 _ := by
  first
  | exact @GlobalTheory.HomStab.conj_map_eq_id
  | exact @GlobalTheory.HomStab.conj_map_eq_id_zero
  | exact @GlobalTheory.HomStab.conjActHom_hom_apply
end
end

