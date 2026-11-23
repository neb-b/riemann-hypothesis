module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.SlopeRamifiedInducedPrimeField
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0006
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocElim

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.MetricDisjointSupportOrthogonal
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Forms NumberField Classical

variable {D : D7} {u : D.what₂.Word}

theorem rational_span_map_surjective {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (hP : P ∈ RatSpan D lam) :
    ∃ Q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL, MvPolynomial.map D.what₂.embLL Q = P := by
  unfold RatSpan at hP
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, -, rfl⟩ := hp
    refine ⟨MvPolynomial.C r * ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), ?_⟩
    simp [ten, MvPolynomial.map_map, MvPolynomial.smul_eq_C_mul]
    left
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [MvPolynomial.map_rename, MvPolynomial.map_map,
      show D.what₂.embLL.comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ from RingHom.ext_int _ _]
  | zero => exact ⟨0, map_zero _⟩
  | add p q _ _ hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [map_add (f := _), ha, hb]⟩
  | neg p _ hp =>
    obtain ⟨a, ha⟩ := hp
    exact ⟨-a, by rw [map_neg, ha]⟩

theorem polynomial_rep_of_rational_form (Tf : FormsTied D u) (x : ((D.fm u).lat 0).V) :
    ∃ Pc : (D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL,
      (∀ c, (D.fm u).emb 0 x c = 0 → Pc c = 0) ∧
      ∀ c z, (D.fm u).emb 0 x c z = fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))
        ((Tf.val 0 (Nat.zero_le _)).eY z) := by
  have hr := ((Tf.val 0 (Nat.zero_le _)).rat ((D.fm u).emb 0 x)).1 ⟨x, rfl⟩
  choose P hP hPe using hr.2
  choose Q hQ using fun c => rational_span_map_surjective _ (P c) (hP c)
  refine ⟨fun c => if (D.fm u).emb 0 x c = 0 then 0 else Q c, fun c h => by simp [h], fun c z => ?_⟩
  by_cases h : (D.fm u).emb 0 x c = 0
  · rw [h]
    simp only [h, if_true, map_zero, Pi.zero_apply]
  · simp only [h, if_false, hQ]
    exact hPe c z

theorem norm_form_zero {n : ℕ} (lam : D.what₂.Tau → DomWeight n) : nfAll lam 0 0 = 0 := by
  simp only [nfAll]
  rw [div_eq_zero_iff]
  left
  unfold REAL.fockF
  simp

theorem majAt_swap_eq_conj {V ι : Type} [AddCommGroup V] [Module D.what₂.LL V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι D.what₂.LL V)
    (X : InfinitePlace D.what₂.LL → Matrix ι ι ℂ) (v : InfinitePlace D.what₂.LL) (x y : V) :
    majAt b X v y x = starRingEnd ℂ (majAt b X v x y) := by
  unfold majAt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, Complex.star_def, Complex.conj_conj]
  ring

theorem metric_disjoint_support_orthogonal (Tf : FormsTied D u) : MetricOrthogonalClasses D u := by
  intro v x y hxy
  set s := v.embedding with hs
  have hv : InfinitePlace.mk s = v := InfinitePlace.mk_embedding v
  obtain ⟨C, hC, -, -⟩ := (Tf.val 0 (Nat.zero_le _)).de
  letI := D.host.cmStar
  obtain ⟨o, ho⟩ := exists_isON_of_gram (sigD D : D.host.E →+* D.host.E) (embS D s)
    (fun τ x => D.sp.cm.cmUnram.2.1 (embS D s τ) x) (gramN D 0 (Nat.zero_le _)) C hC
  obtain ⟨Px, hPx0, hPx⟩ := polynomial_rep_of_rational_form Tf x
  obtain ⟨Py, hPy0, hPy⟩ := polynomial_rep_of_rational_form Tf y
  have hay : ∀ (a : D.what₂.LL) c z, (D.fm u).emb 0 (a • y) c z =
      fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL (MvPolynomial.C a * Py c))
        ((Tf.val 0 (Nat.zero_le _)).eY z) := by
    intro a c z
    rw [map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hPy, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul,
      map_smul, Pi.smul_apply]
  have hxay : ∀ (a : D.what₂.LL) c z, (D.fm u).emb 0 (x + a • y) c z =
      fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL (Px c + MvPolynomial.C a * Py c))
        ((Tf.val 0 (Nat.zero_le _)).eY z) := by
    intro a c z
    rw [map_add (f := _), Pi.add_apply, Pi.add_apply, hPx, hay, map_add (f := _), map_add (f := _), Pi.add_apply]
  have key : ∀ a : D.what₂.LL, (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (x + a • y) (x + a • y)).re =
      (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re + (majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (a • y) (a • y)).re := by
    intro a
    have e1 := Tf.norm 0 (Nat.zero_le _) s (x + a • y) _ (hxay a) o ho
    have e2 := Tf.norm 0 (Nat.zero_le _) s x Px hPx o ho
    have e3 := Tf.norm 0 (Nat.zero_le _) s (a • y) _ (hay a) o ho
    rw [hv] at e1 e2 e3
    rw [e1, e2, e3, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rcases hxy c with h | h
    · rw [hPx0 c h]
      simp only [zero_add, map_zero, norm_form_zero, Complex.zero_re, mul_zero]
    · rw [hPy0 c h]
      simp only [mul_zero, add_zero, map_zero, norm_form_zero, Complex.zero_re]
  have a1 : ∀ x x' y : ((D.fm u).lat 0).V, majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v (x + x') y =
      majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y + majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x' y :=
    (isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v).1
  have a2 : ∀ x y y' : ((D.fm u).lat 0).V, majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x (y + y') =
      majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y + majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y' :=
    (isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v).2.1
  have s2 : ∀ (a : D.what₂.LL) (x y : ((D.fm u).lat 0).V), majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x (a • y) =
      s a * majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y :=
    (isSesq_maj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v).2.2.2
  have hre : ∀ a : D.what₂.LL, (s a * majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y).re = 0 := by
    intro a
    have k := key a
    rw [a1, a2, a2, majAt_swap_eq_conj ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x (a • y)] at k
    rw [s2] at k
    simp only [Complex.add_re, Complex.conj_re] at k
    linarith
  obtain ⟨a0, ha0⟩ := exists_im_ne_zero v
  have h1 := hre 1
  have h2 := hre a0
  rw [map_one, one_mul] at h1
  rw [Complex.mul_re, h1, mul_zero, zero_sub, neg_eq_zero] at h2
  apply Complex.ext
  · exact h1
  · rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h ha0
    · exact h

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocInd
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField Classical
open scoped Matrix

theorem substitution_one {ι : Type} {n : ℕ} (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    subP (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) P = P := by
  have h : (subP (fun _ : ι => (1 : Matrix (Fin n) (Fin n) ℂ)) :
      MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro x
    simp [subP, Matrix.one_apply]
  rw [h]
  rfl

theorem substitution_substitution {ι : Type} {n : ℕ} (o o' : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    subP o (subP o' P) = subP (fun τ => o' τ * o τ) P := by
  have h : (subP o).comp (subP o') = subP (fun τ => o' τ * o τ) := by
    apply MvPolynomial.algHom_ext
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, subP, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  show ((subP o).comp (subP o')) P = _
  rw [h]

variable (D : D7)

def BwGLStab (w : D.what₂.places.Pl) : Prop :=
  ∀ (n : ℕ) (ν : DomWeight n) (s : ℤ) (M M' : Matrix (Fin n) (Fin n) ℂ), M * M' = 1 →
    (∀ a b, M a b ∈ bwA_Ow D w) → (∀ a b, M' a b ∈ bwA_Ow D w) →
    ∀ g ∈ delSq ℤ n ν, M.det ^ s • Formalism.GradedWeylDivisibility.rowAct ℂ M (MvPolynomial.map (Int.castRingHom ℂ) g) ∈
      bwA_span (bwA_Ow D w) le_rfl ν.natW

theorem bwG_intSpan_allSubP (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    (N : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (s : D.what₂.Tau → ℤ)
    (hB : ∀ τ, ∀ g ∈ delSq ℤ n (lam τ), (N τ).det ^ s τ • Formalism.GradedWeylDivisibility.rowAct ℂ (N τ) (MvPolynomial.map (Int.castRingHom ℂ) g) ∈
      bwA_span (bwA_Ow D w) le_rfl (lam τ).natW)
    (Q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) (hQ : Q ∈ Formalism.L2.Forms.IntSpan D w lam) :
    MvPolynomial.C (∏ τ, (N τ).det ^ s τ) * subP N Q ∈ Formalism.L2.Forms.IntSpan D w lam := by
  have key : ∀ S : Finset D.what₂.Tau, MvPolynomial.C (∏ τ ∈ S, (N τ).det ^ s τ) *
      subP (fun τ => if τ ∈ S then N τ else 1) Q ∈ Formalism.L2.Forms.IntSpan D w lam := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, map_one, one_mul, Finset.notMem_empty, if_false]
      rw [substitution_one]
      exact hQ
    | insert τ0 S h0 ih =>
      set U : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := Function.update 1 τ0 (N τ0) with hU
      have hU1 : ∀ τ, τ ≠ τ0 → U τ = 1 := fun τ hτ => by rw [hU, Function.update_of_ne hτ]; rfl
      have hUτ : U τ0 = N τ0 := by rw [hU, Function.update_self]
      have hcomp : (fun τ => (if τ ∈ S then N τ else 1) * U τ) = fun τ => if τ ∈ insert τ0 S then N τ else 1 := by
        funext τ
        by_cases hτ : τ = τ0
        · subst hτ
          rw [if_neg h0, if_pos (Finset.mem_insert_self _ _), one_mul, hUτ]
        · rw [hU1 τ hτ, mul_one]
          by_cases hS : τ ∈ S
          · rw [if_pos hS, if_pos (Finset.mem_insert_of_mem hS)]
          · rw [if_neg hS, if_neg (by simp [hτ, hS])]
      have e : MvPolynomial.C (∏ τ ∈ insert τ0 S, (N τ).det ^ s τ) *
          subP (fun τ => if τ ∈ insert τ0 S then N τ else 1) Q =
          (N τ0).det ^ s τ0 • subP U (MvPolynomial.C (∏ τ ∈ S, (N τ).det ^ s τ) *
            subP (fun τ => if τ ∈ S then N τ else 1) Q) := by
        have hC : ∀ x, subP U (MvPolynomial.C x) = MvPolynomial.C x := fun x => by
          rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
        rw [map_mul, substitution_substitution, hcomp, Finset.prod_insert h0, map_mul, MvPolynomial.smul_eq_C_mul, hC, mul_assoc]
      rw [e]
      refine bwA_intSpan_subP D w lam τ0 U hU1 _ ?_ _ ih
      intro g hg
      rw [hUτ]
      exact hB τ0 g hg
  have h := key Finset.univ
  simp only [Finset.mem_univ, if_true] at h
  exact h

theorem local_GL_stabilises_lattice (w : D.what₂.places.Pl) : BwGLStab D w := by
  intro n ν s M M' hMM' hM hM' g hg
  have hM'M : M' * M = 1 := mul_eq_one_comm.1 hMM'
  have hEO : M ∈ bwA_EO (bwA_Ow D w) n := bwE_elim (bwE_loc_Ow D w) M hM ⟨M', hM', hM'M⟩
  have hg' : MvPolynomial.map (Int.castRingHom ℂ) g ∈ bwA_span (bwA_Ow D w) le_rfl ν.natW :=
    Submodule.subset_span ⟨g, hg, rfl⟩
  have hrow := bwA_span_closure (bwA_Ow D w) le_rfl ν.natW M hEO _ hg'
  have hdet : M.det * M'.det = 1 := by rw [← Matrix.det_mul, hMM', Matrix.det_one]
  have hdM : M.det ∈ bwA_Ow D w := bwE_det_mem hM
  have hdM' : M'.det ∈ bwA_Ow D w := bwE_det_mem hM'
  have hds : M.det ^ s ∈ bwA_Ow D w := by
    rcases s with k | k
    · rw [Int.ofNat_eq_natCast, zpow_natCast]
      exact pow_mem hdM k
    · have e : M.det ^ (Int.negSucc k) = M'.det ^ (k + 1) := by
        rw [zpow_negSucc, ← inv_pow]
        congr 1
        exact inv_eq_of_mul_eq_one_right hdet
      rw [e]
      exact pow_mem hdM' _
  have e : M.det ^ s • Formalism.GradedWeylDivisibility.rowAct ℂ M (MvPolynomial.map (Int.castRingHom ℂ) g) =
      (⟨M.det ^ s, hds⟩ : bwA_Ow D w) • Formalism.GradedWeylDivisibility.rowAct ℂ M (MvPolynomial.map (Int.castRingHom ℂ) g) := rfl
  rw [e]
  exact Submodule.smul_mem _ _ hrow

variable (u : D.what₂.Word)

theorem bwG_change_mem (w : D.what₂.places.Pl) (hw : OverT D u w) (τ : D.what₂.Tau) {n : ℕ}
    {L : Set (Fin n → D.host.E)} {B B₂ : GL (Fin n) D.host.E}
    (hB : IsLocBasis (D.mem u).A.T L B) (hB₂ : IsLocBasis (D.mem u).A.T L B₂) (a b : Fin n) :
    atInf (embT D) ((B₂⁻¹ * B : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ a b ∈ bwA_Ow D w := by
  obtain ⟨s, hs, hx⟩ := bwE_col_loc D u w hw hB b
  have h := bwE_locBasis_int D u w hw τ hB₂ _ s hs hx a
  rw [bwE_mulVec_col, ← Units.val_mul] at h
  exact h

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

