module

public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QaExpEqBidetExp
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCassemLemmas
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0012
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementH

@[expose] public section

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ABridge
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

lemma qa_can_emb {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by
  have := Finset.orderEmbOfFin_unique (s := (canT mu c).1) (canT mu c).2
    (f := fun a : Fin (colH mu c) => Fin.castLE (colH_le mu c) a) (by intro x; simp [canT])
    (Fin.strictMono_castLE _)
  exact (congrFun this a).symm

lemma qa_minor (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) :
    Matrix.det (Matrix.of fun a b : Fin (colH mu c) =>
      genMat R n ((canT mu c).1.orderEmbOfFin (canT mu c).2 a) ((I c).1.orderEmbOfFin (I c).2 b)) =
    rename Prod.swap (initMinor R (qa_row I c) (colH_le mu c)) := by
  conv_rhs => rw [initMinor, AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext a b
  simp [Matrix.transpose_apply, genMat, qa_row, qa_can_emb]

lemma qa_prod_minor (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    ∏ c : ↥(TCols mu), Matrix.det (Matrix.of fun a b : Fin (colH mu c) =>
      genMat R n ((canT mu c).1.orderEmbOfFin (canT mu c).2 a) ((I c).1.orderEmbOfFin (I c).2 b)) =
    rename Prod.swap (qa_P R I) := by
  unfold qa_P
  rw [map_prod]
  exact Finset.prod_congr rfl fun c _ => qa_minor R I c

theorem qa_brkPol_eq {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    brkPol mu I = (genMat ℤ n).det ^ (mu (lastIdx n)).toNat * rename Prod.swap (qa_P ℤ I) := by
  unfold brkPol
  rw [qa_prod_minor]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnInterlacedLowerTri
section
open MvPolynomial

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility
open scoped MonomialOrder

theorem qn_interlaced_lowerTri {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (h : Interlaced m) : LowerTri m := by
  have key : ∀ k : ℕ, ∀ s : Fin n, s.val = k → ∀ a : Fin r, a.val < k → m (a, s) = 0 := by
    intro k
    induction k with
    | zero =>
      intro s _ a ha
      omega
    | succ k ih =>
      intro s hs a ha
      have hl : k < n := by
        have := s.isLt
        omega
      have hI := h ⟨k, hl⟩ s (by simp [hs]) a
      have hR : (∑ b : Fin r with b < a, m (b, (⟨k, hl⟩ : Fin n))) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have hba : b.val < a.val := hb
        exact ih ⟨k, hl⟩ rfl b (by omega)
      rw [hR, add_zero, Nat.le_zero, Finset.sum_eq_zero_iff] at hI
      exact hI a (by simp)
  intro a s has
  exact key s.val s rfl a has

theorem qn_lowerTriIntegral : LowerTriIntegral := by
  classical
  intro r n ν
  haveI := (colLex r n).wellFoundedLT_syn
  obtain ⟨b, hbB, hbdeg⟩ := sSBasis ℤ r n ν
  have hBmem : ∀ i, intQ r n (b i) ∈ dualWeyl ℚ r n ν := by
    intro i
    rw [← span_map_weightBasis_eq_dualWeyl (K := ℚ) hbB]
    apply Submodule.subset_span
    exact ⟨i, by rw [algebraMap_int_eq]; rfl⟩
  suffices H : ∀ s : (colLex r n).syn, ∀ Q : MvPolynomial (Fin r × Fin n) ℚ,
      (colLex r n).toSyn ((colLex r n).degree Q) = s → Q ∈ dualWeyl ℚ r n ν →
      (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, AddMonoidAlgebra.coeff Q e = z) →
      ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, Q = intQ r n Q' by
    intro Q hQ hint
    exact H _ Q rfl hQ hint
  intro s
  induction s using WellFoundedLT.induction with
  | ind s ih =>
    intro Q hs hQ hint
    by_cases hQ0 : Q = 0
    · exact ⟨0, by rw [hQ0, map_zero]⟩
    set m := (colLex r n).degree Q with hm
    have hInt : Interlaced m := leadInterlaced ℚ r n ν Q hQ hQ0
    have hLT : LowerTri m := qn_interlaced_lowerTri m hInt
    have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t := by
      have hhom : IsWeightedHomogeneous (colW r n) Q ν :=
        (mem_weightedHomogeneousSubmodule _ _ _ _).1 (Submodule.mem_inf.1 hQ).1
      have hw : Finsupp.weight (colW r n) m = ν :=
        hhom ((colLex r n).leadingCoeff_ne_zero_iff.2 hQ0)
      intro t
      rw [← hw]
      simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_prod_type, colW, Pi.single_apply]
    let mi : ssIdx r n ν := ⟨m, hInt, hcol⟩
    obtain ⟨hbd, hblc, -⟩ := hbdeg mi
    set B := intQ r n (b mi) with hB
    have hBmap : B = map (Int.castRingHom ℚ) (b mi) := rfl
    have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
    have hBsupp : B.support = (b mi).support := by
      rw [hBmap]
      exact support_map_of_injective _ hinj
    have hBdeg : (colLex r n).degree B = m := by
      have h1 : (colLex r n).degree (b mi) = m := hbd
      rw [← h1]
      unfold MonomialOrder.degree
      rw [hBsupp]
    have hBlc : (colLex r n).leadingCoeff B = 1 := by
      unfold MonomialOrder.leadingCoeff
      rw [hBdeg, hBmap, coeff_map]
      have h1 : (colLex r n).degree (b mi) = m := hbd
      have h2 : (b mi).coeff ((colLex r n).degree (b mi)) = 1 := hblc
      rw [h1] at h2
      rw [h2, map_one]
    obtain ⟨z, hz⟩ := hint m hLT
    have hlcQ : (colLex r n).leadingCoeff Q = (z : ℚ) := hz
    set Q1 := Q - (colLex r n).leadingCoeff Q • B with hQ1
    have hQ1mem : Q1 ∈ dualWeyl ℚ r n ν :=
      Submodule.sub_mem _ hQ (Submodule.smul_mem _ _ (hBmem mi))
    have hQ1int : ∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z' : ℤ, AddMonoidAlgebra.coeff Q1 e = z' := by
      intro e he
      obtain ⟨w, hw⟩ := hint e he
      refine ⟨w - z * (b mi).coeff e, ?_⟩
      rw [hQ1, coeff_sub, coeff_smul, hw, hlcQ, hBmap, coeff_map]
      push_cast
      simp [smul_eq_mul]
    have hfinal : ∀ Q1' : MvPolynomial (Fin r × Fin n) ℤ, Q1 = intQ r n Q1' →
        ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, Q = intQ r n Q' := by
      intro Q1' h
      refine ⟨Q1' + z • b mi, ?_⟩
      rw [map_add (f := _), map_zsmul, ← h, ← hB, hQ1, hlcQ, Int.cast_smul_eq_zsmul]
      abel
    by_cases hQ10 : Q1 = 0
    · exact hfinal 0 (by rw [hQ10, map_zero])
    · have hlt := lcassem_sub_lt (colLex r n) (hBdeg.trans hm) hBlc hQ10
      obtain ⟨Q1', h⟩ := ih _ (by rw [← hs]; exact hlt) Q1 rfl hQ1mem hQ1int
      exact hfinal Q1' h

end Formalism.InvariantFactorPaths.ColumnFamilies
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnPtEmpty
section
open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def qn_pt (n : ℕ) (D : Finset (Fin n × Fin n)) : Fin n × Fin n → MvPolynomial (Fin n × Fin n) ℚ :=
  open Classical in
  fun v => (if v.1 = v.2 then 1 else 0) + (if v ∈ D then X v else 0)

def qn_IntS (n : ℕ) : Subring (MvPolynomial (Fin n × Fin n) ℚ) :=
  (MvPolynomial.map (σ := Fin n × Fin n) (Int.castRingHom ℚ)).range

theorem qn_pt_step (n : ℕ) (D : Finset (Fin n × Fin n)) (a s : Fin n) (hw : (a, s) ∉ D)
    (hs : ∀ c, (s, c) ∉ D) (F : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (qn_pt n (insert (a, s) D)) F =
      Polynomial.eval₂ (aeval (qn_pt n D)).toRingHom (X (a, s)) (rowGen ℚ s a F) := by
  classical
  have h : (aeval (qn_pt n (insert (a, s) D))).toRingHom =
      (Polynomial.eval₂RingHom (aeval (qn_pt n D)).toRingHom (X (a, s))).comp (rowGen ℚ s a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowGen, algebraMap_eq, Polynomial.algebraMap_apply]
    · rintro ⟨b, c⟩
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        rowGen, aeval_X, Polynomial.coe_eval₂RingHom]
      by_cases hb : b = a
      · subst hb
        by_cases hc : c = s
        · subst hc
          simp [qn_pt, hw, hs]
        · have h1 : (b, c) ≠ (b, s) := by simp [hc]
          have h2 : s ≠ c := fun h => hc h.symm
          simp [qn_pt, hs, h1, h2, hc]
      · have h1 : (b, c) ≠ (a, s) := by simp [hb]
        simp [qn_pt, h1, hb]
  exact congrArg (fun φ => φ F) h

theorem qn_pt_empty (n : ℕ) (F : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (qn_pt n ∅) F = C (eval (idFrame ℚ n n) F) := by
  have h : (aeval (qn_pt n ∅)).toRingHom = (C : ℚ →+* MvPolynomial (Fin n × Fin n) ℚ).comp (eval (idFrame ℚ n n)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [algebraMap_eq]
    · rintro ⟨b, c⟩
      by_cases hbc : b = c
      · subst hbc; simp [qn_pt, idFrame]
      · have : b.val ≠ c.val := fun h => hbc (Fin.ext h)
        simp [qn_pt, idFrame, hbc, this]
  exact congrArg (fun φ => φ F) h

theorem qn_X_mem (n : ℕ) (v : Fin n × Fin n) : (X v : MvPolynomial (Fin n × Fin n) ℚ) ∈ qn_IntS n :=
  ⟨X v, by simp⟩

theorem qn_int_pt (n : ℕ) (W : Set (MvPolynomial (Fin n × Fin n) ℚ))
    (hW : ∀ F ∈ W, ∀ (a b : Fin n) (k : ℕ), a ≠ b → rowDiv ℚ a b k F ∈ W)
    (hev : ∀ F ∈ W, ∃ z : ℤ, eval (idFrame ℚ n n) F = z) (D : Finset (Fin n × Fin n)) :
    (∀ x ∈ D, x.2 < x.1) → ∀ F ∈ W, aeval (qn_pt n D) F ∈ qn_IntS n := by
  classical
  induction D using Finset.induction_on_min_value (fun x : Fin n × Fin n => x.1) with
  | empty =>
    intro _ F hF
    obtain ⟨z, hz⟩ := hev F hF
    rw [qn_pt_empty, hz]
    exact ⟨C z, by simp⟩
  | insert w D hw hmin ih =>
    obtain ⟨a, s⟩ := w
    intro hD F hF
    have hsa : s < a := hD (a, s) (Finset.mem_insert_self _ _)
    have hs : ∀ c, (s, c) ∉ D := by
      intro c hc
      have := hmin (s, c) hc
      exact absurd hsa (not_lt.mpr this)
    have ih' := ih (fun x hx => hD x (Finset.mem_insert_of_mem hx))
    rw [qn_pt_step n D a s hw hs, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Subring.sum_mem _ fun k _ => ?_
    exact Subring.mul_mem _ (ih' _ (hW F hF s a k (ne_of_lt hsa))) (Subring.pow_mem _ (qn_X_mem n _) _)

def qn_low (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter fun v => v.2 < v.1

def qn_off {n : ℕ} (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ := m.filter fun v => v.2 < v.1

theorem qn_prod_pt (n : ℕ) (m : Fin n × Fin n →₀ ℕ) :
    (∏ i, qn_pt n (qn_low n) i ^ m i) = open Classical in if LowerTri m then monomial (qn_off m) 1 else 0 := by
  classical
  split_ifs with h
  · rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
    refine Finset.prod_congr rfl fun i _ => ?_
    obtain ⟨a, c⟩ := i
    rcases lt_trichotomy a c with hac | hac | hac
    · have h0 : m (a, c) = 0 := h a c hac
      have h1 : ¬ c < a := not_lt.mpr hac.le
      simp [h0, qn_off, Finsupp.filter_apply, h1]
    · subst hac
      simp [qn_pt, qn_low, qn_off, Finsupp.filter_apply]
    · have h1 : a ≠ c := ne_of_gt hac
      simp [qn_pt, qn_low, qn_off, Finsupp.filter_apply, hac, h1]
  · unfold LowerTri at h
    push Not at h
    obtain ⟨a, c, hac, hne⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ (a, c)) ?_
    have hac' : a < c := hac
    have h1 : ¬ c < a := not_lt.mpr hac'.le
    have h2 : a ≠ c := ne_of_lt hac'
    simp [qn_pt, qn_low, h1, h2, hne]

theorem qn_off_inj {n : ℕ} (ν : Fin n → ℕ) (m e : Fin n × Fin n →₀ ℕ) (hm : LowerTri m) (he : LowerTri e)
    (hmc : ∀ t : Fin n, ∑ a : Fin n, m (a, t) = ν t) (hec : ∀ t : Fin n, ∑ a : Fin n, e (a, t) = ν t)
    (h : qn_off m = qn_off e) : m = e := by
  classical
  have hoff : ∀ a c : Fin n, a ≠ c → m (a, c) = e (a, c) := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h1 | h1
    · rw [hm a c h1, he a c h1]
    · have := DFunLike.congr_fun h (a, c)
      simpa [qn_off, Finsupp.filter_apply, h1] using this
  ext ⟨a, c⟩
  by_cases hac : a = c
  · subst hac
    have h1 := hmc a
    have h2 := hec a
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h1 h2
    have h3 : ∑ x ∈ Finset.univ.erase a, m (x, a) = ∑ x ∈ Finset.univ.erase a, e (x, a) :=
      Finset.sum_congr rfl fun x hx => hoff x a (Finset.ne_of_mem_erase hx)
    omega
  · exact hoff a c hac

theorem qn_coeff_pt (n : ℕ) (ν : Fin n → ℕ) (F : MvPolynomial (Fin n × Fin n) ℚ)
    (hF : IsWeightedHomogeneous (colW n n) F ν) (e : Fin n × Fin n →₀ ℕ) (he : LowerTri e)
    (hec : ∀ t : Fin n, ∑ a : Fin n, e (a, t) = ν t) :
    AddMonoidAlgebra.coeff (aeval (qn_pt n (qn_low n)) F) (qn_off e) = AddMonoidAlgebra.coeff F e := by
  classical
  rw [aeval_def, eval₂_eq', coeff_sum]
  simp only [algebraMap_eq, coeff_C_mul, qn_prod_pt]
  rw [Finset.sum_eq_single e]
  · rw [if_pos he, coeff_monomial, if_pos rfl, mul_one]
  · intro m hm hne
    split_ifs with hl
    · rw [coeff_monomial, if_neg, mul_zero]
      intro hoff
      apply hne
      refine qn_off_inj ν m e hl he ?_ hec hoff
      intro t
      rw [← lhwline_weight_col, hF (mem_support_iff.mp hm)]
    · simp
  · intro h
    rw [notMem_support_iff.mp h, zero_mul]

theorem qn_tri (n : ℕ) (ν : Fin n → ℕ) (W : Set (MvPolynomial (Fin n × Fin n) ℚ))
    (hW : ∀ F ∈ W, ∀ (a b : Fin n) (k : ℕ), a ≠ b → rowDiv ℚ a b k F ∈ W)
    (hev : ∀ F ∈ W, ∃ z : ℤ, eval (idFrame ℚ n n) F = z)
    (hcol : ∀ F ∈ W, IsWeightedHomogeneous (colW n n) F ν) :
    ∀ F ∈ W, ∀ e : Fin n × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, AddMonoidAlgebra.coeff F e = z := by
  classical
  intro F hF e he
  by_cases hec : ∀ t : Fin n, ∑ a : Fin n, e (a, t) = ν t
  · rw [← qn_coeff_pt n ν F (hcol F hF) e he hec]
    obtain ⟨G, hG⟩ := qn_int_pt n W hW hev (qn_low n) (fun x hx => (Finset.mem_filter.mp hx).2) F hF
    refine ⟨AddMonoidAlgebra.coeff G (qn_off e), ?_⟩
    rw [← hG, coeff_map]
    rfl
  · refine ⟨0, ?_⟩
    rw [Int.cast_zero]
    by_contra hne
    apply hec
    intro t
    rw [← lhwline_weight_col, hcol F hF hne]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.TransposeVariables
section
open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def transposeVariables (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) R →ₐ[R] MvPolynomial (Fin n × Fin n) R := rename Prod.swap

theorem transposeVariables_involutive (R : Type*) [CommRing R] (n : ℕ) (f : MvPolynomial (Fin n × Fin n) R) :
    transposeVariables R n (transposeVariables R n f) = f := by
  simp only [transposeVariables, AlgHom.coe_comp, Function.comp_apply, MvPolynomial.rename_rename]
  have h : (Prod.swap ∘ Prod.swap : Fin n × Fin n → Fin n × Fin n) = id := by
    funext x
    simp
  rw [h]
  exact MvPolynomial.rename_id_apply f

theorem qn_T_X (R : Type*) [CommRing R] (n : ℕ) (l a : Fin n) : transposeVariables R n (X (l, a)) = X (a, l) := by
  simp [transposeVariables]

theorem qn_T_map (n : ℕ) (f : MvPolynomial (Fin n × Fin n) ℤ) :
    transposeVariables ℚ n (map (Int.castRingHom ℚ) f) = map (Int.castRingHom ℚ) (transposeVariables ℤ n f) := by
  simp only [transposeVariables]
  exact (MvPolynomial.map_rename _ _ _).symm

def qn_D (n : ℕ) (a b : Fin n) :
    Derivation ℚ (MvPolynomial (Fin n × Fin n) ℚ) (MvPolynomial (Fin n × Fin n) ℚ) :=
  ∑ l : Fin n, (X (l, a) : MvPolynomial (Fin n × Fin n) ℚ) • pderiv (l, b)

theorem qn_D_apply (n : ℕ) (a b : Fin n) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    qn_D n a b f = ∑ l : Fin n, X (l, a) * pderiv (l, b) f := by
  unfold qn_D
  have h := map_sum (Derivation.coeFnAddMonoidHom (R := ℚ) (A := MvPolynomial (Fin n × Fin n) ℚ)
    (M := MvPolynomial (Fin n × Fin n) ℚ)) (fun l : Fin n => (X (l, a) : MvPolynomial (Fin n × Fin n) ℚ) • pderiv (l, b))
    Finset.univ
  have h2 := congrFun h f
  simp only [Finset.sum_apply] at h2
  exact h2.trans (Finset.sum_congr rfl fun l _ => by simp [Derivation.coeFnAddMonoidHom, smul_eq_mul])

theorem qn_E_eq (n : ℕ) (a b : Fin n) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    glOps ℚ n (rowLetters n) Set.univ a b f = qn_D n a b f := by
  rw [qn_D_apply]
  simp [glOps, glAct, rowLetters, LinearMap.sum_apply]

theorem qn_D_X (n : ℕ) (a b : Fin n) (l c : Fin n) :
    qn_D n a b (X (l, c)) = if c = b then X (l, a) else 0 := by
  rw [qn_D_apply]
  simp only [MvPolynomial.pderiv_X, Pi.single_apply, Prod.mk.injEq]
  by_cases hc : c = b
  · subst hc
    simp
  · simp [hc]

theorem qn_deriv_rowGen (n : ℕ) (a b : Fin n) (hab : a ≠ b) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    Polynomial.derivative (rowGen ℚ a b (transposeVariables ℚ n f)) = rowGen ℚ a b (transposeVariables ℚ n (qn_D n a b f)) := by
  have hX : ∀ i : Fin n × Fin n, Polynomial.derivative (rowGen ℚ a b (transposeVariables ℚ n (X i))) =
      rowGen ℚ a b (transposeVariables ℚ n (qn_D n a b (X i))) := by
    rintro ⟨l, c⟩
    rw [qn_D_X, qn_T_X]
    by_cases hc : c = b
    · subst hc
      simp [rowGen, qn_T_X, hab]
    · simp [rowGen, hc]
  induction f using MvPolynomial.induction_on with
  | C r =>
    have hD : qn_D n a b (C r) = 0 := by
      rw [qn_D_apply]
      simp
    rw [hD]
    simp [transposeVariables, rowGen]
  | add p q hp hq =>
    simp only [map_add (f := _), Polynomial.derivative_add, hp, hq]
  | mul_X p i hp =>
    have hL : qn_D n a b (p * X i) = p * qn_D n a b (X i) + X i * qn_D n a b p := by
      rw [Derivation.leibniz]
      simp [smul_eq_mul]
    rw [hL]
    simp only [map_add (f := _), map_mul, Polynomial.derivative_mul, hp, hX i]
    ring

theorem qn_deriv_rowGen_diag (n : ℕ) (a : Fin n) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    (1 + Polynomial.X) * Polynomial.derivative (rowGen ℚ a a (transposeVariables ℚ n f)) =
      rowGen ℚ a a (transposeVariables ℚ n (qn_D n a a f)) := by
  have hX : ∀ i : Fin n × Fin n, (1 + Polynomial.X) * Polynomial.derivative (rowGen ℚ a a (transposeVariables ℚ n (X i))) =
      rowGen ℚ a a (transposeVariables ℚ n (qn_D n a a (X i))) := by
    rintro ⟨l, c⟩
    rw [qn_D_X, qn_T_X]
    by_cases hc : c = a
    · subst hc
      simp [rowGen, qn_T_X]
      ring
    · simp [rowGen, hc]
  induction f using MvPolynomial.induction_on with
  | C r =>
    have hD : qn_D n a a (C r) = 0 := by
      rw [qn_D_apply]
      simp
    rw [hD]
    simp [transposeVariables, rowGen]
  | add p q hp hq =>
    simp only [map_add (f := _), Polynomial.derivative_add, mul_add, hp, hq]
  | mul_X p i hp =>
    have hL : qn_D n a a (p * X i) = p * qn_D n a a (X i) + X i * qn_D n a a p := by
      rw [Derivation.leibniz]
      simp [smul_eq_mul]
    rw [hL, map_mul, map_mul, Polynomial.derivative_mul, mul_add, ← mul_assoc,
      mul_left_comm (1 + Polynomial.X) (rowGen ℚ a a (transposeVariables ℚ n p)), hp, hX i]
    simp only [map_add (f := _), map_mul]
    ring

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

