module

public import Mathlib
public import Formalism.GradedWeylDivisibility.StatementE
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Formalism.HermitianCurvature.StatementB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LowerTriIntegral
section
open MvPolynomial

namespace GlobalTheory.WeylInt

open Formalism.GradedWeylDivisibility

theorem lowerTri_of_interlaced {r n : ℕ} {m : Fin r × Fin n →₀ ℕ} (h : Interlaced m) : LowerTri m := by
  have key : ∀ (k : ℕ) (hk : k < n) (a : Fin r), a.val < k → m (a, ⟨k, hk⟩) = 0 := by
    intro k
    induction k with
    | zero => intro hk a ha; omega
    | succ k ih =>
      intro hk a ha
      have h1 := h ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl a
      have h2 : (∑ b : Fin r with b < a, m (b, ⟨k, by omega⟩)) = 0 := by
        refine Finset.sum_eq_zero fun b hb => ih _ b ?_
        have : b.val < a.val := (Finset.mem_filter.mp hb).2
        omega
      rw [h2] at h1
      have h3 : m (a, ⟨k + 1, hk⟩) ≤ ∑ b : Fin r with b ≤ a, m (b, ⟨k + 1, hk⟩) :=
        Finset.single_le_sum (f := fun b : Fin r => m (b, ⟨k + 1, hk⟩)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩)
      omega
  intro a s has
  exact key s.val s.2 a has

theorem intQ_apply (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n P = MvPolynomial.map (Int.castRingHom ℚ) P := rfl

theorem intQ_bidet {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    intQ r n (bideterminant ℤ sz hsz I) = bideterminant ℚ sz hsz I := by
  rw [intQ_apply]
  simp only [bideterminant, initMinor, map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  ext1 i j
  simp

theorem lowerTriIntegral : Formalism.GradedWeylDivisibility.LowerTriIntegral := by
  intro r n ν
  suffices key : ∀ d : (colLex r n).syn, ∀ f ∈ dualWeyl ℚ r n ν,
      (colLex r n).toSyn ((colLex r n).degree f) = d →
      (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, AddMonoidAlgebra.coeff f e = z) →
      ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, f = intQ r n Q' by
    intro f hf hint
    exact key _ f hf rfl hint
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
    intro f hf hd hz
    by_cases hf0 : f = 0
    · exact ⟨0, by rw [hf0, map_zero]⟩
    set m := (colLex r n).degree f with hm
    have hint : Interlaced m := leadInterlaced ℚ r n ν f hf hf0
    have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t :=
      colSums ℚ r n ν f hf m (((colLex r n).degree_mem_support_iff f).mpr hf0)
    obtain ⟨K, sz, hsz, I, hshape, hmono, hexp⟩ := sSYTExists r n ν m hcol hint
    obtain ⟨hdeg, hlc⟩ := column_lex_bideterminant ℚ r n K sz hsz I hmono
    have hmem : bideterminant ℚ sz hsz I ∈ dualWeyl ℚ r n ν := by
      have := bidetMem ℚ r n K sz hsz I
      rwa [hshape] at this
    obtain ⟨z, hzm⟩ := hz m (lowerTri_of_interlaced hint)
    have hlcf : (colLex r n).leadingCoeff f = (z : ℚ) := hzm
    set f' := f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I with hf'
    have hf'mem : f' ∈ dualWeyl ℚ r n ν := Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hmem)
    have hb : (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I = intQ r n (z • bideterminant ℤ sz hsz I) := by
      rw [map_smul, intQ_bidet, hlcf, Int.cast_smul_eq_zsmul]
    have hdecomp : f = f' + intQ r n (z • bideterminant ℤ sz hsz I) := by
      rw [hf', ← hb]; abel
    have hQ : ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, f' = intQ r n Q' := by
      by_cases h0 : f' = 0
      · exact ⟨0, by rw [h0, map_zero]⟩
      have hlt := lcassem_sub_lt (colLex r n) (f := f) (g := bideterminant ℚ sz hsz I) (hdeg.trans hexp) hlc h0
      refine ih _ (hd ▸ hlt) f' hf'mem rfl fun e he => ?_
      obtain ⟨w, hw⟩ := hz e he
      refine ⟨w - AddMonoidAlgebra.coeff (z • bideterminant ℤ sz hsz I) e, ?_⟩
      rw [hf', hb, coeff_sub, hw, intQ_apply, coeff_map]
      simp only [Int.cast_sub, eq_intCast]
    obtain ⟨Q', hQ'⟩ := hQ
    exact ⟨Q' + z • bideterminant ℤ sz hsz I, by rw [map_add (f := _), ← hQ']; exact hdecomp⟩

end GlobalTheory.WeylInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LowerTriOfInterlaced
section
open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.FockHighestWeight

variable {r n : ℕ}

def diagExp (r : ℕ) (ν : Fin n → ℕ) : Fin r × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => if v.1.val = v.2.val then ν v.2 else 0

theorem diagExp_apply (ν : Fin n → ℕ) (a : Fin r) (s : Fin n) :
    diagExp r ν (a, s) = if a.val = s.val then ν s else 0 := rfl

theorem weight_rowW (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = ∑ s : Fin n, m (a, s) := by
  rw [Finsupp.weight_eq_sum, Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [rowW, Pi.single_apply]

theorem weight_rowW_diagExp (ν : Fin n → ℕ) :
    Finsupp.weight (rowW r n) (diagExp r ν) = rowNu (r := r) ν := by
  funext a
  rw [weight_rowW]
  simp only [diagExp_apply, rowNu]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e
      exact hb (Fin.ext e.symm)
    · simp
  · refine Finset.sum_eq_zero fun s _ => ?_
    rw [if_neg]
    have := s.2
    omega

theorem eq_diagExp_of_offDiag {ν : Fin n → ℕ} {m : Fin r × Fin n →₀ ℕ}
    (hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t)
    (hoff : ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = 0) : m = diagExp r ν := by
  ext ⟨a, s⟩
  rw [diagExp_apply]
  split_ifs with h
  · rw [← hcol s, Finset.sum_eq_single a]
    · intro b _ hb
      apply hoff
      intro e
      exact hb (Fin.ext (e.trans h.symm))
    · simp
  · exact hoff a s h

theorem lowerTri_of_interlaced {m : Fin r × Fin n →₀ ℕ} (hm : Interlaced m) : LowerTri m := by
  have key : ∀ k : ℕ, ∀ (s : Fin n), s.val = k → ∀ a : Fin r, a.val < s.val → m (a, s) = 0 := by
    intro k
    induction k with
    | zero => intro s hs a ha; omega
    | succ k ih =>
      intro s hs a ha
      have hk : k < n := by have := s.2; omega
      have h := hm ⟨k, hk⟩ s hs a
      have h0 : ∑ b : Fin r with b < a, m (b, (⟨k, hk⟩ : Fin n)) = 0 := by
        refine Finset.sum_eq_zero fun b hb => ?_
        have hb' : b.val < a.val := (Finset.mem_filter.mp hb).2
        exact ih ⟨k, hk⟩ rfl b (by simp only; omega)
      rw [h0] at h
      have h1 : m (a, s) ≤ ∑ b : Fin r with b ≤ a, m (b, s) :=
        Finset.single_le_sum (f := fun b => m (b, s)) (fun _ _ => Nat.zero_le _) (by simp)
      omega
  intro a s h
  exact key s.val s rfl a h

theorem eq_diagExp_of_lowerTri (hn : n ≤ r) {ν : Fin n → ℕ} {m : Fin r × Fin n →₀ ℕ} (hm : LowerTri m)
    (hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t)
    (hrow : Finsupp.weight (rowW r n) m = rowNu (r := r) ν) : m = diagExp r ν := by
  refine eq_diagExp_of_offDiag hcol ?_
  have key : ∀ k : ℕ, ∀ (s : Fin n), s.val = k → ∀ a : Fin r, a.val ≠ s.val → m (a, s) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro s hs a ha
      let a0 : Fin r := ⟨s.val, by have := s.2; omega⟩
      have h1 : ∑ t : Fin n, m (a0, t) = ν s := by
        rw [← weight_rowW, hrow]
        simp [rowNu, a0]
      have h2 : m (a0, s) = ν s := by
        rw [← h1, Finset.sum_eq_single s]
        · intro t _ ht
          have ht' : t.val ≠ s.val := fun e => ht (Fin.ext e)
          rcases lt_or_gt_of_ne ht' with h | h
          · exact ih t.val (by omega) t rfl a0 (Ne.symm ht')
          · exact hm a0 t h
        · simp
      have hne : a ≠ a0 := fun e => ha (by rw [e])
      have h3 : ∑ b ∈ ({a, a0} : Finset (Fin r)), m (b, s) ≤ ∑ b : Fin r, m (b, s) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      rw [Finset.sum_pair hne, hcol s] at h3
      omega
  intro a s h
  exact key s.val s rfl a h

theorem eval_idFrame_eq_coeff {R : Type*} [CommRing R] {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) R}
    (hcol : ∀ m ∈ F.support, ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t) :
    eval (idFrame R r n) F = AddMonoidAlgebra.coeff F (diagExp r ν) := by
  rw [eval_eq', Finset.sum_eq_single (diagExp r ν)]
  · rw [Finset.prod_eq_one, mul_one]
    rintro ⟨a, s⟩ _
    rw [diagExp_apply, idFrame]
    split_ifs <;> simp
  · intro m hm hne
    have : ¬ ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = 0 :=
      fun h => hne (eq_diagExp_of_offDiag (hcol m hm) h)
    push Not at this
    obtain ⟨a, s, h1, h2⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ (a, s)), mul_zero]
    simp [idFrame, h1, h2]
  · intro h
    rw [notMem_support_iff.mp h, zero_mul]

theorem eval_idFrame_hw {R : Type*} [CommRing R] (hn : n ≤ r) (ν : Fin n → ℕ) :
    eval (idFrame R r n) (hw R hn ν) = 1 := by
  rw [hw, map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow, lpMinor, RingHom.map_det]
  have : ∀ (k : ℕ) (h1 : k ≤ r) (h2 : k ≤ n), (eval (idFrame R r n)).mapMatrix
      (Matrix.of fun p q : Fin k => (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin r × Fin n) R)) = 1 := by
    intro k h1 h2
    ext p q
    simp [idFrame, Matrix.one_apply, Fin.ext_iff]
  rw [this, Matrix.det_one, one_pow]

theorem component_eq_smul_hw {R : Type} [CommRing R] [IsDomain R] (hn : n ≤ r) {ν : Fin n → ℕ} (hν : Antitone ν)
    {F : MvPolynomial (Fin r × Fin n) R} (hF : F ∈ dualWeyl R r n ν) :
    weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F = eval (idFrame R r n) F • hw R hn ν := by
  classical
  rw [← sub_eq_zero]
  by_contra hG
  set G := weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F - eval (idFrame R r n) F • hw R hn ν with hGdef
  have hH := hwMem R r n hn ν hν
  have hGm : G ∈ dualWeyl R r n ν :=
    Submodule.sub_mem _ (dualWeylRowGraded R r n ν _ F hF) (Submodule.smul_mem _ _ hH)
  have hGw : G ∈ weightedHomogeneousSubmodule R (rowW r n) (rowNu (r := r) ν) :=
    Submodule.sub_mem _ (weightedHomogeneousComponent_mem _ _ _)
      (Submodule.smul_mem _ _ (hwRowWeight R r n hn ν hν))
  have hd : (colLex r n).degree G ∈ G.support := (MonomialOrder.degree_mem_support_iff G).mpr hG
  have he := eq_diagExp_of_lowerTri hn (lowerTri_of_interlaced (leadInterlaced R r n ν G hGm hG))
    (colSums R r n ν G hGm _ hd) (hGw (mem_support_iff.mp hd))
  rw [he, mem_support_iff] at hd
  apply hd
  rw [hGdef, coeff_sub, coeff_weightedHomogeneousComponent, if_pos (weight_rowW_diagExp ν), coeff_smul,
    ← eval_idFrame_eq_coeff (colSums R r n ν F hF), ← eval_idFrame_eq_coeff (colSums R r n ν _ hH),
    eval_idFrame_hw]
  simp

theorem fockQ_hw : Formalism.GradedWeylDivisibility.FockQHW := by
  classical
  intro r n hn ν hν F hF
  have h := component_eq_smul_hw hn hν hF
  unfold fockQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw' := hwRowWeight ℚ r n hn ν hν (mem_support_iff.mp hm)
  have h2 := congrArg (AddMonoidAlgebra.coeff · m) h
  rw [coeff_weightedHomogeneousComponent, if_pos hw', coeff_smul, smul_eq_mul] at h2
  rw [h2]
  ring

end GlobalTheory.FockHighestWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MuModelProductIsModularFormCoeffSeqLocallyAlgebr
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.ZmChar

theorem ch_mul {M : ℕ} (χ : DirichletCharacter ℂ M) (x y : ℤ) : ch χ (x * y) = ch χ x * ch χ y := by
  simp [ch]

theorem ch_add_dvd {M : ℕ} (χ : DirichletCharacter ℂ M) (K : ℕ) (h : M ∣ K) (x : ℤ) : ch χ (x + K) = ch χ x := by
  obtain ⟨t, rfl⟩ := h
  simp [ch, ZMod.natCast_self]

theorem ch_zero {M : ℕ} [Fact (1 < M)] (χ : DirichletCharacter ℂ M) : ch χ 0 = 0 := by
  simp only [ch, Int.cast_zero]
  exact MulChar.map_nonunit χ not_isUnit_zero

theorem inv_apply_neg_one {M : ℕ} (χ : DirichletCharacter ℂ M) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply]
  have : Ring.inverse (-1 : ZMod M) = -1 := by simpa using Ring.inverse_unit (-1 : (ZMod M)ˣ)
  rw [this]

theorem isUnit_of_coprime {M : ℕ} (d : ℤ) (h : IsCoprime d (M : ℤ)) : IsUnit (d : ZMod M) := by
  obtain ⟨a, b, hab⟩ := h
  have := congrArg (Int.cast : ℤ → ZMod M) hab
  push_cast at this
  simp [ZMod.natCast_self] at this
  exact isUnit_iff_exists_inv.2 ⟨a, by rw [mul_comm]; exact this⟩

theorem mul_inv_unit {M : ℕ} (χ : DirichletCharacter ℂ M) (d : ℤ) (h : IsUnit (d : ZMod M)) : ch χ d * ch χ⁻¹ d = 1 := by
  show χ (d : ZMod M) * χ⁻¹ (d : ZMod M) = 1
  rw [← MulChar.mul_apply, mul_inv_cancel]
  exact MulChar.one_apply h

end GlobalTheory.EisM.ZmChar

namespace GlobalTheory.EisM.ZmChar

theorem cop_dvd {d : ℤ} {A B : ℕ} (h : IsCoprime d (B : ℤ)) (hAB : A ∣ B) : IsCoprime d (A : ℤ) :=
  h.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hAB)

end GlobalTheory.EisM.ZmChar


open GlobalTheory.EisM.ZmChar in
theorem GlobalTheory.zm_char_mf : ∀ (k j N l m : ℕ) (ε : DirichletCharacter ℂ N) (u : ℤ → ℂ) (θ ν : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ (l ^ m)), j + 2 ≤ k → 0 < N → l.Prime → 1 ≤ m → ¬ l ∣ N → (∀ x, u (x + N) = u x) → (∀ d x : ℤ, IsCoprime d N → u (x * d) = ch θ⁻¹ d * u x) → ε = θ⁻¹ * ν → ψ (-1) * θ (-1) = (-1) ^ (k - 1 - j) → ψ (-1) * ν (-1) = (-1) ^ (j + 1) → MF k (N * l ^ (m + 1)) (ch ε) (Zm k l u (ch ν) (fun x y => ch ψ x * ch ψ⁻¹ y * ((y : ℂ) / x) ^ j)) := by
  intro k j N l m ε u θ ν ψ hjk hN hl hm hlN hu hmul hε hpar1 hpar2
  have hl1 : 1 < l ^ m := Nat.one_lt_pow (by omega) hl.one_lt
  haveI : Fact (1 < l ^ m) := ⟨hl1⟩
  have hlm : 0 < l ^ m := by omega
  have hup : ∀ K : ℕ, N ∣ K → ∀ x, u (x + K) = u x := by
    intro K hK x
    obtain ⟨t, rfl⟩ := hK
    have e : ((N * t : ℕ) : ℤ) = (t : ℤ) * N := by push_cast; ring
    rw [e]
    exact (Function.Periodic.nat_mul (show Function.Periodic u (N : ℤ) from hu) t) x
  obtain ⟨c, hE1⟩ := _root_.GlobalTheory.eis_periodic_weights (k - 1 - j) (N * l ^ m) 1 (fun x => u x * ch ψ x) (fun _ => 1)
    (fun d => ch θ⁻¹ d * ch ψ d) (fun _ => 1) (by omega) (by positivity) one_pos (by simp [ch_zero])
    (fun x => by rw [hup _ (dvd_mul_right _ _), ch_add_dvd _ _ (dvd_mul_left _ _)]) (fun _ => rfl)
    (fun d hd => by
      have hdN : IsCoprime d (N : ℤ) := cop_dvd hd (by simp)
      refine ⟨fun x => ?_, fun x => by ring⟩
      rw [hmul d x hdN, ch_mul]
      ring)
    (by simp only [ch, Int.cast_neg, Int.cast_one, mul_one]; rw [inv_apply_neg_one, mul_comm, hpar1])
  obtain ⟨c', hE2⟩ := _root_.GlobalTheory.eis_periodic_weights (j + 1) (l ^ m) N (ch ψ⁻¹) (ch ν) (ch ψ⁻¹) (ch ν) (by omega) hlm hN
    (ch_zero _) (ch_add_dvd _ _ dvd_rfl) (ch_add_dvd _ _ dvd_rfl)
    (fun d _ => ⟨fun x => by rw [ch_mul, mul_comm], fun x => by rw [ch_mul, mul_comm]⟩)
    (by simp only [ch, Int.cast_neg, Int.cast_one]; rw [inv_apply_neg_one, hpar2])
  have hD1 := (_root_.GlobalTheory.depletion_mf (k - 1 - j) (N * l ^ m * 1) l _ _ (by omega) hl
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self l (by omega)) _) _)
    (fun d => by rw [ch_add_dvd _ _ (dvd_mul_of_dvd_left (dvd_mul_right _ _) _),
      ch_add_dvd _ _ (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)]) hE1).2
  have hD2 := (_root_.GlobalTheory.depletion_mf (j + 1) (l ^ m * N) l _ _ (by omega) hl
    (dvd_mul_of_dvd_left (dvd_pow_self l (by omega)) _)
    (fun d => by rw [ch_add_dvd _ _ (dvd_mul_right _ _), ch_add_dvd _ _ (dvd_mul_left _ _)]) hE2).2
  have hD1' := (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.2.1 (N * l ^ (m + 1)) _ ⟨1, by ring⟩ hD1
  have hD2' := (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.2.1 (N * l ^ (m + 1)) _ ⟨1, by ring⟩ hD2
  have P := GlobalTheory.EisM.mul_main.2 _ _ _ _ _ _ _ hD1' hD2'
  rw [_root_.GlobalTheory.zm_eq_mul_dep_eis k l j u (ch ν) (ch ψ) (ch ψ⁻¹) c c' hjk]
  have hk : k - 1 - j + (j + 1) = k := by omega
  rw [hk] at P
  refine (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.1 (ch ε) _ (fun d hd => ?_) P
  have hU := mul_inv_unit ψ d (isUnit_of_coprime d (cop_dvd hd (dvd_mul_of_dvd_right (pow_dvd_pow l (by omega)) _)))
  subst hε
  simp only [ch, MulChar.mul_apply] at hU ⊢
  linear_combination (θ⁻¹ (d : ZMod N) * ν (d : ZMod N)) * hU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OpnFrobCompare
section
open Matrix

noncomputable section

namespace GlobalTheory.SOrb.CCBridge

open Formalism.REAL Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

lemma lin_bound {𝕜 L M : Type*} [RCLike 𝕜] [NormedAddCommGroup L] [NormedSpace 𝕜 L] [FiniteDimensional 𝕜 L]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] (u : L →ₗ[𝕜] M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖u x‖ ≤ C * ‖x‖ :=
  ⟨‖LinearMap.toContinuousLinearMap u‖, norm_nonneg _, (LinearMap.toContinuousLinearMap u).le_opNorm⟩

def opEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv

lemma opn_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : opn g = ‖opEquiv n g‖ := rfl

section Frob

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace

lemma opn_frob_compare (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, opn g ≤ K * ‖g‖ ∧ ‖g‖ ≤ K * opn g := by
  obtain ⟨a, ha, h3⟩ := lin_bound (opEquiv n).toLinearMap
  obtain ⟨b, hb, h4⟩ := lin_bound (opEquiv n).symm.toLinearMap
  refine ⟨1 + a + b, by positivity, fun g => ?_⟩
  have h3 : ‖opEquiv n g‖ ≤ a * ‖g‖ := h3 g
  have h4 : ‖(opEquiv n).symm (opEquiv n g)‖ ≤ b * ‖opEquiv n g‖ := h4 (opEquiv n g)
  rw [LinearEquiv.symm_apply_apply] at h4
  rw [opn_eq]
  have := norm_nonneg g
  have := norm_nonneg (opEquiv n g)
  constructor <;> nlinarith

lemma opn_gN_compare (k r : ℕ) : ∃ K : ℝ, 0 < K ∧ ∀ g : Mat k r, opn g ≤ K * gN g ∧ gN g ≤ K * opn g := by
  obtain ⟨K, hK, h⟩ := opn_frob_compare (2 * r + k + 1)
  exact ⟨K, hK, fun g => by rw [gN_eq_frob]; exact h g⟩

end Frob

lemma rpow_compare {K : ℝ} (hK : 0 < K) (A : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h1 : x ≤ K * y)
    (h2 : y ≤ K * x) : x ^ A ≤ K ^ |A| * y ^ A := by
  rcases le_total 0 A with hA | hA
  · rw [abs_of_nonneg hA, ← Real.mul_rpow hK.le hy.le]
    exact Real.rpow_le_rpow hx.le h1 hA
  · have h3 : y / K ≤ x := by rw [div_le_iff₀ hK]; linarith
    have := Real.rpow_le_rpow_of_nonpos (by positivity) h3 hA
    rw [Real.div_rpow hy.le hK.le] at this
    rw [abs_of_nonpos hA, Real.rpow_neg hK.le]
    calc x ^ A ≤ y ^ A / K ^ A := this
      _ = _ := by ring

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end GlobalTheory.SOrb.CCBridge

namespace GlobalTheory.SOrb

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity GlobalTheory.SOrb.CCBridge

end GlobalTheory.SOrb
end
end

