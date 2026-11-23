module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockInj
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0010
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0008
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0004

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SatBlock
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

section

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r] (D : BlockData N)

def beF (v : BVar N r D.T.t) : MvPolynomial (BVar N r D.T.t) (KK O) :=
  match v with
  | Sum.inl a => X (Sum.inl a)
  | Sum.inr (_, false) => 1
  | Sum.inr (i, true) => X (Sum.inr (i, true))

def giF (v : BVar N r D.T.t) : MvPolynomial (BVar N r D.T.t) (KK O) :=
  match v with
  | Sum.inl a => X (Sum.inl a)
  | Sum.inr (i, false) => X (Sum.inr (i, false))
  | Sum.inr (i, true) => X (Sum.inr (i, true)) - qq (O := O) (r := r) D i

theorem qq_fix (f : BVar N r D.T.t → MvPolynomial (BVar N r D.T.t) (KK O)) (hf : ∀ a, f (Sum.inl a) = X (Sum.inl a))
    (i : Fin (D.T.t + 1)) : aeval f (qq (O := O) (r := r) D i) = qq (O := O) (r := r) D i := by
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp [qq, xiVar, hf]
  · simp [qq, hf]

theorem qq_int (i : Fin (D.T.t + 1)) : qq (O := O) (r := r) D i ∈ IntAlg O (BVar N r D.T.t) := by
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp only [qq, Fin.lastCases_last]
    exact Subalgebra.sum_mem _ fun c _ => (IntAlg O _).mul_mem (X_mem_intAlg O _) (X_mem_intAlg O _)
  · simp only [qq, Fin.lastCases_castSucc]
    exact Subalgebra.sum_mem _ fun c _ => (IntAlg O _).mul_mem (X_mem_intAlg O _) (X_mem_intAlg O _)

theorem gi_be_tau (P : MvPolynomial (BVar N r D.T.t) (KK O)) :
    aeval (giF (O := O) (r := r) D) (aeval (beF (O := O) (r := r) D) (tau D P)) = aeval (beF (O := O) (r := r) D) P := by
  have h : ((aeval (giF (O := O) (r := r) D)).comp ((aeval (beF (O := O) (r := r) D)).comp (tau D))) =
      aeval (beF (O := O) (r := r) D) := by
    apply MvPolynomial.algHom_ext
    rintro (a | ⟨i, _ | _⟩)
    · simp [tau, tauF, beF, giF]
    · simp [tau, tauF, beF, giF]
    · simp only [AlgHom.comp_apply, tau, aeval_X, tauF, map_add (f := _), map_mul, beF, one_mul, giF, map_one]
      rw [qq_fix D (beF D) (fun _ => rfl), qq_fix D (giF D) (fun _ => rfl)]
      ring
  exact DFunLike.congr_fun h P

theorem ppi_be (P : MvPolynomial (BVar N r D.T.t) (KK O)) :
    ppi D (aeval (beF (O := O) (r := r) D) P) = ppi D P := by
  have h : (ppi (O := O) (r := r) D).comp (aeval (beF (O := O) (r := r) D)) = ppi D := by
    apply MvPolynomial.algHom_ext
    rintro (a | ⟨i, _ | _⟩)
    · simp [beF]
    · simp [beF, ppi, piF]
    · simp [beF]
  exact DFunLike.congr_fun h P

theorem ppi_int (q : MvPolynomial (BVar N r D.T.t) O) (e : (Fin (D.T.t + 1) ⊕ Fin r) →₀ ℕ) :
    AddMonoidAlgebra.coeff (ppi (O := O) (r := r) D (map (algebraMap O (KK O)) q)) e ∈ IntAlg O (Fin N × Fin r) := by
  classical
  induction q using MvPolynomial.induction_on generalizing e with
  | C a =>
    rw [map_C]
    have : ppi (O := O) (r := r) D (C (algebraMap O (KK O) a)) = C (C (algebraMap O (KK O) a)) := by
      simp [ppi, MvPolynomial.algebraMap_eq]
    rw [this, coeff_C]
    split_ifs
    · exact ⟨C a, by simp⟩
    · exact (IntAlg O _).zero_mem
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), MvPolynomial.coeff_add]
    exact (IntAlg O _).add_mem (hp e) (hq e)
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_X]
    have hv : ppi (O := O) (r := r) D (X v) = piF D v := by simp [ppi]
    rw [hv]
    rcases v with ⟨a, c⟩ | ⟨i, _ | _⟩
    · refine Fin.lastCases ?_ (fun a' => ?_) a
      · simp only [piF, Fin.lastCases_last]
        rw [coeff_mul_X']
        split_ifs
        · exact hp _
        · exact (IntAlg O _).zero_mem
      · simp only [piF, Fin.lastCases_castSucc]
        rw [mul_comm, coeff_C_mul]
        exact (IntAlg O _).mul_mem (X_mem_intAlg O _) (hp e)
    · simp only [piF, mul_one]
      exact hp e
    · simp only [piF]
      rw [coeff_mul_X']
      split_ifs
      · exact hp _
      · exact (IntAlg O _).zero_mem

theorem sat_block (x : MvPolynomial (BVar N r D.T.t) (KK O))
    (hx : x ∈ Submodule.span (KK O) ((D.SSZ O (r := r) : Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) :
      Set (MvPolynomial (BVar N r D.T.t) (KK O)))) (hi : x ∈ IntPol O (BVar N r D.T.t)) : x ∈ D.SSZ O (r := r) := by
  classical
  rw [span_eq_range] at hx
  obtain ⟨v, rfl⟩ := hx
  have hv := Ltot_apply D v
  set B := ∑ i : ↥(IF (r := r) D), base D i.1.1 i.1.2 (v i : MvPolynomial (Fin N × Fin r) (KK O)) with hB
  have hT : Ltot D v = tau D B := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hv, hB, map_sum]
    exact Finset.sum_congr rfl fun i _ => ell_eq_tau D _ _ _
  have h1 : aeval (beF (O := O) (r := r) D) B ∈ IntAlg O (BVar N r D.T.t) := by
    rw [← gi_be_tau D B, ← hT]
    refine aeval_mem_intAlg O _ ?_ (aeval_mem_intAlg O _ ?_ (intPol_le O hi))
    · rintro (a | ⟨i, _ | _⟩)
      · exact X_mem_intAlg O _
      · exact X_mem_intAlg O _
      · exact (IntAlg O _).sub_mem (X_mem_intAlg O _) (qq_int D i)
    · rintro (a | ⟨i, _ | _⟩)
      · exact X_mem_intAlg O _
      · exact (IntAlg O _).one_mem
      · exact X_mem_intAlg O _
  obtain ⟨q, hq⟩ := h1
  have hq' : map (algebraMap O (KK O)) q = aeval (beF (O := O) (r := r) D) B := hq
  have hint : ∀ i0 : ↥(IF (r := r) D), (v i0 : MvPolynomial (Fin N × Fin r) (KK O)) ∈ IntAlg O (Fin N × Fin r) := by
    intro i0
    have h2 := ppi_int D q (eExp D i0.1.1 i0.1.2)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hq', ppi_be, hB, map_sum] at h2
    simp only [ppi_base] at h2
    rw [coeff_sum, Finset.sum_eq_single i0] at h2
    · rwa [coeff_monomial, if_pos rfl] at h2
    · intro b _ hb
      rw [coeff_monomial, if_neg]
      intro he
      obtain ⟨e1, e2⟩ := eExp_inj D he
      exact hb (Subtype.ext (Sigma.ext e1 (heq_of_eq e2)))
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi' := i.2
  unfold IF at hi'
  rw [Finset.mem_sigma] at hi'
  have hlv := (mem_Lv D _).1 hi'.1
  have hβ := Finset.Nat.mem_antidiagonalTuple.1 hi'.2
  obtain ⟨q0, hq0⟩ := hint i
  unfold BlockData.SSZ
  refine Submodule.subset_span ?_
  simp only [Set.mem_iUnion]
  refine ⟨i.1.1.1, i.1.1.2, hlv, (v i : MvPolynomial (Fin N × Fin r) (KK O)), ⟨(v i).2, ⟨q0, hq0⟩⟩,
    xiMon (KK O) N r D.T.t i.1.2, xiMon_mem D _ _ hβ, ?_⟩
  rw [ell_apply]
  simp only [pre, mul_assoc]

end

theorem satAt : SatAt := fun _ _ _ _ _ _ _ D x hx hi => sat_block D x hx hi

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.WeightWLet
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def OPlusAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → ∀ (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m), Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
    b.oPlus ≤ segAPlus X.TT X.aT j

def wLet (X : Loc) (x : X.TT × Bool) : (X.TT × Bool) × Fin (X.m + 1) → ℕ := fun v => if v.1 = x then 1 else 0

theorem weight_wLet (X : Loc) (x : X.TT × Bool) (μ : (X.TT × Bool) × Fin (X.m + 1) →₀ ℕ) :
    Finsupp.weight (wLet X x) μ = multideg μ x := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype μ (fun v k => k • wLet X x v) (fun _ => zero_smul _ _),
    Fintype.sum_prod_type, Finset.sum_eq_single x]
  · unfold multideg wLet
    simp
  · intro y _ hy
    unfold wLet
    simp [hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem TD_wLet (x : X.TT × Bool) (b : SegBlock (segS X.TT j) X.m)
    (hk : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (ho : b.oPlus ≤ segAPlus X.TT X.aT j) :
    TD C0 CE1 CE2 X j b (wLet X x) =
      (if segNext X.TT j = x.1.val then hhDegs X.TT X.aT X.bT x else 0) +
        ∑ i, (if segPos X.TT j i = x.1.val then hhDegs X.TT X.aT X.bT x else 0) := by
  obtain ⟨t, bb⟩ := x
  have hterm : ∀ i : Fin (segS X.TT j),
      ((∑ c : Fin (X.m + 1), (b.rz i c * wLet X (t, bb) ((topOdd X j i, true), c) +
          b.ry i c * wLet X (t, bb) ((topOdd X j i, false), c))) +
     (X.seg C0 CE1 CE2 j).P X.p i *
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * wLet X (t, bb) ((topOdd X j i, true), 0) +
          b.sg i * wLet X (t, bb) ((topOdd X j i, false), 0) + b.w i * wLet X (t, bb) ((topOdd X j i, true), Fin.succ 0) +
          (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i) *
            wLet X (t, bb) ((topOdd X j i, false), Fin.succ 0)
       else
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * wLet X (t, bb) ((topOdd X j i, true), 0) +
          b.o i * wLet X (t, bb) ((topOdd X j i, true), Fin.succ 0) +
          coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i *
            wLet X (t, bb) ((topOdd X j i, false), Fin.succ 0))) =
      (if segPos X.TT j i = t.val then hhDegs X.TT X.aT X.bT (t, bb) else 0) := by
    intro i
    have hodd := (pos_mem X.TT j i).2
    by_cases h : segPos X.TT j i = t.val
    · have ht : topOdd X j i = t := Subtype.ext h
      subst ht
      rw [if_pos h]
      cases bb
      · have w1 : ∀ c, wLet X (topOdd X j i, false) ((topOdd X j i, true), c) = 0 := fun c => if_neg (by simp)
        have w2 : ∀ c, wLet X (topOdd X j i, false) ((topOdd X j i, false), c) = 1 := fun c => if_pos rfl
        simp only [w1, w2, mul_zero, mul_one, zero_add, add_zero]
        have hd := hk.1.2.2 i
        have hPC : (X.seg C0 CE1 CE2 j).P X.p i * coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i =
            segATop X.TT X.aT j i - ∑ c, b.ry i c := Nat.mul_div_cancel' hd.2
        have hdeg : hhDegs X.TT X.aT X.bT (topOdd X j i, false) = segATop X.TT X.aT j i := by
          show hhDeg X.aT X.bT (segPos X.TT j i) false = X.aT (segPos X.TT j i)
          unfold hhDeg
          simp [hodd]
        have hin : (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
            b.sg i + (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i)
            else coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i) =
            coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i := by
          split_ifs with hs
          · have := (hk.2.2.1 i hs).2.2.1
            omega
          · rfl
        rw [hin, hPC, hdeg]
        have := hd.1
        omega
      · have w1 : ∀ c, wLet X (topOdd X j i, true) ((topOdd X j i, true), c) = 1 := fun c => if_pos rfl
        have w2 : ∀ c, wLet X (topOdd X j i, true) ((topOdd X j i, false), c) = 0 := fun c => if_neg (by simp)
        simp only [w1, w2, mul_zero, mul_one, zero_add, add_zero]
        have hd := hk.1.2.1 i
        have hPA : (X.seg C0 CE1 CE2 j).P X.p i * coarseA X.p (X.seg C0 CE1 CE2 j) b i =
            (X.seg C0 CE1 CE2 j).bTop i - ∑ c, b.rz i c := Nat.mul_div_cancel' hd.2
        have hdeg : hhDegs X.TT X.aT X.bT (topOdd X j i, true) = (X.seg C0 CE1 CE2 j).bTop i := by
          show hhDeg X.aT X.bT (segPos X.TT j i) true = X.bT (segPos X.TT j i)
          unfold hhDeg
          simp [hodd]
        have hin : (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
            coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i + b.w i
            else coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i + b.o i) = coarseA X.p (X.seg C0 CE1 CE2 j) b i := by
          split_ifs with hs
          · have := (hk.2.2.1 i hs).2.1
            omega
          · have := (hk.2.1 i (not_lt.1 hs)).1
            omega
        rw [hin, hPA, hdeg]
        have := hd.1
        omega
    · have w0 : ∀ b' c, wLet X (t, bb) ((topOdd X j i, b'), c) = 0 := fun b' c =>
        if_neg (fun e => h (congrArg (fun z : X.TT × Bool => z.1.val) e))
      rw [if_neg h]
      simp only [w0, mul_zero, add_zero, Finset.sum_const_zero, ite_self]
  have hend : (segAPlus X.TT X.aT j - b.oPlus) * wLet X (t, bb) ((topEnd X j, true), 0) +
      b.oPlus * wLet X (t, bb) ((topEnd X j, true), Fin.succ 0) +
      (X.seg C0 CE1 CE2 j).bPlus * wLet X (t, bb) ((topEnd X j, false), Fin.succ 0) =
      (if segNext X.TT j = t.val then hhDegs X.TT X.aT X.bT (t, bb) else 0) := by
    have hev := (next_mem X.TT j).2
    by_cases h : segNext X.TT j = t.val
    · have ht : topEnd X j = t := Subtype.ext h
      subst ht
      rw [if_pos h]
      cases bb
      · have w1 : ∀ c, wLet X (topEnd X j, false) ((topEnd X j, true), c) = 0 := fun c => if_neg (by simp)
        have w2 : ∀ c, wLet X (topEnd X j, false) ((topEnd X j, false), c) = 1 := fun c => if_pos rfl
        simp only [w1, w2, mul_zero, mul_one, zero_add]
        show X.bT (segNext X.TT j) = hhDeg X.aT X.bT (segNext X.TT j) false
        unfold hhDeg
        simp [hev]
      · have w1 : ∀ c, wLet X (topEnd X j, true) ((topEnd X j, true), c) = 1 := fun c => if_pos rfl
        have w2 : ∀ c, wLet X (topEnd X j, true) ((topEnd X j, false), c) = 0 := fun c => if_neg (by simp)
        simp only [w1, w2, mul_zero, mul_one, add_zero]
        rw [Nat.sub_add_cancel ho]
        show X.aT (segNext X.TT j) = hhDeg X.aT X.bT (segNext X.TT j) true
        unfold hhDeg
        simp [hev]
    · have w0 : ∀ b' c, wLet X (t, bb) ((topEnd X j, b'), c) = 0 := fun b' c =>
        if_neg (fun e => h (congrArg (fun z : X.TT × Bool => z.1.val) e))
      rw [if_neg h]
      simp only [w0, mul_zero, add_zero]
  unfold TD
  rw [Finset.sum_congr rfl fun i _ => hterm i, add_assoc, add_assoc, ← add_assoc ((segAPlus X.TT X.aT j - b.oPlus) * _),
    hend, add_comm]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

