module

public import Formalism.LocalToGlobal.Columns.Bundle0031
public import Formalism.LocalToGlobal.Columns.Bundle0018
public import Formalism.LocalToGlobal.Columns.RecChainCUnfPol
public import Formalism.LocalToGlobal.Columns.Bundle0030
public import Mathlib
public import Formalism.LocalToGlobal.Columns.StdBasisFlagSubmoduleOfBlockTriangular
public import Formalism.LocalToGlobal.Columns.ChainOneB
public import Formalism.LocalToGlobal.Columns.Bundle0010

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.DilYStab
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Pairs

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {u : Pr.Word} {m2 j : ℕ}


variable (W cst L u m2 j) in
abbrev PtY (b : L.β j) : Type := (cplAt W sel mu cst L u m2 j b).Pts

@[reducible] def ptYAct (b : L.β j) : MulAction ((chFY W sel mu cst L u m2 j).mem b).G (PtY W cst L u m2 j b) := ((chFY W sel mu cst L u m2 j).mem b).actD

attribute [local instance] ptYAct

def PtY.deco {b : L.β j} (x : PtY W cst L u m2 j b) : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs) := x.1.1.deco

theorem sameOn_QE {d d' : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs)} (h : DecoSet.SameOn (rowSG Pr sel mu) d d') :
    DecoSet.SameOn (QE sel (mu : Chr X.F X.E X.K)) d d' := by
  classical
  exact fun P hP => h P (Finset.mem_union_right _ hP)

theorem cplAt_ys_mv (b : L.β j) (p : ChPt (R := R) sel mu u j) {d' : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs)}
    (h : DecoSet.SameOn (rowSG Pr sel mu) p.deco d') :
    (cplAt W sel mu cst L u m2 j b).ys (p.mv d') = (cplAt W sel mu cst L u m2 j b).ys p := by
  classical
  show (if j = m2 + 1 then ybSet sel mu cst (p.mv d').deco.1.N else {Set.univ}) = if j = m2 + 1 then ybSet sel mu cst p.deco.1.N else {Set.univ}
  rw [DecoF.mv_deco (sameOn_QE h)]
  split_ifs
  · exact ybSet_sameAt sel mu cst h
  · rfl

def PtY.repl {b : L.β j} (x : PtY W cst L u m2 j b) (d' : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs))
    (h : DecoSet.SameOn (rowSG Pr sel mu) x.deco d') : PtY W cst L u m2 j b :=
  ⟨(x.1.1.mv d', x.1.2), by rw [cplAt_ys_mv b x.1.1 h]; exact x.2⟩


open Classical in
def PtY.mv {b : L.β j} (x : PtY W cst L u m2 j b) (d' : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs)) : PtY W cst L u m2 j b :=
  if h : DecoSet.SameOn (rowSG Pr sel mu) x.deco d' then x.repl d' h else x

end Pairs

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.FirstKernelEqLastComponentKernel
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Defs

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (al : ∀ j, j ≤ m2 + 1 → L.β j) (Am : Amb X) (u : Pr.Word)


include hQ in
theorem rcol_rowSG_eq : Pr.vGs = rowSG Pr sel mu := by
  classical
  unfold rowSG uSG
  rw [hQ, Finset.union_empty]

end Defs

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {hQ : QE sel (mu : Chr X.F X.E X.K) = ∅} {m2 : ℕ} {al : ∀ j, j ≤ m2 + 1 → L.β j} {Am : Amb X} {u : Pr.Word}
  (hX : X.Ok) {Gc : ChGlob X R.m} (hL : L.Ok Ch sel mu cst Gc m2) (h0 : Λ 0 = colLev Ch 0)
  (hΛ : ∀ j, j ≤ m2 + 1 → ∀ b : L.β j, L.levG j b = Λ j) (h1 : ∀ j, j ≤ m2 + 1 → ∀ b b' : L.β j, b = b')
  (hE : XiEquiv W Λ Ch sel mu cst Am u (refXi1 Ch sel mu cst L hQ m2 al u))
  {b₁ : L.β (m2 + 1)} {hY : YbHyp (R := R) sel mu cst L u m2 b₁} {P : LevFam X.E X.K R.r Pr.vGs}
  (hK : KerEquivC W Ch sel mu cst L Am u m2 b₁ hY P) (hF : ∀ j, (chF W sel mu L u j).Ok)
  (φ : MfV W Ch u)

end Main

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.FrameEntryAuxiliarySuperdiagonal
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

theorem finset_range_sum_split {A : Type} [AddCommMonoid A] (f : ℕ → A) (c j : ℕ) :
    ∑ i ∈ Finset.range (c + j - 1), f i =
      ∑ i ∈ Finset.range (c - 1), f i + (if 1 ≤ c ∧ 1 ≤ j then f (c - 1) else 0) + ∑ i ∈ Finset.range (j - 1), f (c + i) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  rw [if_pos ⟨hc, hj⟩, show c + j - 1 = (c - 1 + 1) + (j - 1) by omega, Finset.sum_range_add, Finset.sum_range_succ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  omega

section ChrLoc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem frameIndex_of_lt {k₀ c n s : ℕ} (hs : s < k₀) : LocE.fIdx k₀ c n s = s := by
  unfold LocE.fIdx
  rw [if_pos hs]

theorem frameIndex_of_ge {k₀ c n s : ℕ} (h : k₀ + c ≤ s) : LocE.fIdx k₀ c n s = s - c := by
  unfold LocE.fIdx
  rw [if_neg (show ¬ s < k₀ by omega), if_neg (show ¬ s < k₀ + c by omega)]

theorem frameEntry_eq_coord_of_extension {k₀ n c : ℕ} {rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : ∀ x, rr (Loc.inX E n c x) = Loc.inX E n c (g x)) {a b : ℕ} (ha : a < n) (hb : b < n) {p p' : ℕ}
    (hpa : LocE.fIdx k₀ c n p = a) (hpb : LocE.fIdx k₀ c n p' = b) :
    LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap p p' = g (Pi.single ⟨b, hb⟩ 1) ⟨a, ha⟩ := by
  unfold LocE.entB
  rw [hpa, hpb, ciScE_lt _ ha, ciScE_lt _ hb, sub_self, zpow_zero, mul_one, ciEN hb]
  show Loc.atN (rr (Loc.inX E n c (Pi.single ⟨b, hb⟩ 1))) a = _
  rw [hg, ciAtN_inX ha]

theorem reduction_frameEntry_of_extension {k₀ n c : ℕ} {rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : ∀ x, rr (Loc.inX E n c x) = Loc.inX E n c (g x)) {hbar : GL (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (hred : ∀ x ∈ stdAt E n P, redV P (g x) = hbar.1.mulVec (redV P x)) {a b : ℕ} (ha : a < n) (hb : b < n) {p p' : ℕ}
    (hpa : LocE.fIdx k₀ c n p = a) (hpb : LocE.fIdx k₀ c n p' = b) :
    redP P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap p p') = ocbM hbar a b := by
  rw [frameEntry_eq_coord_of_extension hg ha hb hpa hpb, ← ciEntry hred]
  unfold ocbM
  rw [dite_eq_left ⟨ha, hb⟩]

theorem frameEntry_auxiliary_superdiagonal {k₀ n c i : ℕ} (hi : i + 1 < c) (rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + i) (k₀ + i + 1) =
      (q : E) * Loc.atN (rr (Loc.eN E (n + c) (n + i + 1))) (n + i) := by
  have h1 : LocE.fIdx k₀ c n (k₀ + i) = n + i := by
    unfold LocE.fIdx
    rw [if_neg (show ¬ k₀ + i < k₀ by omega), if_pos (show k₀ + i < k₀ + c by omega)]
    omega
  have h2 : LocE.fIdx k₀ c n (k₀ + i + 1) = n + i + 1 := by
    unfold LocE.fIdx
    rw [if_neg (show ¬ k₀ + i + 1 < k₀ by omega), if_pos (show k₀ + i + 1 < k₀ + c by omega)]
    omega
  have h3 : LocE.scE n (fun i => i + 1) (n + i + 1) = (i : ℤ) + 2 := by
    simp only [LocE.scE, if_neg (show ¬ n + i + 1 < n by omega), show n + i + 1 - n = i + 1 by omega]
    push_cast
    ring
  have h4 : LocE.scE n (fun i => i + 1) (n + i) = (i : ℤ) + 1 := by
    simp only [LocE.scE, if_neg (show ¬ n + i < n by omega), show n + i - n = i by omega]
    push_cast
    ring
  unfold LocE.entB
  rw [h1, h2, h3, h4, show (i : ℤ) + 2 - (i + 1) = 1 by ring, zpow_one, mul_comm]
  rfl

theorem frameEntry_last_auxiliary_zero {k₀ n c : ℕ} (hc : 1 ≤ c) (hkn : k₀ < n) {rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : ∀ x, rr (Loc.inX E n c x) = Loc.inX E n c (g x)) :
    LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + (c - 1)) (k₀ + (c - 1) + 1) = 0 := by
  have h1 : LocE.fIdx k₀ c n (k₀ + (c - 1)) = n + (c - 1) := by
    unfold LocE.fIdx
    rw [if_neg (show ¬ k₀ + (c - 1) < k₀ by omega), if_pos (show k₀ + (c - 1) < k₀ + c by omega)]
    omega
  have h2 : LocE.fIdx k₀ c n (k₀ + (c - 1) + 1) = k₀ := by
    rw [frameIndex_of_ge (by omega)]
    omega
  unfold LocE.entB
  rw [h1, h2, ciEN hkn]
  show Loc.atN (rr (Loc.inX E n c (Pi.single ⟨k₀, hkn⟩ 1))) (n + (c - 1)) * _ = 0
  rw [hg]
  unfold Loc.atN
  rw [dite_eq_left (show n + (c - 1) < n + c by omega), ciInX_apply]
  split_ifs with h
  · simp only at h
    omega
  · rw [zero_mul]

theorem columns_fact {k₀ n c : ℕ} (rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    (q : E) * Loc.n1Arg rr = ∑ i ∈ Finset.range (c - 1), LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + i) (k₀ + i + 1) := by
  unfold Loc.n1Arg
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [frameEntry_auxiliary_superdiagonal (by have := Finset.mem_range.1 hi; omega)]

theorem addChar_apply_ne_zero' {A : Type} [AddGroup A] (ψ : AddChar A K) (a : A) : ψ a ≠ 0 := fun h => by
  have h1 := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h1
  exact one_ne_zero h1

theorem lamGBS_eq_addChar_mul_ocbXLam_of_mem_stabL (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ t j n c : ℕ}
    (hk1 : 1 ≤ k₀) (hcj : 1 ≤ c + j) (hn : k₀ + j + j * t ≤ n)
    {rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hrr : rr ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1))
    {g : Sp E n ≃ₗ[E] Sp E n} (hg : ∀ x, rr (Loc.inX E n c x) = Loc.inX E n c (g x))
    {hbar : GL (Fin n) (𝓞 E ⧸ P.asIdeal)} (hred : ∀ x ∈ stdAt E n P, redV P (g x) = hbar.1.mulVec (redV P x)) :
    LocE.lamGBS q ψ₀ χ k₀ (k₀ + c + j) t j n c rr.toLinearMap = ψ₀ (redP P ((q : E) * Loc.n1Arg rr)) * ocbXLam ψ₀ χ k₀ j t hbar := by
  have hq0 := ciQ_ne_zero hu
  have hk : k₀ ≤ n := by omega
  have hint : ∀ p p', p < n + c → p' < n + c →
      IntAt P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap p p') :=
    fun p p' hp hp' => frameEntry_integral_of_stabilizer hq0 hk hp hp' hrr
  have hS : redP P (∑ i ∈ Finset.range (k₀ - 1), LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap i (i + 1) +
      ∑ i ∈ Finset.range (k₀ + c + j - k₀ - 1),
        LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + i) (k₀ + i + 1)) =
      (∑ i ∈ Finset.range (k₀ - 1), ocbM hbar i (i + 1) + ∑ i ∈ Finset.range (j - 1), ocbM hbar (k₀ + i) (k₀ + i + 1)) +
        redP P ((q : E) * Loc.n1Arg rr) := by
    rw [reduction_sum_superdiagonal (show k₀ < k₀ + c + j by omega) _ (fun p hp => hint p (p + 1) (by omega) (by omega)),
      show k₀ + c + j - k₀ - 1 = c + j - 1 by omega, finset_range_sum_split _ c j, columns_fact (k₀ := k₀) rr,
      redP_sum _ _ (fun i hi => hint _ _ (by have := Finset.mem_range.1 hi; omega) (by have := Finset.mem_range.1 hi; omega))]
    have hE : ∀ i ∈ Finset.range (k₀ - 1),
        redP P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap i (i + 1)) = ocbM hbar i (i + 1) := by
      intro i hi
      have := Finset.mem_range.1 hi
      exact reduction_frameEntry_of_extension hg hred (by omega) (by omega) (frameIndex_of_lt (by omega)) (frameIndex_of_lt (by omega))
    have hF : ∀ i ∈ Finset.range (j - 1),
        redP P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + (c + i)) (k₀ + (c + i) + 1)) =
          ocbM hbar (k₀ + i) (k₀ + i + 1) := by
      intro i hi
      have := Finset.mem_range.1 hi
      exact reduction_frameEntry_of_extension hg hred (by omega) (by omega)
        (by rw [frameIndex_of_ge (s := k₀ + (c + i)) (by omega)]; omega)
        (by rw [frameIndex_of_ge (s := k₀ + (c + i) + 1) (by omega)]; omega)
    have hM : (if 1 ≤ c ∧ 1 ≤ j then
        redP P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + (c - 1)) (k₀ + (c - 1) + 1)) else 0) = 0 := by
      split_ifs with h
      · rw [frameEntry_last_auxiliary_zero h.1 (by omega) hg, redP_zero]
      · rfl
    rw [Finset.sum_congr rfl hE, Finset.sum_congr rfl hF, hM]
    abel
  have hBl : ∀ i ∈ Finset.range j, LocE.unitV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t =>
        LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + c + j + i * t + s.1) (k₀ + c + j + i * t + s'.1))) =
      ocbChiK (χ i) (Matrix.det (Matrix.of fun s s' : Fin t => ocbM hbar (k₀ + j + i * t + s.1) (k₀ + j + i * t + s'.1))) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hjt : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right t hi'
    rw [Nat.succ_mul] at hjt
    have hbd : ∀ u : Fin t, k₀ + j + i * t + u.1 < n := fun u => by have := u.2; omega
    show ocbChiK (χ i) (redP P _) = _
    rw [reduction_det_eq_det_reduction _ fun s s' => hint _ _ (by have := hbd s; omega) (by have := hbd s'; omega)]
    congr 1
    congr 1
    ext s s'
    simp only [Matrix.of_apply]
    exact reduction_frameEntry_of_extension hg hred (hbd s) (hbd s')
      (by rw [frameIndex_of_ge (s := k₀ + c + j + i * t + s.1) (by omega)]; omega)
      (by rw [frameIndex_of_ge (s := k₀ + c + j + i * t + s'.1) (by omega)]; omega)
  unfold LocE.lamGBS LocE.lamGvS ocbXLam
  rw [hS, AddChar.map_add_eq_mul, Finset.prod_congr rfl hBl]
  ring

end ChrLoc

section ChrGlob

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem ocbChrGLoc_holds (m2 : ℕ) : OcbChrGLoc Ch sel mu cst m2 := by
  intro hB j hj w hbar g r hr hg hred
  have hw := w.2
  have h2 := R.two_le_m
  have hm := hB.hm
  have hk5 := R.m_add_three_le_k
  have e : j * (R.t + 1) = j * R.t + j := by ring
  have hJ : r ∈ Jat (Pr := Pr) cst.sharp j w.1 := by
    have h := hr.2
    simpa [MulAut.conj_apply] using h
  rw [hB.sharp] at hJ
  have hJ' : r ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
    unfold Jat at hJ
    rwa [if_pos hw, if_pos rfl] at hJ
  have hu := ciQ_notMem_sq hB.hX hB.hPr hw
  have hq0 := ciQ_ne_zero hu
  have hrE : R.r = R.k + cOf R j + j := by
    unfold Ranks.r cOf
    omega
  have hn : R.k + j + j * R.t ≤ R.N j := by
    unfold Ranks.N
    rw [e]
    omega
  have hint : IntAt w.1 ((qOf w.1 : X.E) * Loc.n1Arg r) := by
    rw [columns_fact (k₀ := R.k) r]
    refine ciIntAt_sum _ _ fun i hi => frameEntry_integral_of_stabilizer hq0 (by unfold Ranks.N; omega) ?_ ?_ hJ'.1
    · have := Finset.mem_range.1 hi
      unfold Ranks.N
      omega
    · have := Finset.mem_range.1 hi
      unfold Ranks.N
      omega
  have hpsi := hB.psi0 ⟨w.1, by classical exact Finset.mem_union_left _ w.2⟩ ((qOf w.1 : X.E) * Loc.n1Arg r) hw hint
  rw [mul_div_cancel_left₀ _ hq0] at hpsi
  dsimp only at hpsi
  unfold chiInv lamRow
  dsimp only
  rw [hB.sharp, if_pos hw, if_pos rfl, inv_one, one_mul, mul_one, hpsi, hrE,
    lamGBS_eq_addChar_mul_ocbXLam_of_mem_stabL hu _ _ (by omega) (by unfold cOf; omega) hn hJ'.1 hg hred, ← mul_assoc,
    inv_mul_cancel₀ (addChar_apply_ne_zero' _ _), one_mul]

end ChrGlob

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.OcbLevIsSym
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

def OcbLevIsSym : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (m2 : ℕ), R.m = m2 + 2 → OcbLevIs Ch (colLevSym Ch) m2

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQRec
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QRec

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}
variable (H : Subgroup (GLG (E := E) (n := n) (SG := SG)))

theorem qdf_levUQ_le_UAd (q : QLoc hc n Q Θ) : levUQ hc n ST SG Q H q ≤ UAd hc n := by
  unfold levUQ
  exact inf_le_left.trans (levU_le_UAd ..)

theorem qdf_mk_eq (q : QLoc hc n Q Θ) {x y : UAd hc n} (γ : URat hc n) (k : levUQ hc n ST SG Q H q)
    (e : (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) *
        (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹) :
    (Quotient.mk'' y : Formalism.L2.DIV.Cl hc (1 : Matrix (Fin n) (Fin n) E) (levUQ hc n ST SG Q H q)) = Quotient.mk'' x := by
  have hk : ((k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))⁻¹ ∈ UAd hc n :=
    qdf_levUQ_le_UAd H q (Subgroup.inv_mem _ k.2)
  refine Quotient.sound (DoubleCoset.rel_iff.2 ⟨(Formalism.L2.DIV.ratEl γ : UAd hc n), (Formalism.L2.DIV.ratEl γ).2, ⟨_, hk⟩,
    Subgroup.mem_subgroupOf.2 (Subgroup.inv_mem _ k.2), ?_⟩)
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact e

def qdStab (p : DecoF E n ST SG Q) : MulAction.stabilizer (UF E n × H × Θ.grp) p →* URat hc n :=
  (ratEquiv hc n).symm.toMonoidHom.comp ((MonoidHom.fst (UF E n) (H × Θ.grp)).comp (Subgroup.subtype _))

theorem qdf_ratHom_stab (p : DecoF E n ST SG Q) (a : MulAction.stabilizer (UF E n × H × Θ.grp) p) :
    ratHom hc n (qdStab H p a) = a.1.1 := by
  show ratEquiv hc n ((ratEquiv hc n).symm a.1.1) = a.1.1
  exact MulEquiv.apply_symm_apply _ _

theorem qdf_stab_deco (p : DecoF E n ST SG Q) (a : MulAction.stabilizer (UF E n × H × Θ.grp) p) :
    ((a.1.1, a.1.2.1) : UF E n × H) ∈ MulAction.stabilizer (UF E n × H) p.deco := by
  have h := congrArg DecoF.deco (MulAction.mem_stabilizer_iff.1 a.2)
  exact MulAction.mem_stabilizer_iff.2 h

theorem qdf_stab_fr (p : DecoF E n ST SG Q) (a : MulAction.stabilizer (UF E n × H × Θ.grp) p) (P : Q) :
    (a.1.2.2.1 P).1 = (p.fr P)⁻¹ * a.1.1.1 * p.fr P := by
  have h : (a.1 • p).fr P = p.fr P := congrArg (fun x : DecoF E n ST SG Q => x.fr P) (MulAction.mem_stabilizer_iff.1 a.2)
  change a.1.1.1 * p.fr P * ((a.1.2.2.1 P).1)⁻¹ = p.fr P at h
  rw [mul_inv_eq_iff_eq_mul] at h
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

variable {H}

end QRec

end Formalism.L2.Col
end
end

