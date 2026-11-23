module

public import Formalism.HermitianCurvature.Bundle0008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0053
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.PolyProperOfMx
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.MXMulVecMid

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AnisotropicColumnSums
section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace AnisotropicColumnSums

theorem chat_gen (t n : ℕ) (h : t = n + 1) (A : Type) [Ring A] [Algebra ℂ A] (Eop : Fin t → Fin t → A)
    (P Q : Matrix (Fin t) (Fin t) ℂ) (la : Fin t) (hla : la.val = n) (ι : Fin n → Fin t)
    (hι : ∀ a, (ι a).val = a.val) (hE : GlRel Eop) (hQP : Q * P = 1) (hPQ : P * Q = 1) (u : ℂ) (β : Fin t → ℂ)
    (hβ : ∀ j, j ≠ la → (β ᵥ* P) j = 0) :
    chatA Eop u (fun p => P p la) β = (β ᵥ* P) la • qminor (Econj Eop P Q) ι ι u := by
  subst h
  have e1 : la = Fin.last n := Fin.ext hla
  subst e1
  have e2 : ι = skip1 (Fin.last n) := by
    funext a
    apply Fin.ext
    have := a.isLt
    simp [skip1, hι]
  rw [e2]
  exact first_contraction_adapted A n Eop P Q hE hQP hPQ u β hβ

variable {k r : ℕ}

theorem sum_last {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (w : Fin (2 * r + k + 1) → ℂ) :
    ∑ d, herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) w * v (posL k r (Fin.last r) d) = herm (Hpk k r) v w := by
  have hinj : ∀ c c' : Fin (mdim k r (Fin.last r)), posL k r (Fin.last r) c = posL k r (Fin.last r) c' → c = c' := by
    intro c c' h
    ext
    simp only [posL, Fin.ext_iff] at h
    omega
  have hsurj : ∀ p, Qx2.inV k r (Fin.last r) p → ∃ c, posL k r (Fin.last r) c = p := by
    intro p hp
    simp only [Qx2.inV, Fin.val_last] at hp
    refine ⟨⟨p.val - r, ?_⟩, ?_⟩
    · simp only [mdim, Fin.val_last]
      omega
    · ext
      simp only [posL, Fin.val_last]
      omega
  have hv' : v = ∑ d, v (posL k r (Fin.last r) d) • bvec (posL k r (Fin.last r) d) := by
    ext q
    simp only [Finset.sum_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hq : Qx2.inV k r (Fin.last r) q
    · obtain ⟨d0, rfl⟩ := hsurj q hq
      rw [Fintype.sum_eq_single d0]
      · simp
      · intro d hd
        have hne : posL k r (Fin.last r) d0 ≠ posL k r (Fin.last r) d := fun h => hd (hinj _ _ h).symm
        simp [hne]
    · rw [Finset.sum_eq_zero]
      · apply hv
        simp only [Qx2.inV, Fin.val_last] at hq
        omega
      · intro d _
        have hne : q ≠ posL k r (Fin.last r) d := by
          rintro rfl
          apply hq
          have hd := d.isLt
          simp only [Qx2.inV, posL, mdim, Fin.val_last] at hd ⊢
          omega
        simp [hne]
  conv_rhs => rw [hv']
  unfold herm
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

def bcol (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ)
    (j : Fin (mdim k r (Fin.last r))) : Fin (2 * r + k + 1) → ℂ :=
  if h : j.val < k then Bs ⟨j.val, h⟩ else x

def nrm (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (j : Fin (mdim k r (Fin.last r))) : ℂ :=
  if j.val < k then 1 else (herm (Hpk k r) x x)⁻¹

theorem mdim_last : mdim k r (Fin.last r) = k + 1 := by
  simp [mdim]

theorem bcol_inWb {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x)
    (hB : IsFrameOf k r [x] Bs) (j : Fin (mdim k r (Fin.last r))) : inWb k r (bcol k r x Bs j) := by
  unfold bcol
  split_ifs
  · exact hB.1 _
  · exact hx

theorem herm_bcol_eq_ite {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [x] Bs) (j : Fin (mdim k r (Fin.last r))) :
    herm (Hpk k r) (bcol k r x Bs j) x = if j.val < k then 0 else herm (Hpk k r) x x := by
  unfold bcol
  by_cases h : j.val < k
  · rw [dite_eq_left h, if_pos h]
    exact hB.2.2 _ x (List.mem_singleton_self x)
  · rw [dite_eq_right h, if_neg h]

private theorem herm_eq_star_herm_swap (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  unfold herm
  rw [Matrix.star_dotProduct, Matrix.star_mulVec, Qx2.hpk_h, ← Matrix.dotProduct_mulVec]

theorem gram {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hxx : herm (Hpk k r) x x ≠ 0) (hB : IsFrameOf k r [x] Bs) (j j' : Fin (mdim k r (Fin.last r))) :
    herm (Hpk k r) (bcol k r x Bs j') (bcol k r x Bs j) * nrm k r x j = if j = j' then 1 else 0 := by
  obtain ⟨hBw, hBo, hBx⟩ := hB
  have hx0 : ∀ a, herm (Hpk k r) (Bs a) x = 0 := fun a => hBx a x (List.mem_singleton_self x)
  have hx0' : ∀ a, herm (Hpk k r) x (Bs a) = 0 := fun a => by rw [herm_eq_star_herm_swap, hx0, star_zero]
  have hj : j.val < k + 1 := by
    have := j.isLt
    simp only [mdim, Fin.val_last] at this
    omega
  have hj' : j'.val < k + 1 := by
    have := j'.isLt
    simp only [mdim, Fin.val_last] at this
    omega
  unfold bcol nrm
  by_cases h1 : j.val < k <;> by_cases h2 : j'.val < k
  · rw [dite_eq_left h2, dite_eq_left h1, if_pos h1, mul_one, hBo]
    by_cases hjj : j = j'
    · subst hjj
      simp
    · have hne : ¬ j'.val = j.val := fun h => hjj (Fin.ext h.symm)
      simp [hjj, hne]
  · rw [dite_eq_right h2, dite_eq_left h1, if_pos h1, mul_one, hx0', if_neg]
    rintro rfl
    exact h2 h1
  · rw [dite_eq_left h2, dite_eq_right h1, if_neg h1, hx0, zero_mul, if_neg]
    rintro rfl
    exact h1 h2
  · have hjj : j = j' := by
      ext
      omega
    rw [dite_eq_right h2, dite_eq_right h1, if_neg h1, if_pos hjj, mul_inv_cancel₀ hxx]

end AnisotropicColumnSums

open AnisotropicColumnSums in
theorem qr_chatFrame_of : Formalism.FourierDecayAlt.Qr.FrameMinor → Formalism.FourierDecayAlt.Qr.ChatFrame := by
  intro hFM E _ _ k r D hD x Bs hx hxx hB u φ g hg
  set P : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ :=
    Matrix.of fun c j => bcol k r x Bs j (posL k r (Fin.last r) c) with hP
  set Q : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ :=
    Matrix.of fun j d => herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (bcol k r x Bs j) * nrm k r x j with hQ
  have hQP : Q * P = 1 := by
    ext j j'
    rw [Matrix.mul_apply, Matrix.one_apply, ← gram hxx hB j j', ← sum_last (bcol_inWb hx hB j'), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    simp only [hP, hQ, Matrix.of_apply]
    ring
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  let la : Fin (mdim k r (Fin.last r)) := ⟨k, by rw [mdim_last]; omega⟩
  let ι : Fin k → Fin (mdim k r (Fin.last r)) := fun a => ⟨a.val, by rw [mdim_last]; omega⟩
  have hβP : ∀ j, ((fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) x) ᵥ* P) j =
      if j.val < k then 0 else herm (Hpk k r) x x := by
    intro j
    rw [← herm_bcol_eq_ite hB j, ← sum_last (bcol_inWb hx hB j)]
    rfl
  have hcol : (fun j => x (posL k r (Fin.last r) j)) = fun p => P p la := by
    funext p
    simp [hP, bcol, la]
  have key := chat_gen (mdim k r (Fin.last r)) k mdim_last (Module.End ℂ (SV k r (Fin.last r) D E))
    (EV k r (Fin.last r) D E) P Q la rfl ι (fun _ => rfl) (relation_representation E k r 0 (Fin.last r) D hD).1 hQP hPQ u
    (fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) x) (by
      intro j hj
      rw [hβP, if_pos]
      have h1 : j.val < k + 1 := lt_of_lt_of_eq j.isLt mdim_last
      have : j.val ≠ k := fun e => hj (Fin.ext e)
      omega)
  rw [hcol, key, hβP, if_neg (by simp [la])]
  have hm := hFM E k r k D hD Bs hB.1 P Q ι (fun a b e => Fin.ext (by have e' := congrArg Fin.val e; exact e'))
    (by
      intro a c
      simp [hP, bcol, ι])
    (by
      intro b d
      simp [hQ, bcol, nrm, ι])
    u φ g hg
  rw [← hm]
  rfl

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def GTHyp (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) : Prop :=
  Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' ∧ 2 ≤ P.k ∧ CSec P.k P.r Bs.z Bs.z' Bs.μsec ∧
    Q.IsActualLevel X d.L ∧ Fr.IsStarLevel d.L ∧ d.Rel ∧ ∀ Y : ℂ, X.QQ Y = d.QQ Y

def FnF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
    trR P Bs e (d.L.ζ.1 Φ) = MA.actA P (MA.zA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.ζi.1 Φ) = MA.actA P (MA.ziA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.ζb.1 Φ) = MA.actA P (MA.zbA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.ζbi.1 Φ) = MA.actA P (MA.zbiA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.GG.1 Φ) = MA.actA P (MA.ggA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.GGi.1 Φ) = MA.actA P (MA.ggiA P (MA.DQ P)) (trR P Bs e Φ)

def KapF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
    trR P Bs e ((d.κ f).1 Φ) = MA.actA P (MA.kap P (MA.DQ P) f) (trR P Bs e Φ)

def NabF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
    trR P Bs e (d.L.nab.1 Φ) = MA.actA P (MA.nabA P (MA.DQ P)) (trR P Bs e Φ) ∧
    trR P Bs e (d.L.nabs.1 Φ) = MA.actA P (MA.nabsA P (MA.DQ P)) (trR P Bs e Φ)

def SSF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
    trR P Bs e ((d.SS l).1 Φ) = MA.actA P (MA.SS P (MA.DQ P) l) (trR P Bs e Φ) ∧
    trR P Bs e ((star (d.SS l)).1 Φ) = MA.actA P (star (MA.SS P (MA.DQ P) l)) (trR P Bs e Φ)

end preds

def GTFn : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), FnF P Bs d e

def GTKap : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e ∧ KapF P Bs d e

def GTConn : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∃ e' : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e' ∧ KapF P Bs d e' ∧ NabF P Bs d e'

def GTSS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → NabF P Bs d e →
      ∃ e' : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e' ∧ KapF P Bs d e' ∧ NabF P Bs d e' ∧ SSF P Bs d e'

def GenTransferOfCut : Prop := GTFn → GTKap → GTConn → GTSS → GenTransfer

theorem genTransfer_of_cut : GenTransferOfCut := by
  intro hFn hKap hConn hSS Wp Wq _ _ _ _ _ _ P Bs hpl hk hcs X d hL hS hR hQ
  have hyp : GTHyp P Bs X d := by
    unfold GTHyp
    exact ⟨hpl, hk, hcs, hL, hS, hR, hQ⟩
  obtain ⟨e₀, hf₀, hk₀⟩ := hKap Wp Wq P Bs X d hyp
  obtain ⟨e₁, hf₁, hk₁, hn₁⟩ := hConn Wp Wq P Bs X d hyp e₀ hf₀ hk₀
  obtain ⟨e, hf, hke, hne, hse⟩ := hSS Wp Wq P Bs X d hyp e₁ hf₁ hk₁ hn₁
  refine ⟨e, hf, fun Φ => ?_⟩
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := hFn Wp Wq P Bs X d hyp e Φ
  obtain ⟨b₁, b₂⟩ := hne Φ
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, b₁, b₂, fun f => hke f Φ, fun l hl => (hse l hl Φ).1,
    fun l hl => (hse l hl Φ).2⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddOp
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def BddReal (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (Cb : ℝ)
    (b : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) : Prop :=
  ∃ Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), B.opOrder Θ = 0 ∧ IsAAOp S T v Θ ∧
    CutCoef S T v Θ 0 (Cb * ((S.G.r : ℝ) + 1)) ∧
    ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v ∧
      MA.actA (D.parOf S v) b (trJ S T v e J) = trJ S T v e (B.opApply Θ J)

end defs

def scalSet (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) : Set (MA.A P (MA.DQ P)) :=
  {L.ζi, L.ζbi, L.D * L.Dbi, L.Db * L.Di}

def ssnSet (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) : Set (MA.A P (MA.DQ P)) :=
  (fun i => L.Drb * L.Dri * MA.SS P (MA.DQ P) i) '' Set.Icc 1 (P.k - 1)

def ssnStarSet (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) : Set (MA.A P (MA.DQ P)) :=
  (fun i => star (L.Drb * L.Dri * MA.SS P (MA.DQ P) i)) '' Set.Icc 1 (P.k - 1)

def BddClassOp (cls : ∀ P : M.Par, R.LevelData (MA.A P (MA.DQ P)) P.r → Set (MA.A P (MA.DQ P))) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc Cb : ℝ, K ≤ Cc → K ≤ Cb → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ b ∈ cls (D.parOf S v) L, BddReal S T v e Cb b

def JABddScal : Prop := BddClassOp scalSet

theorem bddSet_cases (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (b : MA.A P (MA.DQ P))
    (hb : b ∈ MA.bddSet P L) :
    b ∈ scalSet P L ∨ b ∈ Set.range (MA.kap P (MA.DQ P)) ∨ b ∈ ssnSet P L ∨ b ∈ ssnStarSet P L := by
  unfold MA.bddSet at hb
  rcases hb with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

def JABddOpQQ : Prop :=
  ∃ Cc Cb : ℝ, 0 ≤ Cb ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ b ∈ MA.bddSet (D.parOf S v) L, ∃ Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), B.opOrder Θ = 0 ∧ IsAAOp S T v Θ ∧
        CutCoef S T v Θ 0 (Cb * ((S.G.r : ℝ) + 1)) ∧
        ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v ∧
          MA.actA (D.parOf S v) b (trJ S T v e J) = trJ S T v e (B.opApply Θ J)

def BddClassOpQQ (cls : ∀ P : M.Par, R.LevelData (MA.A P (MA.DQ P)) P.r → Set (MA.A P (MA.DQ P))) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc Cb : ℝ, K ≤ Cc → K ≤ Cb → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ b ∈ cls (D.parOf S v) L, BddReal S T v e Cb b

theorem bddClassOpQQ_of (cls : ∀ P : M.Par, R.LevelData (MA.A P (MA.DQ P)) P.r → Set (MA.A P (MA.DQ P)))
    (h : BddClassOp cls) : BddClassOpQQ cls := by
  obtain ⟨K, hK, h⟩ := h
  exact ⟨K, hK, fun Cc Cb h1 h2 E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa _ hL =>
    h Cc Cb h1 h2 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hL⟩

def JABddKapQQ : Prop := BddClassOpQQ fun P _ => Set.range (MA.kap P (MA.DQ P))

def JABddSSnQQ : Prop := BddClassOpQQ ssnSet

def JABddSSnStarQQ : Prop := BddClassOpQQ ssnStarSet

theorem jABddOpQQ_of_bddLeaves (h1 : JABddScal) (h2 : JABddKapQQ) (h3 : JABddSSnQQ) (h4 : JABddSSnStarQQ) :
    JABddOpQQ := by
  obtain ⟨K1, hK1, h1⟩ := bddClassOpQQ_of scalSet h1
  obtain ⟨K2, hK2, h2⟩ := h2
  obtain ⟨K3, hK3, h3⟩ := h3
  obtain ⟨K4, hK4, h4⟩ := h4
  set K := max (max K1 K2) (max K3 K4) with hK
  have e1 : K1 ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have e2 : K2 ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have e3 : K3 ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have e4 : K4 ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨K, K, le_trans hK1 e1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b hb
  rcases bddSet_cases _ L b hb with h | h | h | h
  · exact h1 K K e1 e1 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b h
  · exact h2 K K e2 e2 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b h
  · exact h3 K K e3 e3 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b h
  · exact h4 K K e4 e4 E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b h

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatLagrange
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem jdl_pow (d : ℕ) (ν : Fin (d + 1) → ℝ) (hν : Function.Injective ν) (k : ℕ) (hk : k ≤ d) (y : ℂ) :
    y ^ k = ∑ j, lagC ν j y * ((ν j : ℝ) : ℂ) ^ k := by
  classical
  have hinj : Set.InjOn (fun j : Fin (d + 1) => ((ν j : ℝ) : ℂ)) (Finset.univ : Finset (Fin (d + 1))) :=
    fun a _ b _ h => hν (Complex.ofReal_injective h)
  have hdeg : (Polynomial.X ^ k : Polynomial ℂ).degree < (Finset.univ : Finset (Fin (d + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin, Polynomial.degree_X_pow]
    exact_mod_cast Nat.lt_succ_of_le hk
  have hf := Lagrange.eq_interpolate hinj hdeg
  have h := congrArg (Polynomial.eval y) hf
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  congr 1
  unfold lagC Lagrange.basis
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  rw [div_eq_inv_mul]

theorem jdl_interp {R : Type} [Ring R] [Algebra ℂ R] (f : ℂ → R) (d : ℕ)
    (hf : Formalism.FourierDecayAlt.P.MAx3.G.PolyIn (fun s => f (0 + s)) d) (ν : Fin (d + 1) → ℝ) (hν : Function.Injective ν)
    (y : ℂ) : f y = ∑ j, lagC ν j y • f ((ν j : ℝ) : ℂ) := by
  obtain ⟨a, ha⟩ := hf
  have hf' : ∀ s, f s = ∑ k ∈ Finset.range (d + 1), s ^ k • a k := fun s => by simpa using ha s
  have e1 : f y = ∑ k ∈ Finset.range (d + 1), (∑ j, lagC ν j y * ((ν j : ℝ) : ℂ) ^ k) • a k := by
    rw [hf' y]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← jdl_pow d ν hν k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) y]
  rw [e1]
  simp only [hf', Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem hat_lagrange_decay_holds : JDHatLagrange := by
  intro P L ν hν y
  exact ⟨jdl_interp (fun s => L.R0 s) (P.r + 1) (Formalism.FourierDecayAlt.P.MAx3.G.raising_operator_polynomial P L 0) ν hν y,
    jdl_interp (fun s => L.R0v s) (P.r + 1) (Formalism.FourierDecayAlt.P.MAx3.L.raising_variant_polynomial P L 0) ν hν y⟩

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialMapProper
section
theorem Formalism.FourierDecayAlt.P.polynomial_map_proper : Formalism.FourierDecayAlt.C2.PolyProper :=
  PI.PolynomialProperness.polyProper_of_mx PI.PolynomialProperness.mxFacts
end

