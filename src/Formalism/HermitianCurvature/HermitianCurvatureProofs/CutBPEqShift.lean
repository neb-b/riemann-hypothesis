module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0281

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section poly

variable {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']

theorem ckOn_of_polyOp {d : ℕ} {A : B.Mat k r → (Wq' →L[ℂ] Wq)} (hA : PolyOp d A) : B.CkOn ⊤ (B.GV k r) A := by
  obtain ⟨n, c, L, hc, hAe⟩ := hA
  have hconst : ∀ i, B.CkOn ⊤ (B.GV k r) (fun _ : B.Mat k r => L i) := fun i _ _ =>
    ⟨Set.univ, fun _ => L i, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hterm : ∀ i, B.CkOn ⊤ (B.GV k r) (fun g => c i g • L i) := fun i =>
    (Formalism.FourierDecayAlt.P.CutBP.pd_good_of_poly (Wp := Wq) (Wq := Wq') (hc i)).1 _ (hconst i)
  have hsum : ∀ s : Finset (Fin n), B.CkOn ⊤ (B.GV k r) (fun g => ∑ i ∈ s, c i g • L i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun g _ _ => by simp⟩
    | insert a s ha ih =>
      have e : (fun g => ∑ i ∈ insert a s, c i g • L i) = (fun g => c a g • L a) + fun g => ∑ i ∈ s, c i g • L i := by
        funext g; simp [Finset.sum_insert ha]
      rw [e]; exact Formalism.FourierDecayAlt.P.B4.ckOn_add (hterm a) ih
  have e : A = fun g => ∑ i, c i g • L i := funext hAe
  rw [e]; exact hsum Finset.univ

end poly

structure ShiftAt {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) where
  up : ℕ → ℝ
  up' : ℕ → ℝ
  um : ℕ → ℝ
  um' : ℕ → ℝ
  Wqp : Type
  Wqm : Type
  [iNp : NormedAddCommGroup Wqp]
  [iIp : InnerProductSpace ℂ Wqp]
  [iFp : FiniteDimensional ℂ Wqp]
  [iNm : NormedAddCommGroup Wqm]
  [iIm : InnerProductSpace ℂ Wqm]
  [iFm : FiniteDimensional ℂ Wqm]
  pp : KB.Pl (shP P up up') Wp Wqp
  pm : KB.Pl (shP P um um') Wp Wqm
  Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)
  Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)
  ApPt : C.LPt → (Wqp →L[ℂ] Wq)
  AmPt : C.LPt → (Wqm →L[ℂ] Wq)
  hzp : pp.T.base.z = p.T.base.z
  hzp' : pp.T.base.z' = p.T.base.z'
  hzm : pm.T.base.z = p.T.base.z
  hzm' : pm.T.base.z' = p.T.base.z'
  polyP : PolyOp n₀ Ap
  polyM : PolyOp n₀ Am
  amaps : AmapsSh p pp pm f Ap Am ApPt AmPt b n₀

attribute [instance] ShiftAt.iNp ShiftAt.iIp ShiftAt.iFp ShiftAt.iNm ShiftAt.iIm ShiftAt.iFm

end

end Formalism.FourierDecayAlt.P.CutBPEq
