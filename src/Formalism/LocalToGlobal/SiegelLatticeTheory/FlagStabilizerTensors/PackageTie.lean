module

public import Mathlib
public import Formalism.HermitianCurvature.StatementPB
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalRingCardinality.Bundle0002

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.PackageTie

open Formalism.MainNotions.S Formalism.MainNotions.S.Draft Formalism.BasicNotions

section HS

variable {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

abbrev HS (Wq Wp : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] : Type :=
  PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)

def hsEmb : (Wq →L[ℂ] Wp) →ₗ[ℂ] HS Wq Wp where
  toFun A := WithLp.toLp 2 (fun i => A (stdOrthonormalBasis ℂ Wq i))
  map_add' A B := by ext i; simp
  map_smul' c A := by ext i; simp

theorem norm_hsEmb_sq (A : Wq →L[ℂ] Wp) : ‖hsEmb A‖ ^ 2 = hsNormSq A := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [hsNormSq, hsInner, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (hsEmb A) i = A (stdOrthonormalBasis ℂ Wq i) := rfl
  rw [h, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl

end HS

section Comparison₂

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {Word Tau : Type} [Fintype Tau] {hc : Word → Tau → HCParam R}
  (s : SData R F E sig Word Tau hc) (u u' : Word)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]

structure RowIn (τ : Type) : Type 1 where
  Rw : Type
  I : Type
  [fI : Fintype I]
  H₁ : Type
  [n₁ : NormedAddCommGroup H₁]
  [i₁ : InnerProductSpace ℂ H₁]
  [c₁ : CompleteSpace H₁]
  vec : τ → H₁
  rowOf : τ → Rw
  io : Rw → I
  GG : I → I → ℂ
  Gam1 : ℝ
  s0 : τ → τ → ℕ
  scal : τ → τ → Prop

attribute [instance] RowIn.fI RowIn.n₁ RowIn.i₁ RowIn.c₁

end Comparison₂

section Kernel

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {Word Tau : Type} [Fintype Tau] {hc : Word → Tau → HCParam R}
  {s : SData R F E sig Word Tau hc} {u u' : Word}
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  {X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁} {e : τ ≃ s.Term u u'} {J : (s.Cu u' →L[ℂ] s.Cu u) →ₗ[ℂ] H}

theorem K_eq_parts (hs : ∀ S : Set τ, Summable (S.indicator X.op)) (hid : X.IdDegenerate) :
    X.K = X.part X.idSet + X.part X.degSet + X.part X.genSet + X.part X.ngSet := by
  have hpt : ∀ t, X.op t = X.idSet.indicator X.op t + X.degSet.indicator X.op t +
      X.genSet.indicator X.op t + X.ngSet.indicator X.op t := by
    intro t
    by_cases h1 : X.isId t
    · have h0 := hid t h1
      simp [Formalism.FourierDecayAlt.PB.Terms.idSet, Formalism.FourierDecayAlt.PB.Terms.degSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Formalism.FourierDecayAlt.PB.Terms.ngSet, Set.indicator, h1, h0]
    · by_cases h2 : X.G t = 0
      · simp [Formalism.FourierDecayAlt.PB.Terms.idSet, Formalism.FourierDecayAlt.PB.Terms.degSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Formalism.FourierDecayAlt.PB.Terms.ngSet, Set.indicator, h1, h2]
      · by_cases h3 : X.gener t
        · simp [Formalism.FourierDecayAlt.PB.Terms.idSet, Formalism.FourierDecayAlt.PB.Terms.degSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Formalism.FourierDecayAlt.PB.Terms.ngSet, Set.indicator, h1, h2, h3]
        · simp [Formalism.FourierDecayAlt.PB.Terms.idSet, Formalism.FourierDecayAlt.PB.Terms.degSet, Formalism.FourierDecayAlt.PB.Terms.genSet, Formalism.FourierDecayAlt.PB.Terms.ngSet, Set.indicator, h1, h2, h3]
  simp only [Formalism.FourierDecayAlt.PB.Terms.K, Formalism.FourierDecayAlt.PB.Terms.part]
  have hsum := (((hs X.idSet).hasSum.add (hs X.degSet).hasSum).add (hs X.genSet).hasSum).add
    (hs X.ngSet).hasSum
  rw [← hsum.tsum_eq]
  exact tsum_congr hpt

theorem K0_eq_K_of_degSet_eq_zero (hs : ∀ S : Set τ, Summable (S.indicator X.op)) (hid : X.IdDegenerate) (hdeg : X.part X.degSet = 0) : X.K0 = X.K := by
  rw [K_eq_parts hs hid, hdeg]
  simp only [Formalism.FourierDecayAlt.PB.Terms.K0]
  abel

end Kernel

section Link

variable (D : D7) (L : SizeData₂ D)

theorem rpow_neg_six {b : ℝ} (hb : 0 ≤ b) : b ^ (-(6 : ℝ)) = (b ^ 6)⁻¹ := by
  rw [Real.rpow_neg hb, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

def SizeTie (u u' : D.what₂.Word) {ι : Type} [Fintype ι] (G : Formalism.FourierDecayAlt.Sz.Glob ι) (de : ℕ → ℝ) (T : ℕ)
    (bb du du' : ℝ) : Prop :=
  bb = L.sc.b ∧ du = (D.duS u : ℝ) ∧ du' = (D.duS u' : ℝ) ∧ (G.size de T du).Dstar = D.what₂.Dstar

end Link

end Formalism.L2.SG.PackageTie
