module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0166
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0165
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0156
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0150

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairL
section
open Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

def SAPairOne : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)), IsAAOp S T v Θ →
      ∀ K ∈ smoothFormsPositiveCone S T v, ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ K ∈ smoothFormsPositiveCone S T v → B.opAdj Θ J ∈ smoothFormsPositiveCone S T v →
        (∀ π, trJ S T v e K π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) →
        (∀ π, trJ S T v e (B.opApply Θ K) π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) ∧
          MA.ipA (D.parOf S v) (trJ S T v e (B.opApply Θ K)) (trJ S T v e J) =
            MA.ipA (D.parOf S v) (trJ S T v e K) (trJ S T v e (B.opAdj Θ J))

def SAZero : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ X ∈ smoothFormsPositiveCone S T v, ∀ y (hy : y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
        (∀ π, ((trJ S T v e X π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) ⟨y, hy⟩ = 0) →
          X (B.gq (T v).base y) = 0

def SALocal : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), IsAAOp S T v Θ → ∀ K ∈ smoothFormsPositiveCone S T v,
      ∀ V : Set (MA.E (D.parOf S v).r), IsOpen V → V ⊆ MA.Qset (D.parOf S v).r (D.parOf S v).TT → (∀ y ∈ V, K (B.gq (T v).base y) = 0) →
        ∀ y ∈ V, B.opApply Θ K (B.gq (T v).base y) = 0

def SAExh : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v, ∀ X ∈ smoothFormsPositiveCone S T v, ∀ Cs : Set (MA.E (D.parOf S v).r), IsCompact Cs → Cs ⊆ MA.Qset (D.parOf S v).r (D.parOf S v).TT →
      ∃ (F : GFn S v) (U : Set (MA.E (D.parOf S v).r)), IsOpen U ∧ Cs ⊆ U ∧ B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧
        HasCompactSupport F ∧ tsupport F ⊆ OmP S T v ∧
        ∀ y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, (y ∈ U → B.JF (T v).base F (B.gq (T v).base y) = X (B.gq (T v).base y)) ∧
          (X (B.gq (T v).base y) = 0 → B.JF (T v).base F (B.gq (T v).base y) = 0)

def SAJCommC : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), IsAAOp S T v Θ →
      ∀ F : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F → HasCompactSupport F → tsupport F ⊆ OmP S T v →
      ∀ (U : Set (MA.E (D.parOf S v).r)) (X : GFn S v), IsOpen U → X ∈ smoothFormsPositiveCone S T v →
        (∀ y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, y ∈ U → X (B.gq (T v).base y) = B.JF (T v).base F (B.gq (T v).base y)) →
        ∀ y ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, y ∈ U →
          B.opApply Θ X (B.gq (T v).base y) = B.JF (T v).base (B.opApply Θ F) (B.gq (T v).base y) ∧
          B.opAdj Θ X (B.gq (T v).base y) = B.JF (T v).base (B.opAdj Θ F) (B.gq (T v).base y)

def CompactSupportClassMembership : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), IsAAOp S T v Θ →
      ∀ F F' : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F → HasCompactSupport F → tsupport F ⊆ OmP S T v →
        B.CkOn ⊤ (B.GV S.G.k S.G.r) F' → HasCompactSupport F' → tsupport F' ⊆ OmP S T v →
        B.InCC (B.AB S.G.k S.G.r) 5 F ∧ B.InCC (B.AB S.G.k S.G.r) 5 F' ∧
          B.InCC (B.AB S.G.k S.G.r) 5 (B.opApply Θ F) ∧ B.InCC (B.AB S.G.k S.G.r) 5 (B.opAdj Θ F') ∧
          B.beta (T v).base (B.opApply Θ F) F' = B.beta (T v).base F (B.opAdj Θ F')

theorem sAPairL_of_one (hF : JAFFStable) (h1 : SAPairOne) : SAPairL := by
  obtain ⟨C1, hF'⟩ := hF
  obtain ⟨C2, h1'⟩ := h1
  refine ⟨max C1 C2, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he Θs hΘs K hK J hJ hKt
  have hB1 : BuiltOW C1 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_left _ _) hB.1, hB.2⟩
  have hB2 : BuiltOW C2 S T f χ ν' m₀ top A₀ := ⟨isBuiltPlace_mono (le_max_right _ _) hB.1, hB.2⟩
  have stab := hF' E Wp Wq S T f χ ν' m₀ top A₀ hB1 v
  have hmem : ∀ Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), (∀ Θ ∈ Θs, IsAAOp S T v Θ) →
      applyL S v Θs K ∈ smoothFormsPositiveCone S T v := by
    intro Θs
    induction Θs with
    | nil => intro _; exact hK
    | cons Θ Θs ih =>
      intro h
      exact (stab Θ (h Θ (by simp)) _ (ih fun Θ' hΘ' => h Θ' (by simp [hΘ']))).1
  have key : ∀ Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), (∀ Θ ∈ Θs, IsAAOp S T v Θ) →
      ∀ J ∈ smoothFormsPositiveCone S T v,
        (∀ π, trJ S T v e (applyL S v Θs K) π ∈ MA.Test (D.parOf S v).r (D.parOf S v).TT) ∧
          MA.ipA (D.parOf S v) (trJ S T v e (applyL S v Θs K)) (trJ S T v e J) =
            MA.ipA (D.parOf S v) (trJ S T v e K) (trJ S T v e (adjL S v Θs J)) := by
    intro Θs
    induction Θs with
    | nil => intro _ J _; exact ⟨hKt, rfl⟩
    | cons Θ Θs ih =>
      intro h J hJ
      have hΘ : IsAAOp S T v Θ := h Θ (by simp)
      have hrest : ∀ Θ' ∈ Θs, IsAAOp S T v Θ' := fun Θ' hΘ' => h Θ' (by simp [hΘ'])
      have hX := hmem Θs hrest
      obtain ⟨ihT, ihE⟩ := ih hrest (B.opAdj Θ J) (stab Θ hΘ J hJ).2
      obtain ⟨hT, hE⟩ := h1' E Wp Wq S T f χ ν' m₀ top A₀ hB2 v e he Θ hΘ (applyL S v Θs K) hX J hJ
        (stab Θ hΘ _ hX).1 (stab Θ hΘ J hJ).2 ihT
      exact ⟨hT, hE.trans ihE⟩
  exact key Θs hΘs J hJ

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOpFundQ
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA MeasureTheory
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open Formalism.FourierDecayAlt.P.MAx2.Adj

noncomputable section

section fund

variable {r : ℕ} {TT : ℝ}

theorem dR_pos {x : E r} (hx : x ∈ Qset r TT) : 0 < dR x := by
  unfold dR
  exact Finset.prod_pos fun l _ => inv_pos.2 (Complex.normSq_pos.2 (hx.1 l))

theorem dR_nonneg (x : E r) : 0 ≤ dR x := by
  unfold dR
  exact Finset.prod_nonneg fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _)

theorem dR_continuousAt {x : E r} (hx : x ∈ Qset r TT) : ContinuousAt (dR (r := r)) x := by
  unfold dR
  refine tendsto_finsetProd _ fun l _ => ?_
  exact ((Complex.continuous_normSq.comp ((continuous_apply l).comp continuous_fst)).continuousAt).inv₀
    (Complex.normSq_pos.2 (hx.1 l)).ne'

def ofAmb (χ : E r → ℝ) (hχ : ContDiff ℝ sm χ) : SmQ r TT :=
  ⟨fun q => ((χ q.1 : ℝ) : ℂ),
    ((Complex.ofRealCLM.contDiff.comp hχ).contDiffOn).congr fun x hx => by simp [MA.ext, hx]⟩

theorem fund0 (h : SmQ r TT) (hh : ∀ V ∈ Test r TT, ip0 h V = 0) : h = 0 := by
  apply S_ext
  intro q0
  show (h : Qp r TT → ℂ) q0 = 0
  by_contra hne
  have hQ : Qset r TT ∈ nhds q0.1 := (Qset_open r TT).mem_nhds q0.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hQ
  let b : ContDiffBump q0.1 := ⟨ε / 3, 2 * ε / 3, by positivity, by linarith⟩
  have hts : tsupport b ⊆ Qset r TT := fun x hx => by
    rw [b.tsupport_eq] at hx
    exact hball (Metric.closedBall_subset_ball (show (2 * ε / 3 : ℝ) < ε by linarith) hx)
  have hbc : ContDiff ℝ sm (fun x => b x) := b.contDiff
  set χQ : SmQ r TT := ofAmb (fun x => b x) hbc with hχQ
  have hextχ : MA.ext (χQ : Qp r TT → ℂ) = fun x => ((b x : ℝ) : ℂ) := by
    funext x
    by_cases hx : x ∈ Qset r TT
    · simp [MA.ext, hx, hχQ, ofAmb]
    · have : b x = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hx (hts h'))
      simp [MA.ext, hx, this]
  have hχT : χQ ∈ Test r TT := by
    refine ⟨?_, ?_⟩
    · rw [hextχ]; exact b.hasCompactSupport.comp_left Complex.ofReal_zero
    · rw [hextχ]; exact (tsupport_comp_subset Complex.ofReal_zero _).trans hts
  have hVT : χQ * h ∈ Test r TT := test_mul_right hχT h
  have h0 := hh _ hVT

  set G : E r → ℝ := fun x => dR x * (b x * ‖MA.ext (h : Qp r TT → ℂ) x‖ ^ 2) with hG
  have hint : ip0 h (χQ * h) = ((∫ x, G x : ℝ) : ℂ) := by
    unfold ip0
    rw [integral_base_measure, ← integral_complex_ofReal]
    congr 1
    funext x
    by_cases hx : x ∈ Qset r TT
    · simp only [MA.ext, hx, dif_pos, hG, hχQ, ofAmb]
      simp only [Subalgebra.coe_mul, Pi.mul_apply, map_mul, Complex.conj_ofReal]
      push_cast
      rw [← Complex.mul_conj']
      ring
    · simp [MA.ext, hx, hG]
  rw [hint] at h0
  have hG0 : (∫ x, G x) = 0 := by exact_mod_cast h0
  have hcont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ Qset r TT
    · have hh' : ContinuousAt (MA.ext (h : Qp r TT → ℂ)) x :=
        ((h.2 : ContDiffOn ℝ sm (MA.ext (h : Qp r TT → ℂ)) (Qset r TT)).continuousOn.continuousAt
          ((Qset_open r TT).mem_nhds hx))
      exact (dR_continuousAt hx).mul (b.continuous.continuousAt.mul (hh'.norm.pow 2))
    · have hx' : x ∉ tsupport b := fun h' => hx (hts h')
      have hev : G =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 hx')] with y hy
        simp [hG, show b y = 0 from hy]
      exact (continuousAt_const).congr hev.symm
  have hcs : HasCompactSupport G := by
    apply HasCompactSupport.intro (isCompact_closedBall q0.1 (2 * ε / 3))
    intro x hx
    have : b x = 0 := by
      by_contra hb
      have hxs : x ∈ Function.support b := Function.mem_support.2 hb
      rw [b.support_eq] at hxs
      exact hx (Metric.ball_subset_closedBall hxs)
    simp [hG, this]
  have hnn : 0 ≤ G := fun x => mul_nonneg (dR_nonneg x) (mul_nonneg b.nonneg (sq_nonneg _))
  have hpos0 : G q0.1 ≠ 0 := by
    have hb1 : b q0.1 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))
    have he : MA.ext (h : Qp r TT → ℂ) q0.1 = (h : Qp r TT → ℂ) q0 := by simp [MA.ext, q0.2]
    simp only [hG, hb1, one_mul, he]
    exact (mul_pos (dR_pos q0.2) (pow_pos (norm_pos_iff.2 hne) 2)).ne'
  have := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := (volume : Measure (E r))) hcs hnn hpos0
  linarith

theorem inner_product_sub_left {f g V : SmQ r TT} (hV : V ∈ Test r TT) : ip0 (f - g) V = ip0 f V - ip0 g V := by
  rw [inner_conj_symm_alt, sub_eq_add_neg, inner_add_right_alt hV, inner_neg_right_alt, map_add (f := _), map_neg, ← inner_conj_symm_alt, ← inner_conj_symm_alt,
    ← sub_eq_add_neg]

end fund

open Classical in
theorem fundamental_quadratic_identity : SAFundQ := by
  intro P u w h
  funext π
  have key : ∀ V ∈ MA.Test P.r P.TT, MA.ip0 (u π - w π) V = 0 := by
    intro V hV
    have hU : ∀ π', (fun π'' => if π'' = π then V else 0) π' ∈ MA.Test P.r P.TT := by
      intro π'
      by_cases hπ : π' = π
      · simp [hπ, hV]
      · simp [hπ, test_zero]
    have h1 := h _ hU
    have hs : ∀ x : M.Ty P → MA.SmQ P.r P.TT,
        MA.ipA P x (fun π'' => if π'' = π then V else 0) = MA.ip0 (x π) V := by
      intro x
      unfold MA.ipA
      rw [Finset.sum_eq_single π (fun b _ hb => by simp [hb, inner_zero_right_alt]) (by simp)]
      simp
    rw [hs, hs] at h1
    rw [inner_product_sub_left hV, h1, sub_self]
  exact sub_eq_zero.1 (fund0 _ key)

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSDistEigen
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.JfS

noncomputable section

def ClassEigenC : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : NumberField.InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    100 ≤ Cc → JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → ∀ v : Fin S.f,
      Q.CkLev S.G.k S.G.r 0 (2 * S.G.r + S.G.k + 1) (Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z')
          (B.JF (T v).base (f v)) ∧
        ∀ (Y : ℝ), ∀ g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z',
          Q.CV S.G.k S.G.r (Y : ℂ) (B.JF (T v).base (f v)) g = ((S.P v Y : ℝ) : ℂ) • B.JF (T v).base (f v) g

theorem class_eigenvalue_constant : ClassEigenC := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hCc hB v
  obtain ⟨_, _, _, hbuilt, _, _, _, _, _, hCk, hk2, hA, _⟩ := hB
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, _, hCC, heig⟩ := hv v
  have hpos : 0 ≤ ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by positivity
  have hA' : 100 * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ A₀ := by
    calc 100 * ((S.G.r : ℝ) + 1) ^ 4 *
          ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3)
        = 100 * (((S.G.r : ℝ) + 1) ^ 4 *
          ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3)) := by ring
      _ ≤ Cc * (((S.G.r : ℝ) + 1) ^ 4 *
          ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3)) :=
          mul_le_mul_of_nonneg_right hCc hpos
      _ = Cc * ((S.G.r : ℝ) + 1) ^ 4 *
          ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by ring
      _ ≤ A₀ := hA
  have hThr : JF.TransportedAlt S.G.k S.G.r A₀ (2 * S.G.r + S.G.k + 1) :=
    Formalism.FourierDecayAlt.P.CutMP.thr_of_budget S.G.k S.G.r (S.Ntop : ℝ) A₀ hk2 (Nat.cast_nonneg _) hA'
  have hW := Formalism.FourierDecayAlt.P.jacquet_derivative_formula S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A₀
    (2 * S.G.r + S.G.k + 1) (f v) hThr (hCC _)
  refine ⟨hW.1, ?_⟩
  intro Y g hg
  have hgG : g ∈ B.GV S.G.k S.G.r := hg.1
  have hCkn : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (B.GV S.G.k S.G.r) (f v) :=
    Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top (hCk v)
  rw [Formalism.FourierDecayAlt.P.casimir_under_jacquet_integral S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A₀
    (2 * S.G.r + S.G.k + 1) (f v) (Y : ℂ) le_rfl hThr (hCC _) _ hg]
  have hint : ∀ᵐ p ∂(T v).base.μSS,
      JF.xiP (T v).base p • Q.CV S.G.k S.G.r (Y : ℂ) (B.rho (T v).base p (f v)) g =
        ((S.P v Y : ℝ) : ℂ) • (JF.xiP (T v).base p • B.rho (T v).base p (f v) g) := by
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS (T v).base] with p hp
    rw [Formalism.FourierDecayAlt.P.capelli_rho_commute S.G.k S.G.r _ _ (T v).base (Y : ℂ) (f v) p hp hCkn _ hgG]
    have hs := Formalism.FourierDecayAlt.P.B7.sgs_mem (T v).base hp hgG
    simp only [B.rho]
    rw [heig Y _ hs, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]
  rw [integral_congr_ae hint, integral_smul]
  rfl

theorem mem_om_of_mem_omP {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : NumberField.InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    {g : B.Mat S.G.k S.G.r} (hgG : g ∈ B.GV S.G.k S.G.r) (hg : g ∈ OmP S T v) :
    g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' := by
  refine ⟨hgG, ?_, hg.1⟩
  intro l hl
  rcases Nat.eq_zero_or_pos l.val with h0 | hpos
  · have hl0 : l = 0 := Fin.ext h0
    subst hl0
    unfold Dmin
    have : IsEmpty (Fin ((0 : Fin (S.G.r + 2)) : ℕ)) := ⟨fun i => absurd i.isLt (by simp)⟩
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  · have := hg.2 ⟨l.val - 1, by omega⟩
    have e : (⟨(l.val - 1) + 1, by omega⟩ : Fin (S.G.r + 2)) = l := Fin.ext (by simp; omega)
    simpa [e] using this

end

end Formalism.FourierDecayAlt.P.CutMP.JfS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.L2BoundAtBuiltPlaceHolds
section
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem inCC_fold (hC : CVInCC) {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (s : ℂ)
    (F : B.Mat k r → E) : ∀ (b : List C.Letter) (m : ℕ),
      B.InCC A (m + (2 * r + k + 1) * b.length) F → B.InCC A m (foldCV k r s b F)
  | [], m, h => by rw [foldCV_nil]; simpa using h
  | x :: b, m, h => by
    rw [foldCV_cons]
    refine hC k r E A m _ (x.2 : ℂ) s ?_
    refine inCC_fold hC A s F b (m + (2 * r + k + 1)) ?_
    have e : m + (2 * r + k + 1) + (2 * r + k + 1) * b.length = m + (2 * r + k + 1) * (x :: b).length := by
      simp [List.length_cons]; ring
    rw [e]; exact h

theorem weight_budget_L2_inequality (k r N : ℕ) (A₀ : ℝ) (hk : 2 ≤ k) (j : ℕ) (hj : j ≤ 5)
    (hA : 100 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀)
    (ℓ : ℕ) (hℓ : ℓ ≤ N) :
    B.AB k r + 2 * ((r : ℝ) + 1) * ((j + (2 * r + k + 1) * ℓ : ℕ) : ℝ) ≤ A₀ := by
  unfold B.AB
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hj' : (j : ℝ) ≤ 5 := by exact_mod_cast hj
  have hℓ' : (ℓ : ℝ) ≤ N := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have hcast : ((j + (2 * r + k + 1) * ℓ : ℕ) : ℝ) = j + n * ℓ := by rw [hn]; push_cast; ring
  rw [hcast]
  have hn3 : (3 : ℝ) ≤ n := by rw [hn]; linarith
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
  have h4 : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ 4 := by
    have : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
    nlinarith

  have hkr : 2 * ((k : ℝ) + r) ≤ 2 * n := by rw [hn]; linarith
  have hb : 2 * ((k : ℝ) + r) + 1 + 2 * (j + n * ℓ) ≤ 100 * ((N : ℝ) * n ^ 2 + n ^ 3) := by
    have h1 : 2 * n * ℓ ≤ (N : ℝ) * n ^ 2 := by
      have : (ℓ : ℝ) * (2 * n) ≤ N * (n * n) := by
        apply mul_le_mul hℓ' (by nlinarith) (by positivity) (by positivity)
      nlinarith
    have h2 : 2 * n + 1 + 10 ≤ 100 * n ^ 3 := by nlinarith
    have hNn : 0 ≤ (N : ℝ) * n ^ 2 := by positivity
    nlinarith
  have hpos : 0 ≤ 100 * ((N : ℝ) * n ^ 2 + n ^ 3) := by positivity
  calc 2 * ((k : ℝ) + r) * ((r : ℝ) + 1) + 1 + 2 * ((r : ℝ) + 1) * (j + n * ℓ)
      ≤ ((r : ℝ) + 1) * (2 * ((k : ℝ) + r) + 1 + 2 * (j + n * ℓ)) := by nlinarith
    _ ≤ ((r : ℝ) + 1) * (100 * ((N : ℝ) * n ^ 2 + n ^ 3)) := by gcongr
    _ ≤ ((r : ℝ) + 1) ^ 4 * (100 * ((N : ℝ) * n ^ 2 + n ^ 3)) := by gcongr
    _ = 100 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * n ^ 2 + n ^ 3) := by ring
    _ ≤ A₀ := hA

theorem l2BoundAtBuiltPlace_of_cvInCC (hC : CVInCC) : L2BoundAtTowerPlace := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v ε hε a hlen
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, _, hk2, hA, _⟩, _, _, _⟩ := hB
  obtain ⟨hχ, hv⟩ := hbuilt
  obtain ⟨_, _, _, _, hCC, _⟩ := hv v
  have hF : ∀ j ≤ 5, B.InCC (B.AB S.G.k S.G.r) (j + (2 * S.G.r + S.G.k + 1) * a.length)
      (D.cutF (T v).base χ (f v) ε) := fun j hj =>
    Formalism.FourierDecayAlt.P.PBE.cutF_inCC (T v).base hχ hCC hε _ _ (weight_budget_L2_inequality S.G.k S.G.r S.Ntop A₀ hk2 j hj hA a.length hlen)
  have h5 := inCC_fold hC (B.AB S.G.k S.G.r) (M.sgn (D.parOf S v) (S.l + 1)) _ a 5 (hF 5 le_rfl)
  have h4 := inCC_fold hC (B.AB S.G.k S.G.r) (M.sgn (D.parOf S v) (S.l + 1)) _ a 4 (hF 4 (by norm_num))
  obtain ⟨_, _, _, hB1, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base
    (B.AB S.G.k S.G.r) le_rfl
  obtain ⟨C0, hC0⟩ := hB1
  obtain ⟨c4, hc4⟩ := h4
  exact (hC0 _ _ c4 c4 h5 h5 hc4 hc4).1

theorem L2_bound_at_built_place_holds : L2BoundAtTowerPlace := l2BoundAtBuiltPlace_of_cvInCC coefficient_vector_in_L2_class

end Formalism.FourierDecayAlt.P.CutMP.En
end

