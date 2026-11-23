module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0239
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0151
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermPartsCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0118
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPCompactOfStepDensity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0238

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ParamCommF
section
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

abbrev MJ (j : ℕ) : Type := Matrix (Fin j) (Fin j) ℂ

def levi (k r j : ℕ) (x : MJ j) : Q.Mx k r := Matrix.of fun p q =>
  if hp : p.val < j then (if hq : q.val < j then x ⟨p.val, hp⟩ ⟨q.val, hq⟩ else 0)
  else if hp' : 2 * r + k < p.val + j then
    (if hq' : 2 * r + k < q.val + j then
      -conj (x ⟨2 * r + k - q.val, by omega⟩ ⟨2 * r + k - p.val, by omega⟩) else 0)
  else 0

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def EZ {j : ℕ} (a b : Fin j) (h : MJ j → E) : MJ j → E := fun Z =>
  RdV ((1 / 2 : ℂ) • Matrix.single a b (1 : ℂ)) h Z +
    Complex.I • RdV ((1 / (2 * Complex.I)) • Matrix.single a b (1 : ℂ)) h Z

def EZs {j : ℕ} (a b : Fin j) (h : MJ j → E) : MJ j → E := fun Z =>
  RdV (-(1 / 2 : ℂ) • Matrix.single b a (1 : ℂ)) h Z +
    Complex.I • RdV ((1 / (2 * Complex.I)) • Matrix.single b a (1 : ℂ)) h Z

def ParamCommF {j : ℕ} (T : (MJ j → E) → (MJ j → E)) : Prop :=
  ∀ (U : Set (ℂ × (Fin j → Fin j → ℂ))) (κ : ℂ → MJ j → E), IsOpen U →
    U ⊆ {q | (Matrix.of q.2).det ≠ 0} →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => κ q.1 (Matrix.of q.2)) U →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => T (κ q.1) (Matrix.of q.2)) U ∧
    ∀ q ∈ U, PBP.dz (fun τ => T (κ τ) (Matrix.of q.2)) q.1 = T (fun Z => PBP.dz (fun τ => κ τ Z) q.1) (Matrix.of q.2) ∧
      PBP.dzb (fun τ => T (κ τ) (Matrix.of q.2)) q.1 = T (fun Z => PBP.dzb (fun τ => κ τ Z) q.1) (Matrix.of q.2)

structure ZOp {j : ℕ} (T : (MJ j → E) → MJ j → E) : Prop where
  loc : ∀ (h₁ h₂ : MJ j → E) (Z : MJ j), h₁ =ᶠ[𝓝 Z] h₂ → T h₁ Z = T h₂ Z
  add : ∀ (V : Set (MJ j)) (h₁ h₂ : MJ j → E), IsOpen V → V ⊆ {Z | Z.det ≠ 0} → ContDiffOn ℝ ∞ h₁ V →
    ContDiffOn ℝ ∞ h₂ V → ∀ Z ∈ V, T (h₁ + h₂) Z = T h₁ Z + T h₂ Z
  smul : ∀ (V : Set (MJ j)) (c : ℂ) (h : MJ j → E), IsOpen V → V ⊆ {Z | Z.det ≠ 0} → ContDiffOn ℝ ∞ h V →
    ∀ Z ∈ V, T (c • h) Z = c • T h Z
  par : ParamCommF T

end Formalism.FourierDecayAlt.P.WirtingerOperators

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

def CurveLevi : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))) (x : MJ j) (t : ℝ),
    x0 k r j hj Z τ γ * NormedSpace.exp ((t : ℂ) • levi k r j x) =
      x0 k r j hj (Z * NormedSpace.exp ((t : ℂ) • x)) τ γ

def HpartLevi : Prop :=
  ∀ (k r j : ℕ) (hj : j ≤ r) (a b : Fin j),
    hpart1 (Hpk k r) (Matrix.single (eI k r (Fin.castLE hj a)) (eI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j ((1 / 2 : ℂ) • Matrix.single a b (1 : ℂ)) ∧
      hpart2 (Hpk k r) (Matrix.single (eI k r (Fin.castLE hj a)) (eI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j ((1 / (2 * Complex.I)) • Matrix.single a b (1 : ℂ)) ∧
      hpart1 (Hpk k r) (Matrix.single (esI k r (Fin.castLE hj a)) (esI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j (-(1 / 2 : ℂ) • Matrix.single b a (1 : ℂ)) ∧
      hpart2 (Hpk k r) (Matrix.single (esI k r (Fin.castLE hj a)) (esI k r (Fin.castLE hj b)) (1 : ℂ)) =
        levi k r j ((1 / (2 * Complex.I)) • Matrix.single b a (1 : ℂ))

def XiCoef : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))) (a : Fin j)
    (p : Fin (2 * r + k + 1)),
    herm (Hpk k r) (x0 k r j hj Z τ γ *ᵥ bvec p) (bvec (eI k r (Fin.castLE (by omega) a))) =
      if hp : p.val < j then Z a ⟨p.val, hp⟩ else 0

def XiCoefV : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → ∀ (a : Fin j) (p : Fin (2 * r + k + 1)),
    ((x0 k r j hj Z τ γ)⁻¹ *ᵥ bvec (eI k r (Fin.castLE (by omega) a))) p =
      if hp : 2 * r + k < p.val + j then conj (Z a ⟨2 * r + k - p.val, by omega⟩) else 0

def XiMem : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (Z : MJ j) (τ : ℂ) (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Q.Glev k r 0

def XiSmooth : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (τ : ℂ) (γ : B.Mat k (r - (j + 1))),
    ContDiffOn ℝ ∞ (fun Z : MJ j => x0 k r j hj Z τ γ) {Z | Z.det ≠ 0}

def ZOpRd : Prop :=
  ∀ (j : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (x : MJ j), ZOp (E := E) (fun h => RdV x h)

def DzSlice : Prop :=
  ∀ (j : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (U : Set (ℂ × (Fin j → Fin j → ℂ)))
    (κ : ℂ → MJ j → E), IsOpen U →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => κ q.1 (Matrix.of q.2)) U → ∀ τ₀ : ℂ,
    ContDiffOn ℝ ∞ (fun Z : MJ j => PBP.dz (fun τ => κ τ Z) τ₀) {Z : MJ j | (τ₀, (Z : Fin j → Fin j → ℂ)) ∈ U} ∧
    ContDiffOn ℝ ∞ (fun Z : MJ j => PBP.dzb (fun τ => κ τ Z) τ₀) {Z : MJ j | (τ₀, (Z : Fin j → Fin j → ℂ)) ∈ U}

end Formalism.FourierDecayAlt.P.WirtingerOperators
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PtSizeToStd
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory NumberField

noncomputable section

theorem ptSize_toStd (r : ℕ) (g : ℝ) : ∀ (b : ℕ) (P : C.LPt), D.ptSize (D.toStd r g b P) = D.ptSize P := by
  intro b P
  induction P generalizing b with
  | nil => rfl
  | cons block rest ih =>
    obtain ⟨s, t⟩ := block
    simpa only [D.toStd, D.ptSize, List.map_cons, List.sum_cons] using congrArg (s + ·) (ih (b + s))

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def lamP (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (i : ℕ) (P : C.LPt) : ℝ :=
  √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G P) /
    (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P *
      √(D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i * S.sizeAt v a))

end defs

def GNSetC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (i : ℕ)
    (hi : i ≤ S.G.r) (a : List C.Letter) (P Q : C.LPt) (hP : D.IsLocPt P i) (hQ : D.IsLocPt Q i),
    KB.gN (PBL.setC S p F) v ε i a P Q =
      ((lamP S v a i P * lamP S v a i Q : ℝ) : ℂ) *
        D.formLev (p v).T (M.sgn (D.parOf S v) (p v).l0) ⟨i, by have e : (D.parOf S v).r = S.G.r := rfl; omega⟩ a
          (KB.slv (p v).T (F v ε) i hi a (D.toStd S.G.r (S.g : ℝ) 1 P) (by
            rw [← hP.2]; exact FormNormSumIdentities.ptSize_toStd S.G.r (S.g : ℝ) 1 P))
          (KB.slv (p v).T (F v ε) i hi a (D.toStd S.G.r (S.g : ℝ) 1 Q) (by
            rw [← hQ.2]; exact FormNormSumIdentities.ptSize_toStd S.G.r (S.g : ℝ) 1 Q))

def GermConst : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (b s : ℕ), 0 < S.G.g1 → 0 < S.G.g2 →
    1 ≤ b → 2 ≤ s → b + s - 1 ≤ S.G.r → ∀ h : C.LPt, D.ptSize h = b - 1 →
    ∃ μ₀ : ℝ, ∀ x D z : ℂ, x ≠ 0 → D ≠ 0 → z ^ s = D →
      (‖x‖ ^ (s - 1) * (√(KB.dlB S (b + s - 1) 1))⁻¹ * lamP S v a (b + s - 1) (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)]) *
          kapB (s - 2) =
        μ₀ * ((‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (s - 1) x⁻¹‖ ^ (s - 1))⁻¹ *
          ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (s - 1) x⁻¹‖ ^ ((s - 1) * (U.Mlev S.G.k (S.G.r - (b + s - 1)) + (s - 2))) *
          ‖GermFibreKernels.fs S.G.r (S.g : ℝ) (b + s - 1) 1 (x ^ (s - 1) * D)‖ ^ (U.Mlev S.G.k (S.G.r - (b + s - 1)) - 2))) ∧
      ((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ * (√(KB.dlB S b s))⁻¹ * lamP S v a (b + s - 1) (h ++ [(s, z)]) *
          Real.pi ^ (s * (s - 1) / 2) =
        μ₀ * (‖GermFibreKernels.fs S.G.r (S.g : ℝ) (b + s - 1) 1 (x ^ (s - 1) * D) *
            GermFibreKernels.fs S.G.r (S.g : ℝ) b (s - 1) x⁻¹ ^ (s - 1)‖ ^ (U.Mlev S.G.k (S.G.r - (b + s - 1)) - 2) *
          ((s : ℝ)⁻¹ * ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b s z‖ ^ ((s - 1) ^ 2)))

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPCompactOfSquareDensity
section
open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Dens

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S]
  [DecidableEq S]

def Dens (μ : Measure (Mt k r)) (l : Fin r) (u v : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) : ℂ :=
  ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * form μ l.succ u v (Function.update c l t)

theorem dens_int (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (l : Fin r)
    (u v : Ix S → RadSp k r z z' π π')
    (hu : ∀ a, u a ∈ HerC.lcSub k r z z' π π') (hv : ∀ a, v a ∈ HerC.lcSub k r z z' π π')
    (c : Fin r → ℂ) (Iu : ∀ a, LevelSquareIntegrable μ l.castSucc (u a) c) (Iv : ∀ a, LevelSquareIntegrable μ l.castSucc (v a) c) :
    Integrable (Dens μ l u v c) ∧ ∫ t, Dens μ l u v c t = form μ l.castSucc u v c := by
  have hint := formIntOuter_of_l2I μ hμ l.castSucc u v hu hv c Iu Iv
  set f : Cf r l.castSucc → ℂ := fun c' =>
    ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (u a) (v a) (glue l.castSucc c c') with hf
  have hmp := coordinate_split_measurePreserving (r := r) l
  have hval : ∀ p : ℂ × Cf r l.succ, f ((coordinateSplit (r := r) l).symm p) = ((‖p.1‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      (((∏ j, ‖p.2 j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (u a) (v a) (glue l.succ (Function.update c l p.1) p.2)) := by
    intro p
    have hw := weight_coordinate_split (r := r) l ((coordinateSplit (r := r) l).symm p)
    have hg := glue_coordinate_split (r := r) l c ((coordinateSplit (r := r) l).symm p)
    simp only [MeasurableEquiv.apply_symm_apply] at hw hg
    simp only [hf]
    rw [hw, hg, Complex.ofReal_mul, mul_assoc]
  have hF : Integrable (fun p : ℂ × Cf r l.succ => f ((coordinateSplit (r := r) l).symm p)) (volume.prod volume) :=
    (hmp.symm.integrable_comp_emb (coordinateSplit (r := r) l).symm.measurableEmbedding (g := f)).mpr hint
  have h2 := hF.integral_prod_left
  refine ⟨h2.congr (Filter.Eventually.of_forall fun t => ?_), (form_split μ l u v c hint).symm⟩
  show ∫ c'', f ((coordinateSplit (r := r) l).symm (t, c'')) = Dens μ l u v c t
  simp only [hval, Dens, form]
  rw [integral_const_mul]

end Dens

def DecayRest (n : ℕ) (C : ℝ) (D : ℂ → ℂ) : Prop :=
  Integrable (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t) ∧ (∀ t, t ≠ 0 → ContinuousAt D t) ∧
    (∀ s, ‖∫ t, fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))) ∧
    ∀ s, ‖∫ t, fsv s t * (((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t)‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))

def LevelDensitySquareIntegrable : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r), l.val = 0 →
    ∀ (x y : Ix S → RadSp P.k P.r z z' π π'),
      InK (herKc S P z z' π π' L st l0 D l.castSucc) x → InK (herKc S P z z' π π' L st l0 D l.castSucc) y →
      ∀ c ∈ OmX P.r,
      ∃ (n K : ℕ) (C : ℝ) (u v : Fin K → Ix S → RadSp P.k P.r z z' π π') (j : Fin K → ℕ)
        (vv : ∀ i, Fin (j i) → ℂ) (a : Fin K → ℂ),
        (∀ i b, u i b ∈ HerC.lcSub P.k P.r z z' π π' ∧ LevelSquareIntegrable μ l.castSucc (u i b) c ∧
          v i b ∈ HerC.lcSub P.k P.r z z' π π' ∧ LevelSquareIntegrable μ l.castSucc (v i b) c) ∧
        (∀ i, j i ≤ n) ∧ (∀ i, DecayRest n C (Dens μ l (u i) (v i) c)) ∧
        (∀ t, t ≠ 0 → ph L st μ l w x y c t = ∑ i, a i * iteratedFDeriv ℝ (j i) (Dens μ l (u i) (v i) c) t (vv i)) ∧
        ∑ i, a i * (if j i = 0 then form μ l.castSucc (u i) (v i) c else 0) = RRform L st μ l.castSucc w x y c

theorem step_density_of_square (h : LevelDensitySquareIntegrable) : StepExp0 := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw l hl x y hx hy c hc
  have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  obtain ⟨n, K, C, u, v, j, vv, a, hL2, hjn, hrest, hexp, hI⟩ :=
    h Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw l hl x y hx hy c hc
  have hdi := fun i => dens_int μ hD.2.1 l (u i) (v i) (fun b => (hL2 i b).1) (fun b => (hL2 i b).2.2.1) c
    (fun b => (hL2 i b).2.1) (fun b => (hL2 i b).2.2.2)
  refine ⟨n, K, C, fun i => Dens μ l (u i) (v i) c, j, vv, a, hjn, fun i => ⟨(hdi i).1, hrest i⟩, hexp, ?_⟩
  rw [← hI]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [(hdi i).2]
  · rfl

end Formalism.FourierDecayAlt.P5.HerD
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopLocalBuiltPlaces
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem topLocB : TopLocB := by
  intro hDT hVT hTR Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hC hB
  refine ⟨fun s hs2 hsr v => lamTop_thr hC hB s hs2 hsr v, fun F hF (v : Fin S.f) => ?_⟩
  have hB' := hB
  obtain ⟨hg1, hg2, -, -, -, -, -, -, -, -, hGo, hGr, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -⟩ := hv v
  have hCI := PBCut.cutInside_of_built hB
  intro s hs2 hsr a ha haN
  have hsr' : s ≤ S.G.r + 1 := hsr
  have ha' : D.AdmAt S v a := ha
  have haN' : a.length + C.Kst ≤ S.Ntop := haN
  set d := S.G.r + 1 - s with hd
  have hds : d + s = S.G.r + 1 := by omega
  have hd2 : d ≤ 2 * S.G.r := by omega
  obtain ⟨-, grid, hinj, hbnd, hmem, hwords, hprob, -⟩ :=
    Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a C.Kst d ha' haN' hd2
  refine ⟨PBD.pushU grid (fun ys => KB.plusW ys a), PBD.pushTh grid (fun ys => KB.plusW ys a), hprob, ?_⟩
  intro ε hε t Y ht hY
  have hY' : ∀ P ∈ Y, D.ptSize P = d := fun P hP => by rw [hd]; exact hY P hP
  set Λ : ℝ := ∑ n : Fin C.Kst → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| with hΛ
  set C0 : ℝ := Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) * (Real.sqrt (S.T * S.T'))⁻¹
    with hC0
  set τ : ℂ := ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) *
    Complex.I ^ (s - 1) * t with hτ
  set c : ℂ := (((-1 : ℂ) ^ (s - 1) / τ) ^ C.Kst)⁻¹ with hc
  obtain ⟨hg, hk⟩ := glob_posT hB
  have hC0nn : 0 ≤ C0 := mul_nonneg (mul_nonneg (Real.exp_pos 1).le (supA_nonneg S hg hk v false))
    (inv_nonneg.2 (Real.sqrt_nonneg _))
  have hPn : ∀ n : Fin C.Kst → Fin (d + 1), 0 < ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod := by
    intro n
    refine List.prod_pos fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hy
    exact abs_pos.2 ((hGo v).2.2.2.2.2 _ (Or.inl ⟨_, hmem b (n b)⟩)).2.2.1

  have hK1 := top_kernel (H := HV S v) (α := C.LPt) (Ea := Wd.Ix (Fin a.length)) (R := M.Ty (D.parOf S v))
    (N := Fin C.Kst → Fin (d + 1)) (Ew := fun n => Wd.Ix (Fin (KB.plusW (List.ofFn fun b => grid b (n b)) a).length))
    Y (fun n => KB.firstSt (List.ofFn fun b => grid b (n b))) (fun n => firstSt_inj _)
    (fun e ρ => vecT S p F v ε s t a e ρ)
    (fun n e' ρ => vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ)
    (fun e ρ => del2 S p v a e ρ) (fun n e' ρ => del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ)
    (fun e ρ => second_defect_nonneg S p v a e ρ) (fun n e' ρ => second_defect_nonneg S p v _ e' ρ)
    (fun n => ∏ b, F7.lagCo (grid b) (n b))
    (fun n => ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod) hPn c C0 C.Kst hC0nn
    (fun P hP e ρ => vecT_deg hDT hB F v ε (hF v ε hε) s hs2 t ht d hds a e ρ grid hinj
      (fun n => (hwords n).2.2.1) P (hY' P hP))
    (fun n e ρ => by
      have h := second_defect_plus_word_le S p v a e ρ C0 hC0nn (List.ofFn fun b => grid b (n b))
        (rhyp_nodes hTR hB hC v a ha' haN' grid hmem n (hwords n).2.2.1 e ρ)
      rwa [List.length_ofFn] at h)

  change Loe Y (fun P Q => KB.gN (setC S p F) v ε (S.G.r + 1) a (P ++ [(s, t)]) (Q ++ [(s, t)]))
    (fun P Q => (((‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) : ℝ) : ℂ) *
      KB.mix (setC S p F) v ε (S.G.r + 1) (PBD.pushU grid fun ys => KB.plusW ys a)
        (PBD.pushTh grid fun ys => KB.plusW ys a) (P ++ [(s, t)]) (Q ++ [(s, t)]))
  have hsz : ∀ P ∈ Y, D.ptSize P + s = S.G.r + 1 := fun P hP => by rw [hY' P hP]; omega
  have hgpos := g_pos_of_built hB
  have hrd := PBD.rd_pos' E
  have hΓ : 0 < ΓS S (S.G.r + 1) := PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _
  have hsa : 0 < S.sizeAt v a := sizeAt_pos S hGo v a ha'
  set ka : ℝ := 1 / (ΓS S (S.G.r + 1) * S.sizeAt v a) with hka
  have hka0 : 0 ≤ ka := by positivity
  have hΛpos : 0 < Λ := lam_sum_pos grid hinj

  have h1 := loe_diag (omT S s t) (loe_smul ka hka0 hK1)
  have h1' : Loe Y (fun P Q => KB.gN (setC S p F) v ε (S.G.r + 1) a (P ++ [(s, t)]) (Q ++ [(s, t)]))
      (fun P Q => (((‖c‖ ^ 2 * Λ * C0 ^ C.Kst) * Λ : ℝ) : ℂ) * ∑ n : Fin C.Kst → Fin (d + 1),
        ((|∏ b, F7.lagCo (grid b) (n b)| / Λ : ℝ) : ℂ) * ((omT S s t P : ℂ) * (omT S s t Q : ℂ) *
          (((ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod : ℝ) : ℂ) *
            ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
              gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q))) := by
    refine loe_congr (fun P hP Q hQ => ?_) (fun P _ Q _ => ?_) h1
    · rw [gN_top hVT hB F v ε s hs2 t a P Q (hsz P hP) (hsz Q hQ)]
      ring
    · exact mix_alg _ _ _ _ _ _ _ _ hΛpos.ne' fun n => (hPn n).ne'

  have hmixY : ∀ P ∈ Y, ∀ Q ∈ Y, KB.mix (setC S p F) v ε (S.G.r + 1) (PBD.pushU grid fun ys => KB.plusW ys a)
      (PBD.pushTh grid fun ys => KB.plusW ys a) (P ++ [(s, t)]) (Q ++ [(s, t)]) =
      ∑ n : Fin C.Kst → Fin (d + 1),
        ((|∏ b, F7.lagCo (grid b) (n b)| / Λ : ℝ) : ℂ) * ((omT S s t P : ℂ) * (omT S s t Q : ℂ) *
          (((ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod : ℝ) : ℂ) *
            ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
              gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q)) := by
    intro P hP Q hQ
    refine (mix_pushT (setC S p F) v ε (S.G.r + 1) grid (fun ys => KB.plusW ys a) _ _).trans ?_
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [thGrid_eq, ← hΛ, gN_top hVT hB F v ε s hs2 t _ P Q (hsz P hP) (hsz Q hQ), sizeAt_plusW]
    have hk : 1 / (ΓS S (S.G.r + 1) * (((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod *
        S.sizeAt v a)) = ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod := by
      rw [hka]; have := (hPn n).ne'; field_simp
    rw [hk]
    ring
  have hpsdY := psd_mixω Y (omT S s t) (fun n : Fin C.Kst → Fin (d + 1) => |∏ b, F7.lagCo (grid b) (n b)| / Λ)
    (fun n => ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod)
    (fun n => div_nonneg (abs_nonneg _) hΛpos.le) (fun n => div_nonneg hka0 (hPn n).le)
    (fun n P Q => ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
      gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q)
    (fun n => psd_dsum Y _ (fun e' ρ => second_defect_nonneg S p v _ e' ρ) _)
  have hX : 0 ≤ (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) - ‖c‖ ^ 2 * Λ * C0 ^ C.Kst * Λ := by
    have hlv : 0 < ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) :=
      zpow_pos (by positivity) _
    set lv : ℝ := ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) with hlvdef
    have hτn : ‖τ‖ = lv * ‖t‖ := by
      rw [hτ, norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hlv.le]
    have hcn : ‖c‖ = ‖τ‖ ^ C.Kst := by
      rw [hc, norm_inv, norm_pow, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div, inv_pow, inv_inv]
    set B : ℝ := (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ d with hBdef
    have hΛB : Λ ≤ B ^ C.Kst := lam_sum_le grid B hbnd
    have hlenpos := lenI_posT hB (Fin.pos v)
    have hB0 : 0 ≤ B := by
      rw [hBdef, len_eq_lenI']; exact pow_nonneg (div_nonneg (by positivity) hlenpos.le) _

    have hA0 : 0 ≤ (2 * Real.pi / S.G.g) ^ (-(2 * S6.nuBlock S.G.r ((S.G.r + 2 - s : ℕ) : ℤ)
        ((S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ)))) * Real.exp 1 *
        (28 * S.G.N / S.G.lenI) ^ (2 * (S.G.r + 2 - s - 1)) * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
        (√(S.T * S.T'))⁻¹ := by
      have : 0 ≤ S.G.N := by unfold Sz.Glob.N; positivity
      have := supA_nonneg S hg hk v false
      positivity
    have hlam2 : lamTop S (S.G.r + 2 - s) v ^ 2 = lv ^ 2 * B ^ 2 * C0 := by
      unfold lamTop
      rw [Real.sq_sqrt hA0]
      have e1 : ((S.G.r + 2 - s : ℕ) : ℤ) = ((1 + d : ℕ) : ℤ) := by rw [hd]; push_cast; omega
      have e2 : (S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ) = (s : ℤ) := by push_cast; omega
      have e3 : (S.g : ℝ) = S.G.g := by unfold C.HidaSetting.g Sz.Glob.g; push_cast; ring
      have e4 : S.G.r + 2 - s - 1 = d := by omega
      rw [e2, e1, e4, hlvdef, zpow_sq_eq _ (by positivity), inv_div, e3, hBdef, ← pow_mul, ntop_eq_N'',
        len_eq_lenI', hC0, mul_comm d 2]
      ring
    have hfin : ‖c‖ ^ 2 * Λ * C0 ^ C.Kst * Λ ≤ (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) := by
      have e5 : (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) = (‖t‖ ^ 2 * (lv ^ 2 * B ^ 2 * C0)) ^ C.Kst := by
        rw [pow_mul, mul_pow (‖t‖) (lamTop S (S.G.r + 2 - s) v) 2, hlam2]
      rw [e5, hcn, hτn]
      have hΛ0 : 0 ≤ Λ := hΛpos.le
      have hsq : Λ * Λ ≤ B ^ C.Kst * B ^ C.Kst := mul_le_mul hΛB hΛB hΛ0 (pow_nonneg hB0 _)
      calc ((lv * ‖t‖) ^ C.Kst) ^ 2 * Λ * C0 ^ C.Kst * Λ = ((lv * ‖t‖) ^ C.Kst) ^ 2 * C0 ^ C.Kst * (Λ * Λ) := by ring
        _ ≤ ((lv * ‖t‖) ^ C.Kst) ^ 2 * C0 ^ C.Kst * (B ^ C.Kst * B ^ C.Kst) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (‖t‖ ^ 2 * (lv ^ 2 * B ^ 2 * C0)) ^ C.Kst := by ring
    linarith
  have h3 := loe_scale hpsdY hX
  exact loe_trans h1' (loe_congr (fun _ _ _ _ => rfl) (fun P hP Q hQ => by rw [hmixY P hP Q hQ]) h3)

end

end Formalism.FourierDecayAlt.P.PBL

theorem Formalism.FourierDecayAlt.P.top_local_built_places : Formalism.FourierDecayAlt.P.PBL.TopLocB := Formalism.FourierDecayAlt.P.PBL.topLocB
end

