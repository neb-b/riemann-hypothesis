module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0195
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0196
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0041
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0189
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0190
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0194

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CWConsPlus
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd
open scoped ComplexConjugate

noncomputable section

section cs

variable {n : ℕ}

theorem xs_upL (x0 : ℂ → ℂ) : ∀ (L : List (Letter ℂ (Fin n))) (E : Ix (Fin (n + 1))) (Y : ℂ),
    Fr.xs x0 (L.map PBF.upL) E Y = Fr.xs x0 L (fun a => E a.succ) Y
  | [], _, _ => rfl
  | l :: L, E, Y => by
    simp only [List.map_cons, Fr.xs]
    rw [xs_upL x0 L E Y]
    rfl

theorem cs_upL (x0 q0 : ℂ → ℂ) : ∀ (L : List (Letter ℂ (Fin n))) (E : Ix (Fin (n + 1))),
    Fr.cs x0 q0 (L.map PBF.upL) E = Fr.cs x0 q0 L (fun a => E a.succ)
  | [], _ => rfl
  | l :: L, E => by
    simp only [List.map_cons, Fr.cs]
    simp only [cs_upL, xs_upL,
      show qw q0 (L.map PBF.upL) = qw q0 L from funext fun Y => PBF.qw_map_reindex q0 Fin.succ L Y]
    rfl

theorem cW_cons_plus (P : M.Par) (l0 : ℕ) (y : ℝ) (w : List C.Letter) (E : Ix (Fin (w.length + 1))) (ρ : M.Ty P) :
    Top.cW P l0 ((true, y) :: w) E ρ = Top.cW P l0 w (fun a => E a.succ) ρ *
      (if E 0 = 0 then qw (M.qC P) (D.positionted w) (y : ℂ) /
          Fr.xs (fun Y => M.sgn P l0 * M.xC P ρ Y) (D.positionted w) (fun a => E a.succ) ((y : ℂ) + 1)
        else Fr.xs (fun Y => M.sgn P l0 * M.xC P ρ Y) (D.positionted w) (fun a => E a.succ) (y : ℂ)) := by
  unfold Top.cW
  rw [PBF.positioned_cons]
  simp only [Fr.cs, if_true]
  simp only [cs_upL, xs_upL, show qw (M.qC P) ((D.positionted w).map PBF.upL) = qw (M.qC P) (D.positionted w) from
    funext fun Y => PBF.qw_map_reindex _ Fin.succ _ Y]

def topRprod {P : M.Par} (l0 : ℕ) (a : List C.Letter) (e : Ix (Fin a.length)) (ρ : M.Ty P) : List ℝ → ℂ
  | [] => 1
  | y :: ys => topRprod l0 a e ρ ys * topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y

theorem cW_plusW (P : M.Par) (l0 : ℕ) (a : List C.Letter) (e : Ix (Fin a.length)) (ρ : M.Ty P) :
    ∀ ys : List ℝ, Top.cW P l0 (KB.plusW ys a) (KB.firstSt ys e) ρ = Top.cW P l0 a e ρ * topRprod l0 a e ρ ys
  | [] => by simp [topRprod, KB.plusW, KB.firstSt]
  | y :: ys => by
    have h := cW_cons_plus P l0 y (KB.plusW ys a) (Fin.cons (0 : Fin 2) (KB.firstSt ys e)) ρ
    simp only [Fin.cons_zero, Fin.cons_succ, if_true] at h
    show Top.cW P l0 ((true, y) :: KB.plusW ys a) (Fin.cons (0 : Fin 2) (KB.firstSt ys e)) ρ = _
    rw [h, cW_plusW P l0 a e ρ ys]
    simp only [topRprod, topR]
    ring

end cs

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev GenW (k r : ℕ) := Polynomial ℂ × List (ℂ × B.Mat k r)

def fexp {k r : ℕ} : List (GenW k r) → List (Polynomial ℂ × List (B.Mat k r))
  | [] => [(1, [])]
  | gn :: gs => (fexp gs).map (fun t => (gn.1 * t.1, t.2)) ++
      gn.2.flatMap (fun dX => (fexp gs).map (fun t => (Polynomial.C dX.1 * t.1, dX.2 :: t.2)))

section ops

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def genOpR (gn : GenW k r) (u : ℂ) (F : B.Mat k r → E) : B.Mat k r → E :=
  fun h => gn.1.eval u • F h + (gn.2.map fun dX => dX.1 • Formalism.REAL.RdV dX.2 F h).sum

def genOpL (gn : GenW k r) (u : ℂ) (F : B.Mat k r → E) : B.Mat k r → E :=
  fun h => gn.1.eval u • F h + (gn.2.map fun dX => dX.1 • Q.LdV dX.2 F h).sum

def wsEvalR (ws : List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ) (f : B.Mat k r → E) (g : B.Mat k r) : E :=
  (ws.map fun t => t.1.eval u • B.Rw t.2 f g).sum

def wsEvalL (ws : List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ) (f : B.Mat k r → E) (g : B.Mat k r) : E :=
  (ws.map fun t => t.1.eval u • t.2.foldr Q.LdV f g).sum

end ops

def capGen {k r t : ℕ} (Zg : Fin t → Fin t → B.Mat k r) (σ : Equiv.Perm (Fin t)) (i : Fin t) : GenW k r :=
  (if σ i = i then Polynomial.X - Polynomial.C ((i : ℕ) : ℂ) else 0,
    [(1, hpart1 (Hpk k r) (Zg (σ i) i)), (Complex.I, hpart2 (Hpk k r) (Zg (σ i) i))])

def capGens {k r t : ℕ} (Zg : Fin t → Fin t → B.Mat k r) (σ : Equiv.Perm (Fin t)) : List (GenW k r) :=
  List.ofFn (capGen Zg σ)

def zgCV (k r : ℕ) : Fin (Q.mdim k r 0) → Fin (Q.mdim k r 0) → B.Mat k r :=
  fun a b => Matrix.single (Q.posL k r 0 a) (Q.posL k r 0 b) (1 : ℂ)

def zgB {k r : ℕ} (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) : Fin k → Fin k → B.Mat k r :=
  fun a b => Q.unitB (Hpk k r) Bs a b

def RdVRep : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (X : B.Mat k r) (U : Set (B.Mat k r))
    (F f : B.Mat k r → E), B.inLie k r X → IsOpen U → ContDiffOn ℝ 1 F U →
    (∀ g ∈ U, g ∈ B.GV k r → f g = F g) → ∀ h ∈ U, h ∈ B.GV k r →
      Formalism.REAL.RdV X f h = fderiv ℝ F h (h * X) ∧ Q.LdV X f h = fderiv ℝ F h (X * h)

def FExpEvalR : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (gens : List (GenW k r)) (u : ℂ)
    (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
    (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) → B.CkOn (gens.length : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
      (gens.map (fun gn => genOpR gn u)).foldr (fun T h => T h) f g = wsEvalR (fexp gens) u f g

def FExpEvalL : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (gens : List (GenW k r)) (u : ℂ)
    (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
    (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) → B.CkOn (gens.length : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
      (gens.map (fun gn => genOpL gn u)).foldr (fun T h => T h) f g = wsEvalL (fexp gens) u f g

def CVAsGens : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) (f : B.Mat k r → E) (g : B.Mat k r),
    Q.CV k r Y f g = ∑ σ : Equiv.Perm (Fin (Q.mdim k r 0)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((capGens (zgCV k r) σ).map (fun gn => genOpR gn (Q.uC k r 0 Y))).foldr (fun T h => T h) f g

def CapRAsGens : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ)
    (f : B.Mat k r → E) (g : B.Mat k r),
    Q.capR k r Bs w f g = ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((capGens (zgB Bs) σ).map (fun gn => genOpR gn w)).foldr (fun T h => T h) f g

def CapLAsGens : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ)
    (f : B.Mat k r → E) (g : B.Mat k r),
    Q.capLft k r Bs w f g = ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((capGens (zgB Bs) σ).reverse.map (fun gn => genOpL gn w)).foldr (fun T h => T h) f g

def FExpDeg : Prop :=
  ∀ (k r : ℕ) (gens : List (GenW k r)), (∀ gn ∈ gens, gn.1.natDegree ≤ 1) →
    ∀ t ∈ fexp gens, t.1.natDegree + t.2.length ≤ gens.length ∧ ∀ X ∈ t.2, ∃ gn ∈ gens, ∃ d : ℂ, (d, X) ∈ gn.2

def FExpSymb : Prop :=
  ∀ (k r : ℕ) (gens : List (GenW k r)) (τ : B.Mat k r → ℂ) (u s : ℂ),
    ((fexp gens).map fun t => t.1.eval u * s ^ t.2.length * (t.2.map τ).prod).sum =
      (gens.map fun gn => gn.1.eval u + s * (gn.2.map fun dX => dX.1 * τ dX.2).sum).prod

def DetShiftCoeff : Prop :=
  ∀ (t : ℕ) (M : Matrix (Fin t) (Fin t) ℂ) (j : ℕ), j ≤ t →
    AddMonoidAlgebra.coeff (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
        ∏ i : Fin t, ((if σ i = i then MvPolynomial.X 0 - MvPolynomial.C ((i : ℕ) : ℂ) else 0) +
          MvPolynomial.X 1 * MvPolynomial.C (M (σ i) i)))
      (Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j) =
      (-1) ^ j * M.charpoly.coeff (t - j)

def CoeffInterp : Prop :=
  ∀ (N m : ℕ), m ≤ N → ∃ (Ys : Fin (N + 1) → ℝ) (lam : Fin (N + 1) → ℂ),
    ∀ q : Polynomial ℂ, q.natDegree ≤ N → ∑ i, lam i * q.eval (Ys i : ℂ) = q.coeff m

def CapWordsOfParts : Prop :=
  RdVRep → FExpEvalR → CVAsGens → FExpDeg → FExpSymb → DetShiftCoeff → CoeffInterp → CapWords

def CapRWordsOfParts : Prop :=
  RdVRep → FExpEvalR → CapRAsGens → FExpDeg → FExpSymb → DetShiftCoeff → CoeffInterp → CapRWords

def CapLWordsOfParts : Prop :=
  RdVRep → FExpEvalL → CapLAsGens → FExpDeg → FExpSymb → DetShiftCoeff → CoeffInterp → CapLWords

theorem capWords_all_of (hJ : CapWordsOfParts) (hJR : CapRWordsOfParts) (hJL : CapLWordsOfParts) (h1 : RdVRep)
    (hR : FExpEvalR) (hL : FExpEvalL) (hCV : CVAsGens) (hCR : CapRAsGens) (hCL : CapLAsGens) (hD : FExpDeg)
    (hS : FExpSymb) (hDet : DetShiftCoeff) (hI : CoeffInterp) : CapWords ∧ CapRWords ∧ CapLWords :=
  ⟨hJ h1 hR hCV hD hS hDet hI, hJR h1 hR hCR hD hS hDet hI, hJL h1 hL hCL hD hS hDet hI⟩

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CayleyAlgebraicHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace UnitInverseArithmetic

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem mul_inv_of_isUnit {A : Matrix n n ℂ} (h : IsUnit A) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp h)

theorem inv_mul_of_isUnit {A : Matrix n n ℂ} (h : IsUnit A) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp h)

theorem isUnit_of_mul_one {A B : Matrix n n ℂ} (h : A * B = 1) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).mpr (Matrix.isUnit_det_of_right_inverse h)

theorem half_two : ((2 : ℂ)⁻¹) • ((1 : Matrix n n ℂ) + 1) = 1 := by
  rw [← two_smul ℂ (1 : Matrix n n ℂ), smul_smul]; norm_num

theorem half_double (A : Matrix n n ℂ) : ((2 : ℂ)⁻¹) • (A + A) = A := by
  rw [← two_smul ℂ A, smul_smul]; norm_num

theorem fwd {H X : Matrix n n ℂ} (hX : Xᴴ * H + H * X = 0) (hu : IsUnit (1 - X)) :
    ((1 + X) * (1 - X)⁻¹)ᴴ * H * ((1 + X) * (1 - X)⁻¹) = H ∧ IsUnit ((1 + X) * (1 - X)⁻¹ + 1) ∧
      ((1 + X) * (1 - X)⁻¹ - 1) * ((1 + X) * (1 - X)⁻¹ + 1)⁻¹ = X := by
  set V := (1 - X)⁻¹ with hV
  have h1 : (1 - X) * V = 1 := mul_inv_of_isUnit hu
  have h2 : V * (1 - X) = 1 := inv_mul_of_isUnit hu
  have hXV : X * V = V - 1 := by
    have e := h1
    rw [Matrix.sub_mul, Matrix.one_mul] at e
    rw [← e]; abel
  have hg1 : (1 + X) * V + 1 = V + V := by
    rw [Matrix.add_mul, Matrix.one_mul, hXV]; abel
  have hq : (V + V) * ((2⁻¹ : ℂ) • (1 - X)) = 1 := by
    rw [Matrix.mul_smul, Matrix.add_mul, h2, half_two]
  refine ⟨?_, ?_, ?_⟩
  · have ha : (1 + Xᴴ) * H = H * (1 - X) := by
      have e : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
      rw [Matrix.add_mul, Matrix.one_mul, e, Matrix.mul_sub, Matrix.mul_one, sub_eq_add_neg]
    have hb : H * (1 + X) = (1 - Xᴴ) * H := by
      have e : H * X = -(Xᴴ * H) := eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hX)
      rw [Matrix.mul_add, Matrix.mul_one, e, Matrix.sub_mul, Matrix.one_mul, sub_eq_add_neg]
    have hc : (1 - X) * (1 + X) = (1 + X) * (1 - X) := by noncomm_ring
    have hW : Vᴴ * (1 - Xᴴ) = 1 := by
      have e := congrArg Matrix.conjTranspose h1
      rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one] at e
    calc ((1 + X) * V)ᴴ * H * ((1 + X) * V)
        = Vᴴ * (((1 + Xᴴ) * H) * ((1 + X) * V)) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * (H * (((1 - X) * (1 + X)) * V)) := by rw [ha]; simp only [Matrix.mul_assoc]
      _ = Vᴴ * (H * ((1 + X) * ((1 - X) * V))) := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = (Vᴴ * (1 - Xᴴ)) * H := by
          rw [h1, Matrix.mul_one, hb]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hW, Matrix.one_mul]
  · rw [hg1]; exact isUnit_of_mul_one hq
  · rw [hg1, Matrix.inv_eq_right_inv hq, Matrix.mul_smul]
    have e : ((1 + X) * V - 1) * (1 - X) = X + X := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, h2, Matrix.mul_one, Matrix.one_mul]; abel
    rw [e, half_double]

theorem bwd {H g : Matrix n n ℂ} (hg : gᴴ * H * g = H) (hu : IsUnit (g + 1)) :
    ((g - 1) * (g + 1)⁻¹)ᴴ * H + H * ((g - 1) * (g + 1)⁻¹) = 0 ∧ IsUnit (1 - (g - 1) * (g + 1)⁻¹) ∧
      (1 + (g - 1) * (g + 1)⁻¹) * (1 - (g - 1) * (g + 1)⁻¹)⁻¹ = g := by
  set P := (g + 1)⁻¹ with hP
  have h1 : (g + 1) * P = 1 := mul_inv_of_isUnit hu
  have h2 : P * (g + 1) = 1 := inv_mul_of_isUnit hu
  have hgP : g * P = 1 - P := by
    have e := h1
    rw [Matrix.add_mul, Matrix.one_mul] at e
    rw [← e]; abel
  have hX : (g - 1) * P = 1 - P - P := by rw [Matrix.sub_mul, Matrix.one_mul, hgP]
  have hOne : (1 : Matrix n n ℂ) - (1 - P - P) = P + P := by abel
  have hq : (P + P) * ((2⁻¹ : ℂ) • (g + 1)) = 1 := by
    rw [Matrix.mul_smul, Matrix.add_mul, h2, half_two]
  rw [hX]
  refine ⟨?_, ?_, ?_⟩
  · have hQ : Pᴴ * (gᴴ + 1) = 1 := by
      have e := congrArg Matrix.conjTranspose h1
      rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_add, Matrix.conjTranspose_one] at e
    have hm : H * (g + 1) + (gᴴ + 1) * H = (gᴴ + 1) * H * (g + 1) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hg]; abel
    have key : Pᴴ * H + H * P = H := by
      calc Pᴴ * H + H * P = Pᴴ * (H * ((g + 1) * P)) + (Pᴴ * (gᴴ + 1)) * (H * P) := by
            rw [h1, hQ, Matrix.mul_one, Matrix.one_mul]
        _ = Pᴴ * ((H * (g + 1) + (gᴴ + 1) * H) * P) := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = (Pᴴ * (gᴴ + 1)) * H * ((g + 1) * P) := by rw [hm]; simp only [Matrix.mul_assoc]
        _ = H := by rw [hQ, h1, Matrix.one_mul, Matrix.mul_one]
    have key' : Pᴴ * H = H - H * P := eq_sub_of_add_eq key
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, key']
    abel
  · rw [hOne]; exact isUnit_of_mul_one hq
  · rw [hOne, Matrix.inv_eq_right_inv hq, Matrix.mul_smul]
    have e : (1 + (1 - P - P)) * (g + 1) = g + g := by
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, h2]; abel
    rw [e, half_double]

end UnitInverseArithmetic

theorem cayley_algebraic_holds : CayAlg := by
  intro k r
  refine ⟨fun X hX hu => ?_, fun g hg hu => ?_⟩
  · exact UnitInverseArithmetic.fwd hX hu
  · exact UnitInverseArithmetic.bwd hg hu

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousHsInner
section
open Matrix MeasureTheory Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cont

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem continuous_hsInner [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] :
    Continuous fun q : (Wq →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => B.hsInner q.1 q.2 := by
  have hv : Continuous (fun A : Wq →L[ℂ] Wp => B.hsVec A) := by
    unfold B.hsVec
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_eval_const _)
  unfold B.hsInner
  exact (hv.comp continuous_snd).inner (hv.comp continuous_fst)

theorem radSp_contOn {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (Ψ : RadSp k r z z' π π') (c0 : Fin r → ℂ) {g : ℂ → Mx k r} {O : Set ℂ}
    (hO : IsOpen O) (hg : ContinuousOn g O) (hdom : ∀ ζ ∈ O, (c0, g ζ) ∈ DomR k r z z') :
    ContinuousOn (fun ζ => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c0 (g ζ)) O := by
  intro ζ₀ hζ₀
  have hmem := Ψ.2
  obtain ⟨-, hs, -⟩ := hmem
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (c0, g ζ₀) (hdom ζ₀ hζ₀)
  have hgA : ContinuousAt g ζ₀ := hg.continuousAt (hO.mem_nhds hζ₀)
  have hpA : ContinuousAt (fun ζ => ((c0, g ζ) : (Fin r → ℂ) × Mx k r)) ζ₀ :=
    continuousAt_const.prodMk hgA
  have hev : ∀ᶠ ζ in 𝓝 ζ₀, ζ ∈ O ∧ ((c0, g ζ) : (Fin r → ℂ) × Mx k r) ∈ U :=
    Filter.Eventually.and (hO.mem_nhds hζ₀) (hpA.preimage_mem_nhds (hU.mem_nhds hxU))
  have hFc : ContinuousAt F (c0, g ζ₀) := hF.continuousOn.continuousAt (hU.mem_nhds hxU)
  have hcomp : ContinuousAt (fun ζ => F (c0, g ζ)) ζ₀ :=
    ContinuousAt.comp (g := F) (f := fun ζ => ((c0, g ζ) : (Fin r → ℂ) × Mx k r)) hFc hpA
  refine (hcomp.congr ?_).continuousWithinAt
  filter_upwards [hev] with ζ hζ
  exact (hΦ (c0, g ζ) hζ.2 (hdom ζ hζ.1).2.1).symm

theorem topDens_contOn {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S]
    [DecidableEq S] (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (w : List (Letter ℂ S)) (x y : Ix S → RadSp k r z z' π π') (c0 : Fin r → ℂ) {g : ℂ → Mx k r} {O : Set ℂ}
    (hO : IsOpen O) (hg : ContinuousOn g O) (hdom : ∀ ζ ∈ O, (c0, g ζ) ∈ DomR k r z z') :
    ContinuousOn (fun ζ => topDens L st w x y c0 (g ζ)) O := by
  have h1 : ∀ e, ContinuousOn (fun ζ => B.hsInner
      ((act ((Fr.ofWord L st w).d L * (Fr.ofWord L st w).F) x e : Fn k r (Wq →L[ℂ] Wp)) c0 (g ζ))
      ((act (Fr.ofWord L st w).F y e : Fn k r (Wq →L[ℂ] Wp)) c0 (g ζ))) O := by
    intro e
    have ha := radSp_contOn (act ((Fr.ofWord L st w).d L * (Fr.ofWord L st w).F) x e) c0 hO hg hdom
    have hb := radSp_contOn (act (Fr.ofWord L st w).F y e) c0 hO hg hdom
    have hc := continuous_hsInner.comp_continuousOn (ha.prodMk hb)
    exact hc
  have h2 := continuousOn_finsetSum Finset.univ (fun e _ => h1 e)
  refine h2.congr fun ζ _ => ?_
  unfold topDens
  rfl

end cont

theorem one_mem_UWset {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ UWset k r z := by
  simp [UWset, UH]

theorem topContOn_of (hP : P5.ThmPActualCpt) (hHT : KB.HeadTop) : TopContOn := by
  intro Wp Wq _ _ _ _ _ _ P p F w h h' hh hh' Cb hθ hF hw
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨P.r, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X
      (μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - P.r))) L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - P.r)) with hμ
  obtain ⟨K, -, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  have hcx : ∀ e, KB.CptCoef (p.T.bs P.r) (KB.slv p.T F P.r le_rfl w h hh.2 e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F P.r le_rfl w h hh hF e
  have hcx' : ∀ e, KB.CptCoef (p.T.bs P.r) (KB.slv p.T F P.r le_rfl w h' hh'.2 e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F P.r le_rfl w h' hh' hF e
  choose Φ hΦK hΦ using fun e => pic_cpt (p.T.bs P.r) (K 0) hJ (hcx e)
  choose Φ' hΦ'K hΦ' using fun e => pic_cpt (p.T.bs P.r) (K 0) hJ (hcx' e)
  have hHTx := hHT Wp Wq P p F w h h' hh hh' X μ L st Cb Φ Φ' hD hθ hF hw hΦ hΦ'
  have hTT : Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' = P.T * P.T' := by
    have e1 := hPl.2.2.2.1
    have e2 := hPl.2.2.2.2.1
    exact congrArg₂ (· * ·) e1 e2
  let O : Set ℂ := {c : ℂ | P.T * P.T' < Complex.normSq c}
  have hO : IsOpen O := isOpen_lt continuous_const Complex.continuous_normSq
  let g : ℂ → Mx P.k (P.r - P.r) := fun ζ => B2.embWb P.k (P.r - P.r) ((p.T.bs P.r).μsec ζ)
  let c0 : Fin (P.r - P.r) → ℂ := fun _ => 1
  have hfacts : ∀ ζ ∈ O, g ζ ∈ B2.UWb P.k (P.r - P.r) ∧
      herm (Hpk P.k (P.r - P.r)) (g ζ *ᵥ (p.T.bs P.r).z') (p.T.bs P.r).z = ζ := by
    intro ζ hζ
    have hζ' : Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' < Complex.normSq ζ := by rw [hTT]; exact hζ
    have := Formalism.FourierDecayAlt.P.b2_rank_one_mem P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).μsec (p.T.bs P.r).z_mem (p.T.bs P.r).z'_mem (p.T.bs P.r).sec ζ hζ'
      1 (one_mem_UWset _) 1 (one_mem_UWset _)
    simpa using this
  have hdom : ∀ ζ ∈ O, (c0, g ζ) ∈ DomR P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' := by
    intro ζ hζ
    obtain ⟨hmem, hherm⟩ := hfacts ζ hζ
    refine ⟨fun _ => one_ne_zero, Formalism.FourierDecayAlt.P.JCx2.rb_uwb_glev hmem, ?_⟩
    unfold Q.GGl
    rw [P5.Rad.zetaL_last, hherm, hTT]
    exact sub_pos.2 hζ
  have hzeta : ∀ ζ ∈ O, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) (g ζ) = ζ := by
    intro ζ hζ
    rw [P5.Rad.zetaL_last, (hfacts ζ hζ).2]
  have hg : ContinuousOn g O := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    simp only [g, B2.embWb]
    split_ifs
    · exact ((p.T.bs P.r).sec.1 _ _).continuousOn.mono (fun ζ hζ => by
        simp only [Set.mem_ofPred_eq]; rw [hTT]; exact hζ)
    · exact continuousOn_const
    · exact continuousOn_const
  have hcont : ContinuousOn (fun ζ => topDens L st (D.positionted w) Φ Φ' c0 (g ζ)) O :=
    topDens_contOn L st (D.positionted w) Φ Φ' c0 hO hg hdom
  refine hcont.congr fun ζ hζ => ?_
  have := hHTx (c0, g ζ) (hdom ζ hζ)
  simp only [] at this
  rw [hzeta ζ hζ] at this
  exact this.symm

end Formalism.FourierDecayAlt.P.PBO
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnergyReal
section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem energy_reality_holds : EnergyReal :=
  ER.energyReal_of_capAdjInt (ER.capAdjInt_of_scalar ER.capacity_adjoint_scalar)

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocDone
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jALocCC_of_op (h2 : JALocOp) (h3 : JALocAdj) : JALocCC :=
  jALocCC_of_leaves h2 h3 local_phi_transfer_holds local_additivity_transfer local_square_integrable_transfer

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

