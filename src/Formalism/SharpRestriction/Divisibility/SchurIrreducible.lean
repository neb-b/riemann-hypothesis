module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.LocalRingCardinality.DataTheta

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.SchurIrreducible

open Matrix MeasureTheory

open Formalism.BasicNotions.TH

export Formalism.BasicNotions.TH (Ix Mat Jm upq sameBlock IsKC IsPC pR posC Eab hsNorm adjZ conjR IsLieAct wtSub hwSub IsHW KStable OfType casimir GKMod UGKMod GrpData URep KFin IsDer IsDerC Smooth CasEig UgSpan opE DSRep Ln Pol lineSign linePos lowB raiB omE omAct fockAct1 fockAct2 lineEquiv lineEquiv_isLeft omAct_apply fockAct1_Eab fockAct2_Eab X_mul_pderiv_monomial omE_pos omE_neg omE_diag cartan1 cartan2 plusPart minusPart homog FockData IsIntw rhoNC blattner rhoSq normSq IsParam GapGe GapGt shiftNu degW cPair ofBlocks pad JointShape block lamA lamA' lamM' HypA HypG HypGm UnitHW JointHW mcoef eFun ProvA)

section StatementsA

variable (X : ProvA)

def admH1 : Prop := ∀ p q r s : ℕ,
  (∀ Z : Mat p q, IsKC Z → ∀ d, ∀ P ∈ homog (Ix p q × Ix r s) d, (X.fock p q r s).act1 Z P ∈
    homog (Ix p q × Ix r s) d) ∧
  (∀ Z : Mat r s, IsKC Z → ∀ d, ∀ P ∈ homog (Ix p q × Ix r s) d, (X.fock p q r s).act2 Z P ∈
    homog (Ix p q × Ix r s) d) ∧
  (∀ Z : Mat p q, IsPC Z → ∀ P, (X.fock p q r s).act1 Z P =
    plusPart ((X.fock p q r s).act1 Z) P + minusPart ((X.fock p q r s).act1 Z) P) ∧
  (∀ Z : Mat r s, IsPC Z → ∀ P, (X.fock p q r s).act2 Z P =
    plusPart ((X.fock p q r s).act2 Z) P + minusPart ((X.fock p q r s).act2 Z) P) ∧
  (∀ Z : Mat p q, IsPC Z → ∀ P Q,
    inner ℂ ((X.fock p q r s).ι (plusPart ((X.fock p q r s).act1 Z) P)) ((X.fock p q r s).ι Q) =
      - inner ℂ ((X.fock p q r s).ι P)
        ((X.fock p q r s).ι (minusPart ((X.fock p q r s).act1 (conjR Z)) Q))) ∧
  (∀ Z : Mat r s, IsPC Z → ∀ P Q,
    inner ℂ ((X.fock p q r s).ι (plusPart ((X.fock p q r s).act2 Z) P)) ((X.fock p q r s).ι Q) =
      - inner ℂ ((X.fock p q r s).ι P)
        ((X.fock p q r s).ι (minusPart ((X.fock p q r s).act2 (conjR Z)) Q)))

def lowKer {p q r s : ℕ} (F : FockData (X.grp (p * r + q * s) (p * s + q * r)) (X.grp p q) (X.grp r s)) (u1 u2 : Bool) :
    Set (Pol p q r s) :=
  {P | (u1 = true → ∀ Z : Mat p q, IsPC Z → minusPart (F.act1 Z) P = 0) ∧
    (u2 = true → ∀ Z : Mat r s, IsPC Z → minusPart (F.act2 Z) P = 0)}

def raised {p q r s : ℕ} (F : FockData (X.grp (p * r + q * s) (p * s + q * r)) (X.grp p q) (X.grp r s)) (u1 u2 : Bool) (d : ℕ) :
    Set (Pol p q r s) :=
  {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
    (u1 = true ∧ ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (F.act1 Z) Q) ∨
    (u2 = true ∧ ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (F.act2 Z) Q)}

def admH2 : Prop := ∀ p q r s : ℕ,
  (∀ d (μ : Ix p q → ℚ) P, P ∈ homog (Ix p q × Ix r s) d → IsHW (X.fock p q r s).act1 μ P →
    degW (cPair r s) μ ≤ d) ∧
  (∀ d (μ : Ix r s → ℚ) P, P ∈ homog (Ix p q × Ix r s) d → IsHW (X.fock p q r s).act2 μ P →
    degW (cPair p q) μ ≤ d) ∧
  (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (X.fock p q r s).act1 μ P →
    (∀ Z : Mat r s, IsPC Z → minusPart ((X.fock p q r s).act2 Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
  (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (X.fock p q r s).act2 μ P →
    (∀ Z : Mat p q, IsPC Z → minusPart ((X.fock p q r s).act1 Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
  (∀ (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
    (JointShape p q r s μ μ' →
      Module.finrank ℂ ↥(hwSub (X.fock p q r s).act1 μ ⊓ hwSub (X.fock p q r s).act2 μ' ⊓
        Submodule.span ℂ (X.fock p q r s).J) = 1) ∧
    (¬ JointShape p q r s μ μ' →
      hwSub (X.fock p q r s).act1 μ ⊓ hwSub (X.fock p q r s).act2 μ' ⊓
        Submodule.span ℂ (X.fock p q r s).J = ⊥)) ∧
  (∀ (u1 u2 : Bool), (u1 || u2) = true → ∀ d : ℕ,
    homog (Ix p q × Ix r s) (d + 2) =
      (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (lowKer X (X.fock p q r s) u1 u2)) ⊔
      Submodule.span ℂ (raised X (X.fock p q r s) u1 u2 d))

def rangeOfSeventhSum (p q : ℕ) : ℝ := 120 * ((p + q : ℕ) : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2)

def DiscreteSeriesBlattner : Prop := ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam →
  Module.finrank ℂ ↥(hwSub (X.ds p q lam).HK.act (blattner lam)) = 1 ∧
  (∀ v, casimir (X.ds p q lam).HK.act v = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • v) ∧
  (∀ (μ : Ix p q → ℚ) v, IsHW (X.ds p q lam).HK.act μ v →
    ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → lam b < lam a) ∧
      μ = fun c => blattner lam c +
        ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)))

def isoVec {p q : ℕ} {T : GrpData p q} (D : DSRep T) (Λ : Ix p q → ℚ) : Set D.U.H :=
  D.ι '' {v | OfType D.HK.act Λ v}

def DiscreteSeriesPositivity : Prop := ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → ∀ h : ℝ, GapGe lam h →
  rangeOfSeventhSum p q ≤ h →
  (∀ Y ∈ pR p q, ∀ x ∈ isoVec (X.ds p q lam) (blattner lam),
    (inner ℂ x ((X.ds p q lam).U.π ((X.grp p q).expt Y) x)).im = 0 ∧
    0 ≤ (inner ℂ x ((X.ds p q lam).U.π ((X.grp p q).expt Y) x)).re) ∧
  (∀ k ∈ (X.grp p q).Kset, ∀ Y ∈ pR p q, ∀ x ∈ isoVec (X.ds p q lam) (blattner lam),
    ∀ y ∈ isoVec (X.ds p q lam) (blattner lam),
    ‖inner ℂ y ((X.ds p q lam).U.π (k * (X.grp p q).expt Y) x)‖ ≤
      Real.exp (-(h / 8) * min (hsNorm Y ^ 2) (hsNorm Y / Real.sqrt (2 * (min p q : ℕ)))) *
        ‖x‖ * ‖y‖)

def IsHomG {p q : ℕ} {T : GrpData p q} (D : DSRep T) (πU : URep T) (io : D.U.H →L[ℂ] πU.H) :
    Prop :=
  ∀ g, io.comp (D.U.π g) = (πU.π g).comp io

def DiscreteSeriesHighestVector : Prop := ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → ∀ h : ℝ, GapGe lam h →
  rangeOfSeventhSum p q ≤ h → ∀ v, UnitHW (X.ds p q lam) (blattner lam) v →
  Integrable (eFun (X.ds p q lam) v) (X.grp p q).haar ∧
  ∀ πU : URep (X.grp p q),
    (∀ x, opE (X.grp p q) πU.π (eFun (X.ds p q lam) v) x ∈
        (Submodule.span ℂ {z | ∃ io, IsHomG (X.ds p q lam) πU io ∧
          z = io ((X.ds p q lam).ι v)}).topologicalClosure ∧
      ∀ y ∈ (Submodule.span ℂ {z | ∃ io, IsHomG (X.ds p q lam) πU io ∧
          z = io ((X.ds p q lam).ι v)}).topologicalClosure,
        inner ℂ y (x - opE (X.grp p q) πU.π (eFun (X.ds p q lam) v) x) = 0) ∧
    ∀ g x, opE (X.grp p q) πU.π (eFun (X.ds p q lam) v)
        (πU.π g (opE (X.grp p q) πU.π (eFun (X.ds p q lam) v) x)) =
      mcoef (X.ds p q lam) v g • opE (X.grp p q) πU.π (eFun (X.ds p q lam) v) x

def IsHCMod {p q : ℕ} {T : GrpData p q} (πU : URep T) (M : GKMod p q) (io : M.V →ₗ[ℂ] πU.H) : Prop :=
  Function.Injective io ∧ (∀ x, x ∈ Set.range io ↔ KFin T πU.π x) ∧
  ∀ Y ∈ upq p q, ∀ v, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (io v)) (io (M.act Y v)) 0

def IrrU {p q : ℕ} {T : GrpData p q} (πU : URep T) : Prop :=
  Nontrivial πU.H ∧ ∀ S : Submodule ℂ πU.H, IsClosed (S : Set πU.H) →
    (∀ g, ∀ x ∈ S, πU.π g x ∈ S) → S = ⊥ ∨ S = ⊤

def IrrGK {p q : ℕ} (M : GKMod p q) : Prop :=
  Nontrivial M.V ∧ ∀ N : Submodule ℂ M.V, (∀ Z, ∀ y ∈ N, M.act Z y ∈ N) → N = ⊥ ∨ N = ⊤

def AdmGK {p q : ℕ} (M : GKMod p q) : Prop :=
  ∀ μ : Ix p q → ℚ, FiniteDimensional ℂ ↥(hwSub M.act μ)

def admQ5 : Prop := ∀ p q : ℕ, 1 ≤ p + q →
  (∀ πU : URep (X.grp p q), IrrU πU →
    (∀ x, KFin (X.grp p q) πU.π x → Smooth (X.grp p q) πU.π x) ∧
    (∃ (M : GKMod p q) (io : M.V →ₗ[ℂ] πU.H), IsHCMod πU M io) ∧
    ∀ (M : GKMod p q) (io : M.V →ₗ[ℂ] πU.H), IsHCMod πU M io → AdmGK M ∧ IrrGK M) ∧
  (∀ π₁ π₂ : URep (X.grp p q), IrrU π₁ → IrrU π₂ →
    ∀ (M₁ M₂ : GKMod p q) (io₁ : M₁.V →ₗ[ℂ] π₁.H) (io₂ : M₂.V →ₗ[ℂ] π₂.H),
      IsHCMod π₁ M₁ io₁ → IsHCMod π₂ M₂ io₂ →
      ∀ e : M₁.V ≃ₗ[ℂ] M₂.V, (∀ Z v, e (M₁.act Z v) = M₂.act Z (e v)) →
      ∃ U : π₁.H ≃ₗᵢ[ℂ] π₂.H, ∀ g x, U (π₁.π g x) = π₂.π g (U x)) ∧
  (∀ (πU : URep (X.grp p q)) (M : GKMod p q) (io : M.V →ₗ[ℂ] πU.H), IsHCMod πU M io →
    AdmGK M → IrrGK M → IrrU πU)

def pOf {p q : ℕ} (B : Matrix (Fin p) (Fin q) ℂ) : Mat p q := Matrix.fromBlocks 0 B Bᴴ 0

def adMat {p q : ℕ} (Y : Mat p q) : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ :=
  Matrix.kroneckerMap (· * ·) Y (1 : Mat p q) - Matrix.kroneckerMap (· * ·) (1 : Mat p q) Yᵀ

def sinhcAd {p q : ℕ} (Y : Mat p q) : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ :=
  ∑' k : ℕ, (((2 * k + 1).factorial : ℂ)⁻¹) • adMat Y ^ (2 * k)

abbrev PIx (p q : ℕ) : Type := {ab : Ix p q × Ix p q // ¬ sameBlock ab.1 ab.2}

def polJ {p q : ℕ} (Y : Mat p q) : ℝ :=
  ((sinhcAd Y).submatrix (Subtype.val : PIx p q → Ix p q × Ix p q) Subtype.val).det.re

def shc (x : ℝ) : ℝ := if x = 0 then 1 else Real.sinh x / x

def aOf (p q : ℕ) (h : ℕ → ℝ) : Mat p q :=
  pOf (Matrix.of fun (i : Fin p) (j : Fin q) => if (i : ℕ) = (j : ℕ) then ((h i : ℝ) : ℂ) else 0)

def CoverHaarIntegration : Prop := ∀ p q : ℕ,
  (∃ (c : ℝ) (mK : Measure (X.grp p q).G), 0 < c ∧ IsProbabilityMeasure mK ∧
    mK ((X.grp p q).Kset)ᶜ = 0 ∧
    (∀ k ∈ (X.grp p q).Kset, Measure.map (fun x => k * x) mK = mK) ∧
    ∀ f : (X.grp p q).G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂(X.grp p q).haar =
        ENNReal.ofReal c * ∫⁻ B : Fin p → Fin q → ℂ,
          (∫⁻ k, f (k * (X.grp p q).expt (pOf (Matrix.of B))) ∂mK) *
            ENNReal.ofReal (polJ (pOf (Matrix.of B)))) ∧
  (∀ k ∈ (X.grp p q).Kset, ∀ Y ∈ pR p q,
    polJ ((((X.grp p q).cov k : GL (Ix p q) ℂ) : Mat p q) * Y *
      ((((X.grp p q).cov k)⁻¹ : GL (Ix p q) ℂ) : Mat p q)) = polJ Y) ∧
  (∀ Y ∈ pR p q, ∃ k ∈ (X.grp p q).Kset, ∃ h : ℕ → ℝ,
    Y = (((X.grp p q).cov k : GL (Ix p q) ℂ) : Mat p q) * aOf p q h *
      ((((X.grp p q).cov k)⁻¹ : GL (Ix p q) ℂ) : Mat p q)) ∧
  (∀ h : ℕ → ℝ, polJ (aOf p q h) =
    (∏ i ∈ Finset.range (min p q), shc (2 * h i) * shc (h i) ^ (2 * (max p q - min p q))) *
    ∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q),
      if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1)

def IsKLieAct {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : Prop :=
  ∀ Y Z, IsKC Y → IsKC Z → act (Y * Z - Z * Y) = act Y * act Z - act Z * act Y

def tensAct {p q : ℕ} {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V₁) (a₂ : Mat p q →ₗ[ℂ] Module.End ℂ V₂) :
    Mat p q →ₗ[ℂ] Module.End ℂ (TensorProduct ℂ V₁ V₂) :=
  (LinearMap.rTensorHom V₂).comp a₁ + (LinearMap.lTensorHom V₁).comp a₂

def admQ7 : Prop := ∀ (p q : ℕ) (V₁ V₂ : Type) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V₁) (a₂ : Mat p q →ₗ[ℂ] Module.End ℂ V₂),
  IsKLieAct a₁ → IsKLieAct a₂ → FiniteDimensional ℂ V₁ → FiniteDimensional ℂ V₂ →
  (∀ v, v ∈ ⨆ w : Ix p q → ℚ, wtSub a₂ w) →
  ∀ μ : Ix p q → ℚ, (∃ v, IsHW a₁ μ v) → (∀ W, KStable a₁ W → W = ⊥ ∨ W = ⊤) →
  ∀ (ν : Ix p q → ℚ) (u : TensorProduct ℂ V₁ V₂), IsHW (tensAct a₁ a₂) ν u →
    ∃ w : Ix p q → ℚ, wtSub a₂ w ≠ ⊥ ∧ ν = μ + w

section PBW

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

abbrev Ug (p q : ℕ) : Type := UniversalEnvelopingAlgebra ℂ (Mat p q)

def ugι (p q : ℕ) : Mat p q →ₗ[ℂ] Ug p q :=
  (UniversalEnvelopingAlgebra.ι ℂ : Mat p q →ₗ⁅ℂ⁆ Ug p q).toLinearMap

def UgF (p q k : ℕ) : Submodule ℂ (Ug p q) :=
  Submodule.span ℂ {u | ∃ l : List (Mat p q), l.length ≤ k ∧ u = (l.map (ugι p q)).prod}

def indRel {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) :
    Submodule ℂ (TensorProduct ℂ (Ug p q) V) :=
  Submodule.span ℂ {z | ∃ (u : Ug p q) (Y : Mat p q) (v : V), IsKC Y ∧
    z = TensorProduct.tmul ℂ (u * ugι p q Y) v - TensorProduct.tmul ℂ u (act Y v)}

abbrev Ind {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) :
    Type := TensorProduct ℂ (Ug p q) V ⧸ indRel act

def indF {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (k : ℕ) : Submodule ℂ (Ind act) :=
  Submodule.span ℂ {z | ∃ u ∈ UgF p q k, ∃ v : V, z = (indRel act).mkQ (TensorProduct.tmul ℂ u v)}

def indFlt {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (k : ℕ) : Submodule ℂ (Ind act) := ⨆ j : ℕ, ⨆ _ : j < k, indF act j

def symProd {A : Type*} [Ring A] [Algebra ℂ A] {k : ℕ} (x : Fin k → A) : A :=
  ((k.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin k), (List.ofFn fun i => x (σ i)).prod

def symU (p q : ℕ) : MvPolynomial (PIx p q) ℂ →ₗ[ℂ] Ug p q :=
  (MvPolynomial.basisMonomials (PIx p q) ℂ).constr ℂ fun α =>
    symProd fun i : Fin (Finsupp.toMultiset α).toList.length =>
      ugι p q (Eab ((Finsupp.toMultiset α).toList.get i).1.1 ((Finsupp.toMultiset α).toList.get i).1.2)

def pLin {p q : ℕ} (Z : Mat p q) : MvPolynomial (PIx p q) ℂ :=
  ∑ ab : PIx p q, MvPolynomial.C (Z ab.1.1 ab.1.2) * MvPolynomial.X ab

def kOnS {p q : ℕ} (Y : Mat p q) : MvPolynomial (PIx p q) ℂ →ₗ[ℂ] MvPolynomial (PIx p q) ℂ :=
  (MvPolynomial.mkDerivation ℂ fun ab : PIx p q =>
    pLin (Y * Eab ab.1.1 ab.1.2 - Eab ab.1.1 ab.1.2 * Y)).toLinearMap

def symTens (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (k : ℕ) :
    Submodule ℂ (TensorProduct ℂ (MvPolynomial (PIx p q) ℂ) V) :=
  LinearMap.range (LinearMap.rTensor V (homog (PIx p q) k).subtype)

def admQ8 : Prop := ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsKLieAct act →
  ((⨆ k, indF act k) = ⊤) ∧
  ∀ k : ℕ,
    indF act k = indFlt act k ⊔
      (symTens p q V k).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q)) ∧
    (∀ z ∈ symTens p q V k, (indRel act).mkQ (LinearMap.rTensor V (symU p q) z) ∈ indFlt act k →
      z = 0) ∧
    ∀ Y, IsKC Y → ∀ z ∈ symTens p q V k,
      (indRel act).mkQ (LinearMap.rTensor V (symU p q)
          (LinearMap.rTensor V (kOnS Y) z + LinearMap.lTensor _ (act Y) z)) -
        (indRel act).mkQ (LinearMap.rTensor V (LinearMap.mulLeft ℂ (ugι p q Y))
          (LinearMap.rTensor V (symU p q) z)) ∈ indFlt act k

end PBW

def ARi {p q r s : ℕ} (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) : Prop :=
  (∃ Φ, JointHW (X.fock p q r s) (blattner lam) (blattner lam') Φ) ∧
  ∀ Φ v, JointHW (X.fock p q r s) (blattner lam) (blattner lam') Φ →
    UnitHW (X.ds p q lam) (blattner lam) v →
    Integrable (fun g => inner ℂ ((X.fock p q r s).ι Φ)
        ((X.fock p q r s).π (g, 1) ((X.fock p q r s).ι Φ)) * star (mcoef (X.ds p q lam) v g))
      (X.grp p q).haar ∧
    ∫ g, inner ℂ ((X.fock p q r s).ι Φ) ((X.fock p q r s).π (g, 1) ((X.fock p q r s).ι Φ)) *
        star (mcoef (X.ds p q lam) v g) ∂(X.grp p q).haar =
      ((‖opE (X.grp p q) (fun g => (X.fock p q r s).π (g, 1)) (eFun (X.ds p q lam) v)
          ((X.fock p q r s).ι Φ)‖ ^ 2 / (X.ds p q lam).fdeg : ℝ) : ℂ) ∧
    0 < ‖opE (X.grp p q) (fun g => (X.fock p q r s).π (g, 1)) (eFun (X.ds p q lam) v)
          ((X.fock p q r s).ι Φ)‖ ∧
    ((r = 0 ∨ s = 0) → opE (X.grp p q) (fun g => (X.fock p q r s).π (g, 1)) (eFun (X.ds p q lam) v)
          ((X.fock p q r s).ι Φ) = (X.fock p q r s).ι Φ ∧
      ∫ g, inner ℂ ((X.fock p q r s).ι Φ) ((X.fock p q r s).π (g, 1) ((X.fock p q r s).ι Φ)) *
        star (mcoef (X.ds p q lam) v g) ∂(X.grp p q).haar = (((X.ds p q lam).fdeg)⁻¹ : ℝ))

def ARii {p q r s : ℕ} (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) : Prop :=
  ∀ Φ, JointHW (X.fock p q r s) (blattner lam) (blattner lam') Φ →
    ∃ Tm : (X.ds p q lam).U.H →L[ℂ] (X.ds r s lam').U.H →L[ℂ] (X.fock p q r s).H,
      (∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y') ∧
      (∀ g h x y, (X.fock p q r s).π (g, h) (Tm x y) =
        Tm ((X.ds p q lam).U.π g x) ((X.ds r s lam').U.π h y)) ∧
      ∃ x y, inner ℂ (Tm x y) ((X.fock p q r s).ι Φ) ≠ 0

def ARiiiUp {p q r s : ℕ} (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) : Prop :=
  ∀ (MM : UGKMod r s) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ (X.ds p q lam).HK.V MM.M.V),
    IsIntw (X.fock p q r s) (X.ds p q lam).HK MM.M f → f ≠ 0 →
    (∃ N : Submodule ℂ MM.M.V, (∀ Z, ∀ y ∈ N, MM.M.act Z y ∈ N) ∧
      ∃ e : (X.ds r s lam').HK.V ≃ₗ[ℂ] N,
        (∀ Z x, ((e ((X.ds r s lam').HK.act Z x) : N) : MM.M.V) = MM.M.act Z (e x)) ∧
        LinearMap.range f = LinearMap.range (TensorProduct.map LinearMap.id N.subtype)) ∧
    ∀ Φ, JointHW (X.fock p q r s) (blattner lam) (blattner lam') Φ → f Φ ≠ 0 ∧
      ∀ f' : Pol p q r s →ₗ[ℂ] TensorProduct ℂ (X.ds p q lam).HK.V MM.M.V,
        IsIntw (X.fock p q r s) (X.ds p q lam).HK MM.M f' → f' Φ = f Φ → f' = f

def ARiiiDown {p q r s : ℕ} (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) : Prop :=
  ∀ (MM : UGKMod p q) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ MM.M.V (X.ds r s lam').HK.V),
    IsIntw (X.fock p q r s) MM.M (X.ds r s lam').HK f → f ≠ 0 →
    (∃ N : Submodule ℂ MM.M.V, (∀ Z, ∀ y ∈ N, MM.M.act Z y ∈ N) ∧
      ∃ e : (X.ds p q lam).HK.V ≃ₗ[ℂ] N,
        (∀ Z x, ((e ((X.ds p q lam).HK.act Z x) : N) : MM.M.V) = MM.M.act Z (e x)) ∧
        LinearMap.range f = LinearMap.range (TensorProduct.map N.subtype LinearMap.id)) ∧
    ∀ Φ, JointHW (X.fock p q r s) (blattner lam) (blattner lam') Φ → f Φ ≠ 0 ∧
      ∀ f' : Pol p q r s →ₗ[ℂ] TensorProduct ℂ MM.M.V (X.ds r s lam').HK.V,
        IsIntw (X.fock p q r s) MM.M (X.ds r s lam').HK f' → f' Φ = f Φ → f' = f

def ARiiiLine {p q r s : ℕ} (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) : Prop :=
  ∃ f₀ : Pol p q r s →ₗ[ℂ] TensorProduct ℂ (X.ds p q lam).HK.V (X.ds r s lam').HK.V,
    IsIntw (X.fock p q r s) (X.ds p q lam).HK (X.ds r s lam').HK f₀ ∧ f₀ ≠ 0 ∧
    ∀ f, IsIntw (X.fock p q r s) (X.ds p q lam).HK (X.ds r s lam').HK f → ∃ c : ℂ, f = c • f₀

def ARiv {p q r s : ℕ} (lam : Ix p q → ℚ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ r → i ≤ s → ∀ (MM : GKMod (r - i) (s - i))
    (f : Pol p q (r - i) (s - i) →ₗ[ℂ] TensorProduct ℂ (X.ds p q lam).HK.V MM.V),
    IsIntw (X.fock p q (r - i) (s - i)) (X.ds p q lam).HK MM f → f = 0

def ARv {p q r s : ℕ} (t : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) : Prop :=
  (¬ (∃ a, lam a = ((t : ℚ) + 1) / 2) ∨ ¬ (∃ a, lam a = -(((t : ℚ) + 1) / 2))) →
  ∀ i : ℕ, 1 ≤ i → i ≤ p → i ≤ q → ∀ (MM : GKMod (p - i) (q - i))
    (f : Pol (p - i) (q - i) r s →ₗ[ℂ] TensorProduct ℂ MM.V (X.ds r s lam').HK.V),
    IsIntw (X.fock (p - i) (q - i) r s) MM (X.ds r s lam').HK f → f = 0

def DataAR (t : ℕ) (al be ga de : List ℚ) : Prop := HypA t al be ga de ∧ HypG t al be ga de

def DataARm (t : ℕ) (al be ga de : List ℚ) : Prop := HypA t al be ga de ∧ HypGm t al be ga de

def ArchimedeanRallisFirst : Prop :=
  (∀ t al be ga de, DataAR t al be ga de → ARi X (lamA al be ga de) (lamA' t al be ga de)) ∧
  (∀ t al be ga de, DataARm t al be ga de → ARi X (lamA al be ga de) (lamM' t al be ga de))

def ArchimedeanRallisSecond : Prop :=
  (∀ t al be ga de, DataAR t al be ga de → ARii X (lamA al be ga de) (lamA' t al be ga de)) ∧
  (∀ t al be ga de, DataARm t al be ga de → ARii X (lamA al be ga de) (lamM' t al be ga de))

def ArchimedeanRallisUpDownLine : Prop :=
  (∀ t al be ga de, DataAR t al be ga de →
    ARiiiUp X (lamA al be ga de) (lamA' t al be ga de) ∧
    ARiiiDown X (lamA al be ga de) (lamA' t al be ga de) ∧
    ARiiiLine X (lamA al be ga de) (lamA' t al be ga de)) ∧
  (∀ t al be ga de, DataARm t al be ga de →
    ARiiiUp X (lamA al be ga de) (lamM' t al be ga de) ∧
    ARiiiDown X (lamA al be ga de) (lamM' t al be ga de) ∧
    ARiiiLine X (lamA al be ga de) (lamM' t al be ga de))

def ArchimedeanRallisFourth : Prop :=
  (∀ t al be ga de, DataAR t al be ga de →
    ARiv X (r := al.length + de.length + t) (s := ga.length + be.length) (lamA al be ga de)) ∧
  (∀ t al be ga de, DataARm t al be ga de →
    ARiv X (r := al.length + de.length) (s := ga.length + be.length + t) (lamA al be ga de))

def ArchimedeanRallisFifth : Prop :=
  (∀ t al be ga de, DataAR t al be ga de → ARv X t (lamA al be ga de) (lamA' t al be ga de)) ∧
  (∀ t al be ga de, DataARm t al be ga de → ARv X t (lamA al be ga de) (lamM' t al be ga de))

end StatementsA

section PartB

open NumberField IsDedekindDomain

abbrev Pl (F : Type) [Field F] [NumberField F] : Type :=
  InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)

def qNorm {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) : ℕ :=
  Nat.card (𝓞 F ⧸ w.asIdeal)

def wittIdx {E : Type} [Field E] [NumberField E] [StarRing E] (B : Formalism.BasicNotions.HSpace E) : ℕ :=
  sSup {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0}

section Helpers
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsSplit (w : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ P Q : HeightOneSpectrum (𝓞 E), P ≠ Q ∧
    P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal ∧
    Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal

def IsUnram (w : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal →
    Ideal.ramificationIdx P.asIdeal (𝓞 F) = 1


open Classical in
def etaV (w : HeightOneSpectrum (𝓞 F)) : ℂ := if IsSplit (E := E) w then 1 else -1

def dvLoc (n M : ℕ) (w : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  ∏ i ∈ Finset.Icc 1 n,
    (1 - (etaV (E := E) w) ^ (M + n - i) * (qNorm w : ℂ) ^ (-(2 * s + i)))⁻¹

end Helpers

structure RFObj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (A B : Formalism.BasicNotions.HSpace E) where
  GQ : Type
  [msG : MeasurableSpace GQ]

  muG : Measure GQ
  HQ : Type
  [msH : MeasurableSpace HQ]

  muH : Measure HQ
  [probH : IsProbabilityMeasure muH]
  GhQ : Type

  one : GhQ

  io : GQ → GQ → GhQ

  ht : GhQ → ℝ

  Sch : Type

  good : Sch → Prop

  SchD : Type
  factD : SchD → Prop

  tensor : Sch → Sch → SchD
  tensor_fact : ∀ φ₁ φ₂, good φ₁ → good φ₂ → factD (tensor φ₁ φ₂)

  thetaK : Sch → GQ → HQ → ℂ

  thetaD : SchD → GhQ → HQ → ℂ

  muInv : GQ → ℂ

  thetaD_io : ∀ φ₁ φ₂ g₁ g₂ h, thetaK φ₁ g₁ h * star (thetaK φ₂ g₂ h) =
    thetaD (tensor φ₁ φ₂) (io g₁ g₂) h * muInv g₂

  thetaT : SchD → Matrix (Fin A.rank) (Fin A.rank) E → HQ → ℂ

  thetaT_sum : ∀ ph h, HasSum (fun T : Matrix (Fin A.rank) (Fin A.rank) E => thetaT ph T h)
    (thetaD ph one h)

  dens : SchD → Pl F → Matrix (Fin A.rank) (Fin A.rank) E → ℂ

  Pi : Type

  Vec : Pi → Type
  form : ∀ π, Vec π → GQ → ℂ

  be : ∀ π, Vec π → Vec π → ℂ

  sph : ∀ π, Vec π → Vec π → Sch → Sch → Pl F → Prop

  psiXi : HeightOneSpectrum (𝓞 F) → Prop

  zconv : ∀ π, Vec π → Vec π → Sch → Sch → Pl F → ℂ → Prop

  Zv : ∀ π, Vec π → Vec π → Sch → Sch → Pl F → ℂ → ℂ

  Lv : Pi → Pl F → ℂ → ℂ

  dv : Pl F → ℂ → ℂ
  dv_def : ∀ w, IsUnram (E := E) w → ∀ s,
    dv (Sum.inr w) s = dvLoc (E := E) A.rank B.rank w s

  sat : Pi → HeightOneSpectrum (𝓞 F) → Fin A.rank → ℂ

  Eis : SchD → ℂ → GhQ → ℂ

attribute [instance] RFObj.msG RFObj.msH RFObj.probH

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] {A B : Formalism.BasicNotions.HSpace E} (O : RFObj F E A B)

def LS (π : O.Pi) (S : Finset (Pl F)) (s : ℂ) : ℂ :=
  ∏' v : {v : Pl F // v ∉ S}, O.Lv π v s

def dS (S : Finset (Pl F)) (s : ℂ) : ℂ := ∏' v : {v : Pl F // v ∉ S}, O.dv v s

end PartB

structure Prov (D : Formalism.BasicNotions.D7) extends ProvA where
  rf : letI := D.host.cmStar
    ∀ A B : Formalism.BasicNotions.HSpace D.host.E, RFObj D.host.F D.host.E A B

section Packet

variable (D : Formalism.BasicNotions.D7) (X : Prov D)

end Packet

end Formalism.MainNotions.SchurIrreducible
