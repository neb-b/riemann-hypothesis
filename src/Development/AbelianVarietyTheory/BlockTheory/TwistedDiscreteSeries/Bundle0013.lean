module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Formalism.LocalRingCardinality.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BarMatrix
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Mult Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SignCompat {p q n : ℕ} (ε : Fin n → Bool) (e : Ix p q ≃ Fin n) : Prop := ∀ a, ε (e a) = a.isLeft

def plainMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) : Matrix (Fin n) (Fin n) ℂ := Matrix.reindex e e g

def barMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.reindex e e (g.map (starRingEnd ℂ))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def toFrame (M : DSModel V S) (τ : D.what₂.Tau) (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Matrix (Fin V.rank) (Fin V.rank) ℂ := (M.fr τ)⁻¹ * Y * M.fr τ


open Classical in
structure Matches {p q : ℕ} {T : GrpData p q} (R : DSRep T) (M : DSModel V S) (τ : D.what₂.Tau)
    (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ → R.U.H) : Prop where

  grp : ∀ (g : T.G) (x : M.H τ),
    R.U.π g (U x) = ((T.sq g : ℂˣ) : ℂ) ^ (-m) • U (M.σ τ (φ ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x)

  kfin : ∀ x : M.H τ, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) x ↔ U x ∈ Set.range R.ι

  smooth : ∀ x : M.H τ, U x ∈ Set.range R.ι → SmoothVec (lieAt V τ) (M.rep τ) x

  lie : (fun Z => toFrame M τ (φ Z)) '' upq p q = lieAt V τ

  der : ∀ Z ∈ upq p q, ∀ (v : R.HK.V) (x : M.H τ), U x = R.ι v →
    U (dRep (M.rep τ) (toFrame M τ (φ Z)) x) = R.ι (R.HK.act Z v + ((m : ℂ) / 2 * Z.trace) • v)

  derT : ∀ Z ∈ upq p q, ∀ (v : R.HK.V) (x : M.Vec) (y : M.sm τ), U (x τ : M.H τ) = R.ι v →
    U (y : M.H τ) = R.ι (R.HK.act Z v + ((m : ℂ) / 2 * Z.trace) • v) →
    DerT M τ (toFrame M τ (φ Z)) (PiTensorProduct.tprod ℂ x) (PiTensorProduct.tprod ℂ (Function.update x τ y))

def HidaSetting (X : ProvA) (p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ) (S : D.what₂.Tau → SPar) (τ : D.what₂.Tau) : Prop :=
  1 ≤ p + q ∧ l₁.length = p ∧ l₂.length = q ∧ IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ) ∧
    HasParam (X.ds p q (ofBlocks l₁ l₂)) (ofBlocks l₁ l₂) ∧ S τ = dualPar (GlobalTheory.Chain.signed l₁ l₂ c)

def SourceBridge (D : D7) : Prop :=
  ∀ (X : ProvA) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ), HidaSetting X p q l₁ l₂ c S τ →
    (∃ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e) ∧
    ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∀ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e →
      ∃ U : M.H τ ≃ₗᵢ[ℂ] (X.ds p q (ofBlocks l₁ l₂)).U.H,
        Matches (X.ds p q (ofBlocks l₁ l₂)) M τ (barMat e) m U

def TargetBridge (D : D7) : Prop :=
  ∀ (X : ProvA) (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (τ : D.what₂.Tau)
    (r s : ℕ) (l₁ l₂ : List ℚ) (c : ℚ), HidaSetting X r s l₁ l₂ c S τ →
    (∃ e : Ix r s ≃ Fin W.rank, SignCompat (M.ε τ) e) ∧
    ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∀ e : Ix r s ≃ Fin W.rank, SignCompat (M.ε τ) e →
      ∃ U : M.H τ ≃ₗᵢ⋆[ℂ] (X.ds r s (ofBlocks l₁ l₂)).U.H,
        Matches (X.ds r s (ofBlocks l₁ l₂)) M τ (plainMat e) m U

def ModelsAreCoverSeries (D : D7) : Prop := SourceBridge D ∧ TargetBridge D

theorem reindex_form {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) :
    Matrix.reindex e e (Formalism.UG.Jpq p q) = Formalism.REAL.Jm ε := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  have ha := h a
  rcases a with a | a <;> rcases b with b | b <;>
    simp_all [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp_all

theorem plainMat_mem {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) {g : Mat p q}
    (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q) : plainMat e g ∈ Formalism.MainNotions.S.UJset ε := by
  change (plainMat e g)ᴴ * Formalism.REAL.Jm ε * plainMat e g = Formalism.REAL.Jm ε
  rw [← reindex_form h]
  simp only [plainMat, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hg]

theorem barMat_mem {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) {g : Mat p q}
    (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q) : barMat e g ∈ Formalism.MainNotions.S.UJset ε := by
  refine plainMat_mem h ?_
  have hJ : (Formalism.UG.Jpq p q).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp [Formalism.UG.Jpq, Matrix.one_apply] <;> split_ifs <;> simp
  have h1 := congrArg (fun A : Mat p q => A.map (starRingEnd ℂ)) hg
  simp only [Matrix.map_mul, hJ] at h1
  exact h1

end GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ContractionTensorModels
section
noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF]

def IsIsoBilin (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) : Prop :=
  ∀ x x' y y', ⟪Tm x y, Tm x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ

def IsEquivBilin {G₁ G₂ : Type} [Group G₁] [Group G₂] (π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁)) (π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂))
    (ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)) (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) : Prop :=
  ∀ g h x y, Tm (π₁ g x) (π₂ h y) = ρ (g, h) (Tm x y)

def IsContr (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) (It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁) : Prop :=
  ∀ φ y x, ⟪x, It φ y⟫_ℂ = ⟪Tm x y, φ⟫_ℂ

def HasWeakDer {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (c : ℝ → H) (v' : H) : Prop :=
  ∀ w : H, HasDerivAt (fun t : ℝ => ⟪w, c t⟫_ℂ) ⟪w, v'⟫_ℂ 0

def IsFiniteVec {G H : Type} [Group G] [AddCommGroup H] [Module ℂ H] (K : Subgroup G) (π : G → H → H) (v : H) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => π k v))

def imSpan (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) : Submodule ℂ FF :=
  Submodule.span ℂ (Set.range fun p : H₁ × H₂ => Tm p.1 p.2)

structure ContrProps {G₁ G₂ : Type} [Group G₁] [Group G₂] (π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁))
    (π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂)) (ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)) (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF)
    (It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁) : Prop where

  norm_le : ∀ φ y, ‖It φ y‖ ≤ ‖φ‖ * ‖y‖

  equiv : ∀ g φ y, It (ρ (g, 1) φ) y = π₁ g (It φ y)

  inv : ∀ h φ y, It (ρ (1, h) φ) (π₂ h y) = It φ y

  der₁ : ∀ (c : Multiplicative ℝ →* G₁) φ φ' y,
    HasDerivAt (fun t : ℝ => ρ (c (Multiplicative.ofAdd t), 1) φ) φ' 0 →
      HasDerivAt (fun t : ℝ => π₁ (c (Multiplicative.ofAdd t)) (It φ y)) (It φ' y) 0

  weakDer₁ : ∀ (c : Multiplicative ℝ →* G₁) φ φ' y,
    HasWeakDer (fun t : ℝ => ρ (c (Multiplicative.ofAdd t), 1) φ) φ' →
      HasWeakDer (fun t : ℝ => π₁ (c (Multiplicative.ofAdd t)) (It φ y)) (It φ' y)

  der₂ : ∀ (c : Multiplicative ℝ →* G₂) φ φ' y y',
    HasWeakDer (fun t : ℝ => ρ (1, c (Multiplicative.ofAdd t)) φ) φ' →
      HasWeakDer (fun t : ℝ => π₂ (c (Multiplicative.ofAdd t)) y) y' → It φ' y + It φ y' = 0

  ne : ∀ φ, φ ∉ (imSpan Tm)ᗮ → ∀ Y : Set H₂, Dense Y → ∃ y ∈ Y, It φ y ≠ 0

  fin : ∀ (K : Subgroup G₁) φ y, IsFiniteVec K (fun g => ρ (g, 1)) φ → IsFiniteVec K (fun g => π₁ g) (It φ y)

end Hilbert

def ContrHilbert : Prop :=
  ∀ (H₁ H₂ FF : Type)
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [NormedAddCommGroup FF] [InnerProductSpace ℂ FF] [CompleteSpace FF]
    (G₁ G₂ : Type) [Group G₁] [Group G₂] (π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁)) (π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂))
    (ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)) (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF),
    IsIsoBilin Tm → IsEquivBilin π₁ π₂ ρ Tm →
      (∃! It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It) ∧
      ∀ It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It → ContrProps π₁ π₂ ρ Tm It

def IsTensorIt {ι : Type} [Fintype ι] {σ : ι → Type} {Var : Type} (e : (Σ τ, σ τ) ≃ Var) {A B : ι → Type}
    [∀ τ, AddCommGroup (A τ)] [∀ τ, Module ℂ (A τ)] [∀ τ, AddCommGroup (B τ)] [∀ τ, Module ℂ (B τ)]
    (Itl : ∀ τ, MvPolynomial (σ τ) ℂ →ₗ[ℂ] A τ →ₗ[ℂ] B τ)
    (It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ) : Prop :=
  ∀ (P : ∀ τ, MvPolynomial (σ τ) ℂ) (v : ∀ τ, A τ),
    It (∏ τ, MvPolynomial.rename (fun s => e ⟨τ, s⟩) (P τ)) (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ fun τ => Itl τ (P τ) (v τ)

def ContrTensor : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : ι → Type) (Var : Type) (e : (Σ τ, σ τ) ≃ Var) (A B : ι → Type)
    [∀ τ, AddCommGroup (A τ)] [∀ τ, Module ℂ (A τ)] [∀ τ, AddCommGroup (B τ)] [∀ τ, Module ℂ (B τ)]
    (Itl : ∀ τ, MvPolynomial (σ τ) ℂ →ₗ[ℂ] A τ →ₗ[ℂ] B τ),
    ∃ It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ,
      IsTensorIt e Itl It ∧ ((∀ τ, Itl τ ≠ 0) → It ≠ 0)

def Contraction : Prop := ContrHilbert ∧ ContrTensor

section Models

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Models

theorem contrProps_of {H₁ H₂ FF : Type}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [NormedAddCommGroup FF] [InnerProductSpace ℂ FF]
    {G₁ G₂ : Type} [Group G₁] [Group G₂] {π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁)} {π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂)}
    {ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)} {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm)
    (hE : IsEquivBilin π₁ π₂ ρ Tm) {It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁} (hC : IsContr Tm It) :
    ContrProps π₁ π₂ ρ Tm It := by
  have hn : ∀ x y, ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
    intro x y
    have h := hI x x y y
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
    have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hb : ∀ φ y, ‖It φ y‖ ≤ ‖φ‖ * ‖y‖ := by
    intro φ y
    have h := hC φ y (It φ y)
    have h1 : ‖It φ y‖ * ‖It φ y‖ ≤ ‖It φ y‖ * (‖φ‖ * ‖y‖) := by
      have := norm_inner_le_norm (𝕜 := ℂ) (Tm (It φ y) y) φ
      rw [← h, hn, inner_self_eq_norm_sq_to_K] at this
      simp at this
      nlinarith
    rcases (norm_nonneg (It φ y)).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · exact le_of_mul_le_mul_left h1 h0
  have hall : ∀ g h φ y, It (ρ (g, h) φ) (π₂ h y) = π₁ g (It φ y) := by
    intro g h φ y
    apply ext_inner_left ℂ
    intro x
    obtain ⟨x, rfl⟩ := (π₁ g).surjective x
    rw [hC, hE, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map, hC]
  have he : ∀ g φ y, It (ρ (g, 1) φ) y = π₁ g (It φ y) := fun g φ y => by simpa using hall g 1 φ y
  have hi : ∀ h φ y, It (ρ (1, h) φ) (π₂ h y) = It φ y := fun h φ y => by simpa using hall 1 h φ y
  refine ⟨hb, he, hi, ?_, ?_, ?_, ?_, ?_⟩
  · intro c φ φ' y hd
    let L : FF →L[ℂ] H₁ := (It.flip y).mkContinuous ‖y‖ fun φ => by simpa [mul_comm] using hb φ y
    have := ((L.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hd
    simpa [L, Function.comp_def, he] using this
  · intro c φ φ' y hd w
    simpa only [← he, hC _ _ _] using hd (Tm w y)
  · intro c φ φ' y y' hd hd'
    apply ext_inner_left ℂ
    intro x
    let ℓ : H₂ →L[ℂ] ℂ := ((innerₛₗ ℂ φ) ∘ₗ Tm x).mkContinuous (‖φ‖ * ‖x‖) fun y => by
      simpa [hn, mul_assoc] using norm_inner_le_norm (𝕜 := ℂ) φ (Tm x y)
    obtain ⟨w, hw⟩ := (InnerProductSpace.toDual ℂ H₂).surjective ℓ
    have hw' : ∀ z, ⟪w, z⟫_ℂ = ⟪φ, Tm x z⟫_ℂ := fun z => by
      have := congrArg (fun f : H₂ →L[ℂ] ℂ => f z) hw
      simpa [ℓ] using this
    have h1 := hd (Tm x y)
    have h2 := ((hd' w).scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp)).star
    have h3 : (fun t : ℝ => ⟪Tm x y, ρ (1, c (Multiplicative.ofAdd t)) φ⟫_ℂ) =
        fun t : ℝ => star (((fun t : ℝ => ⟪w, π₂ (c (Multiplicative.ofAdd t)) y⟫_ℂ) ∘ Neg.neg) t) := by
      funext t
      have hy : y = π₂ (c (Multiplicative.ofAdd t)) (π₂ (c (Multiplicative.ofAdd (-t))) y) := by
        change y = (π₂ _ * π₂ _) y
        rw [← map_mul, ← map_mul, ← ofAdd_add]; simp
      simp only [Function.comp, hw']
      rw [← hC, Complex.star_def, inner_conj_symm, ← hC]
      conv_lhs => rw [hy, hi]
    rw [h3] at h1
    have h4 := h1.unique h2
    rw [inner_add_right, hC, hC, h4, hw']
    simp
  · intro φ hφ Y hY
    by_contra hcon
    push_neg at hcon
    apply hφ
    let L : H₂ →SL[starRingEnd ℂ] H₁ := (It φ).mkContinuous ‖φ‖ (hb φ)
    have h0 : ∀ y, It φ y = 0 := fun y =>
      congrFun (Continuous.ext_on hY L.continuous (continuous_const (y := (0 : H₁))) hcon) y
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨p, rfl⟩ := hu; simp [← hC φ, h0]
    | zero => simp
    | add a b _ _ ha hb => simp [inner_add_left, ha, hb]
    | smul a b _ hb => simp [inner_smul_left, hb]
  · intro K φ y hf
    unfold IsFiniteVec at *
    have : (Set.range fun k : K => π₁ k (It φ y)) = It.flip y '' Set.range fun k : K => ρ (k, 1) φ := by
      rw [← Set.range_comp]; congr 1; funext k; simp [he]
    rw [this, ← Submodule.map_span]
    infer_instance

end GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DefiniteUnitaryAction
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
open scoped InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiniteUnitaryAction

def IsUnitaryRep {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Representation ℂ G H) : Prop :=
  ∀ (g : G) (x y : H), inner ℂ (ρ g x) (ρ g y) = inner ℂ x y

section ClassSum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ)

def pairAt (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (σ (S.bV.repr x i)) * σ (S.gramV i j) * σ (S.bV.repr y j)

def classSumAt (f f' : S.Forms) : ℂ :=
  ∑ c, ((S.wt c : ℂ))⁻¹ * pairAt S σ ((f : S.Cl → S.V) c) ((f' : S.Cl → S.V) c)

def IsUnitaryAt {G : Type} [Group G] (r : Representation K G S.Forms) : Prop :=
  ∀ (g : G) (f f' : S.Forms), classSumAt S σ (r g f) (r g f') = classSumAt S σ f f'

end ClassSum

section Statement

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}

structure DefiniteUnitary (A : FamIn D.what₂.LL G Pl0 T D.R.m) : Prop where

  what₂ : ∀ (t : T) (σ : D.what₂.LL →+* ℂ), IsUnitaryAt (A.MtildeCSD t) σ (A.leftGroupActionRight t)

  lifts : ∀ (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ), IsUnitaryAt (A.MtCSD i t) σ (A.leftGroupActionLift i t)

variable {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure ActsUnitarily (R : RealDat D A Ks) : Prop where

  what₂ : IsUnitaryRep R.gE

  formsW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), IsUnitaryRep (R.gW i σ)

  definite : DefiniteUnitary A

end Statement

section Basic₂

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.DefiniteUnitaryAction

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HolomorphicLowestType
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT

namespace GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def LowIrr (M : DSModel V S) : Prop :=
  ∀ τ, IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (lowKSub (M.ε τ) (M.lam τ) (M.σ τ))

end Model

section Base

variable {D : D7}

abbrev pW (i : Fin D.R.m) (τ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D τ)).1

abbrev qW (i : Fin D.R.m) (τ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D τ)).2

theorem pW_add_qW (i : Fin D.R.m) (τ : D.what₂.Tau) : pW i τ + qW i τ = (Wc D i).rank :=
  sig_sum _ (D.sp.W_sig _) _

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


end Base

end GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift Formalism.IndefR.Links
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SplitsCompletely (D : D7) (p : ℕ) : Prop :=
  p.Prime ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    Ideal.absNorm w.asIdeal = p ∧ (p : 𝓞 D.host.E) ∉ w.asIdeal ^ 2

def PsiUnramAt (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ α : Af D.host.F, (∀ v', v' ≠ v → evalV D.host.F v' α = 0) →
    ((∀ β ∈ intAf D.host.F, ψ (pairA D.host.F 0 (α * β)) = 1) ↔
      evalV D.host.F v α ∈ v.adicCompletionIntegers D.host.F)

def SideCond (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  IsSplit (E := D.host.E) v ∧ (2 : 𝓞 D.host.F) ∉ v.asIdeal ∧ PsiUnramAt ψ v ∧
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → w.valuation D.host.E D.host.xi0 = 1

def excluded (q t : ℕ) : Set ℂ :=
  {(((q : ℝ) ^ (((t : ℝ) - 1) / 2) : ℝ) : ℂ), (((q : ℝ) ^ (-(((t : ℝ) - 1) / 2)) : ℝ) : ℂ),
    (((q : ℝ) ^ (((t : ℝ) + 1) / 2) : ℝ) : ℂ), (((q : ℝ) ^ (-(((t : ℝ) + 1) / 2)) : ℝ) : ℂ)}

section Cusp

variable (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]

variable {V ν} {W : Submodule ℂ (DividedPowerChartLift V ν)}


end Cusp

section Chain

variable (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
  (th : ∀ k, GA D (Yc D k) → GA D (Yc D (k + 1)) → (WO (Yc D k) (Yc D (k + 1)) → ℂ) → ℂ)
  (ν : ∀ k, Measure (GA D (Yc D k))) [∀ k, (ν k).IsHaarMeasure] [∀ k, (ν k).IsMulRightInvariant]
  (𝓕 : ∀ k, Set (GA D (Yc D k))) (σ : Submodule ℂ (DividedPowerChartLift (Yc D 0) (ν 0)))

end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitarySphericalReps
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsPosReal (z : ℂ) : Prop := z.im = 0 ∧ 0 < z.re

variable {D : D7}




end GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps

end
end

