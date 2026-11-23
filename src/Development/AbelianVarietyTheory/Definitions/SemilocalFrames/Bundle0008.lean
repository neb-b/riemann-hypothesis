module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.LocalToGlobal.HermitianForms.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Dec

variable {n : ℕ}

def muInt (lam : Fin n → ℝ) (a : Fin n) : ℤ := ⌊lam a + Formalism.QuantumDeterminants.rhoStd n a⌋

def sInt (lam : Fin n → ℝ) (i : Fin n) : ℤ :=
  muInt lam i - (if h : i.val + 1 < n then muInt lam ⟨i.val + 1, h⟩ else 0)

def Omega (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {z | ∀ i : Fin n, leadMinor z (i.val + 1) i.isLt ≠ 0}

def Phi (lam : Fin n → ℝ) (z : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ i : Fin n, leadMinor z (i.val + 1) i.isLt ^ (-(sInt lam i))

def IsLo (b : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j, i < j → b i j = 0

def IsUp (b : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ i j, j < i → b i j = 0

def KC (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {y | IsUnit y ∧ y * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * y}

def IsTau (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) : Prop :=
  FiniteDimensional ℂ W ∧ Formalism.QuantumDeterminants.IsCRepOn (KC ε) τ ∧
    (∀ u v : W, DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => ⟪u, τ (Matrix.of y) v⟫_ℂ)
      {y | Matrix.of y ∈ KC ε}) ∧
    (∀ y ∈ KC ε, ∀ u v : W, ⟪τ y u, v⟫_ℂ = ⟪u, τ yᴴ v⟫_ℂ) ∧
    (∀ S : Submodule ℂ W, IsKStableOn ε τ S → S = ⊥ ∨ S = ⊤) ∧
    ‖w‖ = 1 ∧ IsWtOn (Formalism.REAL.Kset ε) τ (-abelian₂) w ∧
    ∀ y ∈ KC ε, IsLoUni y → τ y w = w

def ps (ε : Fin n → Bool) (lam : Fin n → ℝ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (z : Matrix (Fin n) (Fin n) ℂ) : W →L[ℂ] W :=
  (Module.finrank ℂ W : ℂ) • ∫ k : Formalism.REAL.KG ε,
    Phi lam ((Formalism.REAL.toMK k)⁻¹ * z * Formalism.REAL.toMK k) •
      (innerSL ℂ (τ (Formalism.REAL.toMK k) w)).smulRight (τ (Formalism.REAL.toMK k) w) ∂(Formalism.REAL.muK ε)

def U1 (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {z | ∀ k ∈ Formalism.REAL.Kset ε, k⁻¹ * z * k ∈ Omega n}

def posPart (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Classical.epsilon fun p : Matrix (Fin n) (Fin n) ℂ => p.PosDef ∧ p * p = gᴴ * g

def Psi (ε : Fin n → Bool) (lam : Fin n → ℝ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (g : Matrix (Fin n) (Fin n) ℂ) : W →L[ℂ] W :=
  (τ (g * (posPart g)⁻¹)).comp (ps ε lam τ w (posPart g))

def cycWord {m : ℕ} (a : Fin (m + 1) → Fin n) : List (Fin n × Fin n) :=
  List.ofFn fun i => (a i, a (finRotate (m + 1) i))

def gelf (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => ∑ a : Fin (m + 1) → Fin n, Formalism.REAL.Eword ε (cycWord a) f g

def Rhol (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun z => deriv (fun t : ℂ => F (z * NormedSpace.exp (t • Matrix.single a b (1 : ℂ)))) 0

def RholW (w : List (Fin n × Fin n)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  w.foldr (fun p G => Rhol p.1 p.2 G) F

def gelfH (m : ℕ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun z => ∑ a : Fin (m + 1) → Fin n, RholW (cycWord a) F z

def gelfVal (χ : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ a, ∑ b, (Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2) ^ k) a b

def IsZEigen (ε : Fin n → Bool) (χ : Fin n → ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  Formalism.REAL.SmoothOnG ε f ∧ ∀ m : ℕ, ∀ g ∈ UJset ε, gelf ε m f g = gelfVal χ (m + 1) * f g

def IsZFinite (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  Formalism.REAL.SmoothOnG ε f ∧ ∀ m : ℕ, ∃ (N : ℕ) (c : Fin N → ℂ), ∀ g ∈ UJset ε,
    (gelf ε m)^[N] f g = ∑ i, c i * (gelf ε m)^[i.val] f g

def IsBiKFin (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {F : Formalism.REAL.UJ ε → ℂ |
    ∃ k₁ ∈ Formalism.REAL.Kset ε, ∃ k₂ ∈ Formalism.REAL.Kset ε, F = fun g => f (k₁ * umat g * k₂)})

def HasInfChar (ε : Fin n → Bool) (χ : Fin n → ℂ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ v w : H, IsKFin ε σ v → IsKFin ε σ w →
    IsZEigen ε χ (fun g => ⟪w, σ g v⟫_ℂ)

def IsSqIntIrr (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  CompleteSpace H ∧ Nontrivial H ∧ IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ ∧ IsSqIntOn ε σ

def UEquiv (ε : Fin n → Bool) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) : Prop :=
  ∃ T : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ v, T (σ g v) = σ' g (T v)

def decHS (h : ℝ) (q : ℕ) (t : ℝ) : ℝ := Real.exp (-(h / 8) * min (t ^ 2) (t / Real.sqrt (2 * q)))

def stdRep (y : Matrix (Fin n) (Fin n) ℂ) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) y

theorem stdRep_apply (y : Matrix (Fin n) (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    stdRep y v i = ∑ j, y i j * v j := rfl

theorem gelfVal_succ (χ : Fin n → ℂ) (k : ℕ) :
    gelfVal χ (k + 1) = ∑ a, ((Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2) ^ k) *ᵥ
      (fun c => χ c - (Formalism.QuantumDeterminants.rhoStd n c : ℂ))) a := by
  have h : Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2) *ᵥ (fun _ => (1 : ℂ)) =
      fun c => χ c - (Formalism.QuantumDeterminants.rhoStd n c : ℂ) := by
    funext a
    have e : ∀ b : Fin n, (if a = b then χ a + ((n : ℂ) - 1) / 2 else if a < b then -1 else 0) =
        (if a = b then χ a + ((n : ℂ) - 1) / 2 else 0) - (if b ∈ Finset.Ioi a then 1 else 0) := by
      intro b
      by_cases h1 : a = b
      · subst h1; simp
      · by_cases h2 : a < b <;> simp [h1, h2]
    have hc : (((Finset.Ioi a).card : ℕ) : ℂ) = (n : ℂ) - 1 - (a : ℕ) := by
      have := a.isLt
      rw [Fin.card_Ioi, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    simp only [Matrix.mulVec, dotProduct, Formalism.REAL.Amat, Matrix.of_apply, mul_one, e,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, hc, Formalism.QuantumDeterminants.rhoStd]
    push_cast
    ring
  rw [← h, Matrix.mulVec_mulVec, ← pow_succ]
  simp [gelfVal, Matrix.mulVec, dotProduct]

theorem Eword_const (ε : Fin n → Bool) (c : ℂ) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    Formalism.REAL.Eword ε (p :: w) (fun _ => c) = fun _ => 0 := by
  induction w generalizing p with
  | nil => funext g; simp [Formalism.REAL.Eword, Formalism.REAL.Eab, Formalism.REAL.Ec, Formalism.REAL.Rd]
  | cons q w ih =>
    funext g
    rw [Formalism.REAL.Eword]
    simp only [ih q]
    simp [Formalism.REAL.Eab, Formalism.REAL.Ec, Formalism.REAL.Rd]

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Smooth


open scoped MatrixOrder in
theorem posPart_posDef_sq {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) :
    (posPart g).PosDef ∧ posPart g * posPart g = gᴴ * g := by
  apply Classical.epsilon_spec (p := fun p : Matrix (Fin n) (Fin n) ℂ => p.PosDef ∧ p * p = gᴴ * g)
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ gᴴ * g := (Matrix.posSemidef_conjTranspose_mul_self g).nonneg
  have hs : CFC.sqrt (gᴴ * g) * CFC.sqrt (gᴴ * g) = gᴴ * g := CFC.sqrt_mul_sqrt_self _ h0
  refine ⟨CFC.sqrt (gᴴ * g), ?_, hs⟩
  rw [(Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg (gᴴ * g))).posDef_iff_isUnit]
  have hu : IsUnit (gᴴ * g) := (by simpa [Matrix.star_eq_conjTranspose] using hg.star : IsUnit gᴴ).mul hg
  rw [← hs] at hu
  exact isUnit_of_mul_isUnit_left hu


open scoped MatrixOrder in
theorem posPart_eq_of_sq {g p : Matrix (Fin n) (Fin n) ℂ} (hp : p.PosDef) (h : p * p = gᴴ * g) :
    posPart g = p := by
  obtain ⟨h1, h2⟩ : (posPart g).PosDef ∧ posPart g * posPart g = gᴴ * g :=
    Classical.epsilon_spec (p := fun p : Matrix (Fin n) (Fin n) ℂ => p.PosDef ∧ p * p = gᴴ * g) ⟨p, hp, h⟩
  rw [← CFC.sqrt_unique h2 h1.posSemidef.nonneg, ← CFC.sqrt_unique h hp.posSemidef.nonneg]

theorem posPart_unitary_mul {k p : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hp : p.PosDef) : posPart (k * p) = p := by
  apply posPart_eq_of_sq hp
  have h : kᴴ * k = 1 := Unitary.star_mul_self_of_mem hk
  rw [Matrix.conjTranspose_mul, hp.1.eq, Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ, h, Matrix.one_mul]

theorem Psi_unitary_mul (ε : Fin n → Bool) (lam : Fin n → ℝ) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W)
    {k p : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (hp : p.PosDef) :
    Psi ε lam τ w (k * p) = (τ k).comp (ps ε lam τ w p) := by
  unfold Psi
  rw [posPart_unitary_mul hk hp,
    Matrix.mul_nonsing_inv_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det p).1 hp.isUnit)]

theorem Phi_at_one (lam : Fin n → ℝ) : Phi lam 1 = 1 := by
  unfold Phi leadMinor
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Matrix.submatrix_one _ (Fin.castLE_injective _)]
  simp

end GlobalTheory.Dec
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
section
noncomputable section

open Formalism.BasicNotions Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace GlobalTheory.St.G

abbrev Ad (F : Type) [Field F] [NumberField F] : Type := FiniteAdeleRing (𝓞 F) F

abbrev OAd (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : Subring (E ⊗[F] Ad F) :=
  tensInt (F := F) (Ad F) (intOE E) (intAd F)

def SplitsIn (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  (placesOver E p).ncard = Module.finrank ℚ E

section Lat

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

abbrev hat (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F) :=
  latS (F := F) (Ad F) (OAd F E) L

variable {F}

abbrev loc (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (intV E v) (Fin n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) L

def IsLat (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  Module.Finite (𝓞 E) L ∧ Submodule.span E (L : Set (Fin n → E)) = ⊤

def prVec (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E ⊗[F] Ad F) : Fin n → E ⊗[F] v.adicCompletion F :=
  fun i => prV (E := E) v (x i)

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

abbrev dualL (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)

def hR (R : Type) [CommRing R] [Algebra F R] (x y : Fin n → E ⊗[F] R) : E ⊗[F] R :=
  hform (sigR σ R) (J.map (inclE (F := F) R)) x y

def TLat (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  IsLat L ∧ (∀ x ∈ L, x ∈ dualSet (σ : E →+* E) J L) ∧ (∀ y ∈ dualSet (σ : E →+* E) J L, (T : E) • y ∈ L) ∧
  L.toAddSubgroup.relIndex (dualL σ J L).toAddSubgroup = T ^ (2 * f) ∧
  ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∃ x ∈ loc v (dualL σ J L), x ∉ loc v L

def SelfDualAt (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ y, y ∈ loc v L ↔ ∀ z ∈ loc v L, hR σ J (v.adicCompletion F) z y ∈ intV E v

end Lat

def InModL {A : Type} [CommRing A] {O : Subring A} {n : ℕ} (Λ : Submodule O (Fin n → A)) (m : ℕ)
    (S : Set (Fin n → A)) (x : Fin n → A) : Prop :=
  ∃ s ∈ Submodule.span O S, ∃ z ∈ Λ, x = s + (m : A) • z

def supSum {A : Type} [CommRing A] {n k : ℕ} (h : (Fin n → A) → (Fin n → A) → A) (b bd : Fin k → Fin n → A)
    (y : Matrix (Fin n) (Fin n) A) : A :=
  ∑ i : Fin k, if hi : i.1 + 1 < k then h (bd i) (y *ᵥ b ⟨i.1 + 1, hi⟩) else 0

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

structure AdFrame (Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (g k : ℕ) where
  eps : E ⊗[F] Ad F
  eps_idem : eps * eps = eps
  eps_orth : eps * sigR σ (Ad F) eps = 0
  eps_int : eps ∈ OAd F E
  eps_full : ∀ y ∈ Λ, ∃ z ∈ Λ, (1 - eps - sigR σ (Ad F) eps) • y = (g : E ⊗[F] Ad F) • z
  b : Fin k → Fin n → E ⊗[F] Ad F
  bd : Fin k → Fin n → E ⊗[F] Ad F
  b_mem : ∀ i, b i ∈ Λ
  bd_mem : ∀ i, bd i ∈ Λ
  b_eps : ∀ i, b i = eps • b i
  bd_eps : ∀ i, bd i = sigR σ (Ad F) eps • bd i
  dual : ∀ i j, ∃ t ∈ OAd F E, hR σ J (Ad F) (bd i) (b j) - (if i = j then eps else 0) = (g : E ⊗[F] Ad F) * t
  span : ∀ y ∈ Λ, InModL Λ g (Set.range b ∪ Set.range bd) y
  psi : E ⊗[F] Ad F → ℂ
  psi_add : ∀ x y, psi (x + y) = psi x * psi y
  psi_int : ∀ x ∈ OAd F E, psi x = 1
  psi_rat : ∀ x : E, psi (inclE (F := F) (Ad F) x) *
    Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E x : ℚ) : ℂ)) = 1

variable {σ J} {Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)} {g k : ℕ}

def AdFrame.InK (Fr : AdFrame σ J Λ g k) (y : GL (Fin n) (E ⊗[F] Ad F)) : Prop :=
  y ∈ stabGL Λ ∧
  (∀ x, (∀ z ∈ Λ, hR σ J (Ad F) z x ∈ OAd F E) → (y.1 - 1) *ᵥ x ∈ Λ) ∧
  ∀ i : Fin k, InModL Λ g (Fr.b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ Fr.b i)

def AdFrame.chi (Fr : AdFrame σ J Λ g k) (y : GL (Fin n) (E ⊗[F] Ad F)) : ℂ :=
  Fr.psi (algebraMap F (E ⊗[F] Ad F) ((g : F)⁻¹) * supSum (hR σ J (Ad F)) Fr.b Fr.bd y.1)

def AdFrame.LocK (Fr : AdFrame σ J Λ g k) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F))
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∀ i : Fin k, InModL (loc v L) g ((fun j => prVec v (Fr.b j)) '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ prVec v (Fr.b i))

def AdFrame.locChi (Fr : AdFrame σ J Λ g k) (v : HeightOneSpectrum (𝓞 F))
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : ℂ :=
  Fr.psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) *
    supSum (hR σ J (v.adicCompletion F)) (fun j => prVec v (Fr.b j)) (fun j => prVec v (Fr.bd j)) y.1))

end Frame

end GlobalTheory.St.G

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

abbrev UT (r : ℕ) := {p : Fin r × Fin r // p.1 < p.2}

def upper {r : ℕ} (x : UT r → ℂ) : Matrix (Fin r) (Fin r) ℂ := fun a b =>
  if h : a < b then x ⟨(a, b), h⟩ else if a = b then 1 else 0

abbrev UTin {r : ℕ} (β : Fin r → ℕ) := {p : UT r // β p.1.1 = β p.1.2}

abbrev UToff {r : ℕ} (β : Fin r → ℕ) := {p : UT r // β p.1.1 ≠ β p.1.2}

def upperIn {r : ℕ} (β : Fin r → ℕ) (x : UTin β → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  upper fun p => if h : β p.1.1 = β p.1.2 then x ⟨p, h⟩ else 0

def upperOff {r : ℕ} (β : Fin r → ℕ) (x : UToff β → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  upper fun p => if h : β p.1.1 ≠ β p.1.2 then x ⟨p, h⟩ else 0

def skewM {r : ℕ} (s : UT r → ℂ) (t : Fin r → ℝ) : Matrix (Fin r) (Fin r) ℂ := fun a b =>
  if h : a < b then s ⟨(a, b), h⟩ else if h' : b < a then -star (s ⟨(b, a), h'⟩) else (t a : ℂ) * Complex.I

def uEmb (k r : ℕ) (u : Matrix (Fin r) (Fin r) ℂ) : Mat k r := fun i j =>
  if h : i.val < r ∧ j.val < r then u ⟨i.val, h.1⟩ ⟨j.val, h.2⟩
  else if h' : r + k < i.val ∧ r + k < j.val then
    star (u⁻¹ ⟨2 * r + k - j.val, by omega⟩ ⟨2 * r + k - i.val, by omega⟩)
  else if i = j then 1 else 0

def pEl (k r : ℕ) (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) : Mat k r := fun i j =>
  if i = j then 1
  else if h : i.val < r ∧ r ≤ j.val ∧ j.val ≤ r + k then
    -herm (Hb k) (bvec ⟨j.val - r, by omega⟩) (B ⟨i.val, h.1⟩)
  else if h' : r ≤ i.val ∧ i.val ≤ r + k ∧ r + k < j.val then
    B ⟨2 * r + k - j.val, by omega⟩ ⟨i.val - r, by omega⟩
  else if h'' : i.val < r ∧ r + k < j.val then
    S ⟨i.val, h''.1⟩ ⟨2 * r + k - j.val, by omega⟩ -
      herm (Hb k) (B ⟨2 * r + k - j.val, by omega⟩) (B ⟨i.val, h''.1⟩) / 2
  else 0

abbrev PPar (k r : ℕ) := (Fin r → Fin (k + 1) → ℂ) × (UT r → ℂ) × (Fin r → ℝ)

def pOf (k r : ℕ) (q : PPar k r) : Mat k r := pEl k r q.1 (skewM q.2.1 q.2.2)

def lebN (k r : ℕ) : Measure (Mt k r) :=
  (volume : Measure ((UT r → ℂ) × PPar k r)).map fun q => Matrix.of.symm (uEmb k r (upper q.1) * pOf k r q.2)

def mEmb (k r : ℕ) (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Mat k r := fun i j =>
  if h : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then m ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩
  else if i = j then 1 else 0

def Xsp (k r : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun a : Fin r => bvec (eI k r a))

def Xst (k r : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun a : Fin r => bvec (esI k r a))

def Hcom (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) where
  carrier := {w | ∀ a : Fin (r + 1), herm (Hpk k r) w (fvec k r z' a) = 0 ∧ herm (Hpk k r) w (γ⁻¹ *ᵥ fvec k r z a) = 0}
  zero_mem' := by intro a; simp [herm]
  add_mem' := by
    intro v w hv hw a
    have h1 := hv a; have h2 := hw a
    simp only [herm, Matrix.mulVec_add, dotProduct_add] at *
    exact ⟨by rw [h1.1, h2.1, add_zero], by rw [h1.2, h2.2, add_zero]⟩
  smul_mem' := by
    intro c v hv a
    have h1 := hv a
    simp only [herm, Matrix.mulVec_smul, dotProduct_smul] at *
    exact ⟨by rw [h1.1, smul_zero], by rw [h1.2, smul_zero]⟩

def Ppos (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ x : Mat k r) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * r + k + 1))) :=
  (LinearMap.ker (Matrix.toLin' (Hpk k r - 1)) ⊓ (Hcom k r z z' γ ⊔ Xsp k r).comap (Matrix.toLin' x)).comap
    (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).toLinearMap

def gramProj {n r : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (v : Fin r → Fin n → ℂ) : ℝ :=
  Real.sqrt ‖(Matrix.gram ℂ fun a => P.starProjection (WithLp.toLp 2 (v a))).det‖

def Dr (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) : ℝ := ‖Dmin k r z z' γ ⟨r, by omega⟩‖

def Yv (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ x : Mat k r) : ℝ :=
  gramProj (Ppos k r z z' γ x) (fun a : Fin r => x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r a))) / Dr k r z z' γ

def Sg (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (x : Mat k r) : ℝ :=
  Finset.univ.fold max 1 fun a : Fin (r + 1) => lA k r z x a

def DeOK (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (De : ℝ) : Prop :=
  1 ≤ De ∧ ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' γ l ≠ 0 → ‖Dmin k r z z' γ l‖⁻¹ ≤ De

def TwoFl (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) : Prop :=
  inWb k r z ∧ inWb k r z' ∧ 0 < Tz k r z ∧ 0 < Tz k r z' ∧ γ ∈ GG k r ∧ Gf k r z z' γ ≠ 0 ∧ Dr k r z z' γ ≠ 0

def Eset (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (R₀ y : ℝ) : Set (Mt k r) :=
  {x | Matrix.of x ∈ GG k r ∧ Sg k r z' (Matrix.of x) ≤ R₀ ∧ Sg k r z (γ * Matrix.of x) ≤ R₀ ∧
    y < Yv k r z z' γ (Matrix.of x) ∧ Yv k r z z' γ (Matrix.of x) ≤ 2 * y}

def fibVol (k r : ℕ) (R₀ De y : ℝ) : ℝ :=
  (4 * r : ℝ) ^ (11 * r ^ 2) * R₀ ^ (20 * r ^ 3) * De ^ (12 * r ^ 2) *
    (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * (2 * y) ^ (2 * (k - 2 - r))

def SubCut {k r : ℕ} (G : Set (Mat k r)) (μR : Measure (Mt k r)) (φ : Mt k r → ℝ≥0∞) : Prop :=
  Measurable φ ∧ ∀ x : Mt k r, Matrix.of x ∈ G → ∫⁻ ρ, φ (lmulM (Matrix.of ρ) x) ∂μR ≤ 1

def expSet {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) (A : Set (lieE S)) : Set (Fin m → Fin m → ℂ) :=
  (fun X : lieE S => Matrix.of.symm (NormedSpace.exp (unrealify (X : EuclideanSpace ℝ _)))) '' A

def HasDens {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (Fin m → Fin m → ℂ)) (c : ℝ≥0∞) : Prop :=
  Filter.Tendsto (fun ρ : ℝ => μ (expSet S (Metric.ball 0 ρ)) / volume (Metric.ball (0 : lieE S) ρ))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds c)

def volUn (j : ℕ) : ℝ := ∏ i ∈ Finset.range j, (2 * Real.pi) ^ (i + 1) / (i.factorial : ℝ)

end GlobalTheory.Amp
end
end

