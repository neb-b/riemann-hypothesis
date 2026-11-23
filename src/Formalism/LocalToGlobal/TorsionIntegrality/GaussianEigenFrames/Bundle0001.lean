module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementC
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementE
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementH

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementF
section
noncomputable section
open scoped BigOperators
open NumberField

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def mapVec {K : Type} [Field K] (ι : ℂ →+* K) {n : Type} [Fintype n] [DecidableEq n]
    (T : (n → ℂ) →ₗ[ℂ] (n → ℂ)) (m : n → K) : n → K :=
  fun i => ∑ i', ι (T (Pi.single i' 1) i) * m i'

def GramBasic : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
      (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)),
      IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
    ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
      ¬ p ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a b d ha hd lam hlam) Λ (v j)) →
    ∀ B' B : J → ℂ_[p], (∀ j, ‖B' j‖ ≤ 1) → (∀ j, ‖B j‖ ≤ 1) →
      ‖∑ j, ∑ k, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B k‖ ≤ 1 ∧
      (∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
        ∑ j, ∑ k, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B k -
          ∑ j, ∑ k, B j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B' k = ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * e) ∧
      ((∀ i, ∑ k, B k * ι (v k i) = 0) → ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
        ∑ j, ∑ k, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B k = ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * e) ∧
      ((∀ i, ∑ j, B' j * ι (v j i) = 0) →
        ∑ j, ∑ k, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B k = 0)

def EigenCompat : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
      (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)),
      IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
    ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
      ¬ p ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a b d ha hd lam hlam) Λ (v j)) →
    ∀ T T' : (n → ℂ) →ₗ[ℂ] (n → ℂ), (∀ x y, matH h (T x) y = matH h x (T' y)) → (∀ x ∈ Λ, T' x ∈ Λ) →
    ∀ (B' B : J → ℂ_[p]) (χ χ' : ℂ_[p]), (∀ j, ‖B' j‖ ≤ 1) → (∀ j, ‖B j‖ ≤ 1) → ‖χ'‖ ≤ 1 →
      (∀ i, mapVec (ι : ℂ →+* ℂ_[p]) T (fun i' => ∑ j, ι (v j i') * B' j) i = χ * ∑ j, ι (v j i) * B' j) →
      (∀ i, mapVec (ι : ℂ →+* ℂ_[p]) T' (fun i' => ∑ j, ι (v j i') * B j) i = χ' * ∑ j, ι (v j i) * B j) →
      ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
        (χ - χ') * ∑ j, ∑ k, B' j * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * B k = ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * e

def EigenFrame : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
      (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)),
      IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
    ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
      ¬ p ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a b d ha hd lam hlam) Λ (v j)) →
    ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]),
      (∀ j x, ‖A j x‖ ≤ 1) →
    ∀ (Xo : Type) (T T' : Xo → (n → ℂ) →ₗ[ℂ] (n → ℂ)) (chi chi' : Xo → Bool × H → ℂ_[p]),
      (∀ e x y, matH h (T e x) y = matH h x (T' e y)) → (∀ e, ∀ x ∈ Λ, T' e x ∈ Λ) →
      (∀ e τ, ‖chi' e τ‖ ≤ 1) →
      (∀ e x i, mapVec (ι : ℂ →+* ℂ_[p]) (T e) (fun i' => frameM (ι : ℂ →+* ℂ_[p]) v A i' x) i =
        chi e x.1 * frameM (ι : ℂ →+* ℂ_[p]) v A i x) →
      (∀ e x i, mapVec (ι : ℂ →+* ℂ_[p]) (T' e) (fun i' => frameM (ι : ℂ →+* ℂ_[p]) v A i' x) i =
        chi' e x.1 * frameM (ι : ℂ →+* ℂ_[p]) v A i x) →
      (∀ τ ρ : Bool × H, ρ ≠ (!τ.1, τ.2) → ∃ e, ‖chi e τ - chi' e ρ‖ = 1) →
      (∀ (t : H) (ab ab' : Fin N0 × Fin N1), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
        ∑ j, ∑ k, A j ((false, t), ab) * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * A k ((true, t), ab') =
          (if ab = ab' then u t else 0) + ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * e) →
      ∃ q : ((Bool × H) × Fin N0 × Fin N1) → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p],
        IsPairFrame (ι : ℂ →+* ℂ_[p]) (cmL a b d ha hd lam hlam) h Λ v A u (ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ))) q

def IntNorm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ_[p]) (y : 𝓞 E), ‖φ (y : E)‖ ≤ 1

def EigenFrameE : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
      (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)),
      IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
    ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
      ¬ p ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a b d ha hd lam hlam) Λ (v j)) →
    p = d →
    ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (cE s : E ≃+* E) (δ : E), δ ^ 2 = -(p : E) →
      cE δ = -δ → s δ = -δ → (∀ y, cE (cE y) = y) → (∀ y, s (s y) = y) → (∀ y, s (cE y) = cE (s y)) →
    ∀ (H : Type) [Fintype H] [DecidableEq H] (emb : Bool × H → (E →+* ℂ_[p])), Function.Injective emb →
      (∀ τ ρ, emb τ δ = emb ρ δ) → (∀ t y, emb (true, t) y = emb (false, t) (s (cE y))) →
      (∀ τ (y : E), s y = y → emb τ y ∈ MaximalUnramifiedExtension p) →
    ∀ (act : 𝓞 E → (n → ℂ) →ₗ[ℂ] (n → ℂ)),
      (∀ e e' : 𝓞 E, (e' : E) = cE (e : E) → ∀ x y, matH h (act e x) y = matH h x (act e' y)) →
      (∀ e, ∀ x ∈ Λ, act e x ∈ Λ) →
    ∀ (N0 N1 : ℕ) (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ 1) →
      (∀ (e : 𝓞 E) x i, mapVec (ι : ℂ →+* ℂ_[p]) (act e) (fun i' => frameM (ι : ℂ →+* ℂ_[p]) v A i' x) i =
        emb x.1 (e : E) * frameM (ι : ℂ →+* ℂ_[p]) v A i x) →
      (∀ (t : H) (ab ab' : Fin N0 × Fin N1), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
        ∑ j, ∑ k, A j ((false, t), ab) * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * A k ((true, t), ab') =
          (if ab = ab' then u t else 0) + ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * e) →
      ∃ q : ((Bool × H) × Fin N0 × Fin N1) → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p],
        IsPairFrame (ι : ℂ →+* ℂ_[p]) (cmL a b d ha hd lam hlam) h Λ v A u (ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ))) q

end Formalism.L2.Th1.GD
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementH
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4 opU taylorMv)
open Formalism.L2.Th1.Top (IsLatH thetaZ)
open Formalism.L2.Th1.E (IntCurve Unif)
open Formalism.L2.Th1.G (linSub)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)

def TensZ : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (ε : ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
    ¬ p ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
      (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) ≠ 0 →
    ‖ι ε‖ ≤ 1 →
    Formalism.L2.Th1.H.tens4 θ = ε • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₁ →
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ p ∣ N → (N : ℂ) • t ∈ Λ →
    ∃ (κ : Type) (_ : Fintype κ) (r : κ → ℂ_[p]) (s : κ → Fin 4 × n → ℂ) (N' : ℕ),
      (∀ k, ‖r k‖ ≤ 1) ∧ 0 < N' ∧ ¬ p ∣ N' ∧ (∀ k w, (N' : ℂ) * s k w ∈ (cmL a₀ b₀ dK ha hdK lam hlam).lattice) ∧
      linSub (fun w w' => ι (g₁.symm (Pi.single w' 1) w))
          (Formalism.L2.Th1.G.tens4 (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv (opU (matH h) t θ)))) =
        thetaZ p (cmL a₀ b₀ dK ha hdK lam hlam) ι (lam * a₀) r s

def JetsLinZ : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (n : Type) [Fintype n] (T : MvPowerSeries n K) (γ : Fin 4 × n → Fin 4 × n → K),
    JetsIntegral (linSub γ (Formalism.L2.Th1.G.tens4 T)) →
    ∀ (ν : Type) [Fintype ν] (M : n → ν → K) (Cm : Fin 4 × n → Fin 4 × ν → K),
    (∀ w x, ‖Cm w x‖ ≤ 1) →
    (∀ (a : Fin 4) (i : n) (b : Fin 4) (x : ν),
      ∑ w, γ (a, i) w * Cm w (b, x) = if a = b then M i x else 0) →
    JetsIntegral (linSub M T)

def IntOpTwoLoc : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 (cmL a₀ b₀ dK ha hdK lam hlam) ι W → IntCurve W → ‖W.a₁‖ = 1 →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ 2 ι →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[2]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ 2 ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ dK ha hdK lam hlam) Λ (v j)) →
  ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[2]), (∀ j x, ‖A j x‖ ≤ 1) →
    JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[2]) h θ r t (frameM (ι : ℂ →+* ℂ_[2]) v A)) ∧
    ∀ P : MvPolynomial ν ℂ_[2], (∀ k, ‖AddMonoidAlgebra.coeff P k‖ ≤ 1) →
      ‖jetPair P (thetaLin (ι : ℂ →+* ℂ_[2]) h θ r t (frameM (ι : ℂ →+* ℂ_[2]) v A))‖ ≤ 1

end Formalism.L2.Th1.GD
end
end

