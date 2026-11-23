module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PrimInIffSubsingleton
section
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

section Defs

def LieN (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (Y : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  cT σ Y * J + J * Y = 0 ∧ IsStrict A ∧ Y * P = P * A ∧ ∀ x ∈ perpX σ J P, Y *ᵥ x ∈ spanX P

def Relevant (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∀ Y A A', LieN σ J P Y A → LieN σ J P' Y A' →
    (simpleSum A - simpleSum A') + σ (simpleSum A - simpleSum A') = 0

def LiesAt {r : ℕ} (w : Formalism.MainNotions.S.Point E (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∃ l u : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsLo l ∧ IsUp u ∧ Z * eps E r = l * Formalism.MainNotions.S.ptMat w * u

def onePt (E : Type) [Field E] (r : ℕ) : Formalism.MainNotions.S.Point E (r + 1) := ⟨[(1, r + 1)], by simp, by simp⟩


variable [NumberField E]

def IntFrame (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T : E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  IsFrame σ J T P ∧ PrimIn (frameLat P) Λ

def Cong {n r : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  frameLat ((g : E)⁻¹ • (P' - P)) ≤ Λ

def admitted (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T' : E) (g : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  IntFrame σ J T' Λ P' ∧ ∃ u ∈ UO E r, Cong g Λ (P * u) P'

def NO (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Matrix (Fin n) (Fin n) E) :=
  {s | InN σ J P s ∧ latMap s Λ = Λ}

def Move (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P A B : Matrix (Fin n) (Fin (r + 1)) E) : Prop :=
  ∃ s ∈ NO σ J Λ P, ∃ u ∈ UO E r, B = s * A * u

end Defs

section Field

variable {σ : E →+* E} {n r : ℕ} {J s Y : Matrix (Fin n) (Fin n) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
  {u v A Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

end Field

section Lattice

variable [NumberField E] {σ : E →+* E} {n r g : ℕ} {J s : Matrix (Fin n) (Fin n) E}
  {P P' A B C : Matrix (Fin n) (Fin (r + 1)) E} {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Λ Λ' Λ'' M : Submodule (𝓞 E) (Fin n → E)} {T T' : E}

end Lattice

end GlobalTheory.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SplitFacTwistRight
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.ThModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem orthEx (D : D7) : OrthEx D := by
  intro V hV
  obtain ⟨b, hb⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_fin (two_ne_zero : (2 : D.host.E) ≠ 0) V.rank V.hT.flip
    (fun x y => V.herm.eq y x) V.rank_eq
  have ho : ∀ i j, i ≠ j → V.hT (b i) (b j) = 0 := fun i j hij => hb j i hij.symm
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.FockBasisMatrix.basis_matrix D V).2 b
  have hd : ∀ τ, ((V.frame.toMatrix b).map (tauE D τ)).det ≠ 0 := fun τ => by
    have := (tauE D τ).map_det (V.frame.toMatrix b)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (h1.map (tauE D τ)).ne_zero
  choose A hA hA' using fun τ => GlobalTheory.MonomialDiag.exists_monomial _ _ _ (gramAt D V τ) _ _ (hV (tauE D τ)) (hd τ)
    (h3 ho τ).1 (h3 ho τ).2.1
  exact ⟨A, V.frame.toMatrix b, hA, h1, fun i j hij => (h2 i j).trans (ho i j hij), hA'⟩

theorem nonempty_orthDec (D : D7) : Nonempty (OrthDec D) := GlobalTheory.Mem.Th.nonempty_orthDec (orthEx D)

end GlobalTheory.Mem.ThModel

end
end

