module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
section
open Polynomial CategoryTheory
noncomputable section
namespace Formalism.IrreducibleCountingLemmas.TYPES

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

def IsBlockUT {ι : Type} {s : ℕ} (b : ι → Fin s) (M : Matrix ι ι K) : Prop :=
  ∀ i j, b j < b i → M i j = 0

variable {K} in
theorem isBlockUT_mul {ι : Type} [Fintype ι] {s : ℕ} (b : ι → Fin s) {A B : Matrix ι ι K}
    (hA : IsBlockUT K b A) (hB : IsBlockUT K b B) : IsBlockUT K b (A * B) := by
  intro i j h
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : b k < b i
  · simp [hA i k hk]
  · simp [hB k j (lt_of_lt_of_le h (not_lt.mp hk))]

def parab {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) : Subgroup (GL ι K) where
  carrier := {g | IsBlockUT K b (g : Matrix ι ι K) ∧ IsBlockUT K b ((g⁻¹ : GL ι K) : Matrix ι ι K)}
  one_mem' := by
    refine ⟨?_, ?_⟩ <;>
    · intro i j h
      have hij : i ≠ j := by rintro rfl; exact lt_irrefl _ h
      simp [Matrix.one_apply_ne hij]
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨?_, ?_⟩
    · simpa [Units.val_mul] using isBlockUT_mul b hg hh
    · simpa [mul_inv_rev, Units.val_mul] using isBlockUT_mul b hh' hg'
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    exact ⟨hg', by simpa using hg⟩

def unip {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) : Set (GL ι K) :=
  {g | g ∈ parab K b ∧ ∀ i j, b i = b j → (g : Matrix ι ι K) i j = if i = j then 1 else 0}

def IsCuspidal {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)) : Prop :=
  ∀ (s : ℕ) (b : ι → Fin s), Function.Surjective b → 2 ≤ s →
    ∀ v : τ, (∀ u ∈ unip K b, τ.ρ u v = v) → v = 0

def blk {ι : Type} {s : ℕ} (b : ι → Fin s) (c : Fin s) (M : Matrix ι ι K) :
    Matrix {i // b i = c} {i // b i = c} K :=
  M.submatrix Subtype.val Subtype.val

variable {K} in
theorem blk_mul {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) (c : Fin s)
    {A B : Matrix ι ι K} (hA : IsBlockUT K b A) (hB : IsBlockUT K b B) :
    blk K b c (A * B) = blk K b c A * blk K b c B := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [blk, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => b k = c)]
  have h0 : ∑ k : {k // ¬ b k = c}, A i k * B k j = 0 := by
    apply Finset.sum_eq_zero
    rintro ⟨k, hk⟩ _
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA i k (by rw [hi]; exact h)]; simp
    · rw [hB k j (by rw [hj]; exact h)]; simp
  rw [h0, add_zero]

def levi {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s) (c : Fin s)
    (p : parab K b) : GL {i // b i = c} K :=
  ⟨blk K b c (p.1 : Matrix ι ι K), blk K b c ((p.1⁻¹ : GL ι K) : Matrix ι ι K),
    by rw [← blk_mul b c p.2.1 p.2.2, Units.mul_inv]; exact Matrix.submatrix_one _ Subtype.val_injective,
    by rw [← blk_mul b c p.2.2 p.2.1, Units.inv_mul]; exact Matrix.submatrix_one _ Subtype.val_injective⟩

section HC
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
  (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

def infl (p : parab K b) :
    PiTensorProduct ℂ (fun c => (lam c : Type)) →ₗ[ℂ] PiTensorProduct ℂ (fun c => (lam c : Type)) :=
  PiTensorProduct.map (fun c => (lam c).ρ (levi K b c p))

def hcSpace : Submodule ℂ (GL ι K → PiTensorProduct ℂ (fun c => (lam c : Type))) where
  carrier := {f | ∀ (p : parab K b) (x : GL ι K), f (p.1 * x) = infl K b lam p (f x)}
  add_mem' := by
    intro f g hf hg p x
    simp [hf p x, hg p x]
  zero_mem' := by
    intro p x
    simp
  smul_mem' := by
    intro a f hf p x
    simp [hf p x]

def hcRep : Representation ℂ (GL ι K) (hcSpace K b lam) where
  toFun g :=
    { toFun := fun f => ⟨fun x => f.1 (x * g), fun p x => by simpa [mul_assoc] using f.2 p (x * g)⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by
    ext f x
    simp
  map_mul' := by
    intro g h
    ext f x
    simp [mul_assoc]
end HC

section Reps
variable {Γ : Type} [Group Γ]

def Intw {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ V') : Submodule ℂ (V →ₗ[ℂ] V') where
  carrier := {φ | ∀ g, φ ∘ₗ ρ g = ρ' g ∘ₗ φ}
  add_mem' := by
    intro φ ψ hφ hψ g
    rw [LinearMap.add_comp, LinearMap.comp_add, hφ g, hψ g]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro a φ hφ g
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hφ g]

def IsConstituent {V : Type} [AddCommGroup V] [Module ℂ V] (τ : FDRep ℂ Γ)
    (ρ : Representation ℂ Γ V) : Prop :=
  ∃ φ ∈ Intw τ.ρ ρ, φ ≠ 0

def IsIrrRep {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤

def zIdem [Fintype Γ] (τ : FDRep ℂ Γ) : MonoidAlgebra ℂ Γ :=
  ∑ γ : Γ, MonoidAlgebra.single γ
    ((Module.finrank ℂ τ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ τ (τ.ρ γ⁻¹))
end Reps

structure LabelConv where
  ι : AlgebraicClosure K →* ℂ
  ι_inj : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → ι x = ι y → x = y
  gen : ℕ → AlgebraicClosure K
  gen_order : ∀ d, 1 ≤ d → orderOf (gen d) = Fintype.card K ^ d - 1
  gen_norm : ∀ d e, 1 ≤ d → 1 ≤ e →
    gen (d * e) ^ ((Fintype.card K ^ (d * e) - 1) / (Fintype.card K ^ d - 1)) = gen d

def rootsBar (f : K[X]) : Multiset (AlgebraicClosure K) :=
  (f.map (algebraMap K (AlgebraicClosure K))).roots


variable {K} in
def HasCuspLabel (C : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K))
    (P : K[X]) : Prop :=
  P.Monic ∧ Irreducible P ∧ P ≠ X ∧ P.natDegree = Fintype.card ι ∧
    ∀ x : AlgebraicClosure K, aeval x P = 0 →
    ∀ γ : GL ι K, Irreducible (Matrix.charpoly (γ : Matrix ι ι K)) →
    ∀ z : AlgebraicClosure K, aeval z (Matrix.charpoly (γ : Matrix ι ι K)) = 0 →
    ∀ m : ℕ, C.gen (Fintype.card ι) ^ m = z →
      LinearMap.trace ℂ τ (τ.ρ γ) =
        (-1) ^ (Fintype.card ι - 1) *
          ∑ a ∈ Finset.range (Fintype.card ι), C.ι x ^ (m * Fintype.card K ^ a)


variable {K} in
def HasLabel (C : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K))
    (f : K[X]) : Prop :=
  ∃ (s : ℕ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (P : Fin s → K[X]),
    Function.Surjective b ∧
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c) ∧ HasCuspLabel C (lam c) (P c)) ∧
    IsConstituent τ (hcRep K b lam) ∧ f = ∏ c, P c

abbrev q : ℕ := Fintype.card K

def CuspParam (C : LabelConv K) : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    (∀ τ : FDRep ℂ (GL (Fin d) K), Simple τ → IsCuspidal K τ →
      (∃! P : K[X], HasCuspLabel C τ P) ∧
      (Module.finrank ℂ τ : ℤ) = ∏ i ∈ Finset.Ico 1 d, ((q K : ℤ) ^ i - 1)) ∧
    (∀ P : K[X], P.Monic → Irreducible P → P ≠ X → P.natDegree = d →
      ∃ τ : FDRep ℂ (GL (Fin d) K), Simple τ ∧ IsCuspidal K τ ∧ HasCuspLabel C τ P) ∧
    (∀ (τ τ' : FDRep ℂ (GL (Fin d) K)) (P : K[X]), Simple τ → IsCuspidal K τ → Simple τ' → IsCuspidal K τ' →
      HasCuspLabel C τ P → HasCuspLabel C τ' P → Nonempty (τ ≅ τ'))

end Formalism.IrreducibleCountingLemmas.TYPES
end
end

-- bundled from Formalism.PadicSubsetSums.CentralIdempotents.PrimitiveRootFifteenSubOneUnit
section
noncomputable section

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

def CharpolyCoeffClosure : Prop :=
  ∀ (G : Type) [TopologicalSpace G] (R : Type) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (X : Type) [Fintype X] (n : ℕ)
    (r : X → G → Matrix (Fin n) (Fin n) R) (T : Subring (X → R)) (D : Set G),
    (∀ x, Continuous (r x)) → IsClosed (T : Set (X → R)) → Dense D →
    (∀ g ∈ D, ∀ j : ℕ, (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T) →
    ∀ (g : G) (j : ℕ), (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T

def SameResidue : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) [Fintype X] (T : Subalgebra O (X → O)),
    IsLocalRing T → ∀ a ∈ T, ∀ x y : X, IsLocalRing.residue O (a x) = IsLocalRing.residue O (a y)

def BrauerNesbitt : Prop :=
  ∀ (k : Type) [Field k] (G : Type) [Group G] (V W : Type) [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (τ : Representation k G W),
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) τ.asModule →
    (∀ g, (ρ g).charpoly = (τ g).charpoly) →
    ∃ e : V ≃ₗ[k] W, ∀ g, e.toLinearMap ∘ₗ ρ g = τ g ∘ₗ e.toLinearMap

def BrauerNesbittAlg : Prop :=
  ∀ (k A V W : Type) [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W],
    IsSemisimpleModule A V → IsSemisimpleModule A W →
    (∀ a : A, (Algebra.lsmul k k V a).charpoly = (Algebra.lsmul k k W a).charpoly) →
    Nonempty (V ≃ₗ[A] W)

def GoodCuspidal : Prop :=
  ∀ (k : Type) [Field k] (P : Type) [Nonempty P] (r : ℕ) (f : P → k[X]) (I : Type) [Fintype I]
    (n d : I → ℕ) (h : P → I → k[X]),
    (∀ v, (f v).natDegree = r) → (∀ v, Squarefree (f v)) → (∀ v, f v = ∏ i, h v i ^ d i) →
    (∀ v i, (h v i).natDegree = n i) → (∀ i, 1 ≤ n i) → (∀ i, 1 ≤ d i) →
    (¬ ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ r ∧ ∀ v, ∃ g : k[X], g ∣ f v ∧ g.natDegree = a) →
    (∀ i, d i = 1) ∧ Fintype.card I ≤ 1

def SplitEigenAnnihilator : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (A B : Submodule K V)
    (γ₀ γ : Module.End K V) (c : K), IsCompl A B → (∀ v ∈ A, γ₀ v = v) → (∀ v ∈ A, γ v = v) →
    (∀ v ∈ B, γ v = c • v) → (γ₀ - 1) * (γ - algebraMap K (Module.End K V) c) = 0

def UnitEvalOfMultiplicity : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (t : ℕ) (c : O) (s' : O[X]), s'.Monic →
    ((s' * (X - C c) ^ t).map (IsLocalRing.residue O)).rootMultiplicity (IsLocalRing.residue O c) = t →
    IsUnit (s'.eval c)

def ev {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (x : X) : T →+* O :=
  (Pi.evalRingHom (fun _ : X => O) x).comp T.val.toRingHom

def FactorOverLocalSubalgebra : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X' : Type) [Fintype X'] (T : Subalgebra O (X' → O)),
    IsLocalRing T → ∀ (t : ℕ) (c : O) (F : T[X]) (s : X' → O[X]),
    (∀ x, F.map (ev T x) = s x * (X - C c) ^ t) → (∀ x, IsUnit ((s x).eval c)) →
    ∃ P : T[X], F = P * (X - C (algebraMap O T c)) ^ t ∧ IsUnit (P.eval (algebraMap O T c)) ∧
      ∀ x, P.map (ev T x) = s x

def CharpolyFactorAnnihilator : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A B : Submodule K V) (γ₀ γ : Module.End K V) (c cγ : K) (t : ℕ) (P : K[X]), IsCompl A B →
    (∀ v ∈ A, γ₀ v ∈ A) → (∀ v ∈ A, γ v ∈ A) → (∀ v ∈ B, γ₀ v = c • v) → (∀ v ∈ B, γ v = cγ • v) →
    Module.finrank K B = t → γ₀.charpoly = P * (X - C c) ^ t →
    (aeval γ₀ P) * (γ - algebraMap K (Module.End K V) cγ) = 0

def PrimitiveRootFifteenSubOneUnit : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ζ : R), IsPrimitiveRoot ζ 15 → IsUnit (ζ - 1)

def TwistInvertible : Prop :=
  ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (γ₀ : Module.End k V) (c : k), c ≠ 0 → ¬ γ₀.HasEigenvalue c →
    Function.Bijective fun v : V => c⁻¹ • γ₀ v - v

end Formalism.IrreducibleCountingLemmas.Z
end
end

-- bundled from Formalism.PadicSubsetSums.CentralIdempotents.ResidueAvoidanceOfPrimes
section
noncomputable section

open Classical

namespace Formalism.IrreducibleCountingLemmas.TOP

def sg (f ℓ : ℕ) (h : ZMod f → ℕ) (i : ZMod f) : ℤ :=
  ⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)⌋

def SgLe : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ) (H : ℕ), 2 ≤ ℓ → (∀ j, h j ≤ H) →
    ∀ i, (sg f ℓ h i : ℝ) ≤ H / ((ℓ : ℝ) - 1)

def SgRange : Prop :=
  ∀ (ℓ : ℕ) (ℓs b H : ℝ), 0 ≤ H → 1 < ℓs → ℓs < ℓ → H * ℓs ≤ 2 * b * (ℓs - 1) →
    H / ((ℓ : ℝ) - 1) ≤ 2 * b / ℓs

end Formalism.IrreducibleCountingLemmas.TOP
end
end

-- bundled from Formalism.PadicSubsetSums.CentralIdempotents.WindowSums
section
noncomputable section

namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial

def FiltProd : Prop :=
  ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (T : Module.End R V)
    (F : ℕ → Submodule R V) (c : ℕ → R) (k a : ℕ),
    (∀ i, k ≤ i → i < k + a → ∀ x ∈ F i, T x - c i • x ∈ F (i + 1)) →
    ∀ x ∈ F k, aeval T (∏ i ∈ Finset.Ico k (k + a), (X - C (c i))) x ∈ F (k + a)

def ColengthTwoStep : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (l g g₀ e e' : ℕ)
    (Z Bc I : Submodule O M) (s s₀ : Finset M),
    s.card ≤ g → Submodule.span O (s : Set M) ⊔ Bc = Z → Bc ≤ I →
    s₀.card ≤ g₀ → (s₀ : Set M) ⊆ Z →
    (∀ p ∈ Z, (l ^ e : ℕ) • p ∈ Submodule.span O (s₀ : Set M) ⊔ I) →
    (∀ p ∈ Submodule.span O (s₀ : Set M), (l ^ e' : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      ((g : ℕ∞) * (e : ℕ∞) + (g₀ : ℕ∞) * (e' : ℕ∞)) * Module.length O (O ⧸ Ideal.span {(l : O)})

def DigitLemma : Prop :=
  ∀ (l a c ρ : ℕ) (m : ℤ), l.Prime → 1 ≤ a → 0 < c → c < l ^ a - 1 → 1 ≤ ρ →
    (l ^ a - 1) ∣ c * (l ^ ρ - 1) → |m| < l →
    padicValInt l ((c : ℤ) + m * ((l : ℤ) ^ a - 1)) ≤ ρ

def LagrangeBoundT : Prop :=
  ∀ (l a A' r' : ℕ) (Cc : Finset ℕ), l.Prime → 1 ≤ a → 2 * A' < l →
    (∀ c ∈ Cc, c < l ^ a - 1) →
    (∀ c ∈ Cc, ∀ c' ∈ Cc, c ≠ c' → ∃ ρ, 1 ≤ ρ ∧ ρ ≤ r' ∧
      ((l : ℤ) ^ a - 1) ∣ ((c : ℤ) - c') * ((l : ℤ) ^ ρ - 1)) →
    ∀ c ∈ Cc, ∀ n < A',
      (∑ c' ∈ Cc, ∑ n' ∈ Finset.range (2 * A'),
        if c' = c ∧ n' = n then 0
        else padicValInt l (((c : ℤ) + n * ((l : ℤ) ^ a - 1)) - ((c' : ℤ) + n' * ((l : ℤ) ^ a - 1))))
      ≤ (Cc.card - 1) * r'

def LagrangeT : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (D₁ D₂ : Finset ℤ) (ρ : ℕ), Disjoint D₁ D₂ →
    (∀ i ∈ D₁, (∑ j ∈ D₂, padicValInt l (i - j)) + ∑ j ∈ D₁.erase i, padicValInt l (i - j) ≤ ρ) →
    C ((l : ℤ_[l]) ^ ρ) ∈ Ideal.span ({∏ i ∈ D₁, (X - C ((i : ℤ) : ℤ_[l])),
      ∏ j ∈ D₂, (X - C ((j : ℤ) : ℤ_[l]))} : Set ℤ_[l][X])

def LiftExp : Prop :=
  ∀ (l h : ℕ) (J : Finset ℤ), l.Prime → l ≠ 2 → J ⊆ Finset.Icc (-(h : ℤ)) (2 * h) → (0 : ℤ) ∉ J →
    2 * (2 * (2 * h) + padicValNat l (2 * (2 * h)).factorial) +
      ((∑ j ∈ J, (1 + padicValInt l j)) + h + padicValNat l h.factorial) ≤ 18 * h

def GLCardVal : Prop :=
  ∀ (g g' r : ℕ) [Fact g.Prime] [Fact g'.Prime], g ≠ g' →
    padicValNat g (Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g))) = r * (r - 1) / 2 ∧
    padicValNat g (Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g'))) =
      ∑ a ∈ Finset.Icc 1 r, padicValNat g (g' ^ a - 1)

end Formalism.IrreducibleCountingLemmas.WindowSums
end
end

