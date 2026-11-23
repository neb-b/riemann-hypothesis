module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
section
noncomputable section

namespace GlobalTheory.UnRep

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def hermE (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  ∑ a, ∑ b, x a * G a b * c (y b)

def IsUnE (c : E ≃ₐ[F] E) {n : ℕ} (G γ : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ x y, hermE c G (γ *ᵥ x) (γ *ᵥ y) = hermE c G x y

def IsHermForm (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ x, c (c x) = x) ∧ c ≠ 1 ∧ (∀ a b, c (G a b) = G b a) ∧ G.det ≠ 0

def refl (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E) : Matrix (Fin n) (Fin n) E :=
  1 + ((u - 1) / hermE c G x x) • Matrix.vecMulVec x (G *ᵥ fun b => c (x b))

def Moved (c : E ≃ₐ[F] E) (P : Ideal (𝓞 E)) : Prop :=
  ∃ a ∈ P, ∃ b : 𝓞 E, (b : E) = c (a : E) ∧ b ∉ P

def SplitOr (c : E ≃ₐ[F] E) (N : ℕ) (s : 𝓞 E) : Prop :=
  s ≠ 0 ∧ ∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → Moved c P ∨ (N : 𝓞 E) ∈ P

def SplitOff (c : E ≃ₐ[F] E) (N : ℕ) (s : 𝓞 E) : Prop :=
  s ≠ 0 ∧ ∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → Moved c P ∧ (N : 𝓞 E) ∉ P

def CongAt {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ) (δ : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ t : ℕ, t.Coprime N ∧ ∀ v ∈ L, ∃ w ∈ L, t • (δ *ᵥ v - v) = D • w

variable [NumberField F]

def IsUnA (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∀ x y, hermA c G (g *ᵥ x) (g *ᵥ y) = hermA c G x y


variable (F) in
def fm {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) (RA F E) :=
  γ.map fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ x


variable (F) in
def CongAtA {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ) (k : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∃ t : ℕ, t.Coprime N ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)),
    t • (k *ᵥ z - z) = D • w

def SplitPl (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ P : Ideal (𝓞 E), P.IsPrime ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal ∧ Moved c P

def SuppSplit (c : E ≃ₐ[F] E) {n : ℕ} (N : ℕ) (h : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∃ e : FiniteAdeleRing (𝓞 F) F, e * e = e ∧ {v | e v ≠ 0}.Finite ∧
    (∀ v, e v ≠ 0 → SplitPl c v ∧ (N : 𝓞 F) ∉ v.asIdeal) ∧ (e ⊗ₜ[F] (1 : E)) • (h - 1) = h - 1

end GlobalTheory.UnRep
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
section
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CNorm

def pows (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) : Subgroup G := U.map (powMonoidHom p)

def pIdx (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) : ℕ := (pows p U).relIndex U

def pTor (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) : ℕ :=
  Nat.card {x : G // x ∈ U ∧ x ^ p = 1}

def nrm {A : Type} [CommGroup A] (σ : A →* A) (n : ℕ) : A →* A where
  toFun a := ∏ i ∈ Finset.range n, σ^[i] a
  map_one' := by simp [iterate_map_one]
  map_mul' a b := by simp [iterate_map_mul, Finset.prod_mul_distrib]

def dif {A : Type} [CommGroup A] (σ : A →* A) : A →* A where
  toFun a := σ a / a
  map_one' := by simp
  map_mul' a b := by rw [map_mul, mul_div_mul_comm]

def fix {A : Type} [CommGroup A] (σ : A →* A) : Subgroup A := σ.eqLocus (MonoidHom.id A)

theorem nrm_apply {A : Type} [CommGroup A] (σ : A →* A) (n : ℕ) (a : A) :
    nrm σ n a = ∏ i ∈ Finset.range n, σ^[i] a := rfl

theorem dif_apply {A : Type} [CommGroup A] (σ : A →* A) (a : A) : dif σ a = σ a / a := rfl

open NumberField IsDedekindDomain Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.CNorm.mem_fix {A : Type} [CommGroup A] (σ : A →* A) (a : A) :
    a ∈ _root_.GlobalTheory.CNorm.fix σ ↔ σ a = a := Iff.rfl

def oneUnits {O : Type} [CommRing O] (t : O) : Subgroup Oˣ :=
  (Units.map (Ideal.Quotient.mk (Ideal.span {t}) : O →* O ⧸ Ideal.span {t})).ker

def powSub (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L) : Subgroup Fˣ where
  carrier := {x | ∃ r : L, r ^ p = φ (x : F)}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r * s, by rw [mul_pow, hr, hs, Units.val_mul, map_mul]⟩
  inv_mem' := by
    rintro a ⟨r, hr⟩
    exact ⟨r⁻¹, by rw [inv_pow, hr, Units.val_inv_eq_inv_val, map_inv₀]⟩

open NumberField IsDedekindDomain Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.CNorm.mem_powSub (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L)
    (x : Fˣ) : x ∈ _root_.GlobalTheory.CNorm.powSub p φ ↔ ∃ r : L, r ^ p = φ (x : F) := Iff.rfl

def kNorm (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) : Subgroup Fˣ :=
  (Units.map (Algebra.norm L : AdjoinRoot (X ^ p - C (φ δ) : L[X]) →* L)).range.comap
    (Units.map (φ : F →* L))

open NumberField IsDedekindDomain Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.CNorm.mem_kNorm (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L)
    (δ : F) (x : Fˣ) :
    x ∈ _root_.GlobalTheory.CNorm.kNorm p φ δ ↔ ∃ y : (AdjoinRoot (X ^ p - C (φ δ) : L[X]))ˣ,
      Algebra.norm L (y : AdjoinRoot (X ^ p - C (φ δ) : L[X])) = φ (x : F) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by simpa using congrArg Units.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Units.ext (by simpa using hy)⟩

structure IsKum (p : ℕ) {F E : Type} [Field F] [Field E] [Algebra F E] (ζ δ : F) (θ : E)
    (σ : E ≃ₐ[F] E) : Prop where
  prime : p.Prime
  root : IsPrimitiveRoot ζ p
  nonpow : ∀ r : F, r ^ p ≠ δ
  pow : θ ^ p = algebraMap F E δ
  conj : σ θ = algebraMap F E ζ * θ
  gen : Algebra.adjoin F {θ} = ⊤

def TNorm (F E L : Type) [Field F] [Field E] [Algebra F E] [Field L] [Algebra F L] (x : F) : Prop :=
  ∃ y : L ⊗[F] E, Algebra.norm L y = algebraMap F L x

section
variable (p : ℕ) (F : Type) [Field F] [NumberField F]

def finPow (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  ⨅ v ∈ S, powSub p (algebraMap F (v.adicCompletion F))

def finNorm (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  ⨅ v ∈ S, kNorm p (algebraMap F (v.adicCompletion F)) δ

def tNon (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))) : ℕ :=
  Set.ncard {v : HeightOneSpectrum (𝓞 F) |
    v ∈ S ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ}

def AdmP (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  GlobalTheory.QNorm.admitted F S ∧ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v.valuation F (p : F) = 1

end

def LocNorm (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (x : F) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 F), TNorm F E (v.adicCompletion F) x) ∧
    ∀ a : Algebra F ℝ, @TNorm F E ℝ _ _ _ _ a x

def NP (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : Prop :=
  ∀ x : F, x ≠ 0 → LocNorm F E x → ∃ y : E, Algebra.norm F y = x

end GlobalTheory.CNorm

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.NontrivialTransvection
section
noncomputable section
namespace GlobalTheory.UTrans.Model
open GlobalTheory.UTrans
variable {R : Type} [CommRing R] {n : ℕ}

theorem tv_mulVec (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (x v : Fin n → R) (t : R) :
    (tv σ G x t).mulVec v = v + (t * hf σ G v x) • x := by
  rw [tv, Matrix.add_mulVec, Matrix.one_mulVec]
  ext a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.of_apply, hf,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => by ring

theorem hf_add_smul_left (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (v x y : Fin n → R) (c : R) :
    hf σ G (v + c • x) y = hf σ G v y + c * hf σ G x y := by
  simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hf_add_smul_right (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (v x y : Fin n → R) (c : R) :
    hf σ G y (v + c • x) = hf σ G y v + σ c * hf σ G y x := by
  simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hf_conj (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (hσ : ∀ a, σ (σ a) = a)
    (hG : ∀ a b, σ (G a b) = G b a) (x y : Fin n → R) : σ (hf σ G x y) = hf σ G y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, map_sum, map_mul, hσ, hG]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end GlobalTheory.UTrans.Model
end
end

