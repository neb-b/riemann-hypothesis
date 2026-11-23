module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0022
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DiagMemCongruencePairs
section
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob

variable {E : Type} [Field E] [NumberField E]

abbrev Lz (E : Type) [Field E] (m : ℕ) : Type := Submodule (𝓞 E) (Fin m → E) × (Fin m → E)

def zOf {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Fin n → E := fun i => P i (Fin.last r)

def spanX {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Submodule E (Fin n → E) :=
  LinearMap.range (eOf P).mulVecLin

def perpX (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E) :
    Submodule E (Fin n → E) := LinearMap.ker (cT σ (eOf P) * J).mulVecLin

def latIn {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (S : Submodule E (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) := Λ ⊓ S.restrictScalars (𝓞 E)

def mulLat {n : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  Λ.map ((g : 𝓞 E) • LinearMap.id)

def IsRed (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Jb : Matrix (Fin m) (Fin m) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) (x : Lz E m)
    (al : Matrix (Fin m) (Fin n) E) : Prop :=
  (∀ v ∈ perpX σ J P, al *ᵥ v = 0 ↔ v ∈ spanX P) ∧
  (∀ y, ∃ v ∈ perpX σ J P, al *ᵥ v = y) ∧
  (∀ v ∈ perpX σ J P, ∀ w ∈ perpX σ J P, form σ Jb (al *ᵥ v) (al *ᵥ w) = form σ J v w) ∧
  (latIn Λ (perpX σ J P)).map (al.mulVecLin.restrictScalars (𝓞 E)) = x.1 ∧
  al *ᵥ zOf P = x.2

def UO (E : Type) [Field E] [NumberField E] (r : ℕ) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
  {u | IsUp u ∧ ∀ a b : Fin (r + 1), a < b → u a b ∈ dInv E ((b : ℕ) - a)}

section Basic

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}



omit [NumberField E] in
theorem mem_perpX (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ perpX σ J P ↔ (cT σ (eOf P) * J) *ᵥ v = 0 := Iff.rfl


omit [NumberField E] in
theorem mem_perpX_iff_form (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ perpX σ J P ↔ ∀ a : Fin r, form σ J v (fun i => P i a.castSucc) = 0 := by
  rw [mem_perpX, ← Matrix.mulVec_mulVec, funext_iff]
  rfl




omit [NumberField E] in
theorem mem_latMap (γ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E) :
    v ∈ latMap γ Λ ↔ ∃ w ∈ Λ, γ *ᵥ w = v := Iff.rfl









end Basic

section Iota

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}

end Iota

section Iso

variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}



omit [NumberField E] in
theorem isUn_mul {γ δ : Matrix (Fin n) (Fin n) E} (hγ : IsUn σ J γ) (hδ : IsUn σ J δ) :
    IsUn σ J (γ * δ) := by
  have e : cT σ (γ * δ) = cT σ δ * cT σ γ := by rw [cT, Matrix.map_mul, Matrix.transpose_mul]; rfl
  rw [IsUn, e, show cT σ δ * cT σ γ * J * (γ * δ) = cT σ δ * (cT σ γ * J * γ) * δ by
    simp only [Matrix.mul_assoc], hγ, hδ]


theorem latMap_one (Λ : Submodule (𝓞 E) (Fin n → E)) : latMap 1 Λ = Λ := by
  ext v
  simp [mem_latMap]

theorem latMap_mul (γ δ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    latMap (γ * δ) Λ = latMap γ (latMap δ Λ) := by
  rw [latMap, latMap, latMap, ← Submodule.map_comp, Matrix.mulVecLin_mul]
  rfl

end Iso

section Unip

variable {n r : ℕ}

end Unip

section Examples

variable {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

end Examples

end GlobalTheory.SgGlob
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

def GoodSub {W : Type} [AddCommGroup W] (W0 A : AddSubgroup W) (S : Set W) : Prop :=
  A.relIndex W0 ≠ 0 ∧ W0.relIndex A ≠ 0 ∧ (∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) ∧
    ((QuotientAddGroup.mk : W → W ⧸ A) '' S).Finite

def IsCO {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W) : Prop := ∃ A, GoodSub W0 A S

def relVol {W : Type} [AddCommGroup W] (W0 A : AddSubgroup W) : ℝ :=
  (W0.relIndex A : ℝ) / (A.relIndex W0 : ℝ)

def cont {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W) : ℝ :=
  if h : IsCO W0 S then
    (((QuotientAddGroup.mk : W → W ⧸ h.choose) '' S).ncard : ℝ) * relVol W0 h.choose else 0

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def gramT (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x : Fin m → Fin n → E) :
    Matrix (Fin m) (Fin m) E := Matrix.of fun a b => hf L Hm (x b) (x a)

def rmul {n m : ℕ} (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) : Fin m → Fin n → E :=
  fun j => ∑ i, A i j • x i

def IsUni {N : ℕ} (s : Matrix (Fin N) (Fin N) E) : Prop := (∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1

def congK (L : LocE F E) (ϖ : 𝒪[F]) (m i : ℕ) : Set (Matrix (Fin m) (Fin m) E) :=
  {A | ∀ a b, ∃ c ∈ L.O, A a b - (1 : Matrix (Fin m) (Fin m) E) a b = algebraMap F E ((ϖ : F) ^ i) * c}

def thick (L : LocE F E) (ϖ : 𝒪[F]) {n m : ℕ} (Ω : Set (Fin m → Fin n → E)) (i : ℕ) :
    Set (Fin m → Fin n → E) := {x | ∃ y ∈ Ω, ∃ A ∈ congK L ϖ m i, x = rmul y A}

def horb (L : LocE F E) (ϖ : 𝒪[F]) {m : ℕ} (Γ : Matrix (Fin m) (Fin m) E) (i : ℕ) :
    Set (Matrix (Fin m) (Fin m) E) := {X | ∃ A ∈ congK L ϖ m i, X = cT L A * Γ * A}

def tupLat (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) (m : ℕ) :
    AddSubgroup (Fin m → Fin n → E) := AddSubgroup.pi Set.univ fun _ => Λ.toAddSubgroup

def hermLat (L : LocE F E) (m : ℕ) : AddSubgroup (Matrix (Fin m) (Fin m) E) :=
  AddSubgroup.closure {X | IsHerm L X ∧ IsIntM L X}

def IsPrimT (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Λ : Submodule L.O (Fin n → E))
    (x : Fin m → Fin n → E) : Prop :=
  (∀ a, x a ∈ Λ) ∧ ∃ y : Fin m → Fin n → E, (∀ a, y a ∈ Λ) ∧
    ∀ a b, hf L Hm (x a) (y b) = if a = b then 1 else 0

def fixG (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Y : Submodule E (Fin n → E)) :
    Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) := isomG L Hm ⊓ unipOn Y ⊥

abbrev stabL (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) :
    Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) := MulAction.stabilizer ((Fin n → E) ≃ₗ[E] (Fin n → E)) Λ

def torb {n m : ℕ} (K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E))) (x : Fin m → Fin n → E) :
    Set (Fin m → Fin n → E) := {y | ∃ g ∈ K, y = fun a => g (x a)}

def CongId (L : LocE F E) (ϖ : 𝒪[F]) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) (N : ℕ)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Prop :=
  ∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = algebraMap F E ((ϖ : F) ^ N) • w

def sigMass (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Y : Submodule E (Fin n → E))
    (Λ0 Mh : Submodule L.O (Fin n → E)) : ℝ≥0∞ :=
  ∑' o : MulAction.orbitRel.Quotient (fixG L Hm Y) (Submodule L.O (Fin n → E)),
    if IsSD L Hm o.out ∧ o.out ⊓ Y.restrictScalars L.O = Mh then
      ENNReal.ofReal (invVol (fixG L Hm Y ⊓ stabL L Λ0) (fixG L Hm Y ⊓ stabL L o.out)) else 0

def IsQRefl (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a : Fin n → E)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Prop :=
  IsUnit (hf L Hm a a) ∧ g ∈ isomG L Hm ∧ ∃ c : E, ∀ v, g v = v + (c * hf L Hm v a) • a

end GlobalTheory.HL
end
end

