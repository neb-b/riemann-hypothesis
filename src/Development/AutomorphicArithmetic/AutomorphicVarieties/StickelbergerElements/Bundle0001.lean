module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle
section
noncomputable section

open Finset

namespace UpperTheory.V.B4

open UpperTheory.V.Bern

def Ek (M k : ℕ) (b : ZMod M) : ℚ := bcoef M k b.val / k

def yCl {M : ℕ} (a : ℕ) (b : ZMod M) : ZMod M := (a : ZMod M)⁻¹ * b

def jv (M a : ℕ) (b : ZMod M) : ℤ := ((a : ℤ) * (yCl a b).val - b.val) / M

def Eone (M a : ℕ) (b : ZMod M) : ℤ := ((a : ℤ) - 1) / 2 - jv M a b

def ck (l k : ℕ) : ℕ := padicValNat l (2 * k * primorial (k + 1))

def Zl (l : ℕ) [Fact l.Prime] : Subring ℚ where
  carrier := {x | ¬ l ∣ x.den}
  zero_mem' := by simpa using (Fact.out : l.Prime).ne_one
  one_mem' := by simpa using (Fact.out : l.Prime).ne_one
  add_mem' {x y} hx hy h := ((Fact.out : l.Prime).dvd_mul.1 (h.trans (Rat.add_den_dvd x y))).elim hx hy
  mul_mem' {x y} hx hy h := ((Fact.out : l.Prime).dvd_mul.1 (h.trans (Rat.mul_den_dvd x y))).elim hx hy
  neg_mem' {x} hx := by simpa using hx

theorem mem_Zl {l : ℕ} [Fact l.Prime] {x : ℚ} : x ∈ Zl l ↔ ¬ l ∣ x.den := Iff.rfl

section Elements

variable {M : ℕ} [NeZero M] {Γ : Type} [CommGroup Γ]

def sumEl {R : Type} [CommRing R] (φ : (ZMod M)ˣ →* Γ) (f : ZMod M → R) : MonoidAlgebra R Γ :=
  ∑ b : (ZMod M)ˣ, MonoidAlgebra.single (φ b)⁻¹ (f b)

def thetaEl (k : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℚ Γ := -sumEl φ (Ek M k)

def yEl (k a : ℕ) (ha : a.Coprime M) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℚ Γ :=
  (1 - MonoidAlgebra.single (φ (ZMod.unitOfCoprime a ha))⁻¹ ((a : ℚ) ^ k)) * thetaEl k φ

def xEl (a : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℤ Γ := -sumEl φ (Eone M a)

def ytEl (e a : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℤ Γ := -sumEl φ fun b => (b.val : ℤ) ^ e * Eone M a b

end Elements

section Maps

variable {G Γ : Type} [CommGroup G] [CommGroup Γ]

def coefMap (R Γ : Type) [CommRing R] [CommGroup Γ] : MonoidAlgebra ℤ Γ →+* MonoidAlgebra R Γ :=
  (MonoidAlgebra.lift ℤ (MonoidAlgebra R Γ) Γ (MonoidAlgebra.of R Γ)).toRingHom

theorem coefMap_single (R : Type) [CommRing R] (g : Γ) (n : ℤ) :
    coefMap R Γ (MonoidAlgebra.single g n) = MonoidAlgebra.single g (n : R) := by
  simp [coefMap, MonoidAlgebra.smul_single]

def IntAt (l : ℕ) [Fact l.Prime] (r : ℕ) (z : MonoidAlgebra ℚ Γ) : Prop := ∀ g, z.coeff g / (l : ℚ) ^ r ∈ Zl l

end Maps

end UpperTheory.V.B4

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SamePrimesMulPow
section
noncomputable section

open Finset

namespace UpperTheory.V.Stk

open UpperTheory.V.Bern

def Ev (M k : ℕ) (b : ZMod M) : ℚ := bcoef M k b.val / k

def yCl {M : ℕ} (a : ℕ) (b : ZMod M) : ZMod M := (a : ZMod M)⁻¹ * b

def Eva (M k a : ℕ) (b : ZMod M) : ℚ := Ev M k b - (a : ℚ) ^ k * Ev M k (yCl a b)

def jv (M a : ℕ) (b : ZMod M) : ℤ := ((a : ℤ) * (yCl a b).val - b.val) / M

def Eone (M a : ℕ) (b : ZMod M) : ℤ := ((a : ℤ) - 1) / 2 - jv M a b

def dk (k : ℕ) : ℕ := 2 * k * primorial (k + 1)

theorem dk_pos {k : ℕ} (hk : 0 < k) : 0 < dk k := by
  unfold dk
  exact Nat.mul_pos (by omega) (primorial_pos _)

section Elements

variable {M : ℕ} [NeZero M] {Γ : Type} [Group Γ]

def sumEl {R : Type} [CommRing R] (φ : (ZMod M)ˣ →* Γ) (f : ZMod M → R) : MonoidAlgebra R Γ :=
  ∑ b : (ZMod M)ˣ, MonoidAlgebra.single (φ b)⁻¹ (f b)

def yForm (k a : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℚ Γ := -sumEl φ (Eva M k a)

def xEl (a : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℤ Γ := -sumEl φ (Eone M a)

def ytEl (e a : ℕ) (φ : (ZMod M)ˣ →* Γ) : MonoidAlgebra ℤ Γ := -sumEl φ fun b => (b.val : ℤ) ^ e * Eone M a b

end Elements

section Maps

variable {G Γ : Type} [Group G] [Group Γ]

abbrev cf (R Γ : Type) [CommRing R] [Group Γ] : MonoidAlgebra ℤ Γ →+* MonoidAlgebra R Γ :=
  MonoidAlgebra.mapRingHom Γ (Int.castRingHom R)

theorem cf_single (R : Type) [CommRing R] (g : Γ) (n : ℤ) :
    cf R Γ (MonoidAlgebra.single g n) = MonoidAlgebra.single g (n : R) := by
  simp [cf]

theorem cf_sumEl (R : Type) [CommRing R] {M : ℕ} [NeZero M] (φ : (ZMod M)ˣ →* Γ) (f : ZMod M → ℤ) :
    cf R Γ (sumEl φ f) = sumEl φ fun b => (f b : R) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sumEl, map_sum, cf_single]

theorem sumEl_add {R : Type} [CommRing R] {M : ℕ} [NeZero M] (φ : (ZMod M)ˣ →* Γ) (f g : ZMod M → R) :
    sumEl φ (fun b => f b + g b) = sumEl φ f + sumEl φ g := by
  simp only [sumEl, MonoidAlgebra.single_add, Finset.sum_add_distrib]

end Maps

end UpperTheory.V.Stk

end
end

