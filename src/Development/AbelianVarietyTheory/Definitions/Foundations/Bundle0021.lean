module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.LambdaValuationPowers

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def lamv (l : ℕ) [Fact l.Prime] (m : ℕ) (s : G ℚ Ω) : Qbar l :=
  algebraMap ℚ_[l] (Qbar l) ((((cycZ (F := ℚ) (Ω := Ω) l s : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) - 1) / (l : Qbar l) ^ m

theorem natCast_ne_zero : (l : Qbar l) ≠ 0 := by
  have : CharZero (Qbar l) := charZero_of_injective_algebraMap (algebraMap ℚ_[l] (Qbar l)).injective
  exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

theorem norm_natCast_lt_one : ‖(l : Qbar l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem pow_mul_lamv (m : ℕ) (s : G ℚ Ω) :
    (l : Qbar l) ^ m * lamv l m s = algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
  rw [lamv, mul_div_cancel₀ _ (pow_ne_zero m natCast_ne_zero), map_sub, map_one]

theorem lamv_mul (m : ℕ) (s t : G ℚ Ω) :
    lamv l m (s * t) = lamv l m s + lamv l m t + (l : Qbar l) ^ m * lamv l m s * lamv l m t := by
  apply mul_left_cancel₀ (pow_ne_zero m (natCast_ne_zero (l := l)))
  have hs := pow_mul_lamv (l := l) m s
  have ht := pow_mul_lamv (l := l) m t
  rw [pow_mul_lamv, map_mul, Units.val_mul, PadicInt.coe_mul, map_mul]
  linear_combination (-(algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l t : ℤ_[l]ˣ) : ℤ_[l]))) * hs -
    ((l : Qbar l) ^ m * lamv l m s + 1) * ht

theorem exists_lamv_eq {m : ℕ} {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) :
    ∃ a : ℤ_[l], ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ m * a ∧ lamv l m s = algebraMap ℤ_[l] (Qbar l) a := by
  have h1 : PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    simpa [cycMod] using congrArg Units.val hs
  have h2 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈ RingHom.ker (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)) := by
    rw [RingHom.mem_ker, RingHom.map_sub, h1, map_one, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨a, ha⟩ := h2
  have h3 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ m * a := by rw [← ha]; ring
  refine ⟨a, h3, mul_left_cancel₀ (pow_ne_zero m (natCast_ne_zero (l := l))) ?_⟩
  rw [pow_mul_lamv, h3, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
  simp

theorem norm_le_one_of_mem {c : Coef l} {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] a := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨a, ha⟩ : c.O)).map c.O.val
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

theorem norm_lamv_le_one {m : ℕ} {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) : ‖lamv l m s‖ ≤ 1 := by
  obtain ⟨a, -, ha⟩ := exists_lamv_eq hs
  rw [ha, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']
  exact a.2

def cob (c : Coef l) (A : ValuationSubring Ω) (j : Ω →+* Qbar l) : Submodule c.O (G ℚ Ω → Qbar l) :=
  Submodule.span c.O {f | ∃ w ∈ A, f = fun s : G ℚ Ω => j (s w) - j w}

section Cob

variable {c : Coef l} {A : ValuationSubring Ω} {j : Ω →+* Qbar l}

theorem sub_mem_cob {w : Ω} (hw : w ∈ A) : (fun s : G ℚ Ω => j (s w) - j w) ∈ cob c A j :=
  Submodule.subset_span ⟨w, hw, rfl⟩

end Cob

def HTCoIn (c : Coef l) (A : ValuationSubring Ω) (j : Ω →+* Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (m c₀ : ℕ) (y : (ZMod (l ^ m))ˣ) (h : Qbar l) : Prop :=
  ReciprocityTheory.Neutral.Cmp.Compat l A j ∧ ∃ f ∈ cob c A j, ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
    Cg (m - c₀) (Z m s y) (h * lamv l m s + f s)

section Co

variable {c : Coef l} {A : ValuationSubring Ω} {j : Ω →+* Qbar l} {Z Z' : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l}
  {m c₀ : ℕ} {y : (ZMod (l ^ m))ˣ} {h h' : Qbar l}

namespace HTCoIn

end HTCoIn

theorem htCoIn_lamv (hj : ReciprocityTheory.Neutral.Cmp.Compat l A j) {f : G ℚ Ω → Qbar l} (hf : f ∈ cob c A j) (m c₀ : ℕ)
    (y : (ZMod (l ^ m))ˣ) (h : Qbar l) : HTCoIn c A j (fun r s _ => h * lamv l r s + f s) m c₀ y h :=
  ⟨hj, f, hf, fun _ _ _ => by simp [Cg]⟩

end Co

end GlobalTheory.LambdaValuationPowers
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IwSys2
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def Layer2 (c : Coef l) (A : ValuationSubring Ω) (ν : G ℚ Ω → (Qbar l)ˣ) (r : ℕ)
    (z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) : Prop :=
  (∀ s x, z s x ∈ c.O) ∧ ∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ∀ x,
    z (s * t) x = z s x + (ν s : Qbar l) * z t (x * (cycMod ℚ Ω l r s)⁻¹)

def IwSys2 (c : Coef l) (A : ValuationSubring Ω) (ν : G ℚ Ω → (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) :
    Prop :=
  (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ν (s * t) = ν s * ν t) ∧ (∀ r, Layer2 c A ν r (Z r)) ∧
    ∀ r s (x : (ZMod (l ^ r))ˣ),
      Z r s x = ∑ x' ∈ (Finset.univ.filter fun x' : (ZMod (l ^ (r + 1)))ˣ =>
        Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x), Z (r + 1) s x'

end GlobalTheory.KZ

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.KumValUnique
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 PowerSeries

namespace GlobalTheory.Col

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def KumVal (n : ℕ) (ζ u : Ω) (s : G ℚ Ω) (k : ZMod (l ^ n)) : Prop :=
  ∃ v : Ω, v ^ (l ^ n) = u ∧ s v = ζ ^ k.val * v

def KumPres (A : ValuationSubring Ω) (n r : ℕ) (ζ : Ω) (Z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) {ι : Type} [Fintype ι]
    (u : ι → Ω) (o : ι → Qbar l) : Prop :=
  IsPrimitiveRoot ζ (l ^ n) ∧ n ≤ r ∧ (∀ i, u i ∈ A ∧ u i ≠ 0 ∧ (u i)⁻¹ ∈ A) ∧ (∀ i, ‖o i‖ ≤ 1) ∧
    ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l r s = 1 → s ζ = ζ →
      ∃ k : ι → ZMod (l ^ n), (∀ i, KumVal n ζ (u i) s (k i)) ∧ Cg n (Z s 1) (∑ i, o i * ((k i).val : Qbar l))

theorem kumVal_unique {n : ℕ} {ζ u : Ω} {s : G ℚ Ω} {k k' : ZMod (l ^ n)} (hζ : IsPrimitiveRoot ζ (l ^ n)) (hs : s ζ = ζ)
    (hu : u ≠ 0) (hk : KumVal n ζ u s k) (hk' : KumVal n ζ u s k') : k = k' := by
  obtain ⟨v, hv, hsv⟩ := hk
  obtain ⟨w, hw, hsw⟩ := hk'
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have hv0 : v ≠ 0 := by rintro rfl; exact hu (by rw [← hv, zero_pow hpos.ne'])
  have hw0 : w ≠ 0 := by rintro rfl; exact hu (by rw [← hw, zero_pow hpos.ne'])
  have h1 : (w / v) ^ (l ^ n) = 1 := by rw [div_pow, hv, hw, div_self hu]
  obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one h1
  have hwv : w = ζ ^ j * v := by rw [hj]; field_simp
  have e1 : s w = ζ ^ k.val * w := by
    rw [hwv, map_mul, map_pow, hs, hsv]; ring
  have e2 : ζ ^ k.val = ζ ^ k'.val := by
    have := e1.symm.trans hsw
    exact mul_right_cancel₀ hw0 this
  exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt k) (ZMod.val_lt k') e2)

theorem kumVal_one (n : ℕ) (ζ : Ω) (s : G ℚ Ω) : KumVal (l := l) n ζ 1 s 0 :=
  ⟨1, one_pow _, by simp⟩

theorem kumPres_empty (A : ValuationSubring Ω) {n r : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ (l ^ n)) (hnr : n ≤ r)
    (Z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (hZ : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l r s = 1 → Z s 1 = 0) :
    KumPres A n r ζ Z (ι := Empty) (fun i => i.elim) (fun i => i.elim) := by
  refine ⟨hζ, hnr, fun i => i.elim, fun i => i.elim, fun s hs hc _ => ⟨fun i => i.elim, fun i => i.elim, ?_⟩⟩
  rw [Cg, hZ s hs hc, Finset.sum_eq_zero (fun i _ => i.elim), sub_zero, norm_zero]
  exact norm_nonneg _

theorem fix_of_cycMod [∀ i, HasEnoughRootsOfUnity Ω (l ^ i)] {n r : ℕ} (hnr : n ≤ r) {s : G ℚ Ω}
    (hs : cycMod ℚ Ω l r s = 1) {t : Ω} (ht : t ^ (l ^ n) = 1) : s t = t := by
  have ht' : t ^ (l ^ r) = 1 := by
    obtain ⟨d, hd⟩ := pow_dvd_pow l hnr
    rw [hd, pow_mul, ht, one_pow]
  have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) t ht'
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val.toZModPow r = 1 := by
    have := congrArg Units.val hs
    simpa [cycMod, cycZ] using this
  rw [h2, ZMod.val_one_eq_one_mod] at h1
  have h3 : t ^ (1 % l ^ r) = t := by
    rcases Nat.lt_or_ge 1 (l ^ r) with h | h
    · rw [Nat.mod_eq_of_lt h, pow_one]
    · have e : l ^ r = 1 := le_antisymm h (Nat.one_le_pow _ _ (Fact.out : l.Prime).pos)
      rw [e, Nat.mod_self, pow_zero]
      rw [e, pow_one] at ht'
      exact ht'.symm
  exact h1.trans h3

end GlobalTheory.Col
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.LiftSL
section
noncomputable section

open scoped MatrixGroups Matrix
open Filter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ ReciprocityTheory.Gal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def liftK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (a : X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l)))) : X.Khat l :=
  Classical.epsilon fun b : X.Khat l => AdicCompletion.eval (idl l) (X.Kl l) n b = a


open Classical in
def clsK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (w : X.K) : X.Khat l :=
  if h : w ≠ 0 then liftK X l n (X.cls l n (Units.mk0 w h)) else 0

def liftSL (M : ℕ) (g : SL(2, ZMod M)) : SL(2, ℤ) :=
  Classical.epsilon fun γ : SL(2, ℤ) => Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = g


def repC (l : ℕ) [Fact l.Prime] (r : ℕ) (x : (ZMod (l ^ r))ˣ) : Ω ≃ₐ[ℚ] Ω :=
  Classical.epsilon fun s : Ω ≃ₐ[ℚ] Ω => cycMod (F := ℚ) (Ω := Ω) l r s = x

def chik4 (l : ℕ) [Fact l.Prime] (e : ℕ) (ψ : ZMod l → Qbar l) (r : ℕ) (y : (ZMod (l ^ r))ˣ) : Qbar l :=
  ((((y : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * ψ (((y : ZMod (l ^ r)).val : ℕ) : ZMod l)

end GlobalTheory.K4
end
end

