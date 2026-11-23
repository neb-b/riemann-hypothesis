module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.EmbDefY
section
namespace KStar.Ram

open IsLocalRing NumberField

def embOver {B : Type*} [CommRing B] (R : Type*) [CommRing R] [IsLocalRing R] (P : Ideal B) :
    Set (B →+* R) :=
  {σ | (maximalIdeal R).comap σ = P}

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.FieldDefs
section
namespace KStar.Ram

open NumberField
open scoped Pointwise

noncomputable def vdField (E : Type*) [Field E] [NumberField E] (p : ℕ) : ℚ :=
  (padicValInt p (discr E) : ℚ) / (Module.finrank ℚ E : ℚ)

def SplitsIn (p : ℕ) (K : Type*) [Field K] [NumberField K] : Prop :=
  ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).ncard = Module.finrank ℚ K

end KStar.Ram
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.LogRootDiscChar
section
namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ}

noncomputable def condExp (l : ℕ) (ψ : DirichletCharacter ℂ N) : ℕ :=
  ψ.conductor.factorization l

noncomputable def avgCondExp (l : ℕ) (X : Subgroup (DirichletCharacter ℂ N)) : ℚ :=
  (∑ᶠ ψ : X, (condExp l (ψ : DirichletCharacter ℂ N) : ℚ)) / (Nat.card X : ℚ)

noncomputable def charKer (X : Subgroup (DirichletCharacter ℂ N)) : Subgroup (ZMod N)ˣ :=
  ⨅ ψ ∈ X, (MulChar.toUnitHom ψ).ker

noncomputable def fieldCond [NeZero N] (X : Subgroup (DirichletCharacter ℂ N)) : ℕ :=
  (Set.toFinite (X : Set (DirichletCharacter ℂ N))).toFinset.lcm fun ψ => ψ.conductor

noncomputable def logRootDiscChar (X : Subgroup (DirichletCharacter ℂ N)) : ℝ :=
  (∑ᶠ ψ : X, Real.log (ψ : DirichletCharacter ℂ N).conductor) / (Nat.card X : ℝ)

def inertiaUnits (N l : ℕ) : Subgroup (ZMod N)ˣ :=
  (ZMod.unitsMap (Nat.ordCompl_dvd N l)).ker

def decompUnits (N l : ℕ) [NeZero N] [hl : Fact l.Prime] : Subgroup (ZMod N)ˣ :=
  (Subgroup.zpowers (ZMod.unitOfCoprime l (Nat.coprime_ordCompl hl.out (NeZero.ne N)))).comap
    (ZMod.unitsMap (Nat.ordCompl_dvd N l))

def higherUnits (N l t : ℕ) : Subgroup (ZMod N)ˣ :=
  (ZMod.unitsMap (Nat.gcd_dvd_left N (ordCompl[l] N * l ^ t))).ker

noncomputable def crtEquiv (N l : ℕ) [NeZero N] [hl : Fact l.Prime] :
    ZMod N ≃+* ZMod (ordProj[l] N) × ZMod (ordCompl[l] N) :=
  (ZMod.ringEquivCongr (Nat.ordProj_mul_ordCompl_eq_self N l).symm).trans
    (ZMod.chineseRemainder
      (Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hl.out (NeZero.ne N))))

noncomputable def localUnits (N l : ℕ) [NeZero N] [Fact l.Prime] :
    (ZMod (ordProj[l] N))ˣ →* (ZMod N)ˣ :=
  Units.map ((crtEquiv N l).symm.toRingHom.toMonoidHom.comp (MonoidHom.inl _ _))

noncomputable def localPart (N l : ℕ) [NeZero N] [Fact l.Prime] :
    DirichletCharacter ℂ N →* DirichletCharacter ℂ (ordProj[l] N) where
  toFun ψ := MulChar.ofUnitHom ((MulChar.toUnitHom ψ).comp (localUnits N l))
  map_one' := by ext u; simp
  map_mul' ψ χ := by ext u; simp

noncomputable def ramIdx [NeZero N] (l : ℕ) [Fact l.Prime]
    (X : Subgroup (DirichletCharacter ℂ N)) : ℕ :=
  Nat.card (X.map (localPart N l))

def vdFormula (l a e : ℕ) : ℚ :=
  (a : ℚ) - 1 / ((l : ℚ) - 1) + 1 / (((l : ℚ) - 1) * (l : ℚ) ^ (a - 1)) - 1 / (e : ℚ)

end KStar.Ram
end

