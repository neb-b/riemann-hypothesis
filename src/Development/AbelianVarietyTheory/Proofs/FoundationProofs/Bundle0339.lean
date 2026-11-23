module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterPrimeConductorDegreePrimePow
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.PrimeChar

theorem normV_prime (v : Pl) : (normV v).Prime := by
  haveI := v.isPrime
  haveI := v.isMaximal
  haveI : Finite (𝓞 ℚ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hp : (ringChar (𝓞 ℚ ⧸ v.asIdeal)).Prime := CharP.char_is_prime (𝓞 ℚ ⧸ v.asIdeal) _
  haveI : Fact (ringChar (𝓞 ℚ ⧸ v.asIdeal)).Prime := ⟨hp⟩
  have hs : Function.Surjective (ZMod.castHom (dvd_refl (ringChar (𝓞 ℚ ⧸ v.asIdeal))) (𝓞 ℚ ⧸ v.asIdeal)) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    exact ⟨(n : ZMod _), by simp⟩
  have hb := Nat.card_eq_of_bijective _ ⟨RingHom.injective _, hs⟩
  rw [normV, ← hb, Nat.card_zmod]
  exact hp

theorem normV_mem (v : Pl) : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have h : Nat.card (𝓞 ℚ ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  change ((Nat.card (𝓞 ℚ ⧸ v.asIdeal) : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
  rw [h]
  exact Ideal.absNorm_mem _

theorem val_normV_lt_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] {B : ValuationSubring Ω} {v : Pl}
    (h : IsPlaceOver B v) : B.valuation ((normV v : ℕ) : Ω) < 1 := by
  have := (h _).2 (normV_mem v)
  simpa using this

theorem eq_of_normV_eq {v w : Pl} (h : normV v = normV w) : v = w := by
  have hp := normV_prime w
  have hpr : Prime ((normV w : ℕ) : 𝓞 ℚ) := by
    have h1 : Prime ((normV w : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : ((normV w : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((normV w : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h1
  have hI : (Ideal.span {((normV w : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime hpr.ne_zero).mpr hpr)
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  have hv : Ideal.span {((normV w : ℕ) : 𝓞 ℚ)} = v.asIdeal :=
    hI.eq_of_le v.isPrime.ne_top (by rw [Ideal.span_singleton_le_iff_mem, ← h]; exact normV_mem v)
  have hw : Ideal.span {((normV w : ℕ) : 𝓞 ℚ)} = w.asIdeal :=
    hI.eq_of_le w.isPrime.ne_top (by rw [Ideal.span_singleton_le_iff_mem]; exact normV_mem w)
  exact HeightOneSpectrum.ext (hv.symm.trans hw)

theorem exists_surj (p N : ℕ) [Fact p.Prime] (h : N ∣ p - 1) :
    ∃ f : (ZMod p)ˣ →* Multiplicative (ZMod N), Function.Surjective f := by
  have hc : IsCyclic (ZMod p)ˣ := inferInstance
  have hcard : N ∣ Nat.card (ZMod p)ˣ := by rw [Nat.card_eq_fintype_card, ZMod.card_units]; exact h
  let c : ZMod (Nat.card (ZMod p)ˣ) →+ ZMod N := (ZMod.castHom hcard (ZMod N)).toAddMonoidHom
  refine ⟨(AddMonoidHom.toMultiplicative c).comp (zmodCyclicMulEquiv hc).symm.toMonoidHom, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective hcard (Multiplicative.toAdd y)
  refine ⟨zmodCyclicMulEquiv hc (Multiplicative.ofAdd x), ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  show Multiplicative.ofAdd (c x) = y
  exact hx

theorem pow_self_eq_one (N : ℕ) (a : Multiplicative (ZMod N)) : a ^ N = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

end GlobalTheory.Ord2.PrimeChar

namespace GlobalTheory.Ord2.PrimeChar

theorem exists_prime_char : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl),
    1 ≤ n → l ^ n ∣ normV w - 1 → ∃ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)), KillsMu (normV w) ψ ∧
      Function.Surjective ψ ∧ (∀ B : ValuationSubring Ω, IsPlaceOver B w → ∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) ∧
      ∀ v : Pl, v ≠ w → (∃ x : ZMod (normV w), x ^ (l ^ n) = (normV v : ZMod (normV w))) →
        ∀ B : ValuationSubring Ω, IsPlaceOver B v → Dec (F := ℚ) B ≤ ψ.ker := by
  intro l _ Ω _ _ _ n w _ hdiv
  have hp := normV_prime w
  haveI : Fact (normV w).Prime := ⟨hp⟩
  haveI : NeZero (normV w) := ⟨hp.ne_zero⟩
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨f, hf⟩ := exists_surj (normV w) (l ^ n) hdiv

  have hine : ∀ B : ValuationSubring Ω, IsPlaceOver B w →
      ∃ τ ∈ Ine (F := ℚ) B, (f.comp (Chr.cls ℚ Ω (normV w)) τ).toAdd = 1 := by
    intro B hB
    have hBp := val_normV_lt_one hB
    obtain ⟨g0, hg0⟩ := hf (Multiplicative.ofAdd 1)
    have hd : normV w ^ 1 ∣ normV w := by rw [pow_one]
    obtain ⟨w0, hw0⟩ := KStar.TotallyRealRoots.redPow_surjective (l := normV w) 1 (ZMod.unitsMap hd g0)
    obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω (normV w) B hBp w0
    refine ⟨σ, hσ, ?_⟩
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
    haveI : NeZero ((normV w : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
    have hX : PadicInt.toZModPow 1 (w0 : ℤ_[normV w]) = (((g0 : ZMod (normV w)).val : ℕ) : ZMod (normV w ^ 1)) := by
      have h2 := congrArg (fun u : (ZMod (normV w ^ 1))ˣ => (u : ZMod (normV w ^ 1))) hw0
      simp only [ZMod.unitsMap_val] at h2
      rw [← ZMod.cast_natCast (R := ZMod (normV w ^ 1)) hd ((g0 : ZMod (normV w)).val), ZMod.natCast_zmod_val]
      exact h2
    have hcls : Chr.cls ℚ Ω (normV w) σ = g0 := by
      refine (Chr.clsFacts ℚ Ω (normV w)).2.2.1 σ g0 fun ζ hζ => ?_
      have hζ' : ζ ^ (normV w ^ 1) = 1 := by rw [pow_one]; exact hζ
      have hspec : σ ζ = ζ ^ (PadicInt.toZModPow 1 ((cycZ ℚ Ω (normV w) σ : ℤ_[normV w]ˣ) : ℤ_[normV w])).val :=
        cyclotomicCharacter.spec (L := Ω) (normV w) (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) ζ hζ'
      rw [hspec, hσw, hX, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ']
    rw [MonoidHom.comp_apply, hcls, hg0, toAdd_ofAdd]
  refine ⟨f.comp (Chr.cls ℚ Ω (normV w)), fun s hs => ?_, fun y => ?_, hine, fun v hvw hx B hB => ?_⟩
  ·
    have h1 : Chr.cls ℚ Ω (normV w) s = 1 := (Chr.clsFacts ℚ Ω (normV w)).2.2.1 s 1 fun ζ hζ => by
      rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
      exact hs ζ hζ
    rw [MonoidHom.comp_apply, h1, map_one]
  ·
    obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
    obtain ⟨τ, -, hτ⟩ := hine B hB
    refine ⟨τ ^ (Multiplicative.toAdd y).val, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [map_pow, toAdd_pow, hτ, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  ·
    have hq := normV_prime v
    haveI : Fact (normV v).Prime := ⟨hq⟩
    have hne : normV v ≠ normV w := fun h => hvw (eq_of_normV_eq h)
    have hcop : (normV w).Coprime (normV v) := (Nat.coprime_primes hp hq).2 (Ne.symm hne)
    have hBq := val_normV_lt_one hB
    obtain ⟨x, hx⟩ := hx
    have hq0 : ((normV v : ℕ) : ZMod (normV w)) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod (normV w)) (normV w)]
      exact fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hq).1 h).symm
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hx
      exact hq0 hx.symm
    let uq : (ZMod (normV w))ˣ := ZMod.unitOfCoprime (normV v) hcop.symm
    have huq : uq = Units.mk0 x hx0 ^ (l ^ n) := by
      ext
      simp [uq, hx]
    have hfq : f uq = 1 := by rw [huq, map_pow, pow_self_eq_one]
    intro g hg
    obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω (normV v) B hBq (normV w) hcop g hg
    have hcls : Chr.cls ℚ Ω (normV w) g = uq ^ k := by
      refine (Chr.clsFacts ℚ Ω (normV w)).2.2.1 g (uq ^ k) fun ζ hζ => ?_
      rw [hk ζ hζ, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ZMod.val_natCast,
        ← pow_eq_pow_mod _ hζ]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hcls, map_pow, hfq, one_pow]

end GlobalTheory.Ord2.PrimeChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComm
section
noncomputable section

open scoped Matrix

namespace GlobalTheory.CommutingExistence

variable {k : Type} [Field k]

theorem trace_two (A : Matrix (Fin 2) (Fin 2) k) (h1 : A.det = 1) (h2 : (A - 1).det = 0) :
    A 0 0 + A 1 1 = 2 := by
  rw [Matrix.det_fin_two] at h1 h2
  simp at h2
  linear_combination h1 - h2

theorem mul_nil (A B : Matrix (Fin 2) (Fin 2) k) (hA : A.det = 1) (hB : B.det = 1)
    (hA' : (A - 1).det = 0) (hB' : (B - 1).det = 0) (hAB : (A * B - 1).det = 0) :
    (A - 1) * (B - 1) = 0 := by
  have tA := trace_two A hA hA'
  have tB := trace_two B hB hB'
  have tAB := trace_two (A * B) (by rw [Matrix.det_mul, hA, hB, mul_one]) hAB
  rw [Matrix.det_fin_two] at hA hB
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at tAB
  obtain ⟨x, hx⟩ : ∃ x, A 0 0 = 1 + x := ⟨A 0 0 - 1, by ring⟩
  obtain ⟨a, ha⟩ : ∃ a, B 0 0 = 1 + a := ⟨B 0 0 - 1, by ring⟩
  have hx' : A 1 1 = 1 - x := by linear_combination tA - hx
  have ha' : B 1 1 = 1 - a := by linear_combination tB - ha
  rw [hx, hx'] at hA tAB
  rw [ha, ha'] at hB tAB
  have e1 : x ^ 2 + A 0 1 * A 1 0 = 0 := by linear_combination -hA
  have e2 : a ^ 2 + B 0 1 * B 1 0 = 0 := by linear_combination -hB
  have e3 : 2 * x * a + A 0 1 * B 1 0 + A 1 0 * B 0 1 = 0 := by linear_combination tAB
  have f00 : x * a + A 0 1 * B 1 0 = 0 := by
    apply pow_eq_zero_iff (two_ne_zero) |>.mp
    linear_combination a ^ 2 * e1 - A 0 1 * A 1 0 * e2 + A 0 1 * B 1 0 * e3
  have f01 : x * B 0 1 - A 0 1 * a = 0 := by
    apply pow_eq_zero_iff (two_ne_zero) |>.mp
    linear_combination B 0 1 ^ 2 * e1 + A 0 1 ^ 2 * e2 - A 0 1 * B 0 1 * e3
  have f10 : A 1 0 * a - x * B 1 0 = 0 := by
    apply pow_eq_zero_iff (two_ne_zero) |>.mp
    linear_combination B 1 0 ^ 2 * e1 + A 1 0 ^ 2 * e2 - A 1 0 * B 1 0 * e3
  have f11 : A 1 0 * B 0 1 + x * a = 0 := by
    linear_combination e3 - f00
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hx, hx', ha, ha']
  · linear_combination f00
  · linear_combination f01
  · linear_combination f10
  · linear_combination f11

theorem exists_comm [IsAlgClosed k] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) k) (H : Subgroup Γ)
    (hdet : ∀ s ∈ H, (ρ s : Matrix (Fin 2) (Fin 2) k).det = 1)
    (hirr : ∀ V : Submodule k (Fin 2 → k),
      (∀ g ∈ H, ∀ v ∈ V, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤) :
    ∃ φ ∈ ⁅H, H⁆, ((ρ φ : Matrix (Fin 2) (Fin 2) k) - 1).det ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hle : ⁅H, H⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have hconj : ∀ g ∈ H, ∀ φ ∈ ⁅H, H⁆, g⁻¹ * φ * g ∈ ⁅H, H⁆ := by
    intro g hg φ hφ
    have := Subgroup.commutator_mem_commutator (H.inv_mem hg) (hle hφ)
    have h2 := Subgroup.mul_mem _ this hφ
    convert h2 using 1
    rw [commutatorElement_def]
    group
  let F : Submodule k (Fin 2 → k) :=
    { carrier := {v | ∀ φ ∈ ⁅H, H⁆, (ρ φ : Matrix (Fin 2) (Fin 2) k) *ᵥ v = v}
      add_mem' := by
        intro a b ha hb φ hφ
        rw [Matrix.mulVec_add, ha φ hφ, hb φ hφ]
      zero_mem' := by
        intro φ _
        simp
      smul_mem' := by
        intro c a ha φ hφ
        rw [Matrix.mulVec_smul, ha φ hφ] }
  have hF : ∀ v, v ∈ F ↔ ∀ φ ∈ ⁅H, H⁆, (ρ φ : Matrix (Fin 2) (Fin 2) k) *ᵥ v = v := fun _ => Iff.rfl
  have hFinv : ∀ g ∈ H, ∀ v ∈ F, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ F := by
    intro g hg v hv
    rw [hF] at hv ⊢
    intro φ hφ
    have h1 := hv _ (hconj g hg φ hφ)
    have h2 : φ * g = g * (g⁻¹ * φ * g) := by group
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, h2, map_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, h1]
  have hFtop : ∀ v, v ∈ F := by
    rcases hirr F hFinv with h | h
    · intro w
      rw [hF]
      intro ψ hψ
      have : ((ρ ψ : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ w ∈ F := by
        rw [hF]
        intro φ hφ
        have h0 := mul_nil (ρ φ : Matrix (Fin 2) (Fin 2) k) (ρ ψ : Matrix (Fin 2) (Fin 2) k)
          (hdet _ (hle hφ)) (hdet _ (hle hψ)) (hcon _ hφ) (hcon _ hψ)
          (by rw [← Units.val_mul, ← map_mul]; exact hcon _ (Subgroup.mul_mem _ hφ hψ))
        rw [Matrix.mulVec_mulVec]
        congr 1
        rw [sub_mul, one_mul, sub_eq_zero] at h0
        exact h0
      rw [h, Submodule.mem_bot, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
      exact this
    · intro w
      rw [h]
      trivial
  have hcomm : ∀ g ∈ H, ∀ g' ∈ H, ∀ v, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g' : Matrix (Fin 2) (Fin 2) k) *ᵥ v) =
      (ρ g' : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v) := by
    intro g hg g' hg' v
    have h1 := (hF _).1 (hFtop ((ρ g' : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v))) _
      (Subgroup.commutator_mem_commutator hg hg')
    rw [← h1]
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
    congr 3
    rw [commutatorElement_def]
    group
  have hscal : ∀ g ∈ H, ∃ c : k, ∀ v, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v = c • v := by
    intro g hg
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) k))
    refine ⟨c, ?_⟩
    rcases hirr (Module.End.eigenspace (Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) k)) c) (by
      intro g' hg' v hv
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
      rw [hcomm g hg g' hg', hv, Matrix.mulVec_smul]) with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
    · intro v
      have : v ∈ Module.End.eigenspace (Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) k)) c := by
        rw [h]; trivial
      rwa [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at this
  rcases hirr (Submodule.span k {(![1, 0] : Fin 2 → k)}) (by
    intro g hg v hv
    obtain ⟨c, hc⟩ := hscal g hg
    rw [hc]
    exact Submodule.smul_mem _ _ hv) with h | h
  · rw [Submodule.span_singleton_eq_bot] at h
    have := congrFun h 0
    simp at this
  · have : (![0, 1] : Fin 2 → k) ∈ Submodule.span k {(![1, 0] : Fin 2 → k)} := by
      rw [h]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
    have := congrFun hc 1
    simp at this

theorem main (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset GlobalTheory.Ord2.Pl) (A : ValuationSubring Ω) (W : GlobalTheory.Ord2.R2 Ω l) (h : GlobalTheory.Ord2.Nf e S A W) :
    ∃ φ ∈ ⁅GlobalTheory.Ord2.H0g W, GlobalTheory.Ord2.H0g W⁆,
      Matrix.det (GlobalTheory.Ord2.mat W φ - (1 : Matrix (Fin 2) (Fin 2) (Formalism.ConjugateSelfDual.Qbar l))) ≠ (0 : Formalism.ConjugateSelfDual.Qbar l) := by
  refine exists_comm W (GlobalTheory.Ord2.H0g W) ?_ ?_
  · intro s hs
    have h1 : GlobalTheory.Ord2.dt W s = 1 := hs.2
    have h2 := congrArg Units.val h1
    exact h2
  · intro V hV
    exact h.irr.2.2 V le_top (fun g v hv => hV g g.2 v hv)

end GlobalTheory.CommutingExistence

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDivisibleChainPrimaryTorsionGroup
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.DivChain

section
variable {X : Type} [AddCommGroup X]

def DivAll (l : ℕ) (y : X) : Prop := ∀ m : ℕ, ∃ w : X, l ^ m • w = y

lemma divBy_mono {l M m : ℕ} {z : X} (h : m ≤ M) (hz : ∃ w : X, l ^ M • w = z) :
    ∃ w : X, l ^ m • w = z := by
  obtain ⟨w, rfl⟩ := hz
  refine ⟨l ^ (M - m) • w, ?_⟩
  rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' h]

lemma finite_fiber {l : ℕ} (hfin : Finite {x : X // l • x = 0}) (y z0 : X) (hz0 : l • z0 = y) :
    Finite {z : X // l • z = y} := by
  refine Finite.of_injective (fun z : {z : X // l • z = y} =>
    (⟨z.1 - z0, by rw [smul_sub, z.2, hz0, sub_self]⟩ : {x : X // l • x = 0})) ?_
  intro a b hab
  apply Subtype.ext
  have := congrArg Subtype.val hab
  simpa using this

lemma exists_preimage {l : ℕ} (hfin : Finite {x : X // l • x = 0}) {y : X} (hy : DivAll l y) :
    ∃ z : X, l • z = y ∧ DivAll l z := by
  obtain ⟨z0, hz0⟩ := hy 1
  rw [pow_one] at hz0
  haveI := finite_fiber hfin y z0 hz0
  by_contra hcon
  push_neg at hcon
  have hm : ∀ z : {z : X // l • z = y}, ∃ m : ℕ, ∀ w : X, l ^ m • w ≠ z.1 := by
    intro z
    have := hcon z.1 z.2
    simp only [DivAll, not_forall, not_exists] at this
    exact this
  choose f hf using hm
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  obtain ⟨w, hw⟩ := hy (M + 1)
  have hz : l • (l ^ M • w) = y := by rw [← mul_smul, ← pow_succ']; exact hw
  have hle : f ⟨l ^ M • w, hz⟩ ≤ M := hM ⟨⟨l ^ M • w, hz⟩, rfl⟩
  obtain ⟨w', hw'⟩ := divBy_mono (z := l ^ M • w) hle ⟨w, rfl⟩
  exact hf ⟨l ^ M • w, hz⟩ w' hw'

lemma exists_last {l : ℕ} {z : X} (hz : z ≠ 0) :
    ∀ n : ℕ, l ^ n • z = 0 → ∃ k, l ^ k • z ≠ 0 ∧ l ^ (k + 1) • z = 0
  | 0, h => by simp at h; exact absurd h hz
  | n + 1, h => by
    by_cases hk : l ^ n • z = 0
    · exact exists_last hz n hk
    · exact ⟨n, hk, h⟩

lemma exists_start {l : ℕ} (htors : ∀ x : X, ∃ n : ℕ, l ^ n • x = 0)
    (hfin : Finite {x : X // l • x = 0}) (hunb : ∀ m : ℕ, ∃ x : X, l ^ m • x ≠ 0) :
    ∃ y : X, y ≠ 0 ∧ l • y = 0 ∧ DivAll l y := by
  by_contra hcon
  push_neg at hcon
  have hm : ∀ y : {x : X // l • x = 0}, ∃ m : ℕ, y.1 ≠ 0 → ∀ w : X, l ^ m • w ≠ y.1 := by
    intro y
    by_cases hy0 : y.1 = 0
    · exact ⟨0, fun h => absurd hy0 h⟩
    · have := hcon y.1 hy0 y.2
      simp only [DivAll, not_forall, not_exists] at this
      obtain ⟨m, hm⟩ := this
      exact ⟨m, fun _ => hm⟩
  choose f hf using hm
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  obtain ⟨x, hx⟩ := hunb M
  obtain ⟨n, hn⟩ := htors (l ^ M • x)
  obtain ⟨k, hk1, hk2⟩ := exists_last hx n hn
  have hy : l • (l ^ k • (l ^ M • x)) = 0 := by rw [← mul_smul, ← pow_succ']; exact hk2
  have hle : f ⟨_, hy⟩ ≤ M := hM ⟨⟨_, hy⟩, rfl⟩
  apply hf ⟨_, hy⟩ hk1 (l ^ (M - f ⟨_, hy⟩) • (l ^ k • x))
  show l ^ f ⟨_, hy⟩ • l ^ (M - f ⟨_, hy⟩) • l ^ k • x = l ^ k • l ^ M • x
  rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' hle, ← mul_smul, ← mul_smul, mul_comm]

end

theorem exists_divisible_chain : ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X],
    (∀ x : X, ∃ n : ℕ, l ^ n • x = 0) → Finite {x : X // l • x = 0} →
    (∀ m : ℕ, ∃ x : X, l ^ m • x ≠ 0) → ∃ x : ℕ → X, x 0 ≠ 0 ∧ ∀ n, l • x (n + 1) = x n := by
  intro l _ X _ htors hfin hunb
  obtain ⟨y0, hy0, -, hdiv⟩ := exists_start htors hfin hunb
  have H : ∀ y : {y : X // DivAll l y}, ∃ z : X, l • z = y.1 ∧ DivAll l z :=
    fun y => exists_preimage hfin y.2
  choose g hg hgd using H
  let s : ℕ → {y : X // DivAll l y} := fun n => Nat.rec ⟨y0, hdiv⟩ (fun _ y => ⟨g y, hgd y⟩) n
  exact ⟨fun n => (s n).1, hy0, fun n => hg (s n)⟩

end GlobalTheory.Ord2.DivChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitCharacterOfIntegralCyclotomicProduct
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.LocChar.unit_of_integral :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' : G ℚ Ω → Qbar l), ContinuousOn k (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t) → ∃ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) ∧ ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = k g := by
  intro l _ Ω _ _ c A k k' hcont hint hmul

  have heps : ∀ s : G ℚ Ω, eps l s * algebraMap ℤ_[l] (Qbar l) (((cycZ ℚ Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    intro s
    have h1 : algebraMap ℤ_[l] (Qbar l) (((cycZ ℚ Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = (((cycBar ℚ Ω l s)⁻¹ : (Qbar l)ˣ) : Qbar l) := by
      rw [← map_inv]
      simp [cycBar, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
    rw [h1, eps]
    exact Units.mul_inv _
  have hmem : ∀ s : G ℚ Ω, algebraMap ℤ_[l] (Qbar l) (((cycZ ℚ Ω l s)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ∈ c.O :=
    fun s => c.O.algebraMap_mem _
  let f : ↥(Dec (F := ℚ) A) → c.Oˣ := fun g =>
    Units.mkOfMulEqOne ⟨k g, (hint g g.2).1⟩
      (⟨k' g, (hint g g.2).2.1⟩ * ⟨_, hmem g⟩) (by
        apply Subtype.ext
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
        rw [← mul_assoc, (hint g g.2).2.2]
        exact heps g)
  have hf : ∀ g, (((f g : c.Oˣ) : c.O) : Qbar l) = k g := fun g => rfl
  have hone : k 1 = 1 := by
    have h11 := hmul 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [one_mul] at h11
    have hu : IsUnit (((f 1 : c.Oˣ) : c.O) : Qbar l) := by
      have : IsUnit ((f 1 : c.Oˣ) : c.O) := Units.isUnit _
      exact this.map c.O.val
    rw [hf, OneMemClass.coe_one] at hu
    exact hu.mul_left_cancel (by rw [mul_one]; exact h11.symm)
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ?_, hf⟩
  · ext
    change k _ = 1
    rw [OneMemClass.coe_one, hone]
  · intro g h
    ext
    change k _ = k _ * k _
    rw [Subgroup.coe_mul]
    exact hmul g g.2 h h.2
  · have hc : Continuous ((Dec (F := ℚ) A : Set (G ℚ Ω)).restrict k) :=
      continuousOn_iff_continuous_restrict.mp hcont
    exact hc.subtype_mk (fun g => (hint g g.2).1)
end

