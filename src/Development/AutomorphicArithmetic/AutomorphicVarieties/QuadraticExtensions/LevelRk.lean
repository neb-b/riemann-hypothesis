module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0001

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.levelRk :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n r : ℕ), 2 ≤ n → Nat.card (ClassGroup (𝓞 (Fn F Ω l n)) ⧸ (powMonoidHom l : ClassGroup (𝓞 (Fn F Ω l n)) →* ClassGroup (𝓞 (Fn F Ω l n))).range) ≤ l ^ r → XRk l 1 (Un F Ω l n) r := by
  intro F Ω _ _ _ _ _ l _ n r hn hc
  haveI := (fnCyc F Ω l n).1
  have htop : galOf F F Ω = ⊤ := by
    refine eq_top_iff.2 fun σ _ => ?_
    intro x
    exact σ.commutes x
  have hU : Un F Ω l n = galOf F (Fn F Ω l n) Ω := by
    unfold Un
    rw [galOfCyc F Ω l n F (Fn F Ω l n), htop]
  have hmap := pullOnto F Ω (Fn F Ω l n) (Un F Ω l n) hU.le 1 (ZMod l) (ZMod l) one_ne_zero hU.ge
    (Or.inl ((fnCyc F Ω l n).2.2 hn))
  have cardLe_dual_zmod_card (l : ℕ) [Fact l.Prime] (V : Type) [AddCommGroup V] [Module (ZMod l) V]
      [Finite V] : CardLe (V →ₗ[ZMod l] ZMod l) (Nat.card V) := by
    refine ⟨Finite.of_injective (fun f : V →ₗ[ZMod l] ZMod l => (f : V → ZMod l)) DFunLike.coe_injective, ?_⟩
    show Nat.card (Module.Dual (ZMod l) V) ≤ _
    rw [Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq).toEquiv]

  have cardLe_hom (A : Type) [CommGroup A] [Finite A] (l : ℕ) [Fact l.Prime] (P : Type) (θ : P → A → ZMod l)
      (hθ : Function.Injective θ) (hm : ∀ p a b, θ p (a * b) = θ p a + θ p b) :
      CardLe P (Nat.card (A ⧸ (powMonoidHom l : A →* A).range)) := by
    have hpow : ∀ p (c : A) (n : ℕ), θ p (c ^ n) = n • θ p c := by
      intro p c n
      induction n with
      | zero =>
        have h := hm p 1 1
        rw [mul_one] at h
        simpa using h
      | succ n ih => rw [pow_succ, hm, ih, succ_nsmul]
    have h1 : ∀ p, θ p 1 = 0 := fun p => by simpa using hpow p 1 0
    have hV : ∀ v : Additive (A ⧸ (powMonoidHom l : A →* A).range), l • v = 0 := by
      intro v
      change (Additive.toMul v : A ⧸ (powMonoidHom l : A →* A).range) ^ l = 1
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
      rw [← ha, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨a, rfl⟩
    let φ : P → A →* Multiplicative (ZMod l) := fun p =>
      { toFun := fun a => Multiplicative.ofAdd (θ p a)
        map_one' := by
          show Multiplicative.ofAdd (θ p 1) = 1
          rw [h1]
          rfl
        map_mul' := fun a b => by
          show Multiplicative.ofAdd (θ p (a * b)) = _
          rw [hm]
          rfl }
    let ψ : P → (A ⧸ (powMonoidHom l : A →* A).range) →* Multiplicative (ZMod l) := fun p =>
      QuotientGroup.lift _ (φ p) (by
        rintro _ ⟨c, rfl⟩
        show Multiplicative.ofAdd (θ p (c ^ l)) = 1
        rw [hpow, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
        rfl)
    let Φ : P → (Additive (A ⧸ (powMonoidHom l : A →* A).range) →+ ZMod l) := fun p =>
      AddMonoidHom.mk' (fun v => Multiplicative.toAdd (ψ p (Additive.toMul v))) (fun u v => by
        show Multiplicative.toAdd (ψ p (Additive.toMul u * Additive.toMul v)) = _
        rw [map_mul]
        rfl)
    have hΦ : ∀ p (a : A), Φ p (Additive.ofMul (QuotientGroup.mk a)) = θ p a := fun p a => rfl
    have hinj : Function.Injective Φ := by
      intro p q h
      apply hθ
      funext a
      rw [← hΦ p a, ← hΦ q a, h]
    letI : Module (ZMod l) (Additive (A ⧸ (powMonoidHom l : A →* A).range)) := AddCommGroup.zmodModule hV
    exact CardLe.of_injective (cardLe_dual_zmod_card l (Additive (A ⧸ (powMonoidHom l : A →* A).range))) _
      ((AddMonoidHom.toZModLinearMap_injective l (M := Additive (A ⧸ (powMonoidHom l : A →* A).range))
        (M₁ := ZMod l)).comp hinj)
  have cardClDual :
      ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (N : ℕ), CardLe (ClDual K N (ZMod l) (ZMod l)) (Nat.card (ClassGroup (𝓞 K) ⧸ (powMonoidHom l : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K)).range)) := by
    intro K _ _ l _ N
    exact cardLe_hom (ClassGroup (𝓞 K)) l _ (fun θ => θ.1) Subtype.val_injective fun θ => θ.2.1
  obtain ⟨hfin, hcard⟩ := cardClDual (Fn F Ω l n) l 1
  unfold XRk CardLe
  rw [← hmap]
  have hsurj := LinearMap.submoduleMap_surjective (clPull (Fn F Ω l n) hU.le (ZMod l) (ZMod l)) (ClDual (Fn F Ω l n) 1 (ZMod l) (ZMod l))
  exact ⟨Finite.of_surjective _ hsurj, (Nat.card_le_card_of_surjective _ hsurj).trans (hcard.trans hc)⟩
