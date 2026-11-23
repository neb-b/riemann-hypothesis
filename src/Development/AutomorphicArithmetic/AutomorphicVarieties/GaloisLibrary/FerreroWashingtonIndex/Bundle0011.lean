module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AmbHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AmbIndex
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.amb :
    ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (ζ : F), IsPrimitiveRoot ζ l → ∃ B : ℕ, ∀ (n : ℕ) (K : Type) [Field K] [NumberField K] [Algebra F K] [IsCyclotomicExtension {l ^ n} F K] (τ : Gal(K/F)), IsTotallyComplex K → (∀ σ : Gal(K/F), σ ∈ Subgroup.zpowers τ) → (powR (Cl K) l ⊔ difR (clMap τ.toRingEquiv)).index ≤ B := by
  intro F _ _ l _ ζ hζ
  obtain ⟨Ω, _, _, hΩ⟩ : ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra F Ω), IsAlgClosure F Ω :=
    ⟨AlgebraicClosure F, inferInstance, inferInstance, inferInstance⟩
  haveI : IsAlgClosed Ω := hΩ.isAlgClosed
  haveI : Algebra.IsAlgebraic F Ω := hΩ.isAlgebraic
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  refine ⟨{φ : G F Ω → ZMod l | IsLocallyConstant φ ∧ (∀ a b : G F Ω, φ (a * b) = φ a + φ b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine A, φ g = 0}.ncard,
    fun n K _ _ _ _ τ hK hτ => ?_⟩
  haveI hgal : IsGalois F K := IsCyclotomicExtension.isGalois (S := {l ^ n}) (K := F) (L := K)
  let e : K →ₐ[F] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra K Ω := e.toRingHom.toAlgebra
  haveI : IsScalarTower F K Ω := IsScalarTower.of_algebraMap_eq (fun x => (e.commutes x).symm)
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := F) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let ρ : Representation (ZMod l) (G F Ω) (ZMod l) := scalRep (ZMod l) 1
  have hcyc : IsCyclic Gal(K/F) := ⟨⟨τ, hτ⟩⟩
  have hpe := (pullEq F Ω K (galOf F K Ω) le_rfl 1 (ZMod l) (ZMod l) ρ one_ne_zero le_rfl (Or.inl hK)).1
  have hinj := (pullMem F Ω K (galOf F K Ω) le_rfl 1 (ZMod l) (ZMod l) one_ne_zero).2 le_rfl
  haveI hCfin : Finite (ClEq K 1 ρ) := Subtype.finite
  have hcardEq : Nat.card (EqHom 1 (galOf F K Ω) ρ) = Nat.card (ClEq K 1 ρ) := by
    rw [← hpe]
    exact Nat.card_congr (Submodule.equivMapOfInjective _ hinj _).toEquiv.symm
  have hEfin : Finite (EqHom 1 (galOf F K Ω) ρ) := by
    rw [← hpe]
    exact Finite.of_equiv _ (Submodule.equivMapOfInjective _ hinj _).toEquiv
  have hamb := ambHom F Ω K l ζ hζ hcyc (ineCyc F Ω K l n) hEfin
  set H := powR (Cl K) l ⊔ difR (clMap τ.toRingEquiv) with hH
  have hfix : ∀ c : Cl K, (QuotientGroup.mk (clMap τ.toRingEquiv c) : Cl K ⧸ H) = QuotientGroup.mk c := by
    intro c
    rw [QuotientGroup.eq]
    have h1 : c / clMap τ.toRingEquiv c ∈ H := le_sup_right (a := powR (Cl K) l) ⟨c, rfl⟩
    have h2 : (clMap τ.toRingEquiv c)⁻¹ * c = c / clMap τ.toRingEquiv c := by
      rw [div_eq_mul_inv, mul_comm]
    rw [h2]
    exact h1
  have hmulc : ∀ (a b : Gal(K/F)) (c : Cl K),
      clMap (a * b).toRingEquiv c = clMap a.toRingEquiv (clMap b.toRingEquiv c) :=
    fun a b c => clMap_trans b.toRingEquiv a.toRingEquiv c
  have hone1 : ∀ c : Cl K, clMap (1 : Gal(K/F)).toRingEquiv c = c := fun c => clMap_refl K c
  have hinv : ∀ d : Cl K, (QuotientGroup.mk (clMap τ⁻¹.toRingEquiv d) : Cl K ⧸ H) = QuotientGroup.mk d := by
    intro d
    have h3 : clMap τ.toRingEquiv (clMap τ⁻¹.toRingEquiv d) = d := by
      rw [← hmulc, mul_inv_cancel, hone1]
    conv_rhs => rw [← h3]
    rw [hfix]
  have hall : ∀ α : Gal(K/F), ∀ c : Cl K,
      (QuotientGroup.mk (clMap α.toRingEquiv c) : Cl K ⧸ H) = QuotientGroup.mk c := by
    intro α
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hτ α)
    induction k using Int.induction_on with
    | zero =>
      intro c
      rw [zpow_zero, hone1]
    | succ k ih =>
      intro c
      rw [zpow_add_one, hmulc, ih, hfix]
    | pred k ih =>
      intro c
      rw [zpow_sub_one, hmulc, ih, hinv]
  have hlift : ∀ (g : G F Ω) (τ' : K ≃+* K), IsLift τ' g.toRingEquiv → ∀ c : Cl K,
      (QuotientGroup.mk (clMap τ' c) : Cl K ⧸ H) = QuotientGroup.mk c := by
    intro g τ' hl c
    unfold IsLift at hl
    have hF : ∀ x : F, τ' (algebraMap F K x) = algebraMap F K x := by
      intro x
      apply (algebraMap K Ω).injective
      rw [← hl]
      show g (algebraMap K Ω (algebraMap F K x)) = algebraMap K Ω (algebraMap F K x)
      rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
    let α : Gal(K/F) := AlgEquiv.ofRingEquiv (f := τ') hF
    have hα : α.toRingEquiv = τ' := RingEquiv.ext fun x => rfl
    rw [← hα]
    exact hall α c
  have hpowQ : powR (Cl K ⧸ H) l = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    unfold powR at hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    rw [Subgroup.mem_bot]
    show (QuotientGroup.mk c : Cl K ⧸ H) ^ l = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact le_sup_left (b := difR (clMap τ.toRingEquiv)) ⟨c, rfl⟩
  have hcardQ : H.index = Nat.card (Cl K ⧸ H →* Multiplicative (ZMod l)) := by
    rw [(cardTors (Cl K ⧸ H)).2 l, hpowQ, Subgroup.index_bot]
    rfl
  let Φ : (Cl K ⧸ H →* Multiplicative (ZMod l)) → ClEq K 1 ρ := fun ψ =>
    ⟨fun c => Multiplicative.toAdd (ψ (QuotientGroup.mk c)), by
      unfold ClEq
      rw [Submodule.mem_inf, Submodule.mem_iInf]
      refine ⟨?_, fun g => ?_⟩
      · unfold ClDual
        refine ⟨fun a b => ?_, fun v hv => ?_⟩
        · beta_reduce
          rw [QuotientGroup.mk_mul, map_mul, toAdd_mul]
        · exfalso
          unfold Above at hv
          exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using hv))
      · unfold clCond
        intro τ' hl c
        beta_reduce
        rw [hlift g τ' hl c]
        simp [ρ, scalRep]⟩
  have hΦ : Function.Injective Φ := by
    intro ψ1 ψ2 h
    apply MonoidHom.ext
    intro x
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    have h4 := congrFun (congrArg Subtype.val h) c
    exact Multiplicative.toAdd.injective h4
  calc H.index = Nat.card (Cl K ⧸ H →* Multiplicative (ZMod l)) := hcardQ
    _ ≤ Nat.card (ClEq K 1 ρ) := Nat.card_le_card_of_injective Φ hΦ
    _ = Nat.card (EqHom 1 (galOf F K Ω) ρ) := hcardEq.symm
    _ ≤ _ := hamb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.EmbedDeg
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem totient_prime_pow_add_le_pow_mul_totient (l : ℕ) (hl : l.Prime) (n k : ℕ) :
    (l ^ (n + k)).totient ≤ l ^ k * (l ^ n).totient := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using Nat.totient_le (l ^ k)
  · rw [Nat.totient_prime_pow hl (by omega), Nat.totient_prime_pow hl hn]
    have : n + k - 1 = k + (n - 1) := by omega
    rw [this, pow_add, mul_assoc]

theorem UpperTheory.V.FW.embed :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K], ∃ f D : ℕ, f.Coprime l ∧ 1 < f ∧ ∀ (n n₀ : ℕ) (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] [IsCyclotomicExtension {l ^ n} K K'], ∃ (m : ℕ) (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K' L) (_ : IsCyclotomicExtension {f * l ^ m} ℚ L), n₀ ≤ m ∧ Module.finrank K' L ≤ D * l ^ n₀ := by
  intro l hl K _ _ _
  have hp : l.Prime := hl.out
  obtain ⟨N, hN, ⟨φ⟩⟩ := CF.kwHom K
  obtain ⟨e, f₀, hf₀, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hp.one_lt.ne'
  have hf₀c : f₀.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hp).2 hf₀).symm
  have hf₀pos : 0 < f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h | h
    · simp [h] at hN
    · exact h
  have hlc : (l + 1).Coprime l := by
    simp
  refine ⟨f₀ * (l + 1), f₀ * (l + 1) * l ^ e, Nat.Coprime.mul_left hf₀c hlc, ?_, ?_⟩
  · have : 1 < l + 1 := by have := hp.one_lt; omega
    calc 1 < l + 1 := this
      _ ≤ f₀ * (l + 1) := Nat.le_mul_of_pos_left _ hf₀pos
  intro n n₀ K' _ _ _ _
  set m := n + (e + n₀) with hm
  set M := f₀ * (l + 1) * l ^ m with hM
  have hMpos : 0 < M := by
    have := hp.pos
    positivity
  haveI : NeZero M := ⟨hMpos.ne'⟩
  let L := CyclotomicField M K'
  haveI : Module.Finite K' L := IsCyclotomicExtension.finite {M} K' L
  haveI : NumberField L := NumberField.of_module_finite K' L
  have hdvdN : l ^ e * f₀ ∣ M := by
    refine ⟨(l + 1) * l ^ (n + n₀), ?_⟩
    rw [hM, hm]
    ring
  have hdvdm : l ^ n ∣ M := by
    refine ⟨f₀ * (l + 1) * l ^ (e + n₀), ?_⟩
    rw [hM, hm]
    ring
  have hcyc : IsCyclotomicExtension {M} ℚ L :=
    embCyc (l ^ e * f₀) (l ^ n) M K K' L hdvdN hdvdm ⟨φ⟩
  refine ⟨m, L, inferInstance, inferInstance, inferInstance, hcyc, by omega, ?_⟩
  have hL : Module.finrank ℚ L = M.totient := IsCyclotomicExtension.Rat.finrank M L
  have hlnpos : 0 < l ^ n := pow_pos hp.pos n
  have hK' : (l ^ n).totient ≤ Module.finrank ℚ K' := by
    have hz := IsCyclotomicExtension.zeta_spec (l ^ n) K K'
    have h1 := Polynomial.cyclotomic_eq_minpoly_rat hz hlnpos
    have h2 := minpoly.natDegree_le (A := ℚ) (IsCyclotomicExtension.zeta (l ^ n) K K')
    rw [← h1, Polynomial.natDegree_cyclotomic] at h2
    exact h2
  have htow := Module.finrank_mul_finrank ℚ K' L
  have htot : M.totient ≤ f₀ * (l + 1) * l ^ e * l ^ n₀ * (l ^ n).totient := by
    have hco : (f₀ * (l + 1)).Coprime (l ^ m) := (Nat.Coprime.mul_left hf₀c hlc).pow_right m
    rw [hM, Nat.totient_mul hco]
    calc (f₀ * (l + 1)).totient * (l ^ m).totient ≤ f₀ * (l + 1) * (l ^ m).totient :=
          Nat.mul_le_mul_right _ (Nat.totient_le _)
      _ ≤ f₀ * (l + 1) * (l ^ (e + n₀) * (l ^ n).totient) :=
          Nat.mul_le_mul_left _ (totient_prime_pow_add_le_pow_mul_totient l hp n (e + n₀))
      _ = f₀ * (l + 1) * l ^ e * l ^ n₀ * (l ^ n).totient := by
          rw [pow_add]
          ring
  have htpos : 0 < (l ^ n).totient := Nat.totient_pos.2 hlnpos
  refine Nat.le_of_mul_le_mul_right ?_ htpos
  calc Module.finrank K' L * (l ^ n).totient ≤ Module.finrank K' L * Module.finrank ℚ K' :=
        Nat.mul_le_mul_left _ hK'
    _ = M.totient := by rw [mul_comm, htow, hL]
    _ ≤ f₀ * (l + 1) * l ^ e * l ^ n₀ * (l ^ n).totient := htot
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ReflOdd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem reflOdd_index {C : Type} [CommGroup C] [Finite C] (l : ℕ) [Fact l.Prime] (H : Subgroup C)
    (hH : powR C l ≤ H) : H.index = Nat.card (C ⧸ H →* Multiplicative (ZMod l)) := by
  have hbot : powR (C ⧸ H) l = ⊥ := by
    show (powMonoidHom l : (C ⧸ H) →* (C ⧸ H)).range = ⊥
    rw [eq_bot_iff]
    rintro _ ⟨q, rfl⟩
    induction q using QuotientGroup.induction_on with
    | H c =>
      rw [Subgroup.mem_bot, powMonoidHom_apply, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hH ⟨c, rfl⟩
  rw [(cardTors (C ⧸ H)).2 l, hbot, Subgroup.index_bot]
  rfl

private theorem reflOdd_uniq {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {τ τ' : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) (h' : IsLift τ' σ) : τ = τ' := by
  ext x
  apply (algebraMap K Ω).injective
  rw [← h x, ← h' x]

theorem UpperTheory.V.FW.reflOdd :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (l : ℕ) [Fact l.Prime] (ζ : K), l ≠ 2 → IsPrimitiveRoot ζ l → (powR (Cl K) l ⊔ difR (clMap (cE K))).index ≤ l * Nat.card (minK (clMap (cE K)) ⊓ torK (Cl K) l : Subgroup (Cl K)) := by
  intro K _ _ _ l _ ζ hl2 hζ
  have hp : l.Prime := Fact.out
  haveI : NeZero l := ⟨hp.ne_zero⟩
  haveI : Fact (1 < l) := ⟨hp.one_lt⟩
  have hodd : Odd l := hp.odd_of_ne_two hl2
  obtain ⟨σ, hσ⟩ := @exists_isConjOm K (AlgebraicClosure K) _ _ _ _ _
  have hσl : IsLift (cE K) σ := hσ.isLift
  have hchi : ∀ g : G K (AlgebraicClosure K),
      g (algebraMap K (AlgebraicClosure K) ζ) =
        (algebraMap K (AlgebraicClosure K) ζ) ^
          (((1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ) g : (ZMod l)ˣ) : ZMod l).val := by
    intro g
    rw [MonoidHom.one_apply, Units.val_one, ZMod.val_one, pow_one]
    exact g.commutes ζ
  have hR := reflect K (AlgebraicClosure K) K (galOf K K (AlgebraicClosure K)) l 1 ζ 1 1 σ rfl hodd hζ hchi hσ
  have hP := pullEq K (AlgebraicClosure K) K (galOf K K (AlgebraicClosure K)) le_rfl 1 (ZMod l) (ZMod l)
    (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)) one_ne_zero le_rfl (Or.inl (by infer_instance))
  have hinj := (pullMem K (AlgebraicClosure K) K (galOf K K (AlgebraicClosure K)) le_rfl 1 (ZMod l) (ZMod l)
    one_ne_zero).2 le_rfl
  have heq := hP.2 (cE K) σ 1 hσl
  have hcardE := Nat.card_congr (Submodule.equivMapOfInjective _ hinj
    (ClEig K 1 (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)) σ (1 : ZMod l))).toEquiv
  rw [heq] at hcardE
  set H : Subgroup (Cl K) := powR (Cl K) l ⊔ difR (clMap (cE K)) with hH
  have hidx := reflOdd_index l H le_sup_left
  have hmk : ∀ c : Cl K, (QuotientGroup.mk (clMap (cE K) c) : Cl K ⧸ H) = QuotientGroup.mk c := by
    intro c
    symm
    rw [QuotientGroup.eq_iff_div_mem]
    exact le_sup_right (a := powR (Cl K) l) (⟨c, rfl⟩ : c / clMap (cE K) c ∈ difR (clMap (cE K)))
  have hmem : ∀ φ : Cl K ⧸ H →* Multiplicative (ZMod l),
      (fun c : ClassGroup (𝓞 K) => Multiplicative.toAdd (φ (QuotientGroup.mk c))) ∈
        ClEig K 1 (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)) σ (1 : ZMod l) := by
    intro φ
    unfold ClEig ClEq
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, Submodule.mem_iInf _ |>.mpr fun g => ?_⟩, ?_⟩
    · unfold ClDual
      refine ⟨fun a b => ?_, fun v hv => ?_⟩
      · simp [QuotientGroup.mk_mul]
      · have hv' : ((1 : ℕ) : 𝓞 K) ∈ v.asIdeal := hv
        rw [Nat.cast_one] at hv'
        exact absurd ((Ideal.eq_top_iff_one _).mpr hv') v.isPrime.ne_top
    · unfold clCond
      intro τ hτ c
      have h1 : τ = RingEquiv.refl K := reflOdd_uniq hτ (fun x => g.commutes x)
      subst h1
      rw [(clMapBasic K K K (RingEquiv.refl K) (RingEquiv.refl K)).1 c, scalRep_apply]
      simp
    · unfold clCond
      intro τ hτ c
      have h1 : τ = cE K := reflOdd_uniq hτ hσl
      subst h1
      simp only [LinearMap.smul_apply, LinearMap.id_apply, one_smul]
      rw [hmk c]
  let Φ : (Cl K ⧸ H →* Multiplicative (ZMod l)) →
      ClEig K 1 (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)) σ (1 : ZMod l) :=
    fun φ => ⟨_, hmem φ⟩
  have hΦ : Function.Injective Φ := by
    intro φ₁ φ₂ h
    refine MonoidHom.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H c =>
      have := congrFun (congrArg Subtype.val h) c
      simpa [Φ] using this
  have h1 : H.index ≤ Nat.card
      (ClEig K 1 (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)) σ (1 : ZMod l)) :=
    hidx ▸ Nat.card_le_card_of_injective Φ hΦ
  have h2 : Nat.card (scalRep (ZMod l) (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)).invariants ≤ l :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (Nat.card_zmod l).le
  have h3 : Nat.card ↥((ClTw K l (1 * (1 : G K (AlgebraicClosure K) →* (ZMod l)ˣ)⁻¹) ⊓ ClMinus (cE K) :
      Subgroup (ClassGroup (𝓞 K)))) ≤
      Nat.card ↥(minK (clMap (cE K)) ⊓ torK (Cl K) l : Subgroup (Cl K)) := by
    apply Subgroup.card_le_of_le
    intro c hc
    obtain ⟨hc1, hc2⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨hc2, ?_⟩
    show c ∈ (powMonoidHom l : Cl K →* Cl K).ker
    exact hc1.1
  calc H.index ≤ _ := h1
    _ = _ := hcardE
    _ ≤ _ := hR
    _ ≤ l * _ := Nat.mul_le_mul h2 h3
end

