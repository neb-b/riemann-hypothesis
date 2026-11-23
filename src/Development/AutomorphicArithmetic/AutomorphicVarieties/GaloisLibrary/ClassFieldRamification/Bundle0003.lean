module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
public import GroundTheory.GlobalFields.TateThesis.Chebotarev
public import GroundTheory.GlobalFields.KummerTheory.Splitting
public import GroundTheory.GlobalFields.SplittingFromInequality.Decomposition
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.BauerFixIff
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem UpperTheory.V.CF.bauer_fix_iff (K M N : Type) [Field K] [NumberField K] [Field M] [NumberField M]
    [Field N] [NumberField N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N]
    [IsGalois K N] (P : Ideal (𝓞 N)) [P.IsPrime] (hP : P ≠ ⊥) :
    (∀ σ : N ≃ₐ[K] N, σ • P = P → ∀ x : M, σ (algebraMap M N x) = algebraMap M N x) ↔
      (P.under (𝓞 M)).ramificationIdx (𝓞 K) * (P.under (𝓞 M)).inertiaDeg (𝓞 K) = 1 := by
  haveI : IsGalois M N := IsGalois.tower_top_of_isGalois K M N
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  have h1 := Ideal.card_stabilizer_eq (G := N ≃ₐ[K] N) (P.under (𝓞 K)) P
  have h2 := Ideal.card_stabilizer_eq (G := N ≃ₐ[M] N) (P.under (𝓞 M)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (N ≃ₐ[K] N),
    Ideal.inertiaDegIn_eq_inertiaDeg _ P (N ≃ₐ[K] N),
    Ideal.ramificationIdx_tower (P.under (𝓞 M)) P, Ideal.inertiaDeg_tower (P.under (𝓞 M)) P] at h1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (N ≃ₐ[M] N),
    Ideal.inertiaDegIn_eq_inertiaDeg _ P (N ≃ₐ[M] N)] at h2
  have h3 : Nat.card (MulAction.stabilizer (N ≃ₐ[K] N) P) =
      ((P.under (𝓞 M)).ramificationIdx (𝓞 K) * (P.under (𝓞 M)).inertiaDeg (𝓞 K)) *
        Nat.card (MulAction.stabilizer (N ≃ₐ[M] N) P) := by
    rw [h1, h2]; ring
  let j : MulAction.stabilizer (N ≃ₐ[M] N) P → MulAction.stabilizer (N ≃ₐ[K] N) P :=
    fun σ => ⟨σ.1.restrictScalars K, σ.2⟩
  have hj : Function.Injective j := by
    intro a b e
    apply Subtype.ext
    exact AlgEquiv.restrictScalars_injective K (congrArg Subtype.val e)
  have hpos : 0 < Nat.card (MulAction.stabilizer (N ≃ₐ[M] N) P) := Nat.card_pos
  constructor
  · intro h
    have hs : Function.Surjective j := by
      rintro ⟨σ, hσ⟩
      exact ⟨⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (h σ hσ), hσ⟩, rfl⟩
    have := Nat.card_eq_of_bijective j ⟨hj, hs⟩
    rw [h3] at this
    exact (Nat.eq_of_mul_eq_mul_right hpos (by rw [← this, one_mul])).symm
  · intro h σ hσ x
    rw [h, one_mul] at h3
    have hb := (Nat.bijective_iff_injective_and_card j).2 ⟨hj, h3.symm⟩
    obtain ⟨τ, hτ⟩ := hb.2 ⟨σ, hσ⟩
    have : σ = τ.1.restrictScalars K := (congrArg Subtype.val hτ).symm
    rw [this]
    exact τ.1.commutes x

private theorem UpperTheory.V.CF.bauer_fix (K A C N : Type) [Field K] [NumberField K] [Field A] [NumberField A]
    [Field C] [NumberField C] [Field N] [NumberField N] [Algebra K A] [Algebra K C] [Algebra K N]
    [Algebra A N] [Algebra C N] [IsScalarTower K A N] [IsScalarTower K C N] [IsGalois K C] [IsGalois K N]
    (T : Set (HeightOneSpectrum (𝓞 K))) (hT : T.Finite)
    (h : ∀ v ∉ T, GroundTheory.Global.SplitsCompletely C v → GroundTheory.Global.SplitsCompletely A v)
    (σ : Gal(N/K)) (hσ : ∀ x : C, σ (algebraMap C N x) = algebraMap C N x) (x : A) :
    σ (algebraMap A N x) = algebraMap A N x := by
  obtain ⟨v, hv, w, hw, he, hF⟩ := cheb K N σ T hT
  haveI := w.isPrime
  haveI := v.isPrime
  have hst := GroundTheory.Global.stabilizer_eq_zpowers_arithFrobAt v w he
  have hσF : σ = arithFrobAt (𝓞 K) Gal(N/K) w.asIdeal := by
    haveI : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := (Ideal.ramificationIdx_eq_one_iff ..).1 he
    have h1 := AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hF
      (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(N/K) w.asIdeal) (Ideal.primeCompl_le_nonZeroDivisors _)
    refine AlgEquiv.ext fun y => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 N) y
    have h2 : ∀ a : 𝓞 N, σ (algebraMap (𝓞 N) N a) =
        (arithFrobAt (𝓞 K) Gal(N/K) w.asIdeal) (algebraMap (𝓞 N) N a) := fun a =>
      congrArg (algebraMap (𝓞 N) N) (DFunLike.congr_fun h1 a)
    rw [map_div₀, map_div₀, h2, h2]
  rw [← hσF] at hst
  have hC : (w.asIdeal.under (𝓞 C)).ramificationIdx (𝓞 K) * (w.asIdeal.under (𝓞 C)).inertiaDeg (𝓞 K) = 1 := by
    refine (bauer_fix_iff K C N w.asIdeal w.ne_bot).1 fun τ hτ y => ?_
    have hτ' : τ ∈ Subgroup.zpowers σ := hst ▸ (MulAction.mem_stabilizer_iff.2 hτ)
    have : Subgroup.zpowers σ ≤ MulAction.stabilizer Gal(N/K) (algebraMap C N y) :=
      Subgroup.zpowers_le.2 (hσ y)
    exact this hτ'
  have hsC : GroundTheory.Global.SplitsCompletely C v := by
    intro u hu
    haveI := u.isPrime
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal _ Gal(C/K),
      ← Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal _ Gal(C/K)] at hC ⊢
    exact mul_eq_one.1 hC
  have hA := h v hv hsC (w.under (𝓞 A)) (inferInstanceAs ((w.asIdeal.under (𝓞 A)).LiesOver v.asIdeal))
  refine (bauer_fix_iff K A N w.asIdeal w.ne_bot).2 ?_ σ hF.mem_stabilizer x
  exact mul_eq_one.2 hA

theorem UpperTheory.V.CF.bauer :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (A C : IntermediateField K Ω) [NumberField A] [NumberField C] [IsGalois K A] [IsGalois K C] (T : Set (HeightOneSpectrum (𝓞 K))), T.Finite → (∀ v ∉ T, GroundTheory.Global.SplitsCompletely C v → GroundTheory.Global.SplitsCompletely A v) → A ≤ C := by
  intro K Ω _ _ _ _ A C _ _ _ _ T hT h
  let N : IntermediateField K Ω := A ⊔ C
  haveI : NumberField N := NumberField.of_module_finite K N
  haveI : IsGalois K N := { to_isSeparable := inferInstance, to_normal := IntermediateField.normal_sup K Ω A C }
  letI : Algebra A N := (IntermediateField.inclusion (le_sup_left : A ≤ N)).toRingHom.toAlgebra
  letI : Algebra C N := (IntermediateField.inclusion (le_sup_right : C ≤ N)).toRingHom.toAlgebra
  haveI : IsScalarTower K A N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K C N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsGalois C N := IsGalois.tower_top_of_isGalois K C N
  intro x hx
  have : algebraMap A N ⟨x, hx⟩ ∈ (⊥ : IntermediateField C N) := by
    rw [IsGalois.mem_bot_iff_fixed]
    intro τ
    exact bauer_fix K A C N T hT h (τ.restrictScalars K) τ.commutes ⟨x, hx⟩
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 this
  have : (y : Ω) = x := congrArg Subtype.val hy
  exact this ▸ y.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.BurnsideHom
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.burnsideHom :
    ∀ (p : ℕ) [Fact p.Prime] (P : Type) [Group P] [Finite P], IsPGroup p P → ∀ K : Subgroup P, (∀ f : P →* Multiplicative (ZMod p), K ≤ f.ker → f = 1) → K = ⊤ := by
  intro p _ P _ _ hP K hK
  rcases IsCoatomic.eq_top_or_exists_le_coatom K with h | ⟨M, hM, hKM⟩
  · exact h
  exfalso
  obtain ⟨hMn, hMi, -⟩ := UpperTheory.V.CF.phiLe p P hP M hM
  have hcardQ : Nat.card (P ⧸ M) = p := by rw [← Subgroup.index_eq_card, hMi]
  have hcardZ : Nat.card (Multiplicative (ZMod p)) = p := by simp
  let e : (P ⧸ M) ≃* Multiplicative (ZMod p) := mulEquivOfPrimeCardEq hcardQ hcardZ
  let f : P →* Multiplicative (ZMod p) := e.toMonoidHom.comp (QuotientGroup.mk' M)
  have hKf : K ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have : (QuotientGroup.mk' M x) = 1 := (QuotientGroup.eq_one_iff x).mpr (hKM hx)
    show e (QuotientGroup.mk' M x) = 1
    rw [this, map_one]
  have hf1 := hK f hKf
  apply hM.1
  rw [eq_top_iff]
  intro x _
  have hx : f x = 1 := by rw [hf1]; rfl
  have : QuotientGroup.mk' M x = 1 := e.injective (by simpa [f] using hx)
  exact (QuotientGroup.eq_one_iff x).mp this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.GrLocal
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.grLocal :
    ∀ (p : ℕ) [Fact p.Prime] (R G : Type) [CommRing R] [IsLocalRing R] [CommGroup G] [Finite G], (p : R) ∈ IsLocalRing.maximalIdeal R → IsPGroup p G → ∃ _ : IsLocalRing (MonoidAlgebra R G), IsLocalRing.maximalIdeal (MonoidAlgebra R G) = (IsLocalRing.maximalIdeal R).comap (aug R G) ∧ IsLocalRing.maximalIdeal (MonoidAlgebra R G) = (IsLocalRing.maximalIdeal R).map (algebraMap R (MonoidAlgebra R G)) ⊔ augIdeal R G ∧ ∀ x, IsUnit x ↔ IsUnit (aug R G x) := by
  intro p _ R G _ _ _ _ hpm hG
  set J : Ideal (MonoidAlgebra R G) := (IsLocalRing.maximalIdeal R).comap (aug R G) with hJdef
  have hJ : J.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (aug R G) (UpperTheory.V.CF.augKer R G).2
  have huniq : ∃! I : Ideal (MonoidAlgebra R G), I.IsMaximal :=
    ⟨J, hJ, fun M hM => UpperTheory.V.CF.grMaxOf p R G hpm hG M hM⟩
  letI hloc : IsLocalRing (MonoidAlgebra R G) := IsLocalRing.of_unique_max_ideal huniq
  have hmax : IsLocalRing.maximalIdeal (MonoidAlgebra R G) = J :=
    (IsLocalRing.eq_maximalIdeal hJ).symm
  have hsec : ∀ r : R, aug R G (algebraMap R (MonoidAlgebra R G) r) = r := fun r => (aug R G).commutes r
  refine ⟨hloc, hmax, ?_, ?_⟩
  · rw [hmax]
    apply le_antisymm
    · intro x hx
      have hax : aug R G x ∈ IsLocalRing.maximalIdeal R := hx
      have h1 : algebraMap R (MonoidAlgebra R G) (aug R G x) ∈
          (IsLocalRing.maximalIdeal R).map (algebraMap R (MonoidAlgebra R G)) :=
        Ideal.mem_map_of_mem _ hax
      have h2 : x - algebraMap R (MonoidAlgebra R G) (aug R G x) ∈ augIdeal R G := by
        rw [← (UpperTheory.V.CF.augKer R G).1, RingHom.mem_ker]
        show aug R G (x - algebraMap R (MonoidAlgebra R G) (aug R G x)) = 0
        rw [map_sub, hsec, sub_self]
      have : x = algebraMap R (MonoidAlgebra R G) (aug R G x) +
          (x - algebraMap R (MonoidAlgebra R G) (aug R G x)) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
    · apply sup_le
      · rw [Ideal.map_le_iff_le_comap]
        intro r hr
        show aug R G (algebraMap R (MonoidAlgebra R G) r) ∈ IsLocalRing.maximalIdeal R
        rw [hsec]
        exact hr
      · intro x hx
        rw [← (UpperTheory.V.CF.augKer R G).1, RingHom.mem_ker] at hx
        show aug R G x ∈ IsLocalRing.maximalIdeal R
        rw [show aug R G x = 0 from hx]
        exact zero_mem _
  · intro x
    constructor
    · intro hx
      exact hx.map (aug R G)
    · intro hx
      by_contra hnx
      have hxm : x ∈ IsLocalRing.maximalIdeal (MonoidAlgebra R G) := hnx
      rw [hmax] at hxm
      exact hxm hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneFixQ
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.ineFixQ :
    ∀ (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] [IsGalois ℚ K] [IsGalois ℚ H] (p : ℕ), p.Prime → (UnramAt K p ↔ ∀ w : HeightOneSpectrum (𝓞 H), (p : 𝓞 H) ∈ w.asIdeal → w.asIdeal.inertia Gal(H/ℚ) ≤ (resTo ℚ K H).ker) := by
  intro K H _ _ _ _ _ _ _ p hp
  rw [UpperTheory.V.CF.unramIff.1 K p hp]
  constructor
  · intro h w hw
    have hv : (p : 𝓞 K) ∈ w.asIdeal.under (𝓞 K) := by
      simpa [Ideal.under, Ideal.mem_comap, map_natCast] using hw
    let v : HeightOneSpectrum (𝓞 K) := ⟨w.asIdeal.under (𝓞 K), inferInstance, fun hb => by
      rw [hb] at hv
      exact (Nat.cast_ne_zero.mpr hp.ne_zero) ((Ideal.mem_bot).mp hv)⟩
    rw [← Subgroup.map_eq_bot_iff, UpperTheory.V.CF.ineMap ℚ K H w]
    exact h v hv
  · intro h v hv
    have hle : Ideal.comap (algebraMap (𝓞 K) (𝓞 H)) ⊥ ≤ v.asIdeal := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have hx0 : x = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 H) (by rw [hx, map_zero])
      rw [hx0]
      exact v.asIdeal.zero_mem
    obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal ⊥ hle
    have hpQ : (p : 𝓞 H) ∈ Q := by
      have hc : (p : 𝓞 K) ∈ Q.comap (algebraMap (𝓞 K) (𝓞 H)) := by
        change (p : 𝓞 K) ∈ Ideal.under (𝓞 K) Q
        rw [hQv]
        exact hv
      simpa [Ideal.mem_comap, map_natCast] using hc
    let w : HeightOneSpectrum (𝓞 H) := ⟨Q, hQ, fun hb => by
      rw [hb] at hpQ
      exact (Nat.cast_ne_zero.mpr hp.ne_zero) ((Ideal.mem_bot).mp hpQ)⟩
    have h1 := h w hpQ
    rw [← Subgroup.map_eq_bot_iff, UpperTheory.V.CF.ineMap ℚ K H w] at h1
    have hw : Ideal.under (𝓞 K) w.asIdeal = v.asIdeal := hQv
    rwa [hw] at h1
end

