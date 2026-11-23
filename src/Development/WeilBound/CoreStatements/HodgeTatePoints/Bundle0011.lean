module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.Gamdel
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace PositivityTheory.HtPt.Gamdel

theorem mem_mulLat_iff {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {w : Ω} (hw : w ≠ 0)
    (L : AddSubgroup V) (v : V) : v ∈ mulLat w L ↔ w⁻¹ • v ∈ L := by
  unfold GlobalTheory.CompanionTheory.Ar.Num.mulLat
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨u, hu, huv⟩
    rw [← huv]
    simpa [inv_smul_smul₀ hw] using hu
  · intro h
    exact ⟨w⁻¹ • v, h, by simp [smul_inv_smul₀ hw]⟩

theorem smul_mem_stdLat {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    (ι : Type) {a : Ω} (ha : a ∈ R) {v : ι → Ω} (hv : v ∈ stdLat R ι) : a • v ∈ stdLat R ι := by
  unfold GlobalTheory.CompanionTheory.Ar.Num.stdLat at hv ⊢
  rw [AddSubgroup.mem_pi] at hv ⊢
  intro j hj
  have hvj : v j ∈ R := by simpa using hv j hj
  simpa [smul_eq_mul] using R.mul_mem ha hvj

def graphLat {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω V'] (w : Ω) (A : AddSubgroup V) (B : AddSubgroup V') (f : V →ₗ[Ω] V') :
    AddSubgroup (V × V') where
  carrier := {p | w • p.1 ∈ A ∧ p.2 - f p.1 ∈ B}
  zero_mem' := by
    refine ⟨by simp, by simp⟩
  add_mem' := by
    rintro p q ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · have := A.add_mem h1 h3
      simpa [smul_add] using this
    · have := B.add_mem h2 h4
      convert this using 1
      simp only [Prod.snd_add, Prod.fst_add, map_add (f := _)]
      abel
  neg_mem' := by
    rintro p ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := A.neg_mem h1
      simpa [smul_neg] using this
    · have := B.neg_mem h2
      convert this using 1
      simp only [Prod.snd_neg, Prod.fst_neg, map_neg]
      abel

theorem mem_graphLat {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω V'] (w : Ω) (A : AddSubgroup V) (B : AddSubgroup V') (f : V →ₗ[Ω] V') (a : V)
    (b : V') : (a, b) ∈ graphLat w A B f ↔ w • a ∈ A ∧ b - f a ∈ B := Iff.rfl

theorem smul_mem_graphLat {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    [AddCommGroup V'] [Module Ω V'] (w : Ω) (A : AddSubgroup V) (B : AddSubgroup V')
    (f : V →ₗ[Ω] V') (a : Ω) (hA : ∀ v ∈ A, a • v ∈ A) (hB : ∀ v ∈ B, a • v ∈ B)
    (v : V × V') (hv : v ∈ graphLat w A B f) : a • v ∈ graphLat w A B f := by
  have hv' := (PositivityTheory.HtPt.Gamdel.mem_graphLat w A B f v.1 v.2).1 hv
  refine (PositivityTheory.HtPt.Gamdel.mem_graphLat w A B f (a • v).1 (a • v).2).2 ⟨?_, ?_⟩
  · rw [Prod.smul_fst, smul_smul, mul_comm, ← smul_smul]
    exact hA _ hv'.1
  · rw [Prod.smul_snd, Prod.smul_fst, map_smul, ← smul_sub]
    exact hB _ hv'.2

theorem glue_gamdel : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (w : Ω), w ∈ R → w ≠ 0 → ∀ (r s n : ℕ) (W : AddSubgroup (Fin r → Ω)) (om : AddSubgroup (Fin s → Ω)), (∀ a ∈ R, ∀ v ∈ W, a • v ∈ W) → (∀ a ∈ R, ∀ v ∈ om, a • v ∈ om) → ∀ (i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)) (q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)), (∀ a ∈ W, i a ∈ stdLat R (Fin n)) → (∀ b ∈ stdLat R (Fin n), q b ∈ om) → (∀ a ∈ W, i a ∈ mulLat w (stdLat R (Fin n)) → a ∈ mulLat w W) → (∀ b ∈ stdLat R (Fin n), q b ∈ mulLat w om ↔ ∃ a ∈ W, b - i a ∈ mulLat w (stdLat R (Fin n))) → (∀ c ∈ om, ∃ b ∈ stdLat R (Fin n), c - q b ∈ mulLat w om) → ∃ (Gam : AddSubgroup ((Fin r → Ω) × (Fin n → Ω))) (Del : AddSubgroup ((Fin n → Ω) × (Fin s → Ω))), (∀ a b, (a, b) ∈ Gam ↔ w • a ∈ W ∧ b - i a ∈ stdLat R (Fin n)) ∧ (∀ b c, (b, c) ∈ Del ↔ w • b ∈ stdLat R (Fin n) ∧ c - q b ∈ om) ∧ (∀ a ∈ R, (∀ v ∈ Gam, a • v ∈ Gam) ∧ ∀ v ∈ Del, a • v ∈ Del) ∧ ((∀ a, (∃ b, (a, b) ∈ Gam) ↔ w • a ∈ W) ∧ (∀ b, (0, b) ∈ Gam ↔ b ∈ stdLat R (Fin n)) ∧ ∀ a, (a, 0) ∈ Gam ↔ a ∈ W) ∧ ((∀ b, (∃ c, (b, c) ∈ Del) ↔ w • b ∈ stdLat R (Fin n)) ∧ (∀ c, (∃ b, (b, c) ∈ Del) ↔ w • c ∈ om) ∧ (∀ c, (0, c) ∈ Del ↔ c ∈ om) ∧ ∀ b, (b, 0) ∈ Del ↔ ∃ a, (a, b) ∈ Gam) := by
  intro o Ω _ _ _ R w hwR hw r s n W om hW hom i q hiW hqS hexW hexS hsurj
  have hS : ∀ a ∈ R, ∀ v ∈ GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n),
      a • v ∈ GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n) :=
    fun a ha v hv => PositivityTheory.HtPt.Gamdel.smul_mem_stdLat R (Fin n) ha hv
  have hmem := fun {V : Type} [AddCommGroup V] [Module Ω V] (L : AddSubgroup V) (x : V) =>
    PositivityTheory.HtPt.Gamdel.mem_mulLat_iff hw L x
  refine ⟨PositivityTheory.HtPt.Gamdel.graphLat w W (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) i,
    PositivityTheory.HtPt.Gamdel.graphLat w (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) om q,
    fun a b => PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _, fun b c => PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _,
    fun a ha => ⟨PositivityTheory.HtPt.Gamdel.smul_mem_graphLat _ _ _ _ a (hW a ha) (hS a ha),
      PositivityTheory.HtPt.Gamdel.smul_mem_graphLat _ _ _ _ a (hS a ha) (hom a ha)⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro a
    constructor
    · rintro ⟨b, hb⟩
      exact ((PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).1 hb).1
    · intro ha
      refine ⟨i a, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨ha, ?_⟩⟩
      rw [sub_self]
      exact AddSubgroup.zero_mem _
  · intro b
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, smul_zero, map_zero, sub_zero]
    exact ⟨fun h => h.2, fun h => ⟨W.zero_mem, h⟩⟩
  · intro a
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, zero_sub, neg_mem_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : i (w • a) ∈ GlobalTheory.CompanionTheory.Ar.Num.mulLat w (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) := by
        rw [hmem, map_smul, inv_smul_smul₀ hw]
        exact h2
      have h4 := hexW _ h1 h3
      rwa [hmem, inv_smul_smul₀ hw] at h4
    · intro ha
      exact ⟨hW w hwR a ha, hiW a ha⟩
  · intro b
    constructor
    · rintro ⟨c, hc⟩
      exact ((PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).1 hc).1
    · intro hb
      refine ⟨q b, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨hb, ?_⟩⟩
      rw [sub_self]
      exact AddSubgroup.zero_mem _
  · intro c
    constructor
    · rintro ⟨b, hb⟩
      rw [PositivityTheory.HtPt.Gamdel.mem_graphLat] at hb
      have h1 := hom w hwR _ hb.2
      have h2 := hqS _ hb.1
      have hc : w • c = w • (c - q b) + q (w • b) := by
        rw [map_smul, smul_sub, sub_add_cancel]
      rw [hc]
      exact om.add_mem h1 h2
    · intro hc
      obtain ⟨b0, hb0, h⟩ := hsurj _ hc
      rw [hmem, smul_sub, inv_smul_smul₀ hw] at h
      refine ⟨w⁻¹ • b0, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨?_, ?_⟩⟩
      · rwa [smul_inv_smul₀ hw]
      · rwa [map_smul]
  · intro c
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, smul_zero, map_zero, sub_zero]
    exact ⟨fun h => h.2, fun h => ⟨AddSubgroup.zero_mem _, h⟩⟩
  · intro b
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, zero_sub, neg_mem_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : q (w • b) ∈ GlobalTheory.CompanionTheory.Ar.Num.mulLat w om := by
        rw [hmem, map_smul, inv_smul_smul₀ hw]
        exact h2
      obtain ⟨a0, ha0, h4⟩ := (hexS _ h1).1 h3
      rw [hmem, smul_sub, inv_smul_smul₀ hw] at h4
      refine ⟨w⁻¹ • a0, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨?_, ?_⟩⟩
      · rwa [smul_inv_smul₀ hw]
      · rwa [map_smul]
    · rintro ⟨a, ha⟩
      rw [PositivityTheory.HtPt.Gamdel.mem_graphLat] at ha
      obtain ⟨h1, h2⟩ := ha
      have hwb : w • b ∈ GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n) := by
        have e : w • b = w • (b - i a) + i (w • a) := by
          rw [map_smul, smul_sub, sub_add_cancel]
        rw [e]
        exact AddSubgroup.add_mem _ (hS w hwR _ h2) (hiW _ h1)
      refine ⟨hwb, ?_⟩
      have h3 : w • b - i (w • a) ∈ GlobalTheory.CompanionTheory.Ar.Num.mulLat w (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) := by
        rw [hmem, map_smul, ← smul_sub, inv_smul_smul₀ hw]
        exact h2
      have h4 := (hexS _ hwb).2 ⟨w • a, h1, h3⟩
      rwa [hmem, map_smul, inv_smul_smul₀ hw] at h4

end PositivityTheory.HtPt.Gamdel
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.Gsplit
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace PositivityTheory.HtPt.Gsplit

theorem coprime_different (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ NumberField.discr E) :
    IsCoprime (Ideal.span {(p : 𝓞 E)}) (differentIdeal ℤ (𝓞 E)) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨a, b, hab⟩ := (hpz.irreducible.coprime_iff_not_dvd).mpr hd
  rw [Ideal.isCoprime_iff_exists]
  refine ⟨(a : 𝓞 E) * p, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _),
    (b : 𝓞 E) * (NumberField.discr E : 𝓞 E),
    Ideal.mul_mem_left _ _ (NumberField.discr_mem_differentIdeal E (𝓞 E)), ?_⟩
  have := congrArg (Int.cast : ℤ → 𝓞 E) hab
  push_cast at this
  exact this

theorem not_sq_dvd (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ NumberField.discr E) (w : Ideal (𝓞 E)) (hw : w ≠ ⊤) :
    ¬ w ^ 2 ∣ Ideal.span {(p : 𝓞 E)} := by
  intro h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  have hne : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hpz.ne_zero
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hdiff : w ^ (2 - 1) ∣ differentIdeal ℤ (𝓞 E) :=
    pow_sub_one_dvd_differentIdeal ℤ w 2 hne (by rw [hmap]; exact h)
  rw [show 2 - 1 = 1 from rfl, pow_one] at hdiff
  have hspan : w ∣ Ideal.span {(p : 𝓞 E)} := (dvd_pow_self w two_ne_zero).trans h
  exact hw (Ideal.isUnit_iff.mp
    ((PositivityTheory.HtPt.Gsplit.coprime_different E p hp hd).isUnit_of_dvd' hspan hdiff))

theorem glue_split : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (w : Ideal (𝓞 E)) [w.IsPrime], (p : 𝓞 E) ∈ w → ∃ ε : 𝓞 E, ε - 1 ∈ w ∧ (∀ w' : Ideal (𝓞 E), w'.IsPrime → (p : 𝓞 E) ∈ w' → w' ≠ w → ε ∈ w') ∧ (∀ a : 𝓞 E, (p : 𝓞 E) ∣ ε * a ↔ a ∈ w) ∧ (p : 𝓞 E) ∣ ε * ε - ε ∧ IsCoprime (Ideal.span {(p : 𝓞 E)}) (differentIdeal ℤ (𝓞 E)) := by
  intro E hEf hEn p hp hd w hw hpw
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hwtop : w ≠ ⊤ := hw.ne_top
  have hwbot : w ≠ ⊥ := fun h => hp0 (by rw [h] at hpw; exact Ideal.mem_bot.mp hpw)
  have hmax : w.IsMaximal := hw.isMaximal hwbot
  obtain ⟨J, hJ⟩ : w ∣ Ideal.span {(p : 𝓞 E)} := Ideal.dvd_span_singleton.mpr hpw
  have hJw : ¬ J ≤ w := by
    intro hle
    apply PositivityTheory.HtPt.Gsplit.not_sq_dvd E p hp hd w hwtop
    rw [hJ, pow_two]
    exact mul_dvd_mul_left w (Ideal.dvd_iff_le.mpr hle)
  have hsup : w ⊔ J = ⊤ := by
    by_contra hne
    apply hJw
    have heq : w ⊔ J = w := by
      by_contra h'
      exact hne (hmax.out.2 _ (lt_of_le_of_ne le_sup_left (Ne.symm h')))
    exact le_sup_right.trans heq.le
  have h1 : (1 : 𝓞 E) ∈ w ⊔ J := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨x, hx, ε, hε, hxε⟩ := Submodule.mem_sup.mp h1
  have hε1 : ε - 1 ∈ w := by
    have heq : ε - 1 = -x := by
      rw [← hxε]
      ring
    rw [heq]
    exact w.neg_mem hx
  have hεw : ε ∉ w := fun h => hwtop ((Ideal.eq_top_iff_one w).mpr (by
    have h2 := w.sub_mem h hε1
    simpa using h2))
  have hmemI : ∀ b, (p : 𝓞 E) ∣ b ↔ b ∈ w * J := by
    intro b
    rw [← Ideal.mem_span_singleton, hJ]
  refine ⟨ε, hε1, ?_, ?_, ?_, PositivityTheory.HtPt.Gsplit.coprime_different E p hp hd⟩
  · intro w' hw' hpw' hne
    have hle : w * J ≤ w' := by
      rw [← hJ, Ideal.span_singleton_le_iff_mem]
      exact hpw'
    rcases hw'.mul_le.mp hle with h | h
    · exact absurd (hmax.eq_of_le hw'.ne_top h).symm hne
    · exact h hε
  · intro a
    rw [hmemI]
    constructor
    · intro h
      have hle' : w * J ≤ w := Ideal.mul_le_left
      have hw1 : ε * a ∈ w := hle' h
      rcases hw.mem_or_mem hw1 with h' | h'
      · exact absurd h' hεw
      · exact h'
    · intro ha
      rw [mul_comm ε a]
      exact Ideal.mul_mem_mul ha hε
  · rw [hmemI]
    have heq : ε * ε - ε = (ε - 1) * ε := by ring
    rw [heq]
    exact Ideal.mul_mem_mul hε1 hε

end PositivityTheory.HtPt.Gsplit
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBuild
section
noncomputable section

namespace PositivityTheory.HtPt.Htat

open GlobalTheory.CompanionTheory.Ar.HT NumberField TensorProduct

theorem chart_build : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p R N : ℕ) (W Ω : Type) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Projective A W] [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (j : W →ₗ[A] Ω), IsBaseChange K j → ∀ (ρ : 𝓞 E →+* Module.End A W) (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)) (h : (Fin N → 𝓞 E) →+ W), (∀ x, e x x = 0) → (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv c a • y)) → (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ R), ∃ x, e x = φ) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → (∀ (a : 𝓞 E) x, ∃ y, h (a • x) = ρ a (h x) + (p ^ R) • y) → ∃ D : HTChart A K c p R N Ω, D.om = LinearMap.range j ∧ D.e = e ∧ (∀ x, D.h x = j (h x)) ∧ ∀ a w, D.ρΩ a (j w) = j (ρ a w) := by
  intro A K _ _ _ _ _ E _ _ c p R N W Ω _ _ _ _ _ _ _ _ j hj ρ e h halt hadj hsurj hinj hlin
  classical
  have hsym : ∀ w : W, hj.equiv.symm (j w) = (1 : K) ⊗ₜ[A] w := by
    intro w
    rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
  let T : 𝓞 E →+* Module.End K (K ⊗[A] W) := (Module.End.baseChangeHom A K W).toRingHom.comp ρ
  have hT : ∀ a (w : W), T a ((1 : K) ⊗ₜ[A] w) = (1 : K) ⊗ₜ[A] (ρ a w) := fun a w => rfl
  let ρΩ : 𝓞 E →+* Module.End K Ω :=
    { toFun := fun a => hj.equiv.toLinearMap ∘ₗ T a ∘ₗ hj.equiv.symm.toLinearMap
      map_one' := by ext x; simp
      map_mul' := by intro a b; ext x; simp [Module.End.mul_apply]
      map_zero' := by ext x; simp
      map_add' := by intro a b; ext x; simp }
  have hρ : ∀ a w, ρΩ a (j w) = j (ρ a w) := by
    intro a w
    show hj.equiv (T a (hj.equiv.symm (j w))) = _
    rw [hsym, hT, IsBaseChange.equiv_tmul, one_smul]
  have hinjj : Function.Injective j := by
    have h1 : Function.Injective ((Algebra.linearMap A K).rTensor W) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective A K)
    intro x y hxy
    apply (TensorProduct.lid A W).symm.injective
    apply h1
    apply hj.equiv.injective
    simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one,
      IsBaseChange.equiv_tmul, one_smul]
    exact hxy
  have hfg : (LinearMap.range j).FG := Module.Finite.iff_fg.mp (Module.Finite.range j)
  have hspan : Submodule.span K (LinearMap.range j : Set Ω) = ⊤ := by
    rw [eq_top_iff]
    intro ω hω
    clear hω
    obtain ⟨t, rfl⟩ := hj.equiv.surjective ω
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      rw [IsBaseChange.equiv_tmul]
      exact Submodule.smul_mem _ s (Submodule.subset_span ⟨w, rfl⟩)
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
  have hproj : Module.Projective A (LinearMap.range j) :=
    Module.Projective.of_equiv (LinearEquiv.ofInjective j hinjj)
  refine ⟨{ om := LinearMap.range j
            om_lat := by
              have hfull : Submodule.IsFullLattice K (LinearMap.range j) :=
                { toIsLattice := Submodule.IsLattice.of_fg K hfg, span_eq_top := hspan }
              first | exact hfull | exact hfull.toIsLattice
            om_proj := hproj
            ρΩ := ρΩ
            om_stable := ?_
            e := e
            alt := halt
            adj := hadj
            e_surj := hsurj
            e_inj := hinj
            h := j.toAddMonoidHom.comp h
            h_mem := fun x => ⟨h x, rfl⟩
            h_lin := ?_ }, rfl, rfl, fun x => rfl, hρ⟩
  · rintro a x ⟨w, rfl⟩
    exact ⟨ρ a w, (hρ a w).symm⟩
  · intro a x
    obtain ⟨y, hy⟩ := hlin a x
    refine ⟨j y, ⟨y, rfl⟩, ?_⟩
    show j (h (a • x)) = ρΩ a (j (h x)) + p ^ R • j y
    rw [hy, map_add (f := _), map_nsmul, hρ]

end PositivityTheory.HtPt.Htat
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.InChartOfMemCtrSet
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb

theorem mem_ctrSet_of {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {i : Ω →+* Ω'} {p' : Cpt ξ'}
    (c : κ) (hc : x c ≠ 0) (ho : ∀ r : o, i (algebraMap o Ω r) ∈ regAt ξ' p')
    (hx : ∀ j, i (x j / x c) ∈ regAt ξ' p') : p' ∈ ctrSet o x i ξ' := by
  refine ⟨c, hc, fun a ha => ?_⟩
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact hx j
  | algebraMap r => exact ho r
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

theorem join_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ κ' : Type) (x : κ → Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (w : κ' → Ω') (M' : PModel o (joinCo i x w)), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → ∀ p' : Cpt M'.ξ, p' ∈ ctrSet o x i M'.ξ ∧ ∃ l, InChart M'.ξ w l p' := by
  intro o _ Ω _ _ κ κ' x Ω' _ _ i w M' hi p'
  obtain ⟨⟨c, l⟩, hc⟩ := M'.tie.cover p'
  have h0 : i (x c) * w l ≠ 0 := hc.1
  have h1 := left_ne_zero_of_mul h0
  have h2 := right_ne_zero_of_mul h0
  refine ⟨mem_ctrSet_of c ((map_ne_zero i).1 h1) (fun r => ?_) fun j => ?_, l, h2, fun j => ?_⟩
  · rw [hi]
    exact (M'.tie.ring (c, l) hc.1 _).1 (Subalgebra.algebraMap_mem _ r) p' hc
  · have := hc.2 (j, l)
    simp only [joinCo] at this
    rwa [mul_div_mul_right _ _ h2, ← map_div₀] at this
  · have := hc.2 (c, j)
    simp only [joinCo] at this
    rwa [mul_div_mul_left _ _ h1] at this

end PositivityTheory.HtPt.Mb
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Ma

theorem reg_open : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω), a ∈ regAt ξ p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q :=
  fun _ _ _ ξ p a ha => exists_open_mem_regAt ξ p a ha

theorem reg_local : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ p : Cpt ξ, IsLocalRing (regAt ξ p)) ∧ (∀ p q : Cpt ξ, q.1 ⤳ p.1 → regAt ξ p ≤ regAt ξ q) ∧ (IsCptGen ξ → ∀ (p : Cpt ξ) (a : Ω), ∃ u ∈ regAt ξ p, ∃ v ∈ regAt ξ p, v ≠ 0 ∧ a = u / v) := by
  intro X Ω _ ξ
  refine ⟨fun p => ?_, fun p q h => (RegAtMono.regAt_mono X Ω ξ p q h).1, fun hg p a => ?_⟩
  · unfold regAt
    exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (RingHom.rangeRestrict_surjective _)
  · haveI := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg p).2.1
    obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := regAt ξ p) a
    refine ⟨u, u.2, v, v.2, fun h => ?_, rfl⟩
    exact nonZeroDivisors.ne_zero hv (Subtype.ext h)

theorem regat_loc : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ), InChart M.ξ x c p → (∀ a ∈ chRing o x c, a ∈ regAt M.ξ p) ∧ ∀ a : Ω, a ∈ regAt M.ξ p ↔ ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, unitAt M.ξ p v ∧ a = u / v := by
  intro o _ Ω _ _ κ _ x M c p hp
  have h1 : ∀ a ∈ chRing o x c, a ∈ regAt M.ξ p := fun a ha => (M.tie.ring c hp.1 a).1 ha p hp
  refine ⟨h1, fun a => ⟨fun ha => ?_, ?_⟩⟩
  · obtain ⟨s, hs, hu, hsa⟩ := (regAt_iff_exists_chart_fraction M.X Ω M.ξ o κ x M.tie c p hp a).1 ha
    exact ⟨s * a, hsa, s, hs, hu, by field_simp [hu.1]⟩
  · rintro ⟨u, hu, v, -, hv, rfl⟩
    rw [div_eq_mul_inv]
    exact mul_mem (h1 u hu) hv.2.2

theorem prime_pt : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ), x c ≠ 0 → ∀ P : Ideal (chRing o x c), P.IsPrime → ∃! p : Cpt M.ξ, InChart M.ξ x c p ∧ ∀ u : chRing o x c, u ∈ P ↔ ¬ unitAt M.ξ p (u : Ω) := by
  intro o _ Ω _ _ κ _ x M c hc P hP
  obtain ⟨p, ⟨h1, h2⟩, h3⟩ := chart_point_of_prime M.X Ω M.ξ o κ x M.tie c hc P hP
  refine ⟨p, ⟨h1, fun u => ?_⟩, fun q hq => h3 q ⟨hq.1, fun u => ?_⟩⟩
  · rw [← h2 u, not_not]
  · rw [hq.2 u, not_not]

open ChartPrimes in
theorem basic : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ) (U : M.X.Opens), InChart M.ξ x c p → p.1 ∈ U → ∃ f ∈ chRing o x c, unitAt M.ξ p f ∧ ∀ q : Cpt M.ξ, InChart M.ξ x c q → unitAt M.ξ q f → q.1 ∈ U := by
  intro o _ Ω _ _ κ _ x M c p U hp hpU
  have T := M.tie
  have hc := hp.1
  obtain ⟨W, hW, hmem⟩ := T.affine c hc
  have hg : genPt M.ξ ∈ W := (hmem _).2 ⟨specializes_rfl, inChart_genPt T.gen x c hc⟩
  have hpW : p.1 ∈ W := (hmem _).2 ⟨p.2, hp⟩
  obtain ⟨f, hf, hpf⟩ := hW.exists_basicOpen_le (V := U) ⟨p.1, hpU⟩ hpW
  have key : ∀ (q : Cpt M.ξ) (hq : q.1 ∈ W), q.1 ∈ M.X.basicOpen f ↔ unitAt M.ξ q (secVal M.ξ W hg f) := by
    intro q hq
    rw [M.X.mem_basicOpen f _ hq, ← genMap_germ_eq W hg q hq f]
    exact isUnit_iff_unitAt q (T.gen.inj _) _
  refine ⟨secVal M.ξ W hg f, ?_, (key p hpW).1 hpf, fun q hq hu => hf ((key q ((hmem _).2 ⟨q.2, hq⟩)).2 hu)⟩
  exact (T.ring c hc _).2 fun q hq => ⟨_, genMap_germ_eq W hg q ((hmem _).2 ⟨q.2, hq⟩) f⟩

theorem reg_le_spec : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (p q : Cpt M.ξ), regAt M.ξ p ≤ regAt M.ξ q ↔ q.1 ⤳ p.1 := by
  intro o _ Ω _ _ κ _ x M p q
  refine ⟨fun h => ?_, (reg_local M.X Ω M.ξ).2.1 p q⟩
  rw [specializes_iff_forall_open]
  intro s hs hp
  obtain ⟨c, hc⟩ := M.tie.cover p
  obtain ⟨f, -, hu, hf⟩ := basic o Ω κ x M c p ⟨s, hs⟩ hc hp
  exact hf q ⟨hc.1, fun j => h (hc.2 j)⟩ ⟨hu.1, h hu.2.1, h hu.2.2⟩

end PositivityTheory.HtPt.Ma
end

