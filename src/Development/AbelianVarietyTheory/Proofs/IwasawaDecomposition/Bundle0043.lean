module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntValuationNormEqSumResidueDegreeMul
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

noncomputable section

namespace GlobalTheory.NormValuation

def exponent {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R) (I : Ideal R) : ℕ :=
  (Associates.mk w.asIdeal).count (Associates.mk I).factors

section
variable {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R)

theorem exponent_mul {I J : Ideal R} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    exponent w (I * J) = exponent w I + exponent w J := by
  unfold exponent
  rw [← Associates.mk_mul_mk, Associates.count_mul (Associates.mk_ne_zero.2 hI)
    (Associates.mk_ne_zero.2 hJ) w.associates_irreducible]

theorem exponent_pow {I : Ideal R} (hI : I ≠ ⊥) (n : ℕ) :
    exponent w (I ^ n) = n * exponent w I := by
  unfold exponent
  rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.2 hI) w.associates_irreducible]

theorem exponent_self : exponent w w.asIdeal = 1 :=
  Associates.count_self w.associates_irreducible

theorem exponent_top : exponent w ⊤ = 0 := by
  unfold exponent
  rw [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one,
    Associates.count_zero w.associates_irreducible]

theorem exponent_prime_of_ne (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) (h : p ≠ w.asIdeal) :
    exponent w p = 0 := by
  unfold exponent
  refine Associates.count_eq_zero_of_ne w.associates_irreducible
    (HeightOneSpectrum.associates_irreducible ⟨p, inferInstance, hp⟩) ?_
  intro h1
  exact h (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 h1)).symm

theorem log_valuation_of_integer (F : Type) [Field F] [Algebra R F] [IsFractionRing R F] (x : R) (hx : x ≠ 0) :
    WithZero.log (w.valuation F (algebraMap R F x)) = -(exponent w (Ideal.span {x}) : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, w.intValuation_if_neg hx, WithZero.log_exp, exponent]

end

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

theorem exponent_relNorm_prime (v : HeightOneSpectrum (𝓞 E)) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)
    (p : Ideal (𝓞 K)) [p.IsPrime] (hp : p ≠ ⊥) :
    (exponent v (Ideal.relNorm (𝓞 E) p) : ℤ) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * (exponent w p : ℤ) := by
  have : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp inferInstance
  have hq : p.under (𝓞 E) ≠ ⊥ := Ideal.under_ne_bot (𝓞 E) hp
  have : (p.under (𝓞 E)).IsMaximal := Ring.DimensionLEOne.maximalOfPrime hq inferInstance
  rw [Ideal.relNorm_eq_pow_of_isMaximal p (p.under (𝓞 E)), exponent_pow v hq]
  by_cases h : p.under (𝓞 E) = v.asIdeal
  · let w0 : HeightOneSpectrum (𝓞 K) := ⟨p, inferInstance, hp⟩
    have hw0 : w0 ∈ s := (hs w0).2 h
    rw [Finset.sum_eq_single w0]
    · rw [h, exponent_self, exponent_self]
      simp [w0]
    · intro w _ hw
      rw [exponent_prime_of_ne w p hp, Nat.cast_zero, mul_zero]
      intro he
      exact hw (HeightOneSpectrum.ext he.symm)
    · intro h'; exact absurd hw0 h'
  · rw [exponent_prime_of_ne v _ hq h, mul_zero, Nat.cast_zero]
    refine (Finset.sum_eq_zero fun w hw => ?_).symm
    rw [exponent_prime_of_ne w p hp, Nat.cast_zero, mul_zero]
    intro he
    apply h
    rw [← (hs w).1 hw, he]

theorem exponent_relNorm (v : HeightOneSpectrum (𝓞 E)) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)
    (I : Ideal (𝓞 K)) : I ≠ ⊥ →
    (exponent v (Ideal.relNorm (𝓞 E) I) : ℤ) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * (exponent w I : ℤ) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h => absurd rfl h
  | h₂ x hx =>
    intro _
    rw [Ideal.isUnit_iff.1 hx, Ideal.relNorm_top, exponent_top]
    simp [exponent_top]
  | h₃ a p ha hp ih =>
    intro _
    have : p.IsPrime := Ideal.isPrime_of_prime hp
    have hp0 : p ≠ ⊥ := hp.ne_zero
    rw [map_mul, exponent_mul v (Ideal.relNorm_eq_bot_iff.not.2 hp0)
      (Ideal.relNorm_eq_bot_iff.not.2 ha), Nat.cast_add, exponent_relNorm_prime v s hs p hp0, ih ha,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [exponent_mul w hp0 ha, Nat.cast_add, mul_add]

end GlobalTheory.NormValuation

namespace GlobalTheory.NormValuation

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

theorem log_valuation_norm_integer (v : HeightOneSpectrum (𝓞 E)) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)
    (x : 𝓞 K) (hx : x ≠ 0) :
    WithZero.log (v.valuation E (Algebra.norm E (algebraMap (𝓞 K) K x))) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * WithZero.log (w.valuation K (algebraMap (𝓞 K) K x)) := by
  have h1 : algebraMap (𝓞 E) E (Algebra.intNorm (𝓞 E) (𝓞 K) x) = Algebra.norm E (algebraMap (𝓞 K) K x) :=
    Algebra.algebraMap_intNorm (A := 𝓞 E) (K := E) (L := K) (B := 𝓞 K) x
  have h2 : Algebra.intNorm (𝓞 E) (𝓞 K) x ≠ 0 := by
    intro h0
    have : Algebra.norm E (algebraMap (𝓞 K) K x) = 0 := by rw [← h1, h0, map_zero]
    rw [Algebra.norm_eq_zero_iff] at this
    exact hx ((FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).1 this)
  have hI : Ideal.span {x} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [← h1, log_valuation_of_integer v E _ h2, ← Ideal.relNorm_singleton,
    exponent_relNorm v s hs _ hI, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [log_valuation_of_integer w K x hx, mul_neg]

theorem log_valuation_norm (v : HeightOneSpectrum (𝓞 E)) (a : Kˣ) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal) :
    WithZero.log (v.valuation E (Algebra.norm E (a : K))) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * WithZero.log (w.valuation K (a : K)) := by
  obtain ⟨b, c, hc, h⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (a : K)
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply a.ne_zero
    rw [← h, map_zero, zero_div]
  have hK : ∀ y : 𝓞 K, y ≠ 0 → algebraMap (𝓞 K) K y ≠ 0 := fun y hy =>
    (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).not.2 hy
  have hN : ∀ y : 𝓞 K, y ≠ 0 → Algebra.norm E (algebraMap (𝓞 K) K y) ≠ 0 := fun y hy =>
    Algebra.norm_ne_zero_iff.2 (hK y hy)
  have hdiv : Algebra.norm E (algebraMap (𝓞 K) K b / algebraMap (𝓞 K) K c) =
      Algebra.norm E (algebraMap (𝓞 K) K b) / Algebra.norm E (algebraMap (𝓞 K) K c) := by
    rw [eq_div_iff (hN c hc0), ← map_mul, div_mul_cancel₀ _ (hK c hc0)]
  rw [← h, hdiv, map_div₀, WithZero.log_div ((Valuation.ne_zero_iff _).2 (hN b hb0))
    ((Valuation.ne_zero_iff _).2 (hN c hc0)), log_valuation_norm_integer v s hs b hb0,
    log_valuation_norm_integer v s hs c hc0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_div₀, WithZero.log_div ((Valuation.ne_zero_iff _).2 (hK b hb0))
    ((Valuation.ne_zero_iff _).2 (hK c hc0)), mul_sub]

end GlobalTheory.NormValuation

theorem GlobalTheory.NormValuation.log_valuation_norm_eq_sum : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (v : HeightOneSpectrum (𝓞 E)) (a : Kˣ) (s : Finset (HeightOneSpectrum (𝓞 K))), (∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal) → WithZero.log (v.valuation E (Algebra.norm E (a : K))) = ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * WithZero.log (w.valuation K (a : K)) :=
  fun _ _ _ _ _ _ _ v a s hs => GlobalTheory.NormValuation.log_valuation_norm v a s hs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNilpotentZpowSubOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.FrobSemisimpleUnique

theorem isNilpotent_zpow_sub_one {R : Type*} [Ring R] (u : Rˣ) (hu : IsNilpotent ((u : R) - 1))
    (d : ℤ) : IsNilpotent (((u ^ d : Rˣ) : R) - 1) := by
  have hnat : ∀ n : ℕ, IsNilpotent (((u ^ n : Rˣ) : R) - 1) := by
    intro n
    rw [Units.val_pow_eq_pow_val, ← geom_sum_mul]
    refine Commute.isNilpotent_mul_left ?_ hu
    refine Commute.sum_left _ _ _ fun i _ => ?_
    exact ((Commute.refl (u : R)).sub_right (Commute.one_right _)).pow_left i
  obtain ⟨n, rfl | rfl⟩ := d.eq_nat_or_neg
  · rw [zpow_natCast]; exact hnat n
  · rw [zpow_neg, zpow_natCast]
    have h1 := hnat n
    generalize u ^ n = v at h1
    have h2 : ((v⁻¹ : Rˣ) : R) - 1 = -(((v⁻¹ : Rˣ) : R) * ((v : R) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [h2]
    refine (Commute.isNilpotent_mul_left ?_ h1).neg
    exact ((Commute.refl v).inv_left.units_val).sub_right (Commute.one_right _)

theorem nilpotent_part {R : Type*} [Ring R] {f s : R} (v : Rˣ) (hv : IsNilpotent ((v : R) - 1))
    (hc : Commute (v : R) f) (hf : f = s * v) : IsNilpotent (f - s) ∧ Commute (f - s) s := by
  have hs : s = f * ((v⁻¹ : Rˣ) : R) := by rw [hf, Units.mul_inv_cancel_right]
  have hvs : Commute (v : R) s := by
    rw [hs]
    exact hc.mul_right (Commute.refl v).inv_right.units_val
  have h1 : f - s = s * ((v : R) - 1) := by rw [hf, mul_sub, mul_one]
  have h2 : Commute s ((v : R) - 1) := hvs.symm.sub_right (Commute.one_right _)
  rw [h1]
  exact ⟨h2.isNilpotent_mul_left hv, (Commute.refl s).mul_left h2.symm⟩

end GlobalTheory.WeilDeligne.FrobSemisimpleUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.OpenIdeleCongr

variable {F : Type} [Field F] [NumberField F]

theorem exists_ne_zero_lt_val_subset_of_mem_nhds {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] {s : Set K} {x : K} :
    s ∈ nhds x → ∃ c : K, c ≠ 0 ∧ {y | Valued.v (y - x) < Valued.v c} ⊆ s := by
  rw [Valued.mem_nhds]
  rintro ⟨γ, hγ⟩
  obtain ⟨c, hc⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass (Valued.v : Valuation K Γ)) γ.1
  have hc' : (Valued.v : Valuation K Γ).restrict c = γ.1 := hc
  refine ⟨c, ?_, fun y hy => hγ ?_⟩
  · rintro rfl
    rw [map_zero] at hc'
    exact γ.ne_zero hc'.symm
  · change (Valued.v : Valuation K Γ).restrict (y - x) < γ.1
    rw [← hc', Valuation.restrict_lt_iff]
    exact hy

theorem exists_exp_of_nhds (v : HeightOneSpectrum (𝓞 F)) (u : Set (v.adicCompletion F)) (hu : u ∈ nhds 1) :
    ∃ M : ℕ, ∀ y : v.adicCompletion F, Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ)) → y ∈ u := by
  obtain ⟨c, hc, hsub⟩ := exists_ne_zero_lt_val_subset_of_mem_nhds hu
  have h0 : Valued.v c ≠ 0 := by simpa using hc
  set k := WithZero.log (Valued.v c) with hkdef
  have hk : Valued.v c = WithZero.exp k := (WithZero.exp_log h0).symm
  refine ⟨(-k).toNat + 1, fun y hy => hsub ?_⟩
  show Valued.v (y - 1) < Valued.v c
  refine lt_of_le_of_lt hy ?_
  rw [hk, WithZero.exp_lt_exp]
  have := Int.self_le_toNat (-k)
  push_cast
  omega

end GlobalTheory.OpenIdeleCongr

namespace GlobalTheory.OpenIdeleCongr

variable {F : Type} [Field F] [NumberField F]

theorem isOpen_adicIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  Valued.isOpen_valuationSubring _

theorem finiteSingle_mem_of_nhds (Vf : Set (FiniteAdeleRing (𝓞 F) F)) (hV : Vf ∈ nhds (1 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 F))) (M : ℕ), S.Finite ∧ ∀ v (y : v.adicCompletion F),
      y ∈ v.adicCompletionIntegers F → (v ∈ S → Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ))) →
      finiteSingle F v y ∈ Vf := by
  classical
  have hσ := RestrictedProduct.isOpenEmbedding_structureMap (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) isOpen_adicIntegers
  have h1 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite 1 = 1 :=
    RestrictedProduct.ext _ _ fun i => rfl
  have h2 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite ⁻¹' Vf ∈ nhds 1 := by
    apply hσ.continuous.continuousAt.preimage_mem_nhds
    rw [h1]
    exact hV
  rw [nhds_pi, Filter.mem_pi] at h2
  obtain ⟨I, hI, t, ht, hsub⟩ := h2
  have hM : ∀ i : HeightOneSpectrum (𝓞 F), ∃ M : ℕ, ∀ (y : i.adicCompletion F) (hy : y ∈ i.adicCompletionIntegers F),
      Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ)) → (⟨y, hy⟩ : ((i.adicCompletionIntegers F : Set (i.adicCompletion F)))) ∈ t i := by
    intro i
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).mp (ht i)
    obtain ⟨M, hM⟩ := exists_exp_of_nhds i u hu
    exact ⟨M, fun y hy h => hut (hM y h)⟩
  choose M hMs using hM
  refine ⟨I, hI.toFinset.sup M, hI, fun v y hy hS => ?_⟩
  have hmem : (Pi.mulSingle v (⟨y, hy⟩ : ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) :
      (i : HeightOneSpectrum (𝓞 F)) → ((i.adicCompletionIntegers F : Set (i.adicCompletion F)))) ∈ I.pi t := by
    intro i hi
    by_cases hne : i = v
    · subst hne
      rw [Pi.mulSingle_eq_same]
      refine hMs i y hy ((hS hi).trans ?_)
      rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
      exact Finset.le_sup (hI.mem_toFinset.2 hi)
    · rw [Pi.mulSingle_eq_of_ne hne]
      exact mem_of_mem_nhds (ht i)
  have hg := hsub hmem
  have e : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite (Pi.mulSingle v ⟨y, hy⟩) =
      finiteSingle F v y := by
    apply RestrictedProduct.ext
    intro i
    rw [RestrictedProduct.structureMap_apply]
    show _ = Pi.mulSingle v y i
    by_cases hi : i = v
    · subst hi
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi]
      rfl
  rw [← e]
  exact hg

end GlobalTheory.OpenIdeleCongr

namespace GlobalTheory.OpenIdeleCongr

variable {F : Type} [Field F] [NumberField F]

theorem localIdele_mem_of_isOpen (V : Subgroup (Ideles F)) (hV : IsOpen (V : Set (Ideles F))) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 F))) (M : ℕ), S.Finite ∧ ∀ v (x : (v.adicCompletion F)ˣ),
      Valued.v (x : v.adicCompletion F) = 1 →
      (v ∈ S → Valued.v ((x : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M : ℤ))) → localIdele F v x ∈ V := by
  obtain ⟨W, hWo, hWU⟩ := Units.isInducing_embedProduct.isOpen_iff.mp hV
  have hW1 : Units.embedProduct _ (1 : Ideles F) ∈ W := by
    rw [← Set.mem_preimage, hWU]
    exact V.one_mem
  rw [map_one] at hW1
  obtain ⟨W1, hW1n, W2, hW2n, hprod⟩ := mem_nhds_prod_iff.mp (hWo.mem_nhds hW1)
  have hW2' : MulOpposite.op ⁻¹' W2 ∈ nhds (1 : AdeleRing (𝓞 F) F) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hW2n
  have hN : W1 ∩ MulOpposite.op ⁻¹' W2 ∈ nhds ((1 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) :=
    Filter.inter_mem hW1n hW2'
  obtain ⟨Vi, hVi, Vf, hVf, hVprod⟩ := mem_nhds_prod_iff.mp hN
  obtain ⟨S, M, hS, hSV⟩ := finiteSingle_mem_of_nhds Vf hVf
  refine ⟨S, M, hS, fun v x hx hxS => ?_⟩
  have hin : ∀ y : (v.adicCompletion F)ˣ, Valued.v (y : v.adicCompletion F) = 1 →
      (v ∈ S → Valued.v ((y : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M : ℤ))) →
      ((localIdele F v y : Ideles F) : AdeleRing (𝓞 F) F) ∈ W1 ∩ MulOpposite.op ⁻¹' W2 := fun y hy hyS =>
    hVprod ⟨mem_of_mem_nhds hVi, hSV v _ (by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hy.le) hyS⟩
  have hxi : Valued.v ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  have hxiS : v ∈ S → Valued.v (((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤
      WithZero.exp (-(M : ℤ)) := by
    intro hv
    have e : ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1 =
        ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * -((x : v.adicCompletion F) - 1) := by
      rw [mul_neg, mul_sub, Units.inv_mul, mul_one]; ring
    rw [e, map_mul, Valuation.map_neg, hxi, one_mul]
    exact hxS hv
  have h1 := hin x hx hxS
  have h2 := hin x⁻¹ hxi hxiS
  rw [← SetLike.mem_coe, ← hWU, Set.mem_preimage, Units.embedProduct_apply]
  refine hprod ⟨h1.1, ?_⟩
  have h3 := h2.2
  rw [map_inv] at h3
  exact h3

theorem open_subgroup_contains_congr : ∀ (F : Type) [Field F] [NumberField F] (V : Subgroup (Ideles F)),
    IsOpen (V : Set (Ideles F)) → ∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (M : ℕ), S₀ ⊆ S ∧
      (∀ v ∉ S, ∀ x, IsUnitAt v x → localIdele F v x ∈ V) ∧
      ∀ v ∈ S, ∀ a : Fˣ, v.valuation F ((a : F) - 1) ≤ WithZero.exp (-(M : ℤ)) → locUnit F v a ∈ V := by
  intro F _ _ V hV S₀
  classical
  obtain ⟨S₁, M₁, hS₁, key⟩ := localIdele_mem_of_isOpen V hV
  refine ⟨S₀ ∪ hS₁.toFinset, M₁ + 1, Finset.subset_union_left, fun v hv x hx => ?_, fun v _ a ha => ?_⟩
  · refine key v x hx fun hv' => absurd (Finset.mem_union_right _ (hS₁.mem_toFinset.2 hv')) hv
  · rw [locUnit_apply]
    set x := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a with hxdef
    have hxv : (x : v.adicCompletion F) = ((a : F) : v.adicCompletion F) := rfl
    have hsub : Valued.v ((x : v.adicCompletion F) - 1) = v.valuation F ((a : F) - 1) := by
      have e : (x : v.adicCompletion F) - 1 = (((a : F) - 1 : F) : v.adicCompletion F) := by
        show algebraMap F (v.adicCompletion F) (a : F) - 1 = _
        rw [← map_one (algebraMap F (v.adicCompletion F)), ← map_sub]
        rfl
      rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have hle : Valued.v ((x : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M₁ : ℤ)) := by
      rw [hsub]
      refine ha.trans ?_
      rw [WithZero.exp_le_exp]
      push_cast
      omega
    have hlt : Valued.v ((x : v.adicCompletion F) - 1) < 1 := by
      rw [hsub]
      refine lt_of_le_of_lt ha ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      push_cast
      omega
    have hunit : Valued.v (x : v.adicCompletion F) = 1 := by
      have := Valuation.map_one_add_of_lt _ hlt
      rwa [add_sub_cancel] at this
    exact key v x hunit fun _ => hle

end GlobalTheory.OpenIdeleCongr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPurePairIffMonodromyFiltration
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

section Graded

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {U : ℤ → Submodule K V}
  {N : End K V}

theorem eq_zero_of_pow_eq_zero (hb : ∀ i : ℕ, Set.BijOn (N ^ i) (U (-i)) (U i)) {m : ℕ} {d : ℤ}
    (hd : d + m ≤ 0) {v : V} (hv : v ∈ U d) (h0 : (N ^ m) v = 0) : v = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, d = -((c + m : ℕ) : ℤ) := ⟨(-d - m).toNat, by omega⟩
  subst hc
  refine (hb (c + m)).2.1 hv (zero_mem _) ?_
  rw [pow_add, End.mul_apply, h0, map_zero, map_zero]

end Graded

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTorusWeightOfPolyRepCompSwap
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory

theorem isWt_comp_swap : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ),
    IsPolyRep Φ → ∀ μ : Fin n → ℤ, IsWt Φ μ → ∀ i j : Fin n, IsWt Φ (μ ∘ Equiv.swap i j) := by
  intro n ι _ _ Φ hΦ μ ⟨w, hw0, hw⟩ i j
  set σ : Equiv.Perm (Fin n) := Equiv.swap i j with hσ
  set P : Matrix (Fin n) (Fin n) ℂ := σ.toPEquiv.toMatrix with hP
  have hσσ : ∀ k, σ (σ k) = k := fun k => Equiv.swap_apply_self _ _ _
  have hPP : P * P = 1 := by
    rw [hP, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
    have : σ.trans σ = Equiv.refl _ := by ext k; simp [hσσ]
    rw [this, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  let p : GL (Fin n) ℂ := ⟨P, P, hPP, hPP⟩
  have hpp : p * p = 1 := Units.ext hPP
  refine ⟨Φ p *ᵥ w, ?_, ?_⟩
  · intro h
    apply hw0
    have : Φ p *ᵥ (Φ p *ᵥ w) = 0 := by rw [h]; simp
    rwa [mulVec_mulVec, ← hΦ.mul, hpp, hΦ.one, one_mulVec] at this
  · intro D hD
    have hent : ∀ a b, (p * D * p).val a b = D.val (σ a) (σ b) := by
      intro a b
      show (P * D.val * P) a b = _
      rw [hP, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
      simp [hσ, Equiv.symm_swap]
    have hD' : (p * D * p).val.IsDiag := by
      intro a b hab
      rw [hent]
      exact hD (fun h => hab (σ.injective h))
    have key : Φ D * Φ p = Φ p * Φ (p * D * p) := by
      rw [← hΦ.mul, ← hΦ.mul]
      congr 1
      rw [← mul_assoc, ← mul_assoc, hpp, one_mul]
    have hprod : (∏ k, (p * D * p).val k k ^ μ k) = ∏ k, D.val k k ^ (μ ∘ σ) k := by
      simp only [hent, Function.comp]
      rw [← Equiv.prod_comp σ (fun k => D.val k k ^ μ (σ k))]
      simp [hσσ]
    rw [mulVec_mulVec, key, ← mulVec_mulVec, hw _ hD', hprod, mulVec_smul]
end GlobalTheory
end

