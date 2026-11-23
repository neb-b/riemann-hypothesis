module

public import Development.EtaleCohomology.EtaleSheaves.LeafOrdInfLocalPf
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Norm.Defs

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafFinInfPf
section
namespace LateralTheory.E.E4

open Polynomial

theorem finInf_comm {k B L : Type} [Field k] [CommRing B] [Field L] [Algebra k B] [Algebra k L]
    [Algebra B L] [IsScalarTower k B L] (g : Polynomial k →ₐ[k] B) (p : Polynomial k) :
    aeval (algebraMap B L (g X)) p = algebraMap B L (g p) := by
  have h : (aeval (algebraMap B L (g X)) : Polynomial k →ₐ[k] L) =
      (IsScalarTower.toAlgHom k B L).comp g := by
    apply Polynomial.algHom_ext
    simp
  rw [h]; rfl

theorem finInf_integral {k B L : Type} [Field k] [CommRing B] [Field L] [Algebra k B] [Algebra k L]
    [Algebra B L] [IsScalarTower k B L] (g : Polynomial k →ₐ[k] B) (hf : g.Finite)
    (K : IntermediateField k L) (hT : algebraMap B L (g X) ∈ K) (b : B) :
    IsIntegral K (algebraMap B L b) := by
  have hi : g.toRingHom.IsIntegral := RingHom.IsIntegral.of_finite hf
  obtain ⟨p, hp, hpb⟩ := hi b
  let φ : Polynomial k →ₐ[k] K := aeval (⟨_, hT⟩ : K)
  have hc : (algebraMap K L).comp φ.toRingHom = (algebraMap B L).comp g.toRingHom := by
    refine RingHom.ext fun q => ?_
    have h1 := finInf_comm (L := L) g q
    have h2 := Polynomial.aeval_algebraMap_apply L (⟨_, hT⟩ : K) q
    exact h2.symm.trans h1
  refine ⟨p.map φ.toRingHom, hp.map _, ?_⟩
  rw [eval₂_map, hc, ← Polynomial.hom_eval₂, hpb, map_zero]

theorem LeafFinInf_of : LeafFinInf := by
  intro k B _ _ _ _ _ hft g hg hf
  have hinj : Function.Injective (algebraMap B (FractionRing B)) := IsFractionRing.injective B _
  have htr : Transcendental k (algebraMap B (FractionRing B) (g X)) := by
    rw [transcendental_iff]
    intro p hp
    rw [finInf_comm] at hp
    apply hg
    apply hinj
    simpa using hp
  refine ⟨fun h => htr (IsAlgebraic.inv_iff.mp h), ?_⟩
  set K := IntermediateField.adjoin k {(algebraMap B (FractionRing B) (g X))⁻¹} with hK
  have hT : algebraMap B (FractionRing B) (g X) ∈ K := by
    have : (algebraMap B (FractionRing B) (g X))⁻¹ ∈ K :=
      IntermediateField.subset_adjoin k _ (Set.mem_singleton _)
    simpa using K.inv_mem this
  obtain ⟨S, hS⟩ := hft.out
  let S' : Set (FractionRing B) := algebraMap B (FractionRing B) '' (S : Set B)
  have : Finite S' := (S.finite_toSet.image _).to_subtype
  have hfd : FiniteDimensional K (IntermediateField.adjoin K S') :=
    IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨b, -, rfl⟩
      exact finInf_integral g hf K hT b)
  have hB : ∀ b : B, algebraMap B (FractionRing B) b ∈ IntermediateField.adjoin K S' := by
    intro b
    have hb : b ∈ Algebra.adjoin k (S : Set B) := hS ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin K S' ⟨x, hx, rfl⟩
    | algebraMap r =>
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k K (FractionRing B)]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have htop : IntermediateField.adjoin K S' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    exact div_mem (hB a) (hB b)
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end LateralTheory.E.E4
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafFinValPf
section
namespace LateralTheory.E.E4

open Polynomial IsDedekindDomain

theorem finVal_dedekind (D L : Type) [CommRing D] [IsDedekindDomain D] [Field L] [Algebra D L]
    [IsFractionRing D L] [Finite (HeightOneSpectrum D)] :
    ∃ (n : ℕ) (φ : Lˣ →* Multiplicative (Fin n → ℤ)), ∀ x : Lˣ, φ x = 1 →
      (x : L) ∈ (algebraMap D L).range := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (HeightOneSpectrum D)
  refine ⟨n, MonoidHom.mk' (fun x => Multiplicative.ofAdd
    (fun i => WithZero.log ((e.symm i).valuation L (x : L)))) ?_, ?_⟩
  · intro x y
    rw [← ofAdd_add]
    congr 1
    funext i
    simp only [Units.val_mul, Pi.add_apply, map_mul]
    exact WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
      ((Valuation.ne_zero_iff _).mpr y.ne_zero)
  · intro x hx
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have h : WithZero.log ((e.symm (e v)).valuation L (x : L)) = 0 :=
      congrFun (congrArg Multiplicative.toAdd hx) (e v)
    rw [e.symm_apply_apply] at h
    exact WithZero.le_exp_of_log_le h.le

theorem finVal_finite (A D : Type) [CommRing A] [IsLocalRing A] [CommRing D] [IsDedekindDomain D]
    [Algebra A D] [Algebra.IsIntegral A D] [IsDomain A] [Module.IsTorsionFree A D] :
    Finite (HeightOneSpectrum D) := by
  have hf := IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal A) D
  have := hf.to_subtype
  refine Finite.of_injective (β := (IsLocalRing.maximalIdeal A).primesOver D)
    (fun v => ⟨v.asIdeal, v.isPrime, ⟨?_⟩⟩) ?_
  · have := v.isMaximal
    exact (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) v.asIdeal)).symm
  · intro v w h
    exact HeightOneSpectrum.ext (congrArg Subtype.val h)

theorem finVal_sep (A K L : Type) [CommRing A] [IsLocalRing A] [IsDedekindDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ (n : ℕ) (φ : Lˣ →* Multiplicative (Fin n → ℤ)), ∀ x : Lˣ, φ x = 1 → IsIntegral A (x : L) := by
  have := integralClosure.isDedekindDomain A K L
  have := integralClosure.isFractionRing_of_finite_extension (A := A) K L
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : FaithfulSMul A (integralClosure A L) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    exact hinj (congrArg Subtype.val h)
  have := finVal_finite A (integralClosure A L)
  obtain ⟨n, φ, h⟩ := finVal_dedekind (integralClosure A L) L
  refine ⟨n, φ, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h x hx
  rw [← hy]
  exact y.2

theorem finVal_gen (A K L : Type) [CommRing A] [IsLocalRing A] [IsDedekindDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] :
    ∃ (n : ℕ) (φ : Lˣ →* Multiplicative (Fin n → ℤ)), ∀ x : Lˣ, φ x = 1 → IsIntegral A (x : L) := by
  obtain ⟨n, φ, h⟩ := finVal_sep A K (separableClosure K L)
  refine ⟨n, φ.comp (Units.map (Algebra.norm (separableClosure K L))), fun x hx => ?_⟩
  have h1 : IsIntegral A (Algebra.norm (separableClosure K L) (x : L)) := h _ hx
  obtain ⟨m, y, hy⟩ := IsPurelyInseparable.pow_mem (separableClosure K L)
    (ringExpChar (separableClosure K L)) (x : L)
  have hq : 0 < ringExpChar (separableClosure K L) ^ m := expChar_pow_pos (separableClosure K L) _ m
  have h2 : IsIntegral A (y ^ Module.finrank (separableClosure K L) L) := by
    rw [← Algebra.norm_algebraMap, hy, map_pow]
    exact h1.pow _
  have h3 : IsIntegral A y := h2.of_pow Module.finrank_pos
  have : IsScalarTower A (separableClosure K L) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h4 : IsIntegral A (algebraMap (separableClosure K L) L y) := h3.algebraMap
  rw [hy] at h4
  exact h4.of_pow hq

theorem LeafFinVal_of : LeafFinVal := by
  intro k L _ _ _ _ s hs hfd
  have hne : ∀ p : Polynomial k, p ≠ 0 → aeval s p ≠ 0 := fun p hp h0 => hp ((transcendental_iff.mp hs) p h0)
  let P : Ideal k[X] := RingHom.ker (evalRingHom (0 : k))
  have hP : P.IsPrime := RingHom.ker_isPrime _
  let A := Localization.AtPrime P
  let K := IntermediateField.adjoin k {s}
  let t : K := ⟨s, IntermediateField.mem_adjoin_simple_self k s⟩
  have hval : ∀ p : k[X], ((aeval t p : K) : L) = aeval s p := fun p =>
    (aeval_algHom_apply K.val t p).symm
  have hne' : ∀ p : k[X], p ≠ 0 → aeval t p ≠ 0 := fun p hp h0 => hne p hp (by rw [← hval, h0]; rfl)
  have hu : ∀ y : P.primeCompl, IsUnit ((aeval t : k[X] →ₐ[k] K).toRingHom y) := by
    intro y
    refine (hne' y ?_).isUnit
    intro h0
    exact y.2 (by rw [h0]; exact P.zero_mem)
  let f : A →+* K := IsLocalization.lift (M := P.primeCompl) hu
  have hf : ∀ p : k[X], f (algebraMap k[X] A p) = aeval t p := fun p => IsLocalization.lift_eq hu p
  have hfrac : ∀ c : A, ∃ a b : k[X], b.eval 0 ≠ 0 ∧ f c = aeval t a / aeval t b := by
    intro c
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj P.primeCompl c
    refine ⟨a, b, b.2, ?_⟩
    have := congrArg f hab
    rw [map_mul, hf, hf] at this
    exact (eq_div_iff (hu b).ne_zero).mpr this
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj P.primeCompl c
    have h1 := congrArg f hab
    rw [map_mul, hc, zero_mul, hf] at h1
    have ha : a = 0 := by
      by_contra ha
      exact hne' a ha h1.symm
    simp only [ha, map_zero] at hab
    exact (IsLocalization.map_units A b).mul_left_eq_zero.mp hab
  let _ : Algebra A K := f.toAlgebra
  let _ : Algebra A L := ((algebraMap K L).comp f).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr hinj
  have : IsFractionRing A K := by
    refine IsFractionRing.of_field A K (fun z => ?_)
    obtain ⟨r, q, hz⟩ := (IntermediateField.mem_adjoin_simple_iff k (z : L)).mp z.2
    refine ⟨algebraMap k[X] A r, algebraMap k[X] A q, ?_⟩
    change z = f _ / f _
    rw [hf, hf]
    apply Subtype.ext
    rw [hz, ← hval, ← hval]
    rfl
  obtain ⟨n, φ, h⟩ := finVal_gen A K L
  refine ⟨n, φ, fun x hx => ?_⟩
  obtain ⟨p, hp, hpx⟩ := h x hx
  choose a b hb hab using hfrac
  refine ⟨p.natDegree, fun i => a (p.coeff i), fun i => b (p.coeff i), fun i => hb _, ?_⟩
  rw [hp.as_sum, eval₂_add, eval₂_X_pow, eval₂_finsetSum] at hpx
  rw [← hpx]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [eval₂_mul, eval₂_C, eval₂_X_pow]
  congr 1
  change _ = ((f (p.coeff i) : K) : L)
  rw [hab, ← hval, ← hval]
  rfl

end LateralTheory.E.E4
end

