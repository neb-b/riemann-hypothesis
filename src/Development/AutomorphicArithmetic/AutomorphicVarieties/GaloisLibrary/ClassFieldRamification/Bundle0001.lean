module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
public import GroundTheory.GlobalFields.TateThesis.Chebotarev
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0004
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.ArtinA
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0051

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.AugKer
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.augKer :
    ∀ (R G : Type) [CommRing R] [CommGroup G], RingHom.ker (aug R G) = augIdeal R G ∧ Function.Surjective (aug R G) := by
  intro R G _ _
  have key : ∀ x : MonoidAlgebra R G,
      x - algebraMap R (MonoidAlgebra R G) (aug R G x) ∈ augIdeal R G := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
      exact add_mem hx hy
    | single g r =>
      rw [aug_single]
      have h1 : MonoidAlgebra.single g r - algebraMap R (MonoidAlgebra R G) r =
          MonoidAlgebra.single 1 r * (MonoidAlgebra.of R G g - 1) := by
        rw [mul_sub, mul_one, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, one_mul,
          mul_one, MonoidAlgebra.coe_algebraMap]
        rfl
      rw [h1]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, rfl⟩)
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · intro x hx
    have := key x
    rwa [RingHom.mem_ker.mp hx, map_zero, sub_zero] at this
  · rw [augIdeal, Ideal.span_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, MonoidAlgebra.of_apply, aug_single,
      sub_self]
  · intro r
    exact ⟨MonoidAlgebra.single 1 r, aug_single R G 1 r⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Cheb
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.cheb :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (σ : Gal(L/K)) (T : Set (HeightOneSpectrum (𝓞 K))), T.Finite → ∃ v ∉ T, ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal ∧ w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ IsArithFrobAt (𝓞 K) σ w.asIdeal := by
  intro K L _ _ _ _ _ _ σ T hT
  classical
  let C : Set Gal(L/K) := {τ | IsConj σ τ}
  have hCc : ∀ a ∈ C, ∀ τ : Gal(L/K), τ * a * τ⁻¹ ∈ C := by
    intro a ha τ
    exact IsConj.trans ha (isConj_iff.mpr ⟨τ, rfl⟩)
  have hD := GroundTheory.Global.hasDirichletDensity_setOf_exists_arithFrobAt_mem (K := K) (L := L) C hCc
  have hpos : (0 : ℝ) < (Nat.card C : ℝ) / Nat.card Gal(L/K) := by
    have : Nonempty C := ⟨⟨σ, IsConj.refl σ⟩⟩
    apply div_pos
    · exact_mod_cast Nat.card_pos
    · exact_mod_cast Nat.card_pos
  have key : ∀ S : Set (HeightOneSpectrum (𝓞 K)),
      Set.HasDirichletDensity S ((Nat.card C : ℝ) / Nat.card Gal(L/K)) → (S \ T).Nonempty := by
    intro S hS
    refine Set.Infinite.nonempty (Set.Infinite.diff ?_ hT)
    intro hfin
    have h0 := GroundTheory.Global.hasDirichletDensity_zero_of_finite hfin
    exact hpos.ne' (hS.dirichletDensity_eq.symm.trans h0.dirichletDensity_eq)
  obtain ⟨v, ⟨hram, w, hwv, hfw⟩, hvT⟩ := key _ hD
  obtain ⟨c, hc⟩ := isConj_iff.mp hfw
  have hne : c⁻¹ • w.asIdeal ≠ ⊥ := by
    intro h
    apply w.ne_bot
    have := congrArg (fun I : Ideal (𝓞 L) => c • I) h
    simpa using this
  let w' : HeightOneSpectrum (𝓞 L) := ⟨c⁻¹ • w.asIdeal, Ideal.IsPrime.smul c⁻¹, hne⟩
  have hw'v : w'.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.smul c⁻¹
  refine ⟨v, hvT, w', hw'v, (hram w' hw'v), ?_⟩
  have hF := (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal).conj c⁻¹
  rw [← hc] at hF
  have e : c⁻¹ * (c * σ * c⁻¹) * c⁻¹⁻¹ = σ := by group
  rw [e] at hF
  exact hF
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.CycIne
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.cycIne :
    ∀ (N : ℕ) [NeZero N] (C : Type) [Field C] [NumberField C] [IsCyclotomicExtension {N} ℚ C] (ζ : C) (p : ℕ), p.Prime → IsPrimitiveRoot ζ N → ∀ w : HeightOneSpectrum (𝓞 C), (p : 𝓞 C) ∈ w.asIdeal → ∀ (σ : Gal(C/ℚ)) (a : ℕ), σ ζ = ζ ^ a → (σ ∈ w.asIdeal.inertia Gal(C/ℚ) ↔ a ≡ 1 [MOD ordCompl[p] N]) ∧ (σ ∈ MulAction.stabilizer Gal(C/ℚ) w.asIdeal ↔ ∃ i : ℕ, a ≡ p ^ i [MOD ordCompl[p] N]) := by
  intro N _ C _ _ _ ζ p hp hζ w hw σ a hσ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := w.isPrime
  haveI : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
        (Nat.prime_iff_prime_int.1 hp)).isMaximal (by simpa using hp.ne_zero)
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_under]
    simpa using hw
  have hne : NeZero (ordCompl[p] N) := ⟨(Nat.ordCompl_pos p (NeZero.ne N)).ne'⟩
  have hmem : ∀ H : Subgroup Gal(C/ℚ), σ ∈ H ↔ IsCyclotomicExtension.Rat.galEquivZMod N C σ ∈
      H.map (IsCyclotomicExtension.Rat.galEquivZMod N C).toMonoidHom := fun H =>
    (Subgroup.mem_map_iff_mem (f := (IsCyclotomicExtension.Rat.galEquivZMod N C).toMonoidHom)
      (IsCyclotomicExtension.Rat.galEquivZMod N C).injective).symm
  have ha : ((IsCyclotomicExtension.Rat.galEquivZMod N C σ : (ZMod N)ˣ) : ZMod N) = (a : ZMod N) := by
    have h := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N C σ hζ.pow_eq_one
    rw [hσ, (hζ.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hζ.eq_orderOf,
      ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_zmod_val] at h
    exact h.symm
  have hb : ((ZMod.unitsMap (Nat.ordCompl_dvd N p) (IsCyclotomicExtension.Rat.galEquivZMod N C σ) :
      (ZMod (ordCompl[p] N))ˣ) : ZMod (ordCompl[p] N)) = (a : ZMod (ordCompl[p] N)) := by
    rw [ZMod.unitsMap_val, ha, ZMod.cast_natCast (Nat.ordCompl_dvd N p)]
  constructor
  · rw [hmem, KStar.Ram.map_inertia_eq p, KStar.Ram.inertiaUnits, MonoidHom.mem_ker, Units.ext_iff, hb,
      ← ZMod.natCast_eq_natCast_iff, Nat.cast_one, Units.val_one]
  · rw [hmem, KStar.Ram.map_stabilizer_eq p, KStar.Ram.decompUnits, Subgroup.mem_comap,
      ← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff]
    refine exists_congr fun i => ?_
    rw [Units.ext_iff, hb, ← ZMod.natCast_eq_natCast_iff, Units.val_pow_eq_pow_val,
      ZMod.coe_unitOfCoprime, Nat.cast_pow, eq_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.ExistsQuadraticGaussSum
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem UpperTheory.V.CF.exists_quadratic_gauss_sum {K : Type} [Field K] [CharZero K] {d : ℕ} [hd : Fact d.Prime]
    (hd2 : d ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ d) :
    ∃ G : K, G ^ 2 = (pStar d : ℤ) ∧ G ∈ ℚ⟮ζ⟯ ∧ ∀ (σ : K →+* K) (a : ℕ), σ ζ = ζ ^ a →
      σ G = (legendreSym d a : ℤ) * G := by
  classical
  haveI : NeZero d := ⟨hd.out.ne_zero⟩
  have hζd : ζ ^ d = 1 := hζ.pow_eq_one
  let χ : MulChar (ZMod d) K := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom K)
  let ψ : AddChar (ZMod d) K := AddChar.zmodChar d hζd
  have hψp : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root d hζ
  have hchar : ringChar (ZMod d) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hd2
  have hχ1 : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom K) Int.cast_injective).2
      (quadraticChar_ne_one hchar)
  have hχq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod d)).comp _
  have hχa : ∀ a : ZMod d, χ a = ((quadraticChar (ZMod d) a : ℤ) : K) := fun a => by
    simp [χ, MulChar.ringHomComp_apply]
  have hψa : ∀ n : ℕ, ψ (n : ZMod d) = ζ ^ n := fun n => AddChar.zmodChar_apply' hζd n
  refine ⟨gaussSum χ ψ, ?_, ?_, ?_⟩
  · rw [gaussSum_sq hχ1 hχq hψp, hχa, ZMod.card]
    have h1 : quadraticChar (ZMod d) (-1) = legendreSym d (-1) := by
      simp [legendreSym]
    rw [h1, legendreSym.at_neg_one hd2, ZMod.χ₄_nat_eq_if_mod_four, pStar]
    have hodd : d % 2 = 1 := hd.out.eq_two_or_odd.resolve_left hd2
    have h4 : d % 4 = 1 ∨ d % 4 = 3 := by omega
    rcases h4 with h4 | h4
    · have he : Even (d / 2) := by rw [Nat.even_iff]; omega
      simp [hodd, h4, he.neg_one_pow]
    · have ho : Odd (d / 2) := by rw [Nat.odd_iff]; omega
      simp [hodd, h4, ho.neg_one_pow]
  · unfold gaussSum
    refine IntermediateField.sum_mem _ fun a _ => IntermediateField.mul_mem _ ?_ ?_
    · rw [hχa]; exact IntermediateField.intCast_mem _ _
    · rw [← ZMod.natCast_zmod_val a, hψa]
      exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ) _
  · intro σ b hσ
    have hG : σ (gaussSum χ ψ) = gaussSum χ (ψ.mulShift (b : ZMod d)) := by
      unfold gaussSum
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hχa, map_intCast, AddChar.mulShift_apply]
      congr 1
      rw [← ZMod.natCast_zmod_val a, hψa, map_pow, hσ, ← pow_mul, ← Nat.cast_mul, hψa]
    have hb : (b : ZMod d) ≠ 0 := by
      intro h0
      have h1 : σ ζ = 1 := by
        rw [hσ]
        rw [ZMod.natCast_eq_zero_iff] at h0
        obtain ⟨k, rfl⟩ := h0
        rw [pow_mul, hζd, one_pow]
      have h2 : ζ = 1 := σ.injective (by rw [h1, map_one])
      exact hζ.ne_one hd.out.one_lt h2
    have hmul : χ (b : ZMod d) * gaussSum χ (ψ.mulShift (b : ZMod d)) = gaussSum χ ψ :=
      gaussSum_mulShift χ ψ (Units.mk0 _ hb)
    have hu2 : χ (b : ZMod d) * χ (b : ZMod d) = 1 := by
      rw [hχa, ← Int.cast_mul, ← sq, quadraticChar_sq_one hb, Int.cast_one]
    have hleg : ((legendreSym d b : ℤ) : K) = χ (b : ZMod d) := by
      rw [hχa]; simp [legendreSym]
    rw [hG, hleg, ← hmul, ← mul_assoc, hu2, one_mul]

theorem UpperTheory.V.CF.gauss :
    ∀ (K : Type) [Field K] [CharZero K] (p : ℕ) [Fact p.Prime] (ζ : K), p ≠ 2 → IsPrimitiveRoot ζ p → (∃ x : K, x ^ 2 = (pStar p : ℤ)) ∧ ∀ x : K, x ^ 2 = (pStar p : ℤ) → x ∈ ℚ⟮ζ⟯ ∧ ∀ (σ : K →+* K) (b : ℕ), σ ζ = ζ ^ b → σ x = (legendreSym p b : ℤ) * x := by
  intro K _ _ p _ ζ hp hζ
  obtain ⟨G, hG, hmem, hσ⟩ := UpperTheory.V.CF.exists_quadratic_gauss_sum hp hζ
  refine ⟨⟨G, hG⟩, fun x hx => ?_⟩
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hx.trans hG.symm) with rfl | rfl
  · exact ⟨hmem, hσ⟩
  · refine ⟨neg_mem hmem, fun σ b h => ?_⟩
    rw [map_neg, hσ σ b h, mul_neg]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.GrMaxOf
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.grMaxOf :
    ∀ (p : ℕ) [Fact p.Prime] (R G : Type) [CommRing R] [IsLocalRing R] [CommGroup G] [Finite G], (p : R) ∈ IsLocalRing.maximalIdeal R → IsPGroup p G → ∀ M : Ideal (MonoidAlgebra R G), M.IsMaximal → M = (IsLocalRing.maximalIdeal R).comap (aug R G) := by
  intro p _ R G _ _ _ _ hpm hG M hM
  classical
  have hcomap : M.comap (algebraMap R (MonoidAlgebra R G)) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal M)
  letI : Field (MonoidAlgebra R G ⧸ M) := Ideal.Quotient.field M
  have hpQ : ((p : ℕ) : MonoidAlgebra R G ⧸ M) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]
    have h0 : (p : R) ∈ M.comap (algebraMap R (MonoidAlgebra R G)) := by
      rw [hcomap]; exact hpm
    simpa using h0
  haveI : CharP (MonoidAlgebra R G ⧸ M) p := by
    have h := CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) hpQ
    exact h ▸ ringChar.charP _
  have hg : ∀ g : G, Ideal.Quotient.mk M (MonoidAlgebra.single g 1) = 1 := by
    intro g
    obtain ⟨k, hk⟩ := hG g
    have h1 : (Ideal.Quotient.mk M (MonoidAlgebra.single g (1 : R)) - 1) ^ p ^ k = 0 := by
      rw [sub_pow_char_pow, one_pow, ← map_pow, MonoidAlgebra.single_pow, one_pow, hk,
        ← MonoidAlgebra.one_def, map_one, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mp h1)
  have hext : Ideal.Quotient.mkₐ R M = (Algebra.ofId R _).comp (aug R G) := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp [hg, aug_single]
    · exact Subsingleton.elim _ _
  have hle : (IsLocalRing.maximalIdeal R).comap (aug R G) ≤ M := by
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h3 := congrArg (fun f => f x) hext
    simp only [Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, Algebra.ofId_apply] at h3
    rw [h3, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
    have h2 : aug R G x ∈ M.comap (algebraMap R (MonoidAlgebra R G)) := by
      rw [hcomap]; exact hx
    exact h2
  haveI : ((IsLocalRing.maximalIdeal R).comap (aug R G)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (aug R G) (fun r => ⟨MonoidAlgebra.single 1 r, aug_single R G 1 r⟩)
  exact (Ideal.IsMaximal.eq_of_le this hM.ne_top hle).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
section
open NumberField IsDedekindDomain IntermediateField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.ineAbs :
    ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsGalois K L] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)), IsPlaceOver A w → (Ine (F := K) A).map (resTo K L Ω) = w.asIdeal.inertia Gal(L/K) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A w hw
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := K) L
  haveI : IsAlgClosure L Ω := ⟨inferInstance, inferInstance⟩
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact CompanionTheory.FamInh.res_mem_inertia hw hσ
  · intro hτ
    exact CompanionTheory.FamInh.exists_lift_ine hw hτ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneCard
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.ineCard :
    (∀ (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L] [IsGalois k L] (w : HeightOneSpectrum (𝓞 L)), Nat.card (w.asIdeal.inertia Gal(L/k)) = w.asIdeal.ramificationIdx (𝓞 k)) ∧ ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (w : HeightOneSpectrum (𝓞 L)), Nat.card (w.asIdeal.inertia Gal(L/ℚ)) = w.asIdeal.ramificationIdx ℤ := by
  refine ⟨fun k L _ _ _ _ _ _ w => ?_, fun L _ _ _ w => ?_⟩
  · rw [Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under (𝓞 k)) w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under (𝓞 k)) w.asIdeal Gal(L/k)]
  · rw [Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under ℤ) w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under ℤ) w.asIdeal Gal(L/ℚ)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneMap
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.ineMap :
    ∀ (k K H : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Field H] [NumberField H] [Algebra k K] [Algebra K H] [Algebra k H] [IsScalarTower k K H] [IsGalois k K] [IsGalois k H] (w : HeightOneSpectrum (𝓞 H)), (w.asIdeal.inertia Gal(H/k)).map (resTo k K H) = (w.asIdeal.under (𝓞 K)).inertia Gal(K/k) := by
  intro k K H _ _ _ _ _ _ _ _ _ _ _ _ w
  haveI : IsGalois K H := IsGalois.tower_top_of_isGalois k K H
  have comm : ∀ (σ : Gal(H/k)) (x : 𝓞 K),
      algebraMap (𝓞 K) (𝓞 H) (resTo k K H σ • x) = σ • algebraMap (𝓞 K) (𝓞 H) x := by
    intro σ x
    apply FaithfulSMul.algebraMap_injective (𝓞 H) H
    have e1 : algebraMap (𝓞 H) H (σ • algebraMap (𝓞 K) (𝓞 H) x) =
        σ • algebraMap (𝓞 H) H (algebraMap (𝓞 K) (𝓞 H) x) := algebraMap.smul' _ _ _
    have e2 : algebraMap (𝓞 K) K (resTo k K H σ • x) = resTo k K H σ • algebraMap (𝓞 K) K x :=
      algebraMap.smul' _ _ _
    rw [e1, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) K H, IsScalarTower.algebraMap_apply (𝓞 K) K H, e2]
    exact AlgEquiv.restrictNormal_commutes σ K _
  have comm2 : ∀ (τ : Gal(H/K)) (y : 𝓞 H), (τ.restrictScalars k) • y = τ • y := by
    intro τ y
    apply FaithfulSMul.algebraMap_injective (𝓞 H) H
    have e1 : algebraMap (𝓞 H) H ((τ.restrictScalars k) • y) =
        (τ.restrictScalars k) • algebraMap (𝓞 H) H y := algebraMap.smul' _ _ _
    have e2 : algebraMap (𝓞 H) H (τ • y) = τ • algebraMap (𝓞 H) H y := algebraMap.smul' _ _ _
    rw [e1, e2]
    rfl
  set P := w.asIdeal with hP
  set Q := P.under (𝓞 K) with hQ
  set p := P.under (𝓞 k) with hp
  haveI : Nonempty (Q.primesOver (𝓞 H)) := ⟨⟨P, inferInstance, inferInstance⟩⟩
  have hle : (P.inertia Gal(H/k)).map (resTo k K H) ≤ Q.inertia Gal(K/k) := by
    rintro _ ⟨σ, hσ, rfl⟩
    intro x
    have h1 := hσ (algebraMap (𝓞 K) (𝓞 H) x)
    show _ ∈ Ideal.comap (algebraMap (𝓞 K) (𝓞 H)) P
    rw [Ideal.mem_comap, map_sub, comm]
    exact h1
  apply Subgroup.eq_of_le_of_card_ge hle
  have cG : Nat.card (P.inertia Gal(H/k)) = p.ramificationIdxIn (𝓞 H) :=
    Ideal.card_inertia_eq_ramificationIdxIn p P
  have cK : Nat.card (Q.inertia Gal(K/k)) = p.ramificationIdxIn (𝓞 K) :=
    Ideal.card_inertia_eq_ramificationIdxIn p Q
  have cH : Nat.card (P.inertia Gal(H/K)) = Q.ramificationIdxIn (𝓞 H) :=
    Ideal.card_inertia_eq_ramificationIdxIn Q P
  have hmul : p.ramificationIdxIn (𝓞 K) * Q.ramificationIdxIn (𝓞 H) = p.ramificationIdxIn (𝓞 H) :=
    Ideal.ramificationIdxIn_mul_ramificationIdxIn Q Gal(K/k) (𝓞 H) Gal(H/k) Gal(H/K)
  let f : (P.inertia Gal(H/k)) →* Gal(K/k) := (resTo k K H).comp (Subgroup.subtype _)
  have hrange : f.range = (P.inertia Gal(H/k)).map (resTo k K H) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let g : (P.inertia Gal(H/K)) →* (P.inertia Gal(H/k)) :=
    { toFun := fun τ => ⟨(τ.1.restrictScalars k), fun y => by
        rw [comm2]
        exact τ.2 y⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hker : f.ker ≤ g.range := by
    intro σ hσ
    have hfix : ∀ c : K, σ.1 (algebraMap K H c) = algebraMap K H c := by
      intro c
      have h2 : resTo k K H σ.1 = 1 := hσ
      rw [← AlgEquiv.restrictNormal_commutes σ.1 K c]
      have h3 : σ.1.restrictNormal K = 1 := h2
      rw [h3]
      rfl
    let τ : Gal(H/K) := AlgEquiv.ofRingEquiv (f := σ.1.toRingEquiv) hfix
    have hτ : τ ∈ P.inertia Gal(H/K) := by
      intro y
      have h4 := σ.2 y
      rw [← comm2] at *
      exact h4
    exact ⟨⟨τ, hτ⟩, by
      apply Subtype.ext
      ext z
      rfl⟩
  have hcardker : Nat.card f.ker ≤ Nat.card (P.inertia Gal(H/K)) :=
    (Subgroup.card_le_of_le hker).trans
      (Nat.card_le_card_of_surjective g.rangeRestrict g.rangeRestrict_surjective)
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have key := f.ker.card_mul_index
  rw [Subgroup.index_ker, hrange, cG, ← hmul] at key
  rw [cK]
  by_contra hlt
  push_neg at hlt
  have hQpos : 0 < Q.ramificationIdxIn (𝓞 H) := by
    rw [← cH]
    exact Nat.card_pos
  rw [cH] at hcardker
  nlinarith [Nat.mul_le_mul hcardker (le_of_lt hlt)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.MinkRam
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.minkRam :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K ≠ 1 → ∃ p : ℕ, p.Prime ∧ ¬ UnramAt K p := by
  intro K _ _ hK
  have h1 : 1 < Module.finrank ℚ K := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    omega
  have h2 := NumberField.abs_discr_gt_two h1
  set D := differentIdeal ℤ (𝓞 K) with hD
  have hnorm : D.absNorm = (NumberField.discr K).natAbs :=
    NumberField.absNorm_differentIdeal K (𝓞 K)
  have hDtop : D ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at hnorm
    have h3 : ((NumberField.discr K).natAbs : ℤ) = |NumberField.discr K| := Int.natCast_natAbs _
    rw [← hnorm] at h3
    omega
  obtain ⟨P, hPmax, hDP⟩ := Ideal.exists_le_maximal D hDtop
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff] at hDP
    exact differentIdeal_ne_bot hDP
  haveI : NeZero P := ⟨hPne⟩
  refine ⟨Ideal.absNorm (Ideal.under ℤ P), Nat.absNorm_under_prime P, fun hun => ?_⟩
  have hram := hun P hPmax.isPrime (Int.absNorm_under_mem P)
  rw [Ideal.ramificationIdx_eq_one_iff] at hram
  exact (dvd_differentIdeal_iff.mp (Ideal.dvd_iff_le.mpr hDP)) hram
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.RayPrime
section
open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem rayPrime_span (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) (hp : p.Prime)
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
  _root_.UpperTheory.Reformulated.B.Qi16.rayPrime_span v p hp hv

theorem UpperTheory.V.CF.rayPrime :
    ∀ (𝔪 : GroundTheory.Global.Modulus ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ), p.Prime → (p : 𝓞 ℚ) ∈ v.asIdeal → p ≡ 1 [MOD Ideal.absNorm 𝔪.ideal] → ∃ hv : ¬ v.asIdeal ∣ 𝔪.ideal, 𝔪.primeClass hv = 1 := by
  intro 𝔪 v p hp hpv hmod
  have hm : (p : 𝓞 ℚ) - 1 ∈ 𝔪.ideal := by
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hp.one_le).1 hmod.symm
    have : (p : 𝓞 ℚ) - 1 = (Ideal.absNorm 𝔪.ideal : 𝓞 ℚ) * c := by
      rw [← Nat.cast_mul, ← hc, Nat.cast_sub hp.one_le, Nat.cast_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hv : ¬ v.asIdeal ∣ 𝔪.ideal := by
    intro h
    have h1 := (Ideal.dvd_iff_le.1 h) hm
    have h2 := v.asIdeal.sub_mem hpv h1
    rw [sub_sub_cancel] at h2
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  refine ⟨hv, ?_⟩
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  unfold GroundTheory.Global.Modulus.primeClass
  rw [QuotientGroup.eq_one_iff, GroundTheory.Global.Modulus.mem_principalRay]
  refine ⟨Units.mk0 (p : ℚ) hp0, 𝔪.mem_rayUnits.2 ⟨fun w hw => ?_, fun w _ => ?_⟩, ?_⟩
  · have e : ((Units.mk0 (p : ℚ) hp0 : ℚˣ) : ℚ) - 1 = algebraMap (𝓞 ℚ) ℚ ((p : 𝓞 ℚ) - 1) := by simp
    rw [e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact Ideal.dvd_iff_le.1 (𝔪.asIdeal_pow_exponent_dvd w) hm
  · simpa using hp.pos
  · apply Units.ext
    rw [coe_toPrincipalIdeal]
    change _ = ((v.asIdeal : Ideal (𝓞 ℚ)) : FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ)
    rw [rayPrime_span v p hp hpv, FractionalIdeal.coeIdeal_span_singleton]
    simp
end

