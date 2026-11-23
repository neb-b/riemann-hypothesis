module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FirstInequalitySUnits
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private theorem index_sqs_top_eq {G : Type} [CommGroup G] (U : Subgroup G) :
    (sqs (⊤ : Subgroup U)).index = (sqs U).relIndex U := by
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [sqs, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_subgroupOf,
    powMonoidHom_apply]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, by simp⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using h)⟩

private theorem relIndex_sqs_range_eq {U A : Type} [CommGroup U] [CommGroup A] (j : U →* A)
    (hj : Function.Injective j) :
    (sqs j.range).relIndex j.range = (sqs (⊤ : Subgroup U)).index := by
  rw [← Subgroup.index_comap]
  congr 1
  ext x
  simp only [sqs, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_comap,
    powMonoidHom_apply, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, h⟩
    exact ⟨y, hj (by simpa using h)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨j y, ⟨y, rfl⟩, by simp⟩

private theorem arith_first_ineq (m n e s t : ℕ) (hd : m ∣ n) (h : 2 * 2 ^ e * n = (2 ^ s) ^ 2)
    (hs : 2 * s ≤ e + t) : m ≠ 0 ∧ 2 * m ≤ 2 ^ t := by
  have hn : n ≠ 0 := by
    rintro rfl
    have : 0 < (2 ^ s) ^ 2 := by positivity
    omega
  refine ⟨fun h0 => hn (by subst h0; simpa using hd), ?_⟩
  have hmn : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have h1 : 2 ^ e * (2 * n) ≤ 2 ^ e * 2 ^ t := by
    calc 2 ^ e * (2 * n) = (2 ^ s) ^ 2 := by rw [← h]; ring
      _ = 2 ^ (2 * s) := by ring
      _ ≤ 2 ^ (e + t) := Nat.pow_le_pow_right (by norm_num) hs
      _ = 2 ^ e * 2 ^ t := pow_add _ _ _
  have h2 : 2 * n ≤ 2 ^ t := Nat.le_of_mul_le_mul_left h1 (by positivity)
  omega

theorem first_inequality_sUnits :
    ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))),
      admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) →
      (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧
        2 * (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤
          2 ^ (tFin F δ S + tReal F δ) := by
  intro F _ _ δ S hS hδ hns
  obtain ⟨E, _, _, _, θ, σ, hq⟩ := _root_.GlobalTheory.QNorm.exists_isQuad F δ hns
  obtain ⟨SE, hSE⟩ := (_root_.GlobalTheory.QNorm.places_over F E).1 S
  obtain ⟨hinv, hfix, -, hnorm, -, -, -⟩ := _root_.GlobalTheory.QNorm.isQuad_basic F E δ θ σ hq
  obtain ⟨hup, hσ⟩ := _root_.GlobalTheory.QNorm.sUnits_over_and_conj F E δ θ σ hq S SE hSE
  have h90 := _root_.GlobalTheory.QNorm.hilbert90_sUnits_quadratic_extension_qnorm F E δ θ σ hq S SE hSE hS ((mem_sUnits F S δ).1 hδ)
  have hcf := _root_.GlobalTheory.QNorm.two_mul_card_le_card_over F E δ θ σ hq S SE hSE
  have hci := _root_.GlobalTheory.QNorm.two_mul_card_infinitePlace_le F E δ θ σ hq
  let τ : sUnits E SE →* sUnits E SE :=
    ((Units.map (σ : E →* E)).comp (sUnits E SE).subtype).codRestrict _ (fun y => hσ y y.2)
  have hτ : ∀ y : sUnits E SE, (((τ y : sUnits E SE) : Eˣ) : E) = σ ((y : Eˣ) : E) :=
    fun _ => rfl
  let j : sUnits F S →* sUnits E SE :=
    ((Units.map (algebraMap F E : F →* E)).comp (sUnits F S).subtype).codRestrict _
      (fun y => (hup y).2 y.2)
  have hj : ∀ y : sUnits F S, (((j y : sUnits E SE) : Eˣ) : E) = algebraMap F E ((y : Fˣ) : F) :=
    fun _ => rfl
  have hext : ∀ a b : sUnits E SE, ((a : Eˣ) : E) = ((b : Eˣ) : E) → a = b :=
    fun a b h => Subtype.ext (Units.ext h)
  have hjinj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply Units.ext
    apply (algebraMap F E).injective
    rw [← hj, ← hj, h]
  have hm : (-1 : Eˣ) ∈ sUnits E SE := by
    rw [mem_sUnits]
    intro v _
    simp
  have hrange : τ.eqLocus (MonoidHom.id _) = j.range := by
    ext y
    rw [MonoidHom.mem_range]
    change τ y = y ↔ _
    constructor
    · intro h
      obtain ⟨a, ha⟩ := hfix ((y : Eˣ) : E) (by rw [← hτ, h])
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact (y : Eˣ).ne_zero (by simpa using ha)
      have hy : Units.map (algebraMap F E : F →* E) (Units.mk0 a ha0) = y :=
        Units.ext (by simpa using ha.symm)
      refine ⟨⟨Units.mk0 a ha0, (hup _).1 (hy ▸ y.2)⟩, hext _ _ ?_⟩
      rw [hj, ha]; rfl
    · rintro ⟨x, rfl⟩
      apply hext
      rw [hτ, hj, AlgEquiv.commutes]
  have key := _root_.GlobalTheory.QNorm.two_mul_index_sqs_mul_relIndex_norm_involution (sUnits E SE) τ ⟨-1, hm⟩
    (fun a => hext _ _ (by rw [hτ, hτ, hinv]))
    (fun a ha => by
      have h1 : ((a : Eˣ) : E) * σ ((a : Eˣ) : E) = 1 := by
        rw [← hτ]
        have := congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) ha
        simpa using this
      obtain ⟨y, hy, h⟩ := h90 a a.2 h1
      refine ⟨⟨y, hy⟩, hext _ _ ?_⟩
      rw [h, Subgroup.coe_div, Units.val_div_eq_div_val, hτ])
    (fun h => by
      have := congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) h
      simp only [Units.val_neg, Units.val_one, OneMemClass.coe_one] at this
      norm_num at this)
    (hext _ _ (by simp))
    (hext _ _ (by rw [hτ]; simp))
    (fun a ha => by
      have h1 : ((a : Eˣ) : E) ^ 2 = 1 := by
        have := congrArg (fun z : sUnits E SE => ((z : Eˣ) : E)) ha
        simpa using this
      rcases sq_eq_one_iff.1 h1 with h | h
      · exact Or.inl (hext _ _ (by simpa using h))
      · exact Or.inr (hext _ _ (by simpa using h)))
  rw [hrange, relIndex_sqs_range_eq j hjinj, index_sqs_top_eq, index_sqs_top_eq,
    _root_.GlobalTheory.QNorm.relIndex_sqs_sUnits E SE, _root_.GlobalTheory.QNorm.relIndex_sqs_sUnits F S, ← Subgroup.index_comap] at key
  refine arith_first_ineq _ _ _ _ _ ?_ key (by omega)
  apply Subgroup.index_dvd_of_le
  rintro x ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf, mem_normSub]
  obtain ⟨a, b, hab⟩ := hnorm ((y : Eˣ) : E)
  refine ⟨a, b, ?_⟩
  apply (algebraMap F E).injective
  simp only [RingHom.id_apply]
  rw [← hab, ← hj, ← hy, ← hτ]
  simp

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormPrincipleOfCyclicTower
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private theorem prod_univ_eq_prod_range_orderOf_of_generator {G β : Type} [Group G] [Fintype G] [CommMonoid β]
    {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) (f : G → β) :
    ∏ σ, f σ = ∏ i ∈ Finset.range (orderOf g), f (g ^ i) := by
  classical
  rw [← IsCyclic.image_range_orderOf hg, Finset.prod_image]
  intro i hi j hj hij
  exact pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private theorem prod_range_pow_pow_prod_range_eq_prod_range_mul {F E : Type} [Field F] [Field E] [Algebra F E]
    (τ : E ≃ₐ[F] E) (y : E) (d n : ℕ) :
    ∏ j ∈ Finset.range n, ((τ ^ d) ^ j) (∏ i ∈ Finset.range d, (τ ^ i) y) =
      ∏ m ∈ Finset.range (d * n), (τ ^ m) y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.mul_succ, Finset.prod_range_add, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← AlgEquiv.mul_apply, ← pow_mul, ← pow_add]

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private theorem exists_eq_pow_finrank_mul_norm_of_norm_eq_cyclic (F M E : Type) [Field F] [Field M] [Field E]
    [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional F E]
    [IsGalois F E] (hcyc : IsCyclic (E ≃ₐ[F] E)) (x : F) (hx : x ≠ 0) (e₀ : E)
    (he₀ : Algebra.norm M e₀ = algebraMap F M x) :
    ∃ b : F, ∃ c : E, c ≠ 0 ∧ x = b ^ Module.finrank M E * Algebra.norm F c := by
  classical
  haveI : FiniteDimensional M E := FiniteDimensional.right F M E
  haveI : FiniteDimensional F M := FiniteDimensional.left F M E
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  set n := Module.finrank M E with hn
  set d := Module.finrank F M with hd
  have hdn : d * n = Module.finrank F E := Module.finrank_mul_finrank F M E
  have hn0 : 0 < n := Module.finrank_pos
  have hd0 : 0 < d := Module.finrank_pos
  obtain ⟨τ, hτ⟩ := hcyc.exists_generator
  have hcomm : ∀ a b : E ≃ₐ[F] E, a * b = b * a := by
    intro a b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hτ a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hτ b)
    exact ((Commute.refl τ).zpow_zpow i j).eq
  let ρ : (E ≃ₐ[M] E) →* (E ≃ₐ[F] E) :=
    { toFun := fun h => h.restrictScalars F, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hρ : Function.Injective ρ := AlgEquiv.restrictScalars_injective F
  have hρapp : ∀ (h : E ≃ₐ[M] E) (y : E), ρ h y = h y := fun _ _ => rfl
  let K := ρ.range
  haveI : K.Normal := ⟨fun a _ g => by rwa [hcomm g a, mul_inv_cancel_right]⟩
  have hcardK : Nat.card K = n := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv, IsGalois.card_aut_eq_finrank]
  have hcardG : Nat.card (E ≃ₐ[F] E) = d * n := by rw [IsGalois.card_aut_eq_finrank, hdn]
  have hindex : K.index = d := by
    have h := K.index_mul_card
    rw [hcardK, hcardG] at h
    exact Nat.eq_of_mul_eq_mul_right hn0 h
  have hτd : τ ^ d ∈ K := hindex ▸ K.pow_index_mem τ
  obtain ⟨g, hg⟩ := hτd
  have hordτ : orderOf τ = d * n := by rw [orderOf_eq_card_of_forall_mem_zpowers hτ, hcardG]
  have hordτd : orderOf (τ ^ d) = n := by
    rw [orderOf_pow' τ hd0.ne', hordτ, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ hd0]
  have hKz : Subgroup.zpowers (τ ^ d) = K := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le, ← hg]
      exact ⟨g, rfl⟩
    · rw [hcardK, Nat.card_zpowers, hordτd]
  have hgen : ∀ h : E ≃ₐ[M] E, h ∈ Subgroup.zpowers g := by
    intro h
    have hmem : ρ h ∈ Subgroup.zpowers (τ ^ d) := hKz ▸ ⟨h, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, hρ ?_⟩
    rw [map_zpow, hg, hk]
  haveI : IsCyclic (E ≃ₐ[M] E) := ⟨⟨g, hgen⟩⟩
  have hordg : orderOf g = n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]

  have hnormτ : ∀ y : E, algebraMap M E (Algebra.norm M (τ y)) =
      τ (algebraMap M E (Algebra.norm M y)) := by
    intro y
    rw [Algebra.norm_eq_prod_automorphisms, Algebra.norm_eq_prod_automorphisms, map_prod]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [← hρapp σ, ← hρapp σ, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, hcomm]
  have he₀0 : e₀ ≠ 0 := by
    rintro rfl
    exact hx ((algebraMap F M).injective (by rw [← he₀, Algebra.norm_zero, map_zero]))
  have hxE : algebraMap M E (Algebra.norm M e₀) = algebraMap F E x := by
    rw [he₀, ← IsScalarTower.algebraMap_apply]
  have hN0 : Algebra.norm M e₀ ≠ 0 := by rw [he₀]; exact (_root_.map_ne_zero _).mpr hx
  have hu : Algebra.norm M (τ e₀ / e₀) = 1 := by
    have h1 : Algebra.norm M (τ e₀ / e₀) * Algebra.norm M e₀ = Algebra.norm M (τ e₀) := by
      rw [← map_mul, div_mul_cancel₀ _ he₀0]
    have h2 : algebraMap M E (Algebra.norm M (τ e₀)) = algebraMap M E (Algebra.norm M e₀) := by
      rw [hnormτ, hxE, AlgEquiv.commutes]
    rw [(algebraMap M E).injective h2] at h1
    exact mul_right_cancel₀ hN0 (h1.trans (one_mul _).symm)
  obtain ⟨c, hc⟩ := groupCohomology.exists_div_of_norm_eq_one hgen hu
  have hgc : g (c : E) = (τ ^ d) (c : E) := by rw [← hρapp, hg]
  have hc0 : (c : E) ≠ 0 := c.ne_zero
  have hτdc0 : (τ ^ d) (c : E) ≠ 0 := by
    rw [← hgc]; exact (_root_.map_ne_zero _).mpr hc0
  set P := ∏ i ∈ Finset.range d, (τ ^ i) (c : E) with hPdef
  have hτP : τ P * c = P * (τ ^ d) (c : E) := by
    have hs : τ P = ∏ i ∈ Finset.range d, (τ ^ (i + 1)) (c : E) := by
      rw [hPdef, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [pow_succ', AlgEquiv.mul_apply]
    rw [hs]
    have h := Finset.prod_range_succ' (fun i => (τ ^ i) (c : E)) d
    rw [Finset.prod_range_succ] at h
    simp only [pow_zero, AlgEquiv.one_apply] at h
    exact h.symm
  have hτe₀ : τ e₀ * (τ ^ d) (c : E) = e₀ * c := by
    rw [← hgc]
    have h := hc
    rw [div_eq_div_iff ((_root_.map_ne_zero _).mpr hc0) he₀0] at h
    linear_combination -h
  have hfix : τ (e₀ * P) = e₀ * P := by
    rw [map_mul]
    apply mul_right_cancel₀ (mul_ne_zero hτdc0 hc0)
    linear_combination (τ P * c) * hτe₀ + (e₀ * c) * hτP
  obtain ⟨b, hb⟩ : ∃ b : F, algebraMap F E b = e₀ * P := by
    have hall : ∀ σ : E ≃ₐ[F] E, σ (e₀ * P) = e₀ * P := by
      intro σ
      have hst : τ ∈ MulAction.stabilizer (E ≃ₐ[F] E) (e₀ * P) := hfix
      exact (Subgroup.zpowers_le.mpr hst) (hτ σ)
    exact IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed _).mpr hall)
  have hnormP : algebraMap M E (Algebra.norm M P) =
      algebraMap M E (algebraMap F M (Algebra.norm F (c : E))) := by
    rw [Algebra.norm_eq_prod_automorphisms, prod_univ_eq_prod_range_orderOf_of_generator hgen, hordg,
      ← IsScalarTower.algebraMap_apply, Algebra.norm_eq_prod_automorphisms,
      prod_univ_eq_prod_range_orderOf_of_generator hτ, hordτ, ← prod_range_pow_pow_prod_range_eq_prod_range_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← hρapp, map_pow, hg]
  have hbn : algebraMap F M (b ^ n) = algebraMap F M (x * Algebra.norm F (c : E)) := by
    have h := congrArg (Algebra.norm M) hb
    rw [IsScalarTower.algebraMap_apply F M E, Algebra.norm_algebraMap, map_mul, he₀,
      (algebraMap M E).injective hnormP] at h
    rw [map_pow, map_mul, h]
  have hNc : Algebra.norm F (c : E) ≠ 0 := (c.isUnit.map (Algebra.norm F)).ne_zero
  refine ⟨b, ((c⁻¹ : Eˣ) : E), Units.ne_zero _, ?_⟩
  rw [map_units_inv (Algebra.norm F) c, (algebraMap F M).injective hbn, mul_inv_cancel_right₀ hNc]


open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
theorem _root_.GlobalTheory.CNorm.np_of_cyclic_tower : ∀ (F M E : Type) [Field F] [NumberField F] [Field M] [NumberField M]
    [Field E] [NumberField E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E]
    [IsGalois F E], IsCyclic (E ≃ₐ[F] E) → _root_.GlobalTheory.CNorm.NP M E → _root_.GlobalTheory.CNorm.NP F M → _root_.GlobalTheory.CNorm.NP F E := by
  intro F M E _ _ _ _ _ _ _ _ _ _ _ hcyc hME hMF x hx0 hloc
  haveI : FiniteDimensional F E := inferInstance
  haveI : FiniteDimensional F M := inferInstance
  haveI : FiniteDimensional M E := inferInstance
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  have hprops := _root_.GlobalTheory.CNorm.tnorm_baseChange F E
  have hxM : algebraMap F M x ≠ 0 := (_root_.map_ne_zero _).mpr hx0
  have h1 : _root_.GlobalTheory.CNorm.LocNorm M E (algebraMap F M x) := by
    refine ⟨fun w => ?_, fun a => ?_⟩
    · obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.QNorm.exists_ringHom_adicCompletion_under F M w
      letI : Algebra F (w.adicCompletion M) :=
        ((algebraMap M (w.adicCompletion M)).comp (algebraMap F M)).toAlgebra
      haveI : IsScalarTower F M (w.adicCompletion M) := IsScalarTower.of_algebraMap_eq fun _ => rfl
      let ψ : (HeightOneSpectrum.under (𝓞 F) w).adicCompletion F →ₐ[F] w.adicCompletion M :=
        { φ with commutes' := fun r => (hφ r).trans rfl }
      exact _root_.GlobalTheory.CNorm.TNorm.of_tower F M E _ x
        (hprops.1 _ _ ψ x (hloc.1 _))
    · letI : Algebra F ℝ := ((algebraMap M ℝ).comp (algebraMap F M)).toAlgebra
      haveI : IsScalarTower F M ℝ := IsScalarTower.of_algebraMap_eq fun _ => rfl
      exact _root_.GlobalTheory.CNorm.TNorm.of_tower F M E ℝ x (hloc.2 _)
  obtain ⟨e₀, he₀⟩ := hME _ hxM h1
  obtain ⟨b, c, hc0, hxb⟩ := exists_eq_pow_finrank_mul_norm_of_norm_eq_cyclic F M E hcyc x hx0 e₀ he₀
  have hNc : Algebra.norm F c ≠ 0 := by
    intro h
    exact hx0 (by rw [hxb, h, mul_zero])
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [hxb, zero_pow Module.finrank_pos.ne', zero_mul])
  have hpow : ∀ (K : Type) [Field K] [Algebra F K], _root_.GlobalTheory.CNorm.TNorm F E K x →
      _root_.GlobalTheory.CNorm.TNorm F M K b := by
    intro K _ _ hK
    refine _root_.GlobalTheory.CNorm.tnorm_of_tnorm_pow F M E K hcyc b hb0 ?_
    exact hprops.2.2 K _ _ hNc (hxb ▸ hK) (hprops.2.1 K c)
  obtain ⟨m, hm⟩ := hMF b hb0 ⟨fun v => hpow _ (hloc.1 v), fun a => hpow ℝ (hloc.2 a)⟩
  refine ⟨algebraMap M E m * c, ?_⟩
  rw [map_mul, hxb, ← Algebra.norm_norm (S := M), Algebra.norm_algebraMap, map_pow, hm]

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexUnitsLocalSquaresFiniteRealPlacesLe
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private theorem isSquare_real_iff_nonneg (r : ℝ) : IsSquare r ↔ 0 ≤ r :=
  ⟨fun h => h.nonneg, fun h => ⟨Real.sqrt r, (Real.mul_self_sqrt h).symm⟩⟩

theorem index_sqSub_real_dvd_two {F : Type} [Field F] (σ : F →+* ℝ) : (sqSub σ).index ∣ 2 := by
  by_cases h : ∀ x : Fˣ, x ∈ sqSub σ
  · rw [show sqSub σ = ⊤ from eq_top_iff.mpr fun x _ => h x, Subgroup.index_top]
    exact one_dvd 2
  · push_neg at h
    obtain ⟨a, ha⟩ := h
    have hne : ∀ x : Fˣ, σ (x : F) ≠ 0 := fun x => (x.isUnit.map σ).ne_zero
    have hmem : ∀ x : Fˣ, x ∈ sqSub σ ↔ 0 ≤ σ (x : F) := fun x =>
      (mem_sqSub σ x).trans (isSquare_real_iff_nonneg _)
    have ha' : σ (a : F) < 0 := not_le.mp fun h' => ha ((hmem a).mpr h')
    have h2 : (sqSub σ).index = 2 := by
      refine Subgroup.index_eq_two_iff.mpr ⟨a, fun b => ?_⟩
      rw [hmem, hmem, Units.val_mul, map_mul]
      rcases lt_or_gt_of_ne (hne b) with hb | hb
      · exact Or.inl ⟨mul_nonneg_of_nonpos_of_nonpos hb.le ha'.le, not_le.mpr hb⟩
      · exact Or.inr ⟨hb.le, not_le.mpr (mul_neg_of_pos_of_neg hb ha')⟩
    rw [h2]

theorem exists_valuation_two_eq_exp {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ e : ℕ, v.valuation F 2 = WithZero.exp (-(e : ℤ)) := by
  have h2 : (2 : F) = algebraMap (𝓞 F) F 2 := (map_ofNat _ 2).symm
  have hle : v.valuation F 2 ≤ 1 := by
    rw [h2]
    exact v.valuation_le_one 2
  have hne : v.valuation F 2 ≠ 0 := (Valuation.ne_zero_iff _).mpr two_ne_zero
  have hk : WithZero.log (v.valuation F 2) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hne, WithZero.exp_zero]
    exact hle
  refine ⟨(-WithZero.log (v.valuation F 2)).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hne]

private theorem index_biInf_ne_zero_and_le_prod {G ι : Type} [Group G] [DecidableEq ι] (S : Finset ι)
    (f : ι → Subgroup G) :
    (∀ i ∈ S, (f i).index ≠ 0) →
      (⨅ i ∈ S, f i).index ≠ 0 ∧ (⨅ i ∈ S, f i).index ≤ ∏ i ∈ S, (f i).index := by
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp
  · intro a s ha ih hf
    rw [Finset.iInf_insert, Finset.prod_insert ha]
    obtain ⟨h0, hle⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have ha0 := hf a (Finset.mem_insert_self a s)
    exact ⟨Subgroup.index_inf_ne_zero ha0 h0,
      Subgroup.index_inf_le.trans (Nat.mul_le_mul_left _ hle)⟩

theorem index_locSq_le : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (locSq F S).index ≠ 0 ∧ (locSq F S).index ≤ 4 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro F _ _ S
  classical
  choose e he using fun v : HeightOneSpectrum (𝓞 F) => exists_valuation_two_eq_exp v
  have hP := _root_.GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow F S e (fun v _ => he v)
  have hN : ∀ v : HeightOneSpectrum (𝓞 F),
      (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧
        (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e v :=
    fun v => _root_.GlobalTheory.QNorm.index_sqSub_adicCompletion_le F v (e v) (he v)
  obtain ⟨hF0, hFle⟩ := index_biInf_ne_zero_and_le_prod S (fun v => sqSub (algebraMap F (v.adicCompletion F)))
    (fun v _ => (hN v).1)
  have hR2 : ∀ σ : F →+* ℝ, (sqSub σ).index ≤ 2 := fun σ =>
    Nat.le_of_dvd two_pos (index_sqSub_real_dvd_two σ)
  obtain ⟨hR0, hRle⟩ := index_biInf_ne_zero_and_le_prod (Finset.univ : Finset (F →+* ℝ)) (fun σ => sqSub σ)
    (fun σ _ => ne_zero_of_dvd_ne_zero two_ne_zero (index_sqSub_real_dvd_two σ))
  have hRu : (⨅ σ : F →+* ℝ, sqSub σ) = ⨅ σ ∈ (Finset.univ : Finset (F →+* ℝ)), sqSub σ := by
    simp
  have hloc : locSq F S = (⨅ v ∈ S, sqSub (algebraMap F (v.adicCompletion F))) ⊓
      ⨅ σ ∈ (Finset.univ : Finset (F →+* ℝ)), sqSub σ := by
    rw [← hRu]
    rfl
  rw [hloc]
  refine ⟨Subgroup.index_inf_ne_zero hF0 hR0, ?_⟩
  have hF : (⨅ v ∈ S, sqSub (algebraMap F (v.adicCompletion F))).index ≤
      4 ^ S.card * 2 ^ Module.finrank ℚ F := by
    refine hFle.trans ?_
    calc ∏ v ∈ S, (sqSub (algebraMap F (v.adicCompletion F))).index
        ≤ ∏ v ∈ S, (4 * Ideal.absNorm v.asIdeal ^ e v) :=
          Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun v _ => (hN v).2)
      _ = 4 ^ S.card * ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ 4 ^ S.card * 2 ^ Module.finrank ℚ F := Nat.mul_le_mul_left _ hP
  have hR : (⨅ σ ∈ (Finset.univ : Finset (F →+* ℝ)), sqSub σ).index ≤
      2 ^ InfinitePlace.nrRealPlaces F := by
    refine hRle.trans ?_
    calc ∏ σ ∈ (Finset.univ : Finset (F →+* ℝ)), (sqSub σ).index
        ≤ ∏ _σ ∈ (Finset.univ : Finset (F →+* ℝ)), 2 :=
          Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun σ _ => hR2 σ)
      _ = 2 ^ InfinitePlace.nrRealPlaces F := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card, _root_.GlobalTheory.QNorm.card_ringHom_real_eq_nrRealPlaces F]
  refine Subgroup.index_inf_le.trans ((Nat.mul_le_mul hF hR).trans (le_of_eq ?_))
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    ← InfinitePlace.card_add_two_mul_card_eq_rank, show (4 : ℕ) = 2 ^ 2 by norm_num]
  simp only [← pow_mul, ← pow_add]
  congr 1
  ring

end GlobalTheory.QNorm
end

