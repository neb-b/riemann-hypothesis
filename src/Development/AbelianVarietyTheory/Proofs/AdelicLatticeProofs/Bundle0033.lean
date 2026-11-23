module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexUnitsSquareUnderRingHomAdicCompletionLe
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sqIdx_hiUnits_anti {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) {m n : ℕ} (h : m ≤ n) :
    hiUnits w n ≤ hiUnits w m := by
  rintro x ⟨hx, hx'⟩
  refine ⟨hx, hx'.trans ?_⟩
  rw [WithZero.exp_le_exp]
  omega

theorem sqIdx_relIndex_hiUnits_add {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) (π : K)
    (R : Finset K) (hπ : w π = WithZero.exp (-1))
    (hR : ∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) (n k : ℕ) :
    (hiUnits w (n + k)).relIndex (hiUnits w n) ≠ 0 ∧
      (hiUnits w (n + k)).relIndex (hiUnits w n) ≤ R.card ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.QNorm.relIndex_hiUnits_succ_le K w π R (n + k) hπ hR
    have := Subgroup.relIndex_mul_relIndex (hiUnits w (n + k + 1)) (hiUnits w (n + k))
      (hiUnits w n) (sqIdx_hiUnits_anti w (by omega)) (sqIdx_hiUnits_anti w (by omega))
    rw [← add_assoc, ← this]
    refine ⟨mul_ne_zero h1 ih.1, ?_⟩
    rw [pow_succ']
    exact Nat.mul_le_mul h2 ih.2

theorem sqIdx_sqSub_eq_comap {F L : Type} [Field F] [Field L] (φ : F →+* L) :
    sqSub φ = (sqs (⊤ : Subgroup Lˣ)).comap (Units.map (φ : F →* L)) := by
  ext x
  rw [mem_sqSub, Subgroup.mem_comap]
  constructor
  · rintro ⟨r, hr⟩
    have hx : φ (x : F) ≠ 0 := by simp
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hr)
    refine ⟨Units.mk0 r hr0, Subgroup.mem_top _, ?_⟩
    ext
    simp [hr, sq]
  · rintro ⟨r, -, hr⟩
    refine ⟨(r : L), ?_⟩
    have := congrArg (fun u : Lˣ => (u : L)) hr
    simpa [sq] using this.symm

theorem index_sqSub_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), v.valuation F 2 = WithZero.exp (-(e : ℤ)) → (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧ (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e := by
  intro F _ _ v e he
  obtain ⟨⟨π, -, hπ⟩, hval, -, R, hcard, -, hR⟩ := _root_.GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives F v
  have h2 : Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) := by
    rw [← he, ← hval, map_ofNat (algebraMap F (v.adicCompletion F))]
  have hsq := _root_.GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits F v e h2
  set w : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v with hw
  have hA := sqIdx_relIndex_hiUnits_add w _ R hπ hR (e + 1) e
  have hB := sqIdx_relIndex_hiUnits_add w _ R hπ hR 0 (e + 1)
  rw [show e + 1 + e = 2 * e + 1 by ring] at hA
  rw [zero_add] at hB
  have hC0 : (sqs (hiUnits w (e + 1))).relIndex (hiUnits w (e + 1)) ≠ 0 :=
    fun h => hA.1 (Subgroup.relIndex_eq_zero_of_le_left hsq h)
  have hC : (sqs (hiUnits w (e + 1))).relIndex (hiUnits w (e + 1)) ≤ R.card ^ e :=
    (Subgroup.relIndex_le_of_le_left hsq hA.1).trans hA.2
  have hD := _root_.GlobalTheory.QNorm.relIndex_sqs_le_two_mul (v.adicCompletion F)ˣ (hiUnits w 0) (hiUnits w (e + 1)) (-1)
    (sqIdx_hiUnits_anti w (by omega)) hB.1 (fun a ha => by
      have h : (a : v.adicCompletion F) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
      rcases sq_eq_one_iff.mp h with h | h
      · left; exact Units.ext h
      · right; exact Units.ext (by simpa using h)) hC0
  have hE := _root_.GlobalTheory.QNorm.index_sqs_top_le (v.adicCompletion F) w _ hπ hD.1
  rw [sqIdx_sqSub_eq_comap, Subgroup.index_comap]
  rw [← Subgroup.relIndex_top_right] at hE
  refine ⟨fun h => hE.1 (Subgroup.relIndex_eq_zero_of_le_right le_top h), ?_⟩
  refine (Subgroup.relIndex_le_of_le_right le_top hE.1).trans (hE.2.trans ?_)
  have hp : R.card ^ e ≤ Ideal.absNorm v.asIdeal ^ e := Nat.pow_le_pow_left hcard e
  have := hD.2
  omega

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNormFromBaseChangeOfPowFinrankCyclic
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm.LocStep

theorem iter_prod {A ι : Type} [CommMonoid A] (T : A →* A) (n : ℕ) (s : Finset ι) (f : ι → A) :
    T^[n] (∏ i ∈ s, f i) = ∏ i ∈ s, T^[n] (f i) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', ih, map_prod]

theorem prod_range_mul_iter {A : Type} [CommMonoid A] (T : A →* A) (d m : ℕ) (x : A) :
    ∏ i ∈ Finset.range (d * m), T^[i] x
      = ∏ k ∈ Finset.range m, (T^[d])^[k] (∏ j ∈ Finset.range d, T^[j] x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.prod_range_add, ih, Finset.prod_range_succ, ← Function.iterate_mul,
      iter_prod]
    congr 1
    exact Finset.prod_congr rfl fun j _ => Function.iterate_add_apply _ _ _ _

theorem prod_cyc {G A : Type} [Group G] [Fintype G] [CommMonoid A] (σ : G)
    (h : ∀ g, g ∈ Subgroup.zpowers σ) (f : G → A) :
    ∏ g, f g = ∏ i ∈ Finset.range (Nat.card G), f (σ ^ i) := by
  classical
  have ho : orderOf σ = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers h
  symm
  refine Finset.prod_bij (fun i _ => σ ^ i) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro i hi j hj hij
    rw [← ho] at hi hj
    exact pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij
  · intro g _
    have := (mem_zpowers_iff_mem_range_orderOf).1 (h g)
    rw [Finset.mem_image] at this
    obtain ⟨i, hi, e⟩ := this
    exact ⟨i, ho ▸ hi, e⟩

theorem telescope {A : Type} [CommMonoid A] (T : A →* A) (d : ℕ) (z : A) :
    (∏ j ∈ Finset.range d, T^[j] (T z)) * z = (∏ j ∈ Finset.range d, T^[j] z) * T^[d] z := by
  rw [← Finset.prod_range_succ, Finset.prod_range_succ']
  rfl

theorem core {A : Type} [CommMonoid A] (T : A →* A) (d m : ℕ) (x a b : A) (hab : a * b = 1)
    (hb : T b = b) (ha : T a = a) (hx : ∏ i ∈ Finset.range (d * m), T^[i] x = a ^ m)
    (h90 : ∀ u : A, ∏ k ∈ Finset.range m, (T^[d])^[k] u = 1 → ∃ z : Aˣ, u * T^[d] z = z) :
    ∃ x' : A, T^[d] x' = x' ∧ ∏ j ∈ Finset.range d, T^[j] x' = a := by
  set P : A → A := fun u => ∏ j ∈ Finset.range d, T^[j] u with hP
  have Pmul : ∀ u v, P (u * v) = P u * P v := fun u v => by
    simp only [hP, iterate_map_mul, Finset.prod_mul_distrib]
  have Pone : P 1 = 1 := by simp only [hP, iterate_map_one, Finset.prod_const_one]
  have hbk : ∀ k, T^[k] b = b := fun k => Function.IsFixedPt.iterate hb k
  obtain ⟨z, hz⟩ := h90 (P x * b) (by
    rw [prod_range_mul_iter] at hx
    have : ∀ k, (T^[d])^[k] (P x * b) = (T^[d])^[k] (P x) * b := fun k => by
      rw [← Function.iterate_mul, iterate_map_mul, hbk]
    simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [hx, ← mul_pow, hab, one_pow])
  have hzz : P z * P (z⁻¹ : Aˣ) = 1 := by rw [← Pmul, Units.mul_inv, Pone]
  have ht : ∀ u, P (T u) * u = P u * T^[d] u := fun u => telescope T d u
  have h1 : P (x * T z * (z⁻¹ : Aˣ)) = a := by
    rw [← Units.mul_left_inj z, Pmul, Pmul]
    calc P x * P (T z) * P (z⁻¹ : Aˣ) * z = P x * (P (T z) * z) * P (z⁻¹ : Aˣ) := by ac_rfl
      _ = P x * T^[d] z * (P z * P (z⁻¹ : Aˣ)) * (a * b) := by rw [ht, hab, mul_one]; ac_rfl
      _ = a * (P x * b * T^[d] z) := by rw [hzz, mul_one]; ac_rfl
      _ = a * z := by rw [hz]
  refine ⟨_, ?_, h1⟩
  generalize x * T z * (z⁻¹ : Aˣ) = w at h1
  have h2 : P (T w) = a := by
    rw [← ha, ← h1]
    simp only [hP, map_prod]
    exact Finset.prod_congr rfl fun j _ => Function.iterate_succ_apply' _ _ _
  have h3 := ht w
  rw [h1, h2] at h3
  calc T^[d] w = b * (a * T^[d] w) := by rw [← mul_assoc, mul_comm b, hab, one_mul]
    _ = w := by rw [← h3, ← mul_assoc, mul_comm b, hab, one_mul]

theorem map_pow_iter {F E K : Type} [Field F] [Field E] [Algebra F E] [CommRing K] [Algebra F K]
    (σ : E ≃ₐ[F] E) (i : ℕ) (y : K ⊗[F] E) :
    Algebra.TensorProduct.map (AlgHom.id K K) ((σ ^ i : E ≃ₐ[F] E) : E →ₐ[F] E) y
      = (Algebra.TensorProduct.map (AlgHom.id K K) (σ : E →ₐ[F] E))^[i] y := by
  induction i with
  | zero =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k e => simp
    | add u v hu hv => rw [map_add (f := _), hu, hv]; rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ← ih]
    clear ih
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k e => simp [pow_succ']
    | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem exists_pow_of_pow_eq_one {G : Type} [Group G] [Finite G] (σ : G) (d m : ℕ) (hm : m ≠ 0)
    (h : ∀ g, g ∈ Subgroup.zpowers σ) (ho : orderOf σ = d * m) (g : G) (hg : g ^ m = 1) :
    ∃ k : ℕ, g = σ ^ (d * k) := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (h g))
  rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, ho] at hg
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hm) hg
  exact ⟨k, rfl⟩

end GlobalTheory.CNorm.LocStep

namespace GlobalTheory.CNorm
open LocStep

theorem tnorm_of_tnorm_pow : ∀ (F M E K : Type) [Field F] [CharZero F] [Field M] [Field E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional F E] [IsGalois F E] [Field K] [Algebra F K], IsCyclic (E ≃ₐ[F] E) → ∀ a : F, a ≠ 0 → TNorm F E K (a ^ Module.finrank M E) → TNorm F M K a := by
  intro F M E K _ _ _ _ _ _ _ _ _ _ _ _ hc a ha ⟨x, hx⟩
  haveI : IsAbelianGalois F E := IsAbelianGalois.of_isCyclic F E
  haveI : IsGalois F M := (IsAbelianGalois.tower_bot F M E).toIsGalois
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite F M E
  haveI : FiniteDimensional F M := FiniteDimensional.left F M E
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
  set d := Module.finrank F M with hd
  set m := Module.finrank M E with hm
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have hm0 : m ≠ 0 := Module.finrank_pos.ne'
  have hcard : Nat.card (E ≃ₐ[F] E) = d * m := by
    rw [IsGalois.card_aut_eq_finrank, Module.finrank_mul_finrank]
  have ho : orderOf σ = d * m := (orderOf_eq_card_of_forall_mem_zpowers hσ).trans hcard
  have hτ : orderOf (σ ^ d) = m := by
    rw [orderOf_pow_of_dvd hd0 (ho ▸ dvd_mul_right d m), ho,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  set S := Algebra.TensorProduct.map (AlgHom.id K K) (σ : E →ₐ[F] E) with hS
  let T : K ⊗[F] E →* K ⊗[F] E := S
  have hT : (T : K ⊗[F] E → K ⊗[F] E) = S := rfl
  have hSd : (Algebra.TensorProduct.map (AlgHom.id K K) ((σ ^ d : E ≃ₐ[F] E) : E →ₐ[F] E) :
      K ⊗[F] E → K ⊗[F] E) = S^[d] := funext fun y => map_pow_iter σ d y
  have haK : algebraMap F K a ≠ 0 := (_root_.map_ne_zero _).2 ha
  obtain ⟨w, hw, hw'⟩ := core T d m x (algebraMap K _ (algebraMap F K a))
    (algebraMap K _ (algebraMap F K a)⁻¹) (by rw [← map_mul, mul_inv_cancel₀ haK, map_one])
    (S.commutes _) (S.commutes _)
    (by
      have := _root_.GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates F E K x
      rw [hx, prod_cyc σ hσ, hcard, map_pow, map_pow] at this
      rw [this]
      exact Finset.prod_congr rfl fun i _ => (map_pow_iter σ i x).symm)
    (by
      intro u hu
      have := _root_.GlobalTheory.CNorm.hilbert90_baseChange F E K (σ ^ d) m hτ u (by rw [hSd]; exact hu)
      rw [hSd] at this
      exact this)
  obtain ⟨z, rfl⟩ := _root_.GlobalTheory.CNorm.tensor_exists_of_galois_fixed F M E K w (by
    intro h
    obtain ⟨k, hk⟩ := exists_pow_of_pow_eq_one σ d m hm0 hσ ho (h.restrictScalars F) (by
      have h1 : h ^ m = 1 := by
        rw [hm, ← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
      have := map_pow (AlgEquiv.restrictScalarsHom F (S := M) (A := E)) h m
      rw [h1, map_one] at this
      exact this.symm)
    rw [hk, map_pow_iter, Function.iterate_mul]
    exact Function.IsFixedPt.iterate hw k)
  set ι := Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) with hι
  have hinj : Function.Injective ι :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      (IsScalarTower.toAlgHom F M E).toLinearMap (algebraMap M E).injective
  let σ' : M ≃ₐ[F] M := AlgEquiv.restrictNormalHom M σ
  have hσ' : ∀ g, g ∈ Subgroup.zpowers σ' := by
    intro g
    obtain ⟨g', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := M) E g
    obtain ⟨k, rfl⟩ := hσ g'
    exact ⟨k, (map_zpow _ _ _).symm⟩
  have hcomm : ∀ u : K ⊗[F] M,
      ι (Algebra.TensorProduct.map (AlgHom.id K K) (σ' : M →ₐ[F] M) u) = S (ι u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul k e =>
      have : algebraMap M E (σ' e) = σ (algebraMap M E e) :=
        AlgEquiv.restrictNormal_commutes σ M e
      simp [hι, hS, this]
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  refine ⟨z, ?_⟩
  apply (algebraMap K (K ⊗[F] M)).injective
  apply hinj
  rw [_root_.GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates F M K z, prod_cyc σ' hσ', IsGalois.card_aut_eq_finrank, ι.commutes, ← hw',
    map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow_iter]
  exact Function.Semiconj.iterate_right hcomm i z

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OfIntermediateFieldTower
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem bijective_mul_out_inv {H G : Type} [Group H] [Group G] (φ : H →* G)
    (hφ : Function.Injective φ) :
    Function.Bijective (fun p : H × (G ⧸ φ.range) => φ p.1 * (p.2.out)⁻¹) := by
  constructor
  · rintro ⟨h, q⟩ ⟨h', q'⟩ e
    simp only at e
    have hq : q = q' := by
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
      refine ⟨h⁻¹ * h', ?_⟩
      rw [map_mul, map_inv]
      calc (φ h)⁻¹ * φ h' = (φ h)⁻¹ * (φ h' * (q'.out)⁻¹) * q'.out := by group
        _ = (φ h)⁻¹ * (φ h * (q.out)⁻¹) * q'.out := by rw [e]
        _ = _ := by group
    subst hq
    rw [hφ (mul_right_cancel e)]
  · intro g
    have : ((g⁻¹ : G) : G ⧸ φ.range).out⁻¹ * g⁻¹ ∈ φ.range := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    obtain ⟨h, hh⟩ := this
    refine ⟨(h⁻¹, ((g⁻¹ : G) : G ⧸ φ.range)), ?_⟩
    simp only [map_inv, hh]
    group

theorem TNorm.of_tower (F M E K : Type) [Field F] [Field M] [Field E] [Algebra F M] [Algebra M E]
    [Algebra F E] [IsScalarTower F M E] [FiniteDimensional F E] [IsGalois F E] [Field K]
    [Algebra F K] [Algebra M K] [IsScalarTower F M K] (x : F) (hx : TNorm F E K x) :
    TNorm M E K (algebraMap F M x) := by
  classical
  obtain ⟨y, hy⟩ := hx
  haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite F M E
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  let π : K ⊗[F] E →ₐ[K] K ⊗[M] E := Algebra.TensorProduct.mapOfCompatibleSMul M F K K E
  let φ : (E ≃ₐ[M] E) →* (E ≃ₐ[F] E) :=
    { toFun := fun h => h.restrictScalars F, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := AlgEquiv.restrictScalars_injective F
  haveI : Fintype ((E ≃ₐ[F] E) ⧸ φ.range) := Fintype.ofFinite _
  have key : ∀ (h : E ≃ₐ[M] E) (g : E ≃ₐ[F] E) (z : K ⊗[F] E),
      Algebra.TensorProduct.map (AlgHom.id K K) (h : E →ₐ[M] E)
        (π (Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) z)) =
      π (Algebra.TensorProduct.map (AlgHom.id K K) ((φ h * g : E ≃ₐ[F] E) : E →ₐ[F] E) z) := by
    intro h g z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  refine ⟨π (∏ q : (E ≃ₐ[F] E) ⧸ φ.range,
    Algebra.TensorProduct.map (AlgHom.id K K) (((q.out)⁻¹ : E ≃ₐ[F] E) : E →ₐ[F] E) y), ?_⟩
  apply (algebraMap K (K ⊗[M] E)).injective
  rw [_root_.GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates M E K, ← IsScalarTower.algebraMap_apply F M K x, ← hy, ← π.commutes,
    _root_.GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates F E K, map_prod π, map_prod π,
    ← (bijective_mul_out_inv φ hφ).prod_comp (fun g : E ≃ₐ[F] E =>
      π (Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y)), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun h _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun q _ => key h _ y

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowsSubgroupOfSelfSPow
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm


open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
theorem _root_.GlobalTheory.CNorm.pTor_pIdx_sUnits : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F]
    (ζ : F) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p →
    _root_.GlobalTheory.CNorm.pTor p (_root_.GlobalTheory.QNorm.sUnits F S) = p ∧
      _root_.GlobalTheory.CNorm.pIdx p (_root_.GlobalTheory.QNorm.sUnits F S) =
        p ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro p F _ _ ζ S hp hζ
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Group.FG (_root_.GlobalTheory.QNorm.sUnits F S) := _root_.GlobalTheory.QNorm.sUnits_fg F S
  obtain ⟨-, h2⟩ := _root_.GlobalTheory.CNorm.pIdx_top_of_fg p (_root_.GlobalTheory.QNorm.sUnits F S) hp.pos
  have hroots : ∀ x : Fˣ, x ^ p = 1 → x ∈ _root_.GlobalTheory.QNorm.sUnits F S := by
    intro x hx
    rw [_root_.GlobalTheory.QNorm.mem_sUnits]
    intro v _
    have h := congrArg (fun y : Fˣ => HeightOneSpectrum.valuation F v (y : F)) hx
    simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h
    exact (pow_eq_one_iff_of_nonneg zero_le' hp.ne_zero).mp h
  have htor : _root_.GlobalTheory.CNorm.pTor p (_root_.GlobalTheory.QNorm.sUnits F S) = p := by
    unfold _root_.GlobalTheory.CNorm.pTor
    refine (Nat.card_congr ?_).trans hζ.card_rootsOfUnity
    exact
      { toFun := fun x => ⟨x.1, (mem_rootsOfUnity p x.1).mpr x.2.2⟩
        invFun := fun y => ⟨y.1, hroots y.1 ((mem_rootsOfUnity p y.1).mp y.2),
          (mem_rootsOfUnity p y.1).mp y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have htorTop : _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup (_root_.GlobalTheory.QNorm.sUnits F S)) =
      _root_.GlobalTheory.CNorm.pTor p (_root_.GlobalTheory.QNorm.sUnits F S) := by
    unfold _root_.GlobalTheory.CNorm.pTor
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, by rw [← Subgroup.coe_pow, x.2.2, OneMemClass.coe_one]⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, Subgroup.mem_top _, Subtype.ext y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hidxTop : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup (_root_.GlobalTheory.QNorm.sUnits F S)) =
      _root_.GlobalTheory.CNorm.pIdx p (_root_.GlobalTheory.QNorm.sUnits F S) := by
    unfold _root_.GlobalTheory.CNorm.pIdx _root_.GlobalTheory.CNorm.pows
    rw [Subgroup.relIndex_top_right]
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and, powMonoidHom_apply,
      Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, y.2, by rw [← hy]; rfl⟩
    · rintro ⟨y, hyH, hy⟩
      exact ⟨⟨y, hyH⟩, Subtype.ext hy⟩
  refine ⟨htor, ?_⟩
  rw [← hidxTop, h2, htorTop, htor, ← _root_.GlobalTheory.QNorm.sUnits_rank F S, pow_succ]

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexSquaresSUnitsNumberField
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sqs_subgroupOf_self {G : Type} [CommGroup G] (U : Subgroup G) :
    (sqs U).subgroupOf U = sqs (⊤ : Subgroup U) := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, Subgroup.mem_top _, Subtype.ext h⟩
  · rintro ⟨y, -, h⟩
    exact ⟨y.1, y.2, congrArg Subtype.val h⟩

theorem card_sq_eq_one_sUnits (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Nat.card {a : sUnits F S // a ^ 2 = 1} = 2 := by
  have hm : (-1 : Fˣ) ∈ sUnits F S := by
    rw [mem_sUnits]; intro v _; simp
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, by simp⟩, ⟨⟨-1, hm⟩, Subtype.ext (by simp)⟩, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun a : {a : sUnits F S // a ^ 2 = 1} => ((a.1.1 : Fˣ) : F)) h
    simp only [OneMemClass.coe_one, Units.val_one, Units.val_neg] at h1
    norm_num at h1
  · rw [Set.eq_univ_iff_forall]
    rintro ⟨⟨a, ha⟩, h⟩
    have h1 : (a : F) ^ 2 = 1 := by
      have := congrArg (fun a : sUnits F S => ((a.1 : Fˣ) : F)) h
      simpa using this
    rcases sq_eq_one_iff.mp h1 with h2 | h2
    · left
      exact Subtype.ext (Subtype.ext (Units.ext h2))
    · right
      exact Subtype.ext (Subtype.ext (Units.ext h2))

theorem relIndex_sqs_sUnits : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (sqs (sUnits F S)).relIndex (sUnits F S) = 2 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro F _ _ S
  haveI := _root_.GlobalTheory.QNorm.sUnits_fg F S
  rw [Subgroup.relIndex, sqs_subgroupOf_self, _root_.GlobalTheory.QNorm.index_sqs_top_of_fg, card_sq_eq_one_sUnits,
    ← _root_.GlobalTheory.QNorm.sUnits_rank F S, pow_succ]

end GlobalTheory.QNorm
end

