module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ProdAbsNormPowValuationTwoLe
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem prod_absNorm_pow_le_two_pow :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ), (∀ v ∈ S, v.valuation F 2 = WithZero.exp (-(e v : ℤ))) → ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ 2 ^ Module.finrank ℚ F := by
  intro F _ _ S e h
  have hdvd : ∀ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(2 : 𝓞 F)} := by
    intro v hv
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd]
    have h2 : v.valuation F (algebraMap (𝓞 F) F 2) = v.intValuation 2 :=
      HeightOneSpectrum.valuation_of_algebraMap v 2
    rw [map_ofNat, h v hv] at h2
    exact h2.ge
  have hprod : ∏ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(2 : 𝓞 F)} := by
    refine Finset.prod_dvd_of_coprime ?_ hdvd
    intro v _ w _ hvw
    refine IsCoprime.pow ?_
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal
      (fun hh => hvw (HeightOneSpectrum.ext hh))
  have hn : Ideal.absNorm (Ideal.span {(2 : 𝓞 F)}) = 2 ^ Module.finrank ℚ F := by
    rw [Ideal.absNorm_span_singleton]
    have : (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have h3 := map_dvd Ideal.absNorm hprod
  rw [hn, map_prod] at h3
  simp only [map_pow] at h3
  exact Nat.le_of_dvd (by positivity) h3

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatMemRatZariskiClosurePoints
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatPts


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
lemma _root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap {ι R : Type} [CommRing R] [Algebra ℚ R]
    (f : MvPolynomial (ι × ι) ℚ) (γ : Matrix ι ι ℚ) :
    _root_.GlobalTheory.ClassFin.ev f (γ.map (algebraMap ℚ R)) = algebraMap ℚ R (_root_.GlobalTheory.ClassFin.ev f γ) := by
  unfold _root_.GlobalTheory.ClassFin.ev
  rw [← MvPolynomial.aeval_algebraMap_apply]
  rfl


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.RatPts.rat_mem_pts : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ γ : Matrix ι ι ℚ, γ.map (algebraMap ℚ ℂ) ∈ Γ → γ ∈ _root_.GlobalTheory.ClassFin.pts Γ ℚ) ∧ ∀ (R : Type) [CommRing R] [Algebra ℚ R], ∀ γ ∈ _root_.GlobalTheory.ClassFin.pts Γ ℚ, γ.map (algebraMap ℚ R) ∈ _root_.GlobalTheory.ClassFin.pts Γ R := by
  intro ι _ _ Γ
  refine ⟨fun γ hγ => ?_, fun R _ _ γ hγ => ?_⟩
  · simp only [_root_.GlobalTheory.ClassFin.pts, Set.mem_setOf_eq]
    intro f hf
    have h := hf _ hγ
    rw [_root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap] at h
    exact (algebraMap ℚ ℂ).injective (by rw [h, map_zero])
  · simp only [_root_.GlobalTheory.ClassFin.pts, Set.mem_setOf_eq] at hγ ⊢
    intro f hf
    rw [_root_.GlobalTheory.ClassFin.RatPts.ev_map_algebraMap, hγ f hf, map_zero]

end GlobalTheory.ClassFin.RatPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexHigherUnitsSuccLeCard
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

private theorem le_exp_sub_one_of_lt_exp {a : ℤᵐ⁰} {m : ℤ} (h : a < WithZero.exp m) :
    a ≤ WithZero.exp (m - 1) := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [← WithZero.exp_log ha] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem relIndex_hiUnits_succ_le :
    ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K) (R : Finset K) (n : ℕ),
      w π = WithZero.exp (-1) → (∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) →
      (hiUnits w (n + 1)).relIndex (hiUnits w n) ≠ 0 ∧
        (hiUnits w (n + 1)).relIndex (hiUnits w n) ≤ R.card := by
  intro K _ w π R n hπ hR
  have hπn : w (π ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; simp
  have hπn0 : w (π ^ n) ≠ 0 := by rw [hπn]; exact WithZero.exp_ne_zero
  have hπn0' : π ^ n ≠ 0 := by
    intro h; rw [h] at hπn0; simp at hπn0
  have hex : ∀ x : hiUnits w n, ∃ r : R, w ((((x : Kˣ) : K) - 1) / π ^ n - r) < 1 := by
    intro x
    have hx : w (((x : Kˣ) : K) - 1) ≤ WithZero.exp (-(n : ℤ)) := x.2.2
    obtain ⟨r, hr, h⟩ := hR ((((x : Kˣ) : K) - 1) / π ^ n) (by
      rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr hπn0), hπn]; exact hx)
    exact ⟨⟨r, hr⟩, h⟩
  choose f hf using hex
  have key : ∀ x y : hiUnits w n, f x = f y →
      x⁻¹ * y ∈ (hiUnits w (n + 1)).subgroupOf (hiUnits w n) := by
    intro x y hxy
    have hx1 : w ((x : Kˣ) : K) = 1 := x.2.1
    have hy1 : w ((y : Kˣ) : K) = 1 := y.2.1
    have h1 := hf x
    have h2 := hf y
    rw [← hxy] at h2
    have h3 := w.map_sub_lt h2 h1
    have h4 : (((y : Kˣ) : K) - 1) / π ^ n - (f x : K) -
        ((((x : Kˣ) : K) - 1) / π ^ n - (f x : K)) =
        (((y : Kˣ) : K) - ((x : Kˣ) : K)) / π ^ n := by ring
    rw [h4, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hπn0), hπn] at h3
    have h5 := le_exp_sub_one_of_lt_exp h3
    rw [Subgroup.mem_subgroupOf]
    have hv : ((((x⁻¹ * y : hiUnits w n) : Kˣ)) : K) =
        ((x : Kˣ) : K)⁻¹ * ((y : Kˣ) : K) := by simp
    refine ⟨by rw [hv, map_mul, map_inv₀, hx1, hy1]; simp, ?_⟩
    have hx0 : ((x : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have h6 : ((x : Kˣ) : K)⁻¹ * ((y : Kˣ) : K) - 1 =
        ((x : Kˣ) : K)⁻¹ * (((y : Kˣ) : K) - ((x : Kˣ) : K)) := by
      field_simp
    rw [hv, h6, map_mul, map_inv₀, hx1, inv_one, one_mul]
    refine h5.trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  have hinj : Function.Injective
      (fun q : hiUnits w n ⧸ (hiUnits w (n + 1)).subgroupOf (hiUnits w n) => f q.out) := by
    intro p q hpq
    have := key _ _ hpq
    rw [← QuotientGroup.eq] at this
    simpa using this
  have hfin : Finite (hiUnits w n ⧸ (hiUnits w (n + 1)).subgroupOf (hiUnits w n)) :=
    Finite.of_injective _ hinj
  refine ⟨?_, ?_⟩
  · exact Subgroup.index_ne_zero_of_finite
  · have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := R), Fintype.card_coe] at this
    exact this

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexNormMulRelIndexSqsKer
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem relIndex_norm_mul_relIndex_sqs_ker :
    ∀ (A : Type) [CommGroup A] (σ : A →* A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → (MonoidHom.id A * σ).range.relIndex (σ.eqLocus (MonoidHom.id A)) * (sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) := by
  intro A _ σ hσ h90
  set N : A →* A := MonoidHom.id A * σ with hN
  set B : Subgroup A := σ.eqLocus (MonoidHom.id A) with hB
  let f : A →* A := MonoidHom.id A / σ
  have hNa : ∀ a, N a = a * σ a := fun a => rfl
  have hfa : ∀ a, f a = a / σ a := fun a => rfl
  have hBa : ∀ a, a ∈ B ↔ σ a = a := fun a => Iff.rfl
  have hK : ∀ a, a ∈ N.ker ↔ a * σ a = 1 := fun a => Iff.rfl
  have hsq : ∀ (U : Subgroup A) (a : A), a ∈ sqs U ↔ ∃ b ∈ U, b ^ 2 = a := fun U a => Iff.rfl
  have h1 : sqs B ≤ N.range := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := (hsq _ _).1 ha
    exact ⟨b, by rw [hNa, (hBa b).1 hb, sq]⟩
  have h2 : N.range ≤ B := by
    rintro _ ⟨a, rfl⟩
    rw [hBa, hNa, map_mul, hσ, mul_comm]
  have h3 : f.range = N.ker := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      rw [hK, hfa, map_div, hσ]
      simp
    · intro ha
      obtain ⟨b, hb⟩ := h90 a ((hK a).1 ha)
      exact ⟨b, hb.symm⟩
  have h4 : (sqs B).comap N = (sqs N.ker).comap f := by
    ext a
    rw [Subgroup.mem_comap, Subgroup.mem_comap, hsq, hsq]
    constructor
    · rintro ⟨b, hb, hab⟩
      rw [hBa] at hb
      rw [hNa] at hab
      refine ⟨a / b, ?_, ?_⟩
      · rw [hK, map_div, hb, div_mul_div_comm, ← hab, sq, div_self']
      · rw [hfa, div_pow, hab, sq, mul_div_mul_left_eq_div]
    · rintro ⟨c, hc, hac⟩
      rw [hK] at hc
      rw [hfa] at hac
      have hc' : σ c = c⁻¹ := eq_inv_of_mul_eq_one_right hc
      have ha' : σ a = a / c ^ 2 := by rw [hac]; simp
      refine ⟨a / c, ?_, ?_⟩
      · rw [hBa, map_div, hc', ha', sq, div_inv_eq_mul, div_mul_eq_div_div, div_mul_cancel]
      · rw [hNa, ha', div_pow, sq a, mul_div_assoc]
  have h5 : (sqs B).relIndex N.range = (sqs N.ker).relIndex N.ker := by
    rw [← Subgroup.index_comap, h4, Subgroup.index_comap, h3]
  rw [← h5, mul_comm]
  exact Subgroup.relIndex_mul_relIndex _ _ _ h1 h2

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexSquaresLeTwoMulOfSubgroup
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem relIndex_le_two_of_coset {G : Type} [CommGroup G] (H K : Subgroup G) (ε : G)
    (h : ∀ x ∈ K, x ∈ H ∨ x * ε⁻¹ ∈ H) : H.relIndex K ≤ 2 := by
  by_cases hK : K ≤ H
  · rw [Subgroup.relIndex_eq_one.mpr hK]; norm_num
  · obtain ⟨a, haK, haH⟩ := SetLike.not_le_iff_exists.mp hK
    have ha := (h a haK).resolve_left haH
    apply le_of_eq
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a⁻¹, K.inv_mem haK⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : G) ∈ H
    · right
      refine ⟨hb, fun hba => haH ?_⟩
      have := H.mul_mem hb (H.inv_mem hba)
      simpa using this
    · left
      refine ⟨?_, hb⟩
      have := H.mul_mem ((h b b.2).resolve_left hb) (H.inv_mem ha)
      have e : (b : G) * ε⁻¹ * (a * ε⁻¹)⁻¹ = b * a⁻¹ := by
        rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
      rwa [e] at this

theorem relIndex_sqs_le_two_mul :
    ∀ (G : Type) [CommGroup G] (U H : Subgroup G) (ε : G), H ≤ U → H.relIndex U ≠ 0 →
      (∀ a : G, a ^ 2 = 1 → a = 1 ∨ a = ε) → (sqs H).relIndex H ≠ 0 →
      (sqs U).relIndex U ≠ 0 ∧ (sqs U).relIndex U ≤ 2 * (sqs H).relIndex H := by
  intro G _ U H ε hHU hfin hε hsq
  have hle : ∀ V : Subgroup G, sqs V ≤ V := by
    rintro V x ⟨y, hy, rfl⟩
    exact V.pow_mem hy 2
  have hmono : sqs H ≤ sqs U := Subgroup.map_mono hHU
  have h1 := Subgroup.relIndex_mul_relIndex (sqs H) H U (hle H) hHU
  have h2 := Subgroup.relIndex_mul_relIndex (sqs H) (sqs U) U hmono (hle U)
  set H' : Subgroup G := (sqs H).comap (powMonoidHom 2) with hH'
  have h3 : H'.relIndex U = (sqs H).relIndex (sqs U) := by
    rw [hH', Subgroup.relIndex_comap]; rfl
  have hHH' : H ≤ H' ⊓ U := le_inf (Subgroup.le_comap_map _ _) hHU
  have h4 := Subgroup.relIndex_mul_relIndex H (H' ⊓ U) U hHH' inf_le_right
  rw [Subgroup.inf_relIndex_right, h3] at h4
  have h5 : H.relIndex (H' ⊓ U) ≤ 2 := by
    apply relIndex_le_two_of_coset H _ ε
    rintro x ⟨⟨y, hy, hxy⟩, -⟩
    simp only [powMonoidHom_apply] at hxy
    have : (x * y⁻¹) ^ 2 = 1 := by rw [mul_pow, ← hxy, inv_pow, mul_inv_cancel]
    rcases hε _ this with h | h
    · left
      rw [mul_inv_eq_one] at h
      rw [h]; exact hy
    · right
      have e : x * ε⁻¹ = y := by
        rw [← h, mul_inv_rev, inv_inv, mul_comm y, mul_inv_cancel_left]
      rw [e]; exact hy
  have hne : (sqs H).relIndex (sqs U) * (sqs U).relIndex U ≠ 0 := by
    rw [h2, ← h1]; exact mul_ne_zero hsq hfin
  obtain ⟨hb, ha⟩ := mul_ne_zero_iff.mp hne
  refine ⟨ha, ?_⟩
  apply Nat.le_of_mul_le_mul_left _ (Nat.pos_of_ne_zero hb)
  rw [h2, ← h1, ← h4]
  calc (sqs H).relIndex H * (H.relIndex (H' ⊓ U) * (sqs H).relIndex (sqs U))
      ≤ (sqs H).relIndex H * (2 * (sqs H).relIndex (sqs U)) := by gcongr
    _ = _ := by ring

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RestrictScalarsMatrixOfBasisHomInjectiveIsUnit
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem res_mulVec_repr {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
    [Fintype κ] (b : Module.Basis β R A) (g : Matrix κ κ A) (v : κ → A) :
    res b g *ᵥ (fun p : κ × β => b.repr (v p.1) p.2) = fun p : κ × β => b.repr ((g *ᵥ v) p.1) p.2 := by
  funext p
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, res, Matrix.of_apply, Fintype.sum_prod_type, map_sum,
    Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (Algebra.leftMulMatrix_mulVec_repr b (g p.1 j) (v j)) p.2
  simpa [Matrix.mulVec, dotProduct] using h

theorem res_one_mul_injective_isUnit :
    ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), res b (1 : Matrix κ κ A) = 1 ∧ (∀ g h : Matrix κ κ A, res b (g * h) = res b g * res b h) ∧ Function.Injective (fun g : Matrix κ κ A => res b g) ∧ ∀ g : Matrix κ κ A, IsUnit (res b g).det → IsUnit g := by
  intro R A β κ _ _ _ _ _ _ _ b
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext ⟨i, k⟩ ⟨j, l⟩
    by_cases h : i = j
    · subst h
      simp [res, Matrix.one_apply]
    · simp [res, Matrix.one_apply, h]
  · intro g h
    ext ⟨i, k⟩ ⟨j, l⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [res, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, map_sum, map_mul,
      Matrix.sum_apply]
  · intro g h hgh
    ext i j
    apply Algebra.leftMulMatrix_injective b
    ext k l
    exact congrFun (congrFun hgh (i, k)) (j, l)
  · intro g hg
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro w
    have hs : Function.Surjective (res b g).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hg)
    obtain ⟨u, hu⟩ := hs (fun p : κ × β => b.repr (w p.1) p.2)
    refine ⟨fun i => b.equivFun.symm (fun k => u (i, k)), ?_⟩
    have h := res_mulVec_repr b g (fun i => b.equivFun.symm (fun k => u (i, k)))
    have hu' : (fun p : κ × β => b.repr (b.equivFun.symm (fun k => u (p.1, k))) p.2) = u := by
      funext p
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hu', hu] at h
    funext i
    apply b.repr.injective
    ext k
    exact (congrFun h (i, k)).symm

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsNumberFieldFg
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

noncomputable section

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma valuation_algebraMap_unit_eq_one {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (u : (𝓞 F)ˣ) : v.valuation F (algebraMap (𝓞 F) F u) = 1 := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact fun h => v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma exists_unit_of_valuation_eq_one {F : Type} [Field F] [NumberField F] (y : Fˣ)
    (hy : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y = 1) :
    ∃ u : (𝓞 F)ˣ, algebraMap (𝓞 F) F u = y := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (y : F)
    fun v => (hy v).le
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F ((y⁻¹ : Fˣ) : F)
    fun v => by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hy v, inv_one]
  have hab : a * b = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, ha⟩


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.sUnits_fg :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
      Group.FG (_root_.GlobalTheory.QNorm.sUnits F S) := by
  intro F _ _ S
  set G := _root_.GlobalTheory.QNorm.sUnits F S
  let val : HeightOneSpectrum (𝓞 F) → G →* Multiplicative ℤ := fun v =>
    (WithZero.unitsWithZeroEquiv.toMonoidHom.comp
      (Units.map (v.valuation F : F →* ℤᵐ⁰))).comp G.subtype
  have hval : ∀ v x, val v x = 1 ↔ v.valuation F ((x : Fˣ) : F) = 1 := by
    intro v x
    simp only [val, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, Units.ext_iff, Units.coe_map, Units.val_one]
    rfl
  let f : Additive G →+ (S → ℤ) :=
    { toFun := fun x v => Multiplicative.toAdd (val v.1 x.toMul)
      map_zero' := by ext v; simp
      map_add' := fun x y => by ext v; simp }
  let ψ : (𝓞 F)ˣ →* G :=
    { toFun := fun u => ⟨Units.map (algebraMap (𝓞 F) F : (𝓞 F) →* F) u, by
        rw [_root_.GlobalTheory.QNorm.mem_sUnits]
        intro v _
        exact valuation_algebraMap_unit_eq_one v u⟩
      map_one' := by ext; simp
      map_mul' := fun u w => by ext; simp }
  let g : Additive (𝓞 F)ˣ →+ Additive G := MonoidHom.toAdditive ψ
  have hker : f.toIntLinearMap.ker = LinearMap.range g.toIntLinearMap := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range, AddMonoidHom.coe_toIntLinearMap]
    constructor
    · intro hx
      obtain ⟨u, hu⟩ := exists_unit_of_valuation_eq_one ((x.toMul : G) : Fˣ) fun v => by
        by_cases hv : v ∈ S
        · rw [← hval]
          have := congrFun hx ⟨v, hv⟩
          simpa [f] using this
        · exact (_root_.GlobalTheory.QNorm.mem_sUnits F S _).mp x.toMul.2 v hv
      refine ⟨Additive.ofMul u, ?_⟩
      apply Additive.toMul.injective
      ext
      simpa [g, ψ] using hu
    · rintro ⟨u, rfl⟩
      ext v
      have : val v.1 (ψ u.toMul) = 1 :=
        (hval _ _).mpr (valuation_algebraMap_unit_eq_one v.1 u.toMul)
      simpa [f, g] using this
  have htop : (⊤ : Submodule ℤ (Additive G)).FG := by
    refine Submodule.fg_of_fg_map_of_fg_inf_ker f.toIntLinearMap (IsNoetherian.noetherian _) ?_
    rw [top_inf_eq, hker, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  have : Module.Finite ℤ (Additive G) := ⟨htop⟩
  rw [Group.fg_iff_monoid_fg, Monoid.fg_iff_add_fg, ← AddGroup.fg_iff_addMonoid_fg]
  exact Module.Finite.iff_addGroup_fg.mp this

end GlobalTheory.QNorm

end
end

