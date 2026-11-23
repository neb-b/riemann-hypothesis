module

public import Formalism.HermitianCurvature.StatementJ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OutsideSystemsBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AxiomsFromFamilies
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0019
public import Formalism.HermitianCurvature.StatementWd
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0016
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QEFirstMulSecondEqSwap

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PullLatticeTypedUnit
section
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J

open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.Jx12

theorem mem_idl_shift (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (hg : 0 < g) (k ν : ℤ)
    (y : E) : y ∈ S6.zsub E (S6.idl E g k ν) ↔ (g : E) ^ 2 * y ∈ S6.zsub E (S6.idl E g (k + 2) ν) := by
  have hg0 : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  have key : S6.idl E g (k + 2) ν =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) ((g : E) ^ 2) * S6.idl E g k ν := by
    unfold S6.idl
    rw [zpow_add₀ hg0, ← FractionalIdeal.spanSingleton_mul_spanSingleton, zpow_two, sq]
    ring
  simp only [S6.zsub, Submodule.restrictScalars_mem, FractionalIdeal.mem_coe, key,
    FractionalIdeal.mem_singleton_mul]
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    rwa [mul_left_cancel₀ (pow_ne_zero 2 hg0) hzy]

theorem lift_per (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (hg : 0 < g) (ν : ℤ) (s : ℕ)
    (y : E) : y ∈ S6.liftLat E g ν s ↔ (g : E) ^ 2 * y ∈ S6.perLat E g (-ν) s := by
  have h1 : y ∈ S6.zsub E (S6.idl E g (-1) (-ν)) ↔ (g : E) ^ 2 * y ∈ S6.zsub E (S6.idl E g 1 (-ν)) := by
    have h := mem_idl_shift E g hg (-1) (-ν) y
    rwa [show (-1 : ℤ) + 2 = 1 by norm_num] at h
  have h2 : ∀ z : E, z ∈ S6.zsub E (S6.idl E g 0 (-ν)) ↔
      (g : E) ^ 2 * z ∈ S6.zsub E (S6.idl E g 2 (-ν)) := fun z => by
    have h := mem_idl_shift E g hg 0 (-ν) z
    rwa [zero_add] at h
  have hφ : (LinearMap.id - ((-1 : ℤ) ^ s) • S6.conjZ E : E →ₗ[ℤ] E) ((g : E) ^ 2 * y) =
      (g : E) ^ 2 * (LinearMap.id - ((-1 : ℤ) ^ s) • S6.conjZ E : E →ₗ[ℤ] E) y := by
    show (g : E) ^ 2 * y - ((-1 : ℤ) ^ s) • (IsCMField.complexConj E) ((g : E) ^ 2 * y) =
      (g : E) ^ 2 * (y - ((-1 : ℤ) ^ s) • (IsCMField.complexConj E) y)
    rw [map_mul, map_pow, map_natCast, zsmul_eq_mul, zsmul_eq_mul]
    ring
  unfold S6.liftLat S6.perLat S6.twLat
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_comap, hφ, h1, h2]

end Formalism.FourierDecayAlt.P.Jx12

namespace Formalism.FourierDecayAlt.P

private lemma unit_mul_mem_iff' {M : Type} [CommRing M] (R : Subring M) (c : Mˣ) (hc : (c : M) ∈ R)
    (hci : ((c⁻¹ : Mˣ) : M) ∈ R) (x : M) : (c : M) * x ∈ R ↔ x ∈ R := by
  constructor
  · intro h
    have h' := R.mul_mem hci h
    rwa [Units.inv_mul_cancel_left] at h'
  · intro h
    exact R.mul_mem hc h

private lemma mul_unit_mul_mem_iff {M : Type} [CommRing M] (R : Subring M) (c : Mˣ) (hc : (c : M) ∈ R)
    (hci : ((c⁻¹ : Mˣ) : M) ∈ R) (x y : M) : x * (c : M) * y ∈ R ↔ x * y ∈ R := by
  rw [show x * (c : M) * y = (c : M) * (x * y) by ring]
  exact unit_mul_mem_iff' R c hc hci _

theorem pull_lattice_typed_unit : Formalism.FourierDecayAlt.J.PullLatticeTypedUnit := by
  intro hT E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ R u c α ψ η Θ hR hc hci hu t
  refine Iff.trans ?_ (Formalism.FourierDecayAlt.P.pull_lattice_typed hT E g ν s hg hpd P hP hgP K o σ hσ R
    (c⁻¹ * u) α ψ η Θ hR (by rw [Units.val_mul, hu, Units.inv_mul_cancel_left]) t)
  show (u : K × K) * _ ∈ R ↔ ((c⁻¹ * u : (K × K)ˣ) : K × K) * _ ∈ R
  rw [hu, Units.val_mul, hu, Units.inv_mul_cancel_left, mul_assoc]
  exact unit_mul_mem_iff' R c hc hci _

theorem pull_lift_typed : Formalism.FourierDecayAlt.J.PullLiftTyped := by
  intro hT E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ R u α ψ η Θ hR hu x
  have h0 := Formalism.FourierDecayAlt.P.pull_lattice_typed hT E g (-ν) s hg hpd P hP hgP K o σ hσ R u α ψ η Θ
    hR hu ((g : E) ^ 2 * x)
  have hloc : (g : E) ^ 2 * x ∈ S6.locAt E P (S6.perLat E g (-ν) s) ↔
      x ∈ S6.locAt E P (S6.liftLat E g ν s) := by
    simp only [S6.locAt, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, ha, h⟩
      refine ⟨a, ha, (Formalism.FourierDecayAlt.P.Jx12.lift_per E g hg ν s _).2 ?_⟩
      rwa [mul_left_comm]
    · rintro ⟨a, ha, h⟩
      refine ⟨a, ha, ?_⟩
      have h' := (Formalism.FourierDecayAlt.P.Jx12.lift_per E g hg ν s _).1 h
      rwa [mul_left_comm] at h'
  refine Iff.trans ?_ (h0.trans hloc)
  have hg' : (g : K) ≠ 0 := by
    intro h
    apply Units.ne_zero u
    rw [hu, h, inv_zero, mul_zero]
    rfl
  have hs2 : ((-1 : K) ^ s) * (-1) ^ s = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hgg : (g : K)⁻¹ * (g : K)⁻¹ * (g : K) ^ 2 = 1 := by field_simp
  have hinv : ((u⁻¹ : (K × K)ˣ) : K × K) = (u : K × K) * (g : K × K) ^ 2 := by
    rw [Units.val_inv_eq_inv_val]
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [hu]
    ext
    · simp only [Prod.fst_mul, Prod.pow_fst, Prod.fst_natCast, Prod.fst_one]
      linear_combination hgg
    · simp only [Prod.snd_mul, Prod.pow_snd, Prod.snd_natCast, Prod.snd_one]
      linear_combination ((g : K)⁻¹ * (g : K)⁻¹ * (g : K) ^ 2) * hs2 + hgg
  show ((u⁻¹ : (K × K)ˣ) : K × K) * (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) x ∈ R ↔
    (u : K × K) * (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) ((g : E) ^ 2 * x) ∈ R
  rw [hinv, map_mul, map_pow, map_natCast, mul_assoc]

theorem pull_lift_typed_unit : Formalism.FourierDecayAlt.J.PullLiftTypedUnit := by
  intro hT E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ R u c α ψ η Θ hR hc hci hu x
  refine Iff.trans ?_ (pull_lift_typed hT E g ν s hg hpd P hP hgP K o σ hσ R (c⁻¹ * u) α ψ η Θ hR
    (by rw [Units.val_mul, hu, Units.inv_mul_cancel_left]) x)
  show ((u⁻¹ : (K × K)ˣ) : K × K) * _ ∈ R ↔ (((c⁻¹ * u)⁻¹ : (K × K)ˣ) : K × K) * _ ∈ R
  rw [mul_inv_rev, inv_inv, Units.val_mul]
  exact (mul_unit_mul_mem_iff R c hc hci _ _).symm

private lemma isPSD_comp_of_isPSD_image {X Y : Type} {inst : DecidableEq Y} (F : Finset X) (η : X → Y)
    (k : Y → Y → ℂ) (hk : A5.IsPSD (F.image η) k) : A5.IsPSD F (fun h h' => k (η h) (η h')) := by
  intro a
  have hmap : ∀ x ∈ F, η x ∈ F.image η := fun x hx => Finset.mem_image_of_mem η hx
  have key : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y) =
      ∑ p ∈ F.image η, ∑ q ∈ F.image η,
        (∑ x ∈ F.filter (fun x => η x = p), a x) * conj (∑ y ∈ F.filter (fun y => η y = q), a y) *
          k p q := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun p _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => enter [2, q]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun q _ => ?_
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [(Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy).2]
  have hk' := hk (fun p => ∑ x ∈ F.filter (fun x => η x = p), a x)
  beta_reduce at hk' ⊢
  rw [key]
  exact hk'


open Classical in
theorem top_unit_heads : Formalism.FourierDecayAlt.J.TopUnitHeads := by
  intro hAg hN0 K _ _ _ R ψ hLD E α _ m σ u τ₀ η F Θ hm hG hτ hA t
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => by
    have h1 := (hLD.selfDual 1).2 R.one_mem
    simpa using h1 r hr
  have h7 := hA.2.2.2.2.2.2 (by
      intro p hp
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hp
      exact hG h hh) ((u : K) * σ t - τ₀)
  have hmem : ((u : K) * σ t - τ₀ ∈ R) ↔ t ∈ (topSys R ψ σ u τ₀ η Θ).L := by
    show _ ↔ (u : K) * σ t ∈ R
    constructor
    · intro h
      simpa using R.add_mem h hτ
    · intro h
      exact R.sub_mem h hτ
  have hpull := isPSD_comp_of_isPSD_image F η _ h7
  have hF : A5.IsPSD F (fun h h' => (if t ∈ (topSys R ψ σ u τ₀ η Θ).L then (1 : ℂ) else 0) -
      (topSys R ψ σ u τ₀ η Θ).N t t h h') := by
    intro a
    have e : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((if t ∈ (topSys R ψ σ u τ₀ η Θ).L then (1 : ℂ) else 0) -
        (topSys R ψ σ u τ₀ η Θ).N t t x y) =
        ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((if (u : K) * σ t - τ₀ ∈ R then A5.N0 R ψ (η x) (η y) else 0) -
          Θ ((u : K) * σ t - τ₀) (η x) (η y)) := by
      refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
      have hN : (topSys R ψ σ u τ₀ η Θ).N t t x y = Θ ((u : K) * σ t - τ₀) (η x) (η y) := by
        simp [topSys]
      have h1 : A5.N0 R ψ (η x) (η y) = 1 :=
        hN0 K R ψ hψ (η x) (η y) ((hm x hx).trans (hm y hy).symm) (hG x hx) (hG y hy)
      simp only [hN, h1, hmem]
    have hp := hpull a
    beta_reduce at hp ⊢
    rw [e]
    exact hp
  exact ((hAg α F _).1.trans (hAg α F _).2.symm).2 hF

theorem diagonal_phase_conj : Formalism.FourierDecayAlt.J.DiagPhase := by
  classical
  intro α F k d hk
  unfold TB.PSDOn at hk ⊢
  have h := Matrix.PosSemidef.mul_mul_conjTranspose_same hk (Matrix.diagonal fun x : F => d x)
  convert h using 1
  ext x y
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_conjTranspose] <;> ring

theorem block_diagonal_psd : Formalism.FourierDecayAlt.J.BlockDiagPSD := by
  classical
  intro α β _ F c k hb
  unfold TB.PSDOn at hb ⊢
  let Fb : β → Finset α := fun b => F.filter fun x => c x = b
  let Q : ∀ b, Matrix F (Fb b) ℂ := fun b => Matrix.of fun x z => if (x : α) = (z : α) then 1 else 0
  have hQM : ∀ b (x : F) (w : Fb b),
      (Q b * Matrix.of (fun x y : Fb b => k x y)) x w = if c x = b then k x w else 0 := by
    intro b x w
    rw [Matrix.mul_apply]
    simp only [Q, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_coe_sort (Fb b) (fun z => if (x : α) = z then k z w else 0), Finset.sum_ite_eq]
    simp [Fb, x.2]
  have hA : ∀ b (x y : F), (Q b * Matrix.of (fun x y : Fb b => k x y) * Matrix.conjTranspose (Q b)) x y =
      if c x = b ∧ c y = b then k x y else 0 := by
    intro b x y
    rw [Matrix.mul_apply]
    simp only [hQM, Matrix.conjTranspose_apply, Q, Matrix.of_apply, apply_ite star, star_one, star_zero,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_coe_sort (Fb b) (fun w => if (y : α) = w then (if c x = b then k x w else 0) else 0),
      Finset.sum_ite_eq]
    by_cases hx : c x = b <;> by_cases hy : c y = b <;> simp [Fb, hx, hy, y.2]
  have hsum : (Matrix.of fun x y : F => if c x = c y then k x y else 0) =
      ∑ b ∈ F.image c, Q b * Matrix.of (fun x y : Fb b => k x y) * Matrix.conjTranspose (Q b) := by
    ext x y
    rw [Matrix.sum_apply]
    simp only [hA, Matrix.of_apply]
    rw [Finset.sum_eq_single (c x)]
    · by_cases h : c x = c y
      · simp [h]
      · simp [h, Ne.symm h]
    · intro b _ hb'
      simp [Ne.symm hb']
    · intro h
      exact absurd (Finset.mem_image_of_mem c x.2) h
  beta_reduce
  rw [hsum]
  exact Matrix.posSemidef_sum _ fun b _ => (hb b).mul_mul_conjTranspose_same (Q b)

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferMatrixFactorization
section
namespace Formalism.FourierDecayAlt.P.Wd5

open Matrix Formalism.FourierDecayAlt.Wd

section Free

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem eU_apply (a : S) (i j : Fin 2) (x y : Ix S) :
    (eU a i j : SlopeTestRemainingChoices S A) x y = if x a = i ∧ y = Function.update x a j then 1 else 0 := by
  have key : (x a = i ∧ y a = j ∧ ∀ b, b ≠ a → x b = y b) ↔ (x a = i ∧ y = Function.update x a j) := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, funext fun b => ?_⟩
      by_cases hb : b = a
      · subst hb
        simp [h2]
      · simp only [Function.update_apply, if_neg hb]
        exact (h3 b hb).symm
    · rintro ⟨h1, rfl⟩
      exact ⟨h1, by simp, fun b hb => by simp [Function.update_apply, hb]⟩
  simp only [eU, Matrix.of_apply, key]

theorem eU_mul_apply (a : S) (i j : Fin 2) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    ((eU a i j : SlopeTestRemainingChoices S A) * B) x y = if x a = i then B (Function.update x a j) y else 0 := by
  rw [Matrix.mul_apply]
  simp only [eU_apply]
  by_cases h : x a = i
  · simp [h, ite_mul, Finset.sum_ite_eq']
  · simp [h]

theorem eU_comm_of_ne {a c : S} (hc : c ≠ a) (i j k l : Fin 2) :
    Commute (eU c i j : SlopeTestRemainingChoices S A) (eU a k l) := by
  show (eU c i j : SlopeTestRemainingChoices S A) * eU a k l = eU a k l * eU c i j
  ext x y
  rw [eU_mul_apply, eU_mul_apply, eU_apply, eU_apply]
  have h1 : Function.update x c j a = x a := by simp [Function.update_apply, Ne.symm hc]
  have h2 : Function.update x a l c = x c := by simp [Function.update_apply, hc]
  have h3 : Function.update (Function.update x c j) a l = Function.update (Function.update x a l) c j :=
    Function.update_comm hc j l x
  rw [h1, h2, h3]
  by_cases hx : x c = i <;> by_cases hy : x a = k <;> simp [hx, hy]

theorem free_io (c : S) (x : A) : FreeOf c (io x : SlopeTestRemainingChoices S A) := by
  intro i j
  show (eU c i j : SlopeTestRemainingChoices S A) * io x = io x * eU c i j
  ext p q
  simp only [io, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, eU, Matrix.of_apply]
  split_ifs <;> simp

theorem free_one (c : S) : FreeOf c (1 : SlopeTestRemainingChoices S A) := fun i j => Commute.one_right _

theorem free_zero (c : S) : FreeOf c (0 : SlopeTestRemainingChoices S A) := fun i j => Commute.zero_right _

theorem free_mul {c : S} {b b' : SlopeTestRemainingChoices S A} (h : FreeOf c b) (h' : FreeOf c b') : FreeOf c (b * b') := fun i j => (h i j).mul_right (h' i j)

theorem free_sub {c : S} {b b' : SlopeTestRemainingChoices S A} (h : FreeOf c b) (h' : FreeOf c b') : FreeOf c (b - b') := fun i j => (h i j).sub_right (h' i j)

theorem free_smul {c : S} {b : SlopeTestRemainingChoices S A} (k : K) (h : FreeOf c b) : FreeOf c (k • b) := by
  intro i j
  show (eU c i j : SlopeTestRemainingChoices S A) * (k • b) = (k • b) * eU c i j
  rw [Matrix.mul_smul, Matrix.smul_mul, (h i j).eq]

theorem free_eU {a c : S} (hc : c ≠ a) (k l : Fin 2) : FreeOf c (eU a k l : SlopeTestRemainingChoices S A) := fun i j => eU_comm_of_ne hc i j k l

theorem freeOf2_mul {c : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) (hN : FreeOf2 c N) :
    FreeOf2 c (M * N) := by
  intro i j p q
  rw [Matrix.mul_apply]
  exact Commute.sum_right _ _ _ fun k _ => (hM i k p q).mul_right (hN k j p q)

theorem freeOf2_transpose {c : S} {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) : FreeOf2 c Mᵀ := fun i j => hM j i

theorem freeOf2_one (c : S) : FreeOf2 c (1 : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact free_one c
  · exact free_zero c

theorem freeOf2_rmatrix {a c : S} (hc : c ≠ a) (D : K) : FreeOf2 c (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  simp only [Rh0, Matrix.smul_apply, Matrix.sub_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc j i))

theorem freeOf2_rmatrix_transpose {a c : S} (hc : c ≠ a) (d : K) : FreeOf2 c (Rht0 a d : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  simp only [Rht0, Matrix.smul_apply, Matrix.sub_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc i j))

theorem free_ins {a c : S} (hc : c ≠ a) {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) :
    FreeOf c (ins a M) := by
  intro p q
  unfold ins
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
    (eU_comm_of_ne hc p q i j).mul_right (hM i j p q)

theorem freeOf2_lift (c : S) (M : M2 A) : FreeOf2 c (lift0 M : M2 (SlopeTestRemainingChoices S A)) := fun i j => free_io c (M i j)

theorem word_free (QQ : K → M2 A) (w : List (Letter K S)) (c : S)
    (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) : FreeOf c (RRw QQ w) ∧ ∀ Y, FreeOf2 c (TTw QQ w Y) := by
  induction w with
  | nil => exact ⟨free_one c, fun Y => freeOf2_lift c (QQ Y)⟩
  | cons l w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hc
    obtain ⟨hcl, hcw⟩ := hc
    obtain ⟨hR, hT⟩ := ih hcw
    have hT' : ∀ Y, FreeOf2 c (TTw QQ (l :: w) Y) := by
      intro Y
      simp only [TTw]
      split_ifs
      · exact freeOf2_mul (hT Y) (freeOf2_rmatrix hcl _)
      · exact freeOf2_mul (freeOf2_rmatrix_transpose hcl _) (hT Y)
    refine ⟨?_, hT'⟩
    simp only [RRw]
    apply free_mul hR
    apply free_ins hcl
    split_ifs
    · exact hT _
    · exact freeOf2_transpose (hT _)

end Free

theorem wordModule_of (hS : StartModule) (hP : LetterPlus) (hM : LetterMinus) (hF : WordFree) :
    WordModule := by
  intro K A S _ _ _ _ _ _ _ _ QQ q w hQ hw
  induction w with
  | nil =>
    have hset : {Y : K | Reg ([] : List (Letter K S)) Y} = Set.univ := by
      ext Y
      simp [Reg]
    rw [hset]
    exact hS K A S QQ q hQ
  | cons l w ih =>
    obtain ⟨hnd, hreal, hpw⟩ := hw
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hpw
    have hMod := ih ⟨hnd.2, fun l' hl' => hreal l' (List.mem_cons_of_mem _ hl'), hpw.2⟩
    obtain ⟨hFR, hFT⟩ := hF K A S QQ w l.intersection_update_fsHerm_neg_one hnd.1
    have hmem : l.pt ∈ {Y : K | Reg w Y} := fun l' hl' => hpw.1 l' hl'
    have hstar : star l.pt = l.pt := hreal l (by simp)
    cases hpl : l.plus
    · have key := hM K A S _ _ _ _ l.intersection_update_fsHerm_neg_one l.pt hMod hFR hFT hmem hstar
      convert key using 1
      all_goals first
        | (simp [RRw, hpl]; done)
        | (ext Y; simp [Reg, RegL, TTw, qw, hpl, and_comm]; done)
        | (funext Y; simp [TTw, qw, hpl])
    · have key := hP K A S _ _ _ _ l.intersection_update_fsHerm_neg_one l.pt hMod hFR hFT hmem hstar
      convert key using 1
      all_goals first
        | (simp [RRw, hpl]; done)
        | (ext Y; simp [Reg, RegL, TTw, qw, hpl, and_comm]; done)
        | (funext Y; simp [TTw, qw, hpl])

end Formalism.FourierDecayAlt.P.Wd5

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.Wd

theorem word_free_of_unused_positions : Formalism.FourierDecayAlt.Wd.WordFree := by
  intro K A S _ _ _ _ _ _ _ _ QQ w c hc
  exact Formalism.FourierDecayAlt.P.Wd5.word_free QQ w c hc

theorem word_module_structure : Formalism.FourierDecayAlt.Wd.WordModule := Formalism.FourierDecayAlt.P.Wd5.wordModule_of initial_module_structure letter_module_plus letter_module_minus
  word_free_of_unused_positions

end Formalism.FourierDecayAlt.P
end

