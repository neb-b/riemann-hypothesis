module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0045

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntAlgebraMapInjectiveOfCharZero
section
open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr

theorem padicInt_algebraMap_injective_of_charZero {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O]
    [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] : Function.Injective (algebraMap ℤ_[l] O) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast] at hx
  have hu : IsUnit (algebraMap ℤ_[l] O (PadicInt.unitCoeff hx0 : ℤ_[l])) :=
    (PadicInt.unitCoeff hx0).isUnit.map _
  have hp : (l : O) ^ x.valuation = 0 := (mul_eq_zero.1 hx).resolve_left hu.ne_zero
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) (pow_eq_zero_iff'.1 hp).1

theorem exists_eq_X_pow_mul_of_ne_zero {O : Type} [CommRing O] {a : O⟦X⟧} (ha : a ≠ 0) :
    ∃ (m : ℕ) (w : O⟦X⟧), a = X ^ m * w ∧ constantCoeff w ≠ 0 := by
  refine ⟨a.order.toNat, a.divXPowOrder, X_pow_order_mul_divXPowOrder.symm, ?_⟩
  rw [constantCoeff_divXPowOrder]
  exact coeff_order ha

theorem X_pow_card_dvd_of_invariant {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [CharZero O] [Algebra ℤ_[l] O] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (a : O⟦X⟧)
    (h0 : constantCoeff a = 0) (ha : ∀ δ ∈ Δ, act O (δ : ℤ_[l]) a = a) :
    (X : O⟦X⟧) ^ Nat.card Δ ∣ a := by
  by_cases ha0 : a = 0
  · rw [ha0]
    exact dvd_zero _
  obtain ⟨m, w, rfl, hw⟩ := exists_eq_X_pow_mul_of_ne_zero ha0
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp only [pow_zero, one_mul] at h0
      exact absurd h0 hw
    · exact h
  have hpow : ∀ δ ∈ Δ, (δ : ℤ_[l]) ^ m = 1 := by
    intro δ hδ
    obtain ⟨v, hv, hv0⟩ := exists_act_X (O := O) (δ : ℤ_[l])
    have e := ha δ hδ
    rw [map_mul, map_pow, hv, mul_pow, mul_assoc] at e
    have e' := mul_left_cancel₀ (pow_ne_zero m X_ne_zero) e
    have e'' := congrArg constantCoeff e'
    rw [map_mul, map_pow, hv0, constantCoeff_act] at e''
    have h1 : (algebraMap ℤ_[l] O (δ : ℤ_[l])) ^ m = 1 := by
      have h2 : ((algebraMap ℤ_[l] O (δ : ℤ_[l])) ^ m - 1) * constantCoeff w = 0 := by
        rw [sub_mul, one_mul, e'', sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hw)
    apply padicInt_algebraMap_injective_of_charZero O
    rw [map_pow, h1, map_one]
  have hexp : Monoid.exponent Δ ∣ m := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
    apply Subtype.ext
    apply Units.ext
    simp [hpow g g.2]
  rw [IsCyclic.exponent_eq_card] at hexp
  exact (pow_dvd_pow X (Nat.le_of_dvd hm hexp)).trans (dvd_mul_right _ _)

theorem X_pow_dvd_mk_sub_sum {O : Type} [CommRing O] (c : ℕ → O) (N : ℕ) :
    (X : O⟦X⟧) ^ N ∣ PowerSeries.mk c - ∑ k ∈ Finset.range N, C (c k) * X ^ k := by
  rw [X_pow_dvd_iff]
  intro m hm
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, hm]

theorem injective_and_range_eq_invariants {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ]
    (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (hj : Associated (j X) (X ^ Nat.card Δ))
    (hinv : ∀ δ ∈ Δ, act O (δ : ℤ_[l]) (j X) = j X) :
    Function.Injective j ∧
      ∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ Δ, act O (δ : ℤ_[l]) a = a := by
  have hd : 0 < Nat.card Δ := Nat.card_pos
  obtain ⟨u, hu⟩ := hj
  have hjX0 : j X ≠ 0 := by
    intro h
    rw [h, zero_mul] at hu
    exact pow_ne_zero _ X_ne_zero hu.symm
  have hXj : (X : O⟦X⟧) ∣ j X := by
    have e : j X = X ^ Nat.card Δ * ((u⁻¹ : O⟦X⟧ˣ) : O⟦X⟧) := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [e]
    exact (dvd_pow_self (X : O⟦X⟧) hd.ne').mul_right _
  have hinj : Function.Injective j := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    obtain ⟨m, w, rfl, hw⟩ := exists_eq_X_pow_mul_of_ne_zero hb0
    rw [map_mul, map_pow] at hb
    rcases mul_eq_zero.1 hb with h | h
    · exact pow_ne_zero m hjX0 h
    · apply hw
      rw [← constantCoeff_algHom j hXj w, h, map_zero]
  have hact : ∀ δ ∈ Δ, (act O (δ : ℤ_[l])).comp j = j := fun δ hδ =>
    algHom_ext_X _ _ (by rw [AlgHom.comp_apply, hinv δ hδ]; exact hXj)
      (by rw [AlgHom.comp_apply, hinv δ hδ])
  have hstep : ∀ q : O⟦X⟧, (∀ δ ∈ Δ, act O (δ : ℤ_[l]) q = q) →
      ∃ q' : O⟦X⟧, (∀ δ ∈ Δ, act O (δ : ℤ_[l]) q' = q') ∧
        q = C (constantCoeff q) + j X * q' := by
    intro q hq
    have h0 : constantCoeff (q - C (constantCoeff q)) = 0 := by simp
    have hi : ∀ δ ∈ Δ, act O (δ : ℤ_[l]) (q - C (constantCoeff q)) = q - C (constantCoeff q) := by
      intro δ hδ
      rw [map_sub, hq δ hδ, act_C]
    obtain ⟨r, hr⟩ := X_pow_card_dvd_of_invariant Δ _ h0 hi
    have hq' : q - C (constantCoeff q) = j X * (↑u * r) := by rw [hr, ← mul_assoc, hu]
    refine ⟨↑u * r, fun δ hδ => ?_, by rw [← hq']; ring⟩
    apply mul_left_cancel₀ hjX0
    rw [← hq', ← hinv δ hδ, ← map_mul, ← hq', hi δ hδ]
  choose f hf1 hf2 using hstep
  refine ⟨hinj, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨b, rfl⟩ δ hδ
    exact DFunLike.congr_fun (hact δ hδ) b
  · intro ha
    let S := {q : O⟦X⟧ // ∀ δ ∈ Δ, act O (δ : ℤ_[l]) q = q}
    let nxt : S → S := fun q => ⟨f q.1 q.2, hf1 q.1 q.2⟩
    let sq : ℕ → S := fun n => nxt^[n] ⟨a, ha⟩
    let c : ℕ → O := fun k => constantCoeff (sq k).1
    have hexp : ∀ N, a = ∑ k ∈ Finset.range N, C (c k) * j X ^ k + j X ^ N * (sq N).1 := by
      intro N
      induction N with
      | zero => simp [sq]
      | succ N ih =>
        have e1 : (sq (N + 1)).1 = f (sq N).1 (sq N).2 := by
          simp only [sq, Function.iterate_succ_apply']
          rfl
        have e2 : (sq N).1 = C (c N) + j X * (sq (N + 1)).1 := by
          rw [e1]
          exact hf2 _ _
        calc a = ∑ k ∈ Finset.range N, C (c k) * j X ^ k + j X ^ N * (sq N).1 := ih
          _ = ∑ k ∈ Finset.range N, C (c k) * j X ^ k +
              j X ^ N * (C (c N) + j X * (sq (N + 1)).1) := by rw [← e2]
          _ = _ := by rw [Finset.sum_range_succ]; ring
    have hjsum : ∀ N, j (∑ k ∈ Finset.range N, C (c k) * X ^ k) =
        ∑ k ∈ Finset.range N, C (c k) * j X ^ k := by
      intro N
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, algHom_C]
    have hdvd : ∀ N, (X : O⟦X⟧) ^ N ∣ j (PowerSeries.mk c) - a := by
      intro N
      obtain ⟨r, hr⟩ := X_pow_dvd_mk_sub_sum c N
      have e3 : PowerSeries.mk c = ∑ k ∈ Finset.range N, C (c k) * X ^ k + X ^ N * r := by
        rw [← hr]
        ring
      have e4 : j (PowerSeries.mk c) - a = j X ^ N * (j r - (sq N).1) := by
        conv_lhs => rw [e3, map_add (f := _), map_mul, map_pow, hjsum, hexp N]
        ring
      rw [e4]
      exact (pow_dvd_pow_of_dvd hXj N).trans (dvd_mul_right _ _)
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    have h' := (X_pow_dvd_iff.1 (hdvd (n + 1))) n (Nat.lt_succ_self n)
    rw [map_sub, sub_eq_zero] at h'
    exact h'

end GlobalTheory.CycFr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamilyImageOfSurjective
section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Img

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W]
  [IsScalarTower k⟦X⟧ k⸨X⸩ W]

theorem map_sh (f : V →ₗ[k⸨X⸩] W) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    (sh a N).map (f.restrictScalars k⟦X⟧) = sh a (N.map (f.restrictScalars k⟦X⟧)) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact mem_sh_iff_exists.2 ⟨f y, ⟨y, hy, rfl⟩, (f.map_smul _ y).symm⟩
  · intro hx
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := mem_sh_iff_exists.1 hx
    exact ⟨_, mem_sh_iff_exists.2 ⟨y, hy, rfl⟩, f.map_smul _ y⟩

theorem isLat_map (f : V →ₗ[k⸨X⸩] W) (hf : Function.Surjective f) {N : Submodule k⟦X⟧ V} (h : IsLat N) :
    IsLat (N.map (f.restrictScalars k⟦X⟧)) := by
  refine ⟨h.1.map _, ?_⟩
  have : ((N.map (f.restrictScalars k⟦X⟧) : Submodule k⟦X⟧ W) : Set W) = f '' (N : Set V) := rfl
  rw [this, ← Submodule.map_span, h.2, Submodule.map_top, LinearMap.range_eq_top.2 hf]

theorem map_pull [Module k V] [Module k W] (f g : V →ₗ[k⸨X⸩] W) (φ : V →ₗ[k] V) (φ' : W →ₗ[k] W)
    (h : ∀ x, f (φ x) = φ' (g x)) (N : Submodule k⟦X⟧ V) :
    (pull φ N).map (f.restrictScalars k⟦X⟧) = pull φ' (N.map (g.restrictScalars k⟦X⟧)) := by
  rw [pull, pull, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ => h x

end

theorem image_lattice :
    ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l)
      {n : ℕ} [NeZero n]
      {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
      [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
      [FiniteDimensional k⸨X⸩ V]
      {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W]
      [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W]
      [FiniteDimensional k⸨X⸩ W] (D : ModPG R n V) (D' : ModPG R n W)
      (f : ZMod n → V →ₗ[k⸨X⸩] W),
      (∀ i, Function.Surjective (f i)) →
      (∀ i x, f i (D.φ i x) = D'.φ i (f (i - 1) x)) →
      (∀ i x, f i (D.γ i x) = D'.γ i (f i x)) →
      ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V),
        (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) →
        (let N' := fun i => (N i).map ((f i).restrictScalars k⟦X⟧)
         (∀ i, IsLat (N' i)) ∧ CondAB D'.φ w w' N' ∧ ∀ i, CondC (D'.γ i) (N' i)) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC N'
  refine ⟨fun i => isLat_map (f i) (hf i) (hN i), fun i => ?_, fun i => ?_⟩
  · simp only [N']
    rw [← map_pull (f i) (f (i - 1)) (D.φ i) (D'.φ i) (hφ i), ← map_sh, ← map_sh]
    exact ⟨Submodule.map_mono (hAB i).1, Submodule.map_mono (hAB i).2⟩
  · rintro _ ⟨x, hx, rfl⟩
    simp only [N']
    rw [← map_sh]
    refine ⟨_, hC i x hx, ?_⟩
    change f i _ = D'.γ i (f i x) - f i x
    rw [map_sub, hγ]

end GlobalTheory.PhiGam.Img
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexNeZeroOfBetween
section
open GlobalTheory.UnitLemma Polynomial
open scoped Pointwise

namespace GlobalTheory.UnitLemma.StabIndex

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

theorem smul_eq_mulLat (t : Aˣ) (L : Submodule O A) : t • L = mulLat O (t : A) L := by
  ext y
  simp [mulLat, Submodule.mem_smul_pointwise_iff_exists, Units.smul_def]

theorem mem_stabLat_iff (t : Aˣ) (L : Submodule O A) : t ∈ stabLat O L ↔ t • L = L := by
  have key : ∀ y, y ∈ t • L ↔ ((t⁻¹ : Aˣ) : A) * y ∈ L := by
    intro y
    rw [smul_eq_mulLat]
    simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [← mul_assoc, Units.inv_mul, one_mul]; exact hb
    · intro h
      exact ⟨_, h, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩
  constructor
  · intro ht
    ext y
    rw [key, ht (((t⁻¹ : Aˣ) : A) * y), ← mul_assoc, Units.mul_inv, one_mul]
  · intro ht y
    have := key ((t : A) * y)
    rw [ht, ← mul_assoc, Units.inv_mul, one_mul] at this
    exact this.symm

end GlobalTheory.UnitLemma.StabIndex

namespace GlobalTheory.UnitLemma.StabIndex

theorem isUnit_algebraMap (K : UQ) (B : InvAlg K) (c : K.O) (hc : c ≠ 0) :
    IsUnit (algebraMap K.O B.A c) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
  refine (isUnit_iff_ne_zero.mpr ?_).map (algebraMap K.E B.A)
  exact (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).mpr hc

theorem relIndex_ne_zero_of_between (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A) (c : K.O) (hc : c ≠ 0)
    (hfin : {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A (c * c)) L ≤ M ∧ M ≤ L}.Finite)
    (h : ∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) :
    (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  set G := intUnits K.O B.A ⊓ B.T
  set γ : B.Aˣ := (isUnit_algebraMap K B c hc).unit
  have hγ : (γ : B.A) = algebraMap K.O B.A c := rfl
  have hsub : (stabLat K.O L ⊓ B.T).subgroupOf G = MulAction.stabilizer G L := by
    ext u
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.mem_inf, Subgroup.smul_def,
      ← mem_stabLat_iff]
    exact ⟨fun hu => hu.1, fun hu => ⟨hu, (Subgroup.mem_inf.mp u.2).2⟩⟩
  have horb : (MulAction.orbit G L).Finite := by
    refine (hfin.preimage (MulAction.injective γ).injOn).subset ?_
    rintro _ ⟨u, rfl⟩
    have hu := (Subgroup.mem_inf.mp u.2).1
    have hM : γ • ((u : B.Aˣ) • L) = mulLat K.O (algebraMap K.O B.A c * ((u : B.Aˣ) : B.A)) L := by
      rw [smul_smul, smul_eq_mulLat, Units.val_mul, hγ]
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Subgroup.smul_def, hM]
    constructor
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨algebraMap K.O B.A c * (((u : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * y, h _ hu.2 y hy, ?_⟩
      simp only [LinearMap.mulLeft_apply, map_mul]
      calc algebraMap K.O B.A c * ((u : B.Aˣ) : B.A) * (algebraMap K.O B.A c * (((u : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * y)
          = algebraMap K.O B.A c * algebraMap K.O B.A c * (((u : B.Aˣ) : B.A) * (((u : B.Aˣ)⁻¹ : B.Aˣ) : B.A)) * y := by ring
        _ = _ := by rw [Units.mul_inv, mul_one]
    · rintro _ ⟨y, hy, rfl⟩
      simp only [LinearMap.mulLeft_apply]
      exact h _ hu.1 y hy
  rw [Subgroup.relIndex, hsub]
  haveI : Finite (MulAction.orbit G L) := horb.to_subtype
  haveI : Finite (G ⧸ MulAction.stabilizer G L) := Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G L)
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.UnitLemma.StabIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexStandardLatticeTransposeInvDvr
section
noncomputable section

open Matrix

namespace GlobalTheory.IndexTranspose

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ}

abbrev stdLat (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ) : Submodule O (Fin r → K) :=
  Submodule.span O (Set.range (Pi.basisFun K (Fin r)))

theorem mem_stdLat {v : Fin r → K} :
    v ∈ stdLat O K r ↔ ∃ w : Fin r → O, v = fun i => algebraMap O K (w i) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, funext fun i => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · rintro ⟨w, rfl⟩
    refine ⟨w, funext fun i => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]

def latOf (O : Type) [CommRing O] [Algebra O K] (A : Matrix (Fin r) (Fin r) K) : Submodule O (Fin r → K) :=
  (stdLat O K r).map ((A.mulVecLin).restrictScalars O)

theorem mem_latOf {A : Matrix (Fin r) (Fin r) K} {v : Fin r → K} :
    v ∈ latOf O A ↔ ∃ w ∈ stdLat O K r, A *ᵥ w = v := by
  simp [latOf, Submodule.mem_map]

theorem latOf_mul (A B : Matrix (Fin r) (Fin r) K) :
    latOf O (A * B) = (latOf O B).map ((A.mulVecLin).restrictScalars O) := by
  ext v
  rw [Submodule.mem_map, mem_latOf]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨B *ᵥ w, mem_latOf.2 ⟨w, hw, rfl⟩, by simp [Matrix.mulVec_mulVec]⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨w, hw, rfl⟩ := mem_latOf.1 hu
    exact ⟨w, hw, by simp [Matrix.mulVec_mulVec]⟩

theorem latOf_one : latOf O (1 : Matrix (Fin r) (Fin r) K) = stdLat O K r := by
  ext v
  rw [mem_latOf]
  simp

theorem map_mulVec_mem (N : Matrix (Fin r) (Fin r) O) {v : Fin r → K} (hv : v ∈ stdLat O K r) :
    (N.map (algebraMap O K)) *ᵥ v ∈ stdLat O K r := by
  obtain ⟨w, rfl⟩ := mem_stdLat.1 hv
  refine mem_stdLat.2 ⟨N *ᵥ w, funext fun i => ?_⟩
  exact (RingHom.map_mulVec (algebraMap O K) N w i).symm

theorem latOf_unimod (N : Matrix (Fin r) (Fin r) O) (hN : IsUnit N.det) :
    latOf O (N.map (algebraMap O K)) = stdLat O K r := by
  apply le_antisymm
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latOf.1 hv
    exact map_mulVec_mem N hw
  · intro v hv
    refine mem_latOf.2 ⟨(N⁻¹).map (algebraMap O K) *ᵥ v, map_mulVec_mem _ hv, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hN,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

theorem det_map_ne_zero (N : Matrix (Fin r) (Fin r) O) (hN : IsUnit N.det) :
    (N.map (algebraMap O K)).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (hN.map _).ne_zero

theorem toAddSubgroup_map (A : Matrix (Fin r) (Fin r) K) (p : Submodule O (Fin r → K)) :
    (p.map ((A.mulVecLin).restrictScalars O)).toAddSubgroup =
      p.toAddSubgroup.map A.mulVecLin.toAddMonoidHom := by
  ext v
  simp [Submodule.mem_map, AddSubgroup.mem_map]

def idx (O : Type) [CommRing O] [Algebra O K] (A : Matrix (Fin r) (Fin r) K) : ℕ :=
  (latOf O A).toAddSubgroup.relIndex (stdLat O K r).toAddSubgroup

theorem idx_mul_right (A U : Matrix (Fin r) (Fin r) K) (hU : latOf O U = stdLat O K r) :
    idx O (A * U) = idx O A := by
  unfold idx
  rw [latOf_mul, hU]
  rfl

theorem idx_mul_left (U A : Matrix (Fin r) (Fin r) K) (hU : latOf O U = stdLat O K r) (hd : U.det ≠ 0) :
    idx O (U * A) = idx O A := by
  have hinj : Function.Injective U.mulVecLin.toAddMonoidHom :=
    fun a b hab => Matrix.mulVec_injective_of_det_ne_zero hd hab
  have e : (stdLat O K r).toAddSubgroup = (stdLat O K r).toAddSubgroup.map U.mulVecLin.toAddMonoidHom := by
    rw [← toAddSubgroup_map]
    exact congrArg Submodule.toAddSubgroup hU.symm
  unfold idx
  rw [latOf_mul, toAddSubgroup_map]
  conv_lhs => rw [e]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj

theorem idx_transpose [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K]
    (g : Matrix (Fin r) (Fin r) K) (hg : g.det ≠ 0) : idx O gᵀ = idx O g := by
  classical
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin r × Fin r)) (fun ij => g ij.1 ij.2)
  have hc' := fun ij : Fin r × Fin r => RingHom.mem_rangeS.1 (hc ij (Finset.mem_univ ij))
  choose N0 hN0 using hc'
  set a : K := algebraMap O K (c : O) with ha_def
  have ha : a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors c.2
  let N : Matrix (Fin r) (Fin r) O := Matrix.of fun i j => N0 (i, j)
  have hNmap : N.map (algebraMap O K) = a • g := by
    ext i j
    simp only [N, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, hN0 (i, j), ha_def, smul_eq_mul, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
  have hNdet : N.det ≠ 0 := by
    intro h0
    have e := RingHom.map_det (algebraMap O K) N
    rw [h0, map_zero, RingHom.mapMatrix_apply, hNmap, Matrix.det_smul] at e
    exact mul_ne_zero (pow_ne_zero _ ha) hg e.symm
  obtain ⟨P, Q, hP, hQ, d, hPQ⟩ := GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal N hNdet
  set D : Matrix (Fin r) (Fin r) K := a⁻¹ • Matrix.diagonal (fun i => algebraMap O K (d i)) with hD
  have hmap := congrArg (fun M : Matrix (Fin r) (Fin r) O => M.map (algebraMap O K)) hPQ
  simp only [Matrix.map_mul, hNmap, Matrix.diagonal_map (map_zero _)] at hmap
  have key : g * Q.map (algebraMap O K) = P.map (algebraMap O K) * D := by
    rw [hD, Matrix.mul_smul, ← hmap, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hDT : Dᵀ = D := by
    rw [hD, Matrix.transpose_smul, Matrix.diagonal_transpose]
  have hQT : IsUnit Qᵀ.det := by rwa [Matrix.det_transpose]
  have hPT : IsUnit Pᵀ.det := by rwa [Matrix.det_transpose]
  have e1 : idx O g = idx O D := by
    rw [← idx_mul_right g _ (latOf_unimod Q hQ), key,
      idx_mul_left _ _ (latOf_unimod P hP) (det_map_ne_zero P hP)]
  have e2 : idx O gᵀ = idx O D := by
    have hQ' := latOf_unimod (K := K) Qᵀ hQT
    rw [Matrix.transpose_map] at hQ'
    have hP' := latOf_unimod (K := K) Pᵀ hPT
    rw [Matrix.transpose_map] at hP'
    have hQd := det_map_ne_zero (K := K) Qᵀ hQT
    rw [Matrix.transpose_map] at hQd
    rw [← idx_mul_left _ gᵀ hQ' hQd, ← Matrix.transpose_mul, key, Matrix.transpose_mul, hDT,
      idx_mul_right _ _ hP']
  rw [e1, e2]

theorem relIndex_transpose_inv : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (h : GL (Fin r) K), ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map ((((h⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ.mulVecLin).restrictScalars O)).toAddSubgroup.relIndex (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup.relIndex ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup := by
  intro O K _ _ _ _ _ _ _ r h
  set g : Matrix (Fin r) (Fin r) K := ((h⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) with hg_def
  set hM : Matrix (Fin r) (Fin r) K := (h : Matrix (Fin r) (Fin r) K) with hM_def
  have hgh : g * hM = 1 := Units.inv_mul h
  have hg : g.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hgh
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at e
    exact zero_ne_one e
  have hginj : Function.Injective g.mulVecLin.toAddMonoidHom :=
    fun a b hab => Matrix.mulVec_injective_of_det_ne_zero hg hab
  change idx O gᵀ = (stdLat O K r).toAddSubgroup.relIndex (latOf O hM).toAddSubgroup
  have e1 : (latOf O g).toAddSubgroup = (stdLat O K r).toAddSubgroup.map g.mulVecLin.toAddMonoidHom :=
    toAddSubgroup_map g _
  have e2 : (stdLat O K r).toAddSubgroup = (latOf O hM).toAddSubgroup.map g.mulVecLin.toAddMonoidHom := by
    rw [← toAddSubgroup_map, ← latOf_mul, hgh, latOf_one]
  rw [idx_transpose g hg, ← AddSubgroup.relIndex_map_map_of_injective _ _ hginj, ← e1, ← e2]
  rfl

end GlobalTheory.IndexTranspose
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldTsumIntegralFundamentalDomainStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfold_tsum_integral_fundamentalDomain : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → ∀ (a b P : G → ℂ), Continuous a → Continuous b →
    (∀ γ ∈ Γ, ∀ g, b (γ * g) = b g) → StronglyMeasurable P →
    ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : Γ, ‖P (g₁⁻¹ * (γ : G)⁻¹ * g₂)‖ₑ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤ →
    Integrable (fun g => P g * ∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ν ∧
    ∑' γ : Γ, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * P (p.1⁻¹ * (γ : G)⁻¹ * p.2) ∂(ν.prod ν) =
      ∫ g, P g * (∫ x in 𝓖, star (a x) * b (x * g) ∂ν) ∂ν := by
  first | exact @GlobalTheory.unfold_tsum_fundamentalDomain | exact GlobalTheory.unfold_tsum_fundamentalDomain | (intros; apply GlobalTheory.unfold_tsum_fundamentalDomain <;> assumption)
end

