module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFgIsSeparated
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTypeLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SymSignature

theorem finite_hom (E : Type) [Field E] [NumberField E] (K : Type) [Field K] :
    Finite (𝓞 E →+* K) :=
  Finite.of_injective (fun τ : 𝓞 E →+* K => τ.toIntAlgHom) RingHom.toIntAlgHom_injective

theorem card_hom_le (E : Type) [Field E] [NumberField E] (K : Type) [Field K] :
    Nat.card (𝓞 E →+* K) ≤ Module.finrank ℚ E := by
  rw [← RingOfIntegers.rank E]
  exact (Nat.card_le_card_of_injective (fun τ : 𝓞 E →+* K => τ.toIntAlgHom)
    RingHom.toIntAlgHom_injective).trans (card_algHom_le_finrank ℤ (𝓞 E) K)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem root_ne_neg (H : Host E) {K : Type} [Field K] [CharZero K] {ρ : K}
    (hρ : ρ ^ 2 = -(H.d : K)) : -ρ ≠ ρ := by
  intro h
  have h0 : ρ = 0 := by linear_combination (-1 / 2 : K) * h
  rw [h0] at hρ
  have : (H.d : K) = 0 := by linear_combination hρ
  exact H.d_prime.ne_zero (by exact_mod_cast this)

theorem map_rt (H : Host E) {K : Type} [Field K] {ρ : K} (hρ : ρ ^ 2 = -(H.d : K))
    (τ : 𝓞 E →+* K) : τ H.rt = ρ ∨ τ H.rt = -ρ := by
  have := congrArg τ H.rt_sq
  rw [map_pow, map_neg, map_natCast, ← hρ] at this
  exact sq_eq_sq_iff_eq_or_eq_neg.mp this

theorem card_type_le (H : Host E) {K : Type} [Field K] [CharZero K] {ρ : K}
    (hρ : ρ ^ 2 = -(H.d : K)) :
    Nat.card {τ : 𝓞 E →+* K // τ H.rt = ρ} ≤ Module.finrank ℚ E / 2 := by
  haveI := finite_hom E K
  have hne := root_ne_neg H hρ
  let f : {τ : 𝓞 E →+* K // τ H.rt = ρ} ⊕ {τ : 𝓞 E →+* K // τ H.rt = ρ} → (𝓞 E →+* K) :=
    Sum.elim (fun τ => τ.1) (fun τ => τ.1.comp (H.bar : 𝓞 E →+* 𝓞 E))
  have hf : Function.Injective f := by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exfalso
      have := RingHom.congr_fun h H.rt
      simp [f, HostModel.bar_rt, a.2, b.2] at this
      exact hne this.symm
    · exfalso
      have := RingHom.congr_fun h H.rt
      simp [f, HostModel.bar_rt, a.2, b.2] at this
      exact hne this
    · refine congrArg Sum.inr (Subtype.ext (RingHom.ext fun x => ?_))
      have := RingHom.congr_fun h (H.bar x)
      simpa [f, HostModel.bar_bar] using this
  have h1 := (Nat.card_le_card_of_injective f hf).trans (card_hom_le E K)
  rw [Nat.card_sum] at h1
  omega

theorem finrank_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q g : ℕ) (K : Type) [Field K] [CharZero K] (ρ : K) (ty : Fin g → (𝓞 E →+* K)) (V : Submodule K (Matrix (Fin g) (Fin g) K)), ρ ^ 2 = -(H.d : K) → (∀ τ : 𝓞 E →+* K, (τ H.rt = ρ → Nat.card {i // ty i = τ} = p) ∧ (τ H.rt ≠ ρ → Nat.card {i // ty i = τ} = q)) → (∀ Θ ∈ V, Θ.IsSymm ∧ ∀ a : 𝓞 E, Matrix.diagonal (fun i => ty i a) * Θ = Θ * (Matrix.diagonal (fun i => ty i (H.bar a))).transpose) → Module.finrank K V ≤ Module.finrank ℚ E / 2 * p * q := by
  intro E _ _ _ H p q g K _ _ ρ ty V hρ hty hV
  classical
  haveI := finite_hom E K
  have hne := root_ne_neg H hρ
  let S : Type := Σ τ : {τ : 𝓞 E →+* K // τ H.rt = ρ},
    {i // ty i = τ.1} × {j // ty j = τ.1.comp (H.bar : 𝓞 E →+* 𝓞 E)}
  haveI : Fintype S := Fintype.ofFinite S
  haveI : Fintype {τ : 𝓞 E →+* K // τ H.rt = ρ} := Fintype.ofFinite _
  have hS : Nat.card S = Nat.card {τ : 𝓞 E →+* K // τ H.rt = ρ} * p * q := by
    rw [Nat.card_sigma, Finset.sum_congr rfl (g := fun _ => p * q)]
    · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, Nat.mul_assoc]
    · intro τ _
      rw [Nat.card_prod, (hty τ.1).1 τ.2, (hty _).2]
      simpa [HostModel.bar_rt, τ.2] using hne
  let f : V →ₗ[K] (S → K) :=
    { toFun := fun Θ s => Θ.1 s.2.1.1 s.2.2.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro Θ h0
    obtain ⟨hs, hc⟩ := hV Θ.1 Θ.2
    have key : ∀ i j, ty i H.rt = ρ → Θ.1 i j = 0 := by
      intro i j hi
      by_contra hij
      refine hij (congrFun h0 ⟨⟨ty i, hi⟩, ⟨i, rfl⟩, ⟨j, RingHom.ext fun a => ?_⟩⟩)
      have := congrFun (congrFun (hc (H.bar a)) i) j
      rw [Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal,
        HostModel.bar_bar, mul_comm] at this
      exact (mul_left_cancel₀ hij this).symm
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    show Θ.1 i j = 0
    rcases map_rt H hρ (ty i) with hi | hi
    · exact key i j hi
    · by_contra hij
      have := congrFun (congrFun (hc H.rt) i) j
      rw [Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal,
        HostModel.bar_rt, mul_comm, map_neg, hi] at this
      have hj : ty j H.rt = ρ := (neg_injective (mul_left_cancel₀ hij this)).symm
      exact hij ((hs.apply j i).trans (key j i hj))
  have h1 := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hS] at h1
  exact h1.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (card_type_le H hρ)))

end GlobalTheory.SymSignature
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CommutatorPairingE8SharpLevelPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpWeil

section Abstract
variable {G C : Type} [CommGroup G] [CommGroup C] {k : ℕ}

private theorem rel_one_one {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) : R 1 1 := by
  obtain ⟨c, hc, hu⟩ := hex 1 (one_pow k)
  have hcc : c * c = c := hu _ (by simpa using hmul 1 1 c c hc hc)
  have hc1 : c = 1 := by simpa using hcc
  rwa [hc1] at hc

private theorem rel_inv_of_rel {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {x : G} {c : C} (hx : x ^ k = 1)
    (h : R x c) : R x⁻¹ c⁻¹ := by
  obtain ⟨d, hd, -⟩ := hex x⁻¹ (by rw [inv_pow, hx, inv_one])
  have h1 : R 1 (c * d) := by simpa using hmul _ _ _ _ h hd
  obtain ⟨e, -, hu⟩ := hex 1 (one_pow k)
  have hcd : c * d = 1 := (hu _ h1).trans (hu _ (rel_one_one hex hmul)).symm
  rwa [eq_inv_of_mul_eq_one_right hcd] at hd

private theorem rel_pow_of_rel {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {x : G} {c : C} (h : R x c) (n : ℕ) :
    R (x ^ n) (c ^ n) := by
  induction n with
  | zero => simpa using rel_one_one hex hmul
  | succ n ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ ih h

private theorem rel_zpow_of_rel {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {x : G} {c : C} (hx : x ^ k = 1)
    (h : R x c) (n : ℤ) : R (x ^ n) (c ^ n) := by
  cases n with
  | ofNat n => simpa using rel_pow_of_rel hex hmul h n
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc]
    exact rel_inv_of_rel hex hmul (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]) (rel_pow_of_rel hex hmul h (n + 1))

theorem rel_prod {R : G → C → Prop} (hex : ∀ x, x ^ k = 1 → ∃! c, R x c)
    (hmul : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) {I : Type} (s : Finset I) (q : I → G) (c : I → C)
    (hq : ∀ i, q i ^ k = 1) (h : ∀ i, R (q i) (c i)) (a : I → ℤ) :
    R (∏ i ∈ s, q i ^ a i) (∏ i ∈ s, c i ^ a i) := by
  classical
  refine Finset.induction_on s (by simpa using rel_one_one hex hmul) ?_
  intro i s hi ih
  rw [Finset.prod_insert hi, Finset.prod_insert hi]
  exact hmul _ _ _ _ (rel_zpow_of_rel hex hmul (hq i) (h i) (a i)) ih

theorem prod_zpow_pow {I : Type} [Fintype I] (q : I → G) (hq : ∀ i, q i ^ k = 1) (a : I → ℤ) :
    (∏ i, q i ^ a i) ^ k = 1 := by
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm (a i), zpow_mul, zpow_natCast, hq i, one_zpow]

theorem zpow_sum' {I : Type} (s : Finset I) (ζ : C) (a : I → ℤ) : ζ ^ (∑ i ∈ s, a i) = ∏ i ∈ s, ζ ^ a i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem rel_biprod {R : G → G → C → Prop} (hex : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, R x y c)
    (hmul : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c'))
    (hsymm : ∀ x y c, R x y c → R y x c⁻¹) {I : Type} [Fintype I] (q : I → G) (ζ : C) (ω : I → I → ℤ)
    (hq : ∀ i, q i ^ k = 1) (h : ∀ i j, R (q i) (q j) (ζ ^ ω i j)) (a b : I → ℤ) :
    R (∏ i, q i ^ a i) (∏ i, q i ^ b i) (ζ ^ ∑ i, ∑ j, a i * b j * ω i j) := by
  have hy : (∏ j, q j ^ b j) ^ k = 1 := prod_zpow_pow q hq b
  have hrow : ∀ i, R (q i) (∏ j, q j ^ b j) (ζ ^ ∑ j, b j * ω i j) := by
    intro i
    have H : R (∏ j, q j ^ b j) (q i) (∏ j, ((ζ ^ ω i j)⁻¹) ^ b j) :=
      rel_prod (R := fun x c => R x (q i) c) (fun x hx => hex x (q i) hx (hq i))
        (fun x x' c c' h1 h2 => hmul x x' (q i) c c' h1 h2) Finset.univ q (fun j => (ζ ^ ω i j)⁻¹) hq
        (fun j => hsymm _ _ _ (h i j)) b
    have e : ζ ^ ∑ j, b j * ω i j = (∏ j, ((ζ ^ ω i j)⁻¹) ^ b j)⁻¹ := by
      rw [zpow_sum', ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [inv_zpow, inv_inv, ← zpow_mul, mul_comm (b j)]
    rw [e]
    exact hsymm _ _ _ H
  have H : R (∏ i, q i ^ a i) (∏ j, q j ^ b j) (∏ i, (ζ ^ ∑ j, b j * ω i j) ^ a i) :=
    rel_prod (R := fun x c => R x (∏ j, q j ^ b j) c) (fun x hx => hex x _ hx hy)
      (fun x x' c c' h1 h2 => hmul x x' _ c c' h1 h2) Finset.univ q (fun i => ζ ^ ∑ j, b j * ω i j) hq hrow a
  have e : ζ ^ ∑ i, ∑ j, a i * b j * ω i j = ∏ i, (ζ ^ ∑ j, b j * ω i j) ^ a i := by
    rw [zpow_sum']
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  exact H

end Abstract

theorem eq_sum_basis {n : ℕ} {M : Type} [AddCommGroup M] (bas : (Fin n → ℤ) ≃ₗ[ℤ] M) (X : M) :
    X = ∑ i, bas.symm X i • bas (Pi.single i 1) := by
  apply bas.symm.injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_zsmul, LinearEquiv.symm_apply_apply]
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

def omegaLin (h : ℕ) : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ omegaStd
    (fun a a' b => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)
    (fun a b b' => by simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)

theorem form_eq {h g : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} (hb : IsSharpBasis W bas)
    (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) :
    ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v) =
      ∑ i, ∑ j, bas.symm X i * bas.symm Y j * Out.stdSymp g i j := by
  have hω : ∀ a b : Fin h ⊕ Fin h → ℤ, omegaStd a b = omegaLin h a b := fun a b => by simp [omegaLin]
  have hX : ∀ u, X u = ∑ i, bas.symm X i • bas (Pi.single i 1) u := fun u => by
    conv_lhs => rw [eq_sum_basis bas X]
    simp [Finset.sum_apply]
  have hY : ∀ v, Y v = ∑ j, bas.symm Y j • bas (Pi.single j 1) v := fun v => by
    conv_lhs => rw [eq_sum_basis bas Y]
    simp [Finset.sum_apply]
  have hs : ∀ i j, Out.stdSymp g i j = ∑ u, ∑ v, (W + W.transpose) u v *
      omegaLin h (bas (Pi.single i 1) u) (bas (Pi.single j 1) v) := fun i j => by
    rw [← hb i j]; simp only [hω]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hs, hω, hX, hY, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine (Finset.sum_congr rfl fun u _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun i _ =>
    (Finset.sum_congr rfl fun u _ => Finset.sum_comm).trans Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

theorem pull_unitS {o K : Type} [CommRing o] [CommRing K] {S : Scheme.{0}} (s : S ⟶ Sp o) (p : Sp K ⟶ S)
    (β : o →+* K) (u : oˣ) (z : Kˣ) (hp : p ≫ s = spMap β) (hz : (z : K) = β u) :
    Units.map p.appTop.hom.toMonoidHom (unitS s u) = unitOn z := by
  apply Units.ext
  have hc := congrArg (fun f : Sp K ⟶ Sp o => f.appTop.hom (unitOn u).val) hp
  simp only [unitS, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.comp_apply] at hc ⊢
  rw [hc]
  unfold unitOn spMap Sp
  have hn := congrArg (fun φ => φ.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  simp only [Units.coe_map, hz]
  exact hn.symm

end GlobalTheory.SharpWeil

namespace GlobalTheory


open SharpWeil in
theorem weilIs_sharp_levelPoints : Out.Laws → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp o) (t : TObj g k J b s) (A : Over S) [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (t.A ⟶ A)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)), IsSharpBasis W bas → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left) → ∀ (K : Type) [Field K] (p : Sp K ⟶ S) (β : o →+* K) (z : Kˣ), p ≫ s = spMap β → (z : K) = β b.ζ → ∀ (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) (y y' : Over.mk p ⟶ t.A), (∀ u, y ≫ pr u = toUnit _ ≫ lev (X u)) → (∀ u, y' ≫ pr u = toUnit _ ≫ lev (Y u)) → Out.WeilIs t.A t.L k y y' (unitOn z ^ ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v)) := by
  intro hL h g W J bas k o _ b S _ s t A _ _ pr lev hb hpr huniv hlev hpt K _ p β z hps hz X Y y y' hy hy'
  have := t.ab.comm
  let e : Over.mk p ⟶ Out.baseOver S := Over.homMk p (by simp)
  let q : Fin (2 * g) → (Over.mk p ⟶ t.A) := fun i => e ≫ t.pt i
  obtain ⟨hex, hmul, -, -⟩ := hL.weil S t.pol k (Over.mk p)
  have hq : ∀ i, q i ^ k = 1 := fun i => by
    simp only [q]
    rw [← MonObj.comp_pow, t.torsion i, MonObj.comp_one]
  have hpair : ∀ i j, Out.WeilIs t.A t.L k (q i) (q j) (unitOn z ^ Out.stdSymp g i j) := fun i j => by
    have H := CommPairing.weilIs_pull hL.globalFns t.ab t.isLB e (t.pairing i j)
    have e1 : Units.map e.left.appTop.hom.toMonoidHom (unitS s b.ζ) = unitOn z := pull_unitS s p β b.ζ z hps hz
    rwa [map_zpow, e1] at H
  have htu : (toUnit (Over.mk p)).left = e.left :=
    congrArg Over.Hom.left (toUnit_unique (toUnit (Over.mk p)) (Over.homMk p (by simp) : Over.mk p ⟶ 𝟙_ (Over S)))
  have hqlev : ∀ i u, q i ≫ pr u = toUnit (Over.mk p) ≫ lev (bas (Pi.single i 1) u) := fun i u => by
    apply Over.OverMorphism.ext
    simp only [q]
    rw [Category.assoc, Over.comp_left, hpt i u, Over.comp_left, htu]
  let levHom : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (𝟙_ (Over S) ⟶ A) :=
    MonoidHom.mk' (fun a => lev a.toAdd) (fun a c => hlev _ _)
  let ψ : (𝟙_ (Over S) ⟶ A) →* (Over.mk p ⟶ A) :=
    MonoidHom.mk' (fun f => toUnit (Over.mk p) ≫ f) (fun f f' => MonObj.comp_mul _ f f')
  have hprod : ∀ (V : Fin 8 → Fin h ⊕ Fin h → ℤ) (w : Over.mk p ⟶ t.A),
      (∀ u, w ≫ pr u = toUnit (Over.mk p) ≫ lev (V u)) → w = ∏ i, q i ^ bas.symm V i := by
    intro V w hw
    obtain ⟨x0, -, hu⟩ := huniv (Over.mk p) (fun u => w ≫ pr u)
    refine (hu w fun u => rfl).trans (hu _ fun u => ?_).symm
    have := hpr u
    let φ : (Over.mk p ⟶ t.A) →* (Over.mk p ⟶ A) :=
      MonoidHom.mk' (fun x => x ≫ pr u) (fun a c => MonObj.mul_comp a c (pr u))
    have hV : V u = ∑ i, bas.symm V i • bas (Pi.single i 1) u := by
      conv_lhs => rw [eq_sum_basis bas V]
      simp [Finset.sum_apply]
    have h1 : (∏ i, q i ^ bas.symm V i) ≫ pr u = ∏ i, (q i ≫ pr u) ^ bas.symm V i := by
      change φ (∏ i, q i ^ bas.symm V i) = ∏ i, (φ (q i)) ^ bas.symm V i
      simp only [map_prod, map_zpow]
    have h2 : toUnit (Over.mk p) ≫ lev (V u) =
        ∏ i, (toUnit (Over.mk p) ≫ lev (bas (Pi.single i 1) u)) ^ bas.symm V i := by
      change ψ (levHom (Multiplicative.ofAdd (V u))) =
        ∏ i, (ψ (levHom (Multiplicative.ofAdd (bas (Pi.single i 1) u)))) ^ bas.symm V i
      rw [hV, ofAdd_sum]
      simp only [ofAdd_zsmul, map_prod, map_zpow]
    rw [h1, hw u, h2]
    exact Finset.prod_congr rfl fun i _ => by rw [hqlev i u]
  rw [form_eq hb X Y, hprod X y hy, hprod Y y' hy']
  exact rel_biprod (R := fun a c d => Out.WeilIs t.A t.L k a c d) (fun a c ha hc => hex a c ha hc)
    (fun a a' c d d' h1 h2 => hmul a a' c d d' h1 h2) (fun a c d H => CommPairing.weilIs_symm t.isLB H)
    q (unitOn z) (Out.stdSymp g) hq hpair (bas.symm X) (bas.symm Y)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseE8SharpAfterAdjoiningAllMatrices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpExt

variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}

theorem isMonHom_prod {G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj H] {I : Type} (T : Finset I)
    (f : I → (G ⟶ H)) (hf : ∀ i, IsMonHom (f i)) : IsMonHom (∏ i ∈ T, f i) :=
  Finset.prod_induction f (fun x => IsMonHom x) (fun x y _ _ => GlobalTheory.Serre.isMonHom_mul x y) GlobalTheory.Serre.isMonHom_one
    fun i _ => hf i

def matEnd (e : Fin 8 → Fin 8 → J) (t : TObj g k J b s) (m : Matrix (Fin 8) (Fin 8) ℤ) : t.A ⟶ t.A :=
  letI := t.ab.comm
  ∏ u, ∏ v, t.act (e u v) ^ m u v

theorem isMonHom_matEnd (e : Fin 8 → Fin 8 → J) (t : TObj g k J b s) (m : Matrix (Fin 8) (Fin 8) ℤ) :
    IsMonHom (matEnd e t m) :=
  letI := t.ab.comm
  isMonHom_prod _ _ fun u => isMonHom_prod _ _ fun v =>
    haveI := t.hom (e u v)
    GlobalTheory.Serre.isMonHom_zpow _ _

def ext (e : Fin 8 → Fin 8 → J) (t : TObj g k J b s) : TObj g k (J ⊕ Matrix (Fin 8) (Fin 8) ℤ) b s :=
  { t with
    act := Sum.elim t.act (matEnd e t)
    hom := fun j => match j with
      | .inl j => t.hom j
      | .inr m => isMonHom_matEnd e t m }

theorem tMap_ext (e : Fin 8 → Fin 8 → J) {t : TObj g k J b s} {t' : TObj g k J b s'} {f : S' ⟶ S}
    (H : TMap t' t f) : TMap (ext e t') (ext e t) f := by
  obtain ⟨φ, h, hL, hpt, hact⟩ := H
  refine ⟨φ, h, hL, hpt, ?_⟩
  rintro (j | m)
  · exact hact j
  · letI := t.ab.comm
    letI := t'.ab.comm
    let U : Over.mk (t'.A.hom ≫ f) ⟶ t.A := Over.homMk φ h.1.w
    have key : pushHom h t'.A (matEnd e t' m) = preHom (G := t.A) U (matEnd e t m) := by
      simp only [matEnd, map_prod, map_zpow]
      refine Finset.prod_congr rfl fun u _ => Finset.prod_congr rfl fun v _ => congrArg (· ^ m u v) ?_
      exact Over.OverMorphism.ext (hact _)
    exact congrArg (fun q => q.left) key

theorem isSharp_ext {h : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ} {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {e : Fin 8 → Fin 8 → J}
    (he : ∀ u v, a (e u v) = Matrix.single u v 1) {t : TObj g k J b s} {c : SiegPre h k (b.ζ : o) s}
    (H : IsSharp W a bas t c) : IsSharp W (Sum.elim a id) bas (ext e t) c := by
  obtain ⟨pr, hmon, huniv, hL, hmat, hpt⟩ := H
  refine ⟨pr, hmon, huniv, hL, ?_, hpt⟩
  have hpr : ∀ u v w, t.act (e u v) ≫ pr w = if w = u then pr v else 1 := by
    intro u v w
    rw [hmat, he, List.prod_ofFn]
    split_ifs with hw
    · subst hw
      rw [Finset.prod_eq_single v] <;> simp +contextual [Matrix.single_apply, eq_comm]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp [Ne.symm hw]
  rintro (j | m) w
  · exact hmat j w
  · letI := t.ab.comm
    haveI := hmon w
    let P : (t.A ⟶ t.A) →* (t.A ⟶ c.A) := MonoidHom.mk' (· ≫ pr w) fun x y => MonObj.mul_comp x y (pr w)
    have hP : ∀ x, P x = x ≫ pr w := fun _ => rfl
    have key : P (matEnd e t m) = (List.ofFn fun v => pr v ^ m w v).prod := by
      simp only [matEnd, map_prod, map_zpow]
      simp only [hP, hpr]
      rw [List.prod_ofFn, Finset.prod_eq_single w]
      · simp
      · intro u _ hu
        simp [Ne.symm hu]
      · simp
    exact key

end GlobalTheory.SharpExt

namespace GlobalTheory

open SharpExt

theorem exists_dense_sharp_all_matrices : ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s), (∀ u v, ∃ j, a j = Matrix.single u v 1) → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ t' : TObj g k (J ⊕ Matrix (Fin 8) (Fin 8) ℤ) b s, Dense (fromSet em (SharpClass (b := b) W (Sum.elim a id) bas em) t') ∧ ∀ c : SiegPre h k (b.ζ : o) s, IsSharp W (Sum.elim a id) bas t' c → IsSharp W a bas t c := by
  intro h g W J a bas k o _ b em S s t he hd
  choose e he using he
  refine ⟨SharpExt.ext e t, hd.mono ?_, ?_⟩
  · rintro p ⟨K, _, x, hp, K₀, _, β, i, j, t₀, tx, tc, h₁, h₂, h₃, h₄, h₅, c, hc, hs⟩
    exact ⟨K, _, x, hp, K₀, _, β, i, j, SharpExt.ext e t₀, SharpExt.ext e tx, SharpExt.ext e tc, h₁, h₂,
      tMap_ext e h₃, tMap_ext e h₄, tMap_ext e h₅, c, hc, isSharp_ext he hs⟩
  · rintro c ⟨pr, hmon, huniv, hL, hmat, hpt⟩
    exact ⟨pr, hmon, huniv, hL, fun j u => hmat (.inl j) u, hpt⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFgIsSeparatedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.exists_fg_subalgebra_isSeparated_pullback_snd : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k), LocallyOfFiniteType p → QuasiCompact p → IsSeparated (pullback.snd p (spMap (algebraMap k V))) → ∃ R : Subalgebra k V, R.FG ∧ IsSeparated (pullback.snd p (spMap (algebraMap k R))) := by
  first | exact @GlobalTheory.SpreadSep.exists_fg_isSeparated | exact GlobalTheory.SpreadSep.exists_fg_isSeparated | (intros; apply GlobalTheory.SpreadSep.exists_fg_isSeparated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSectionCoordinateVectorOfLocallyOnRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), M.IsLB → Ideal.span (Set.range v) = ⊤ → (∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) → SecCoord M th x v := by
  first | exact @GlobalTheory.ZM.secCoord_of_locally | exact GlobalTheory.ZM.secCoord_of_locally | (intros; apply GlobalTheory.ZM.secCoord_of_locally <;> assumption)
end

