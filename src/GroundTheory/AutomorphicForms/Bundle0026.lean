module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0024
public import GroundTheory.AutomorphicForms.Bundle0025
public import GroundTheory.AutomorphicForms.MacdonaldNormalization

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.FiniteLengthLeviBlock
section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal Topology

section Smooth

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem isSmooth_comp_of_continuous {ρ : Representation ℂ H V} (hρ : IsSmooth ρ) (f : G →* H)
    (hf : Continuous f) : IsSmooth (ρ.comp f) := by
  intro v
  have : (stabilizerOf (ρ.comp f) v : Set G) = f ⁻¹' (stabilizerOf ρ v : Set H) := by
    ext g
    rfl
  rw [this]
  exact (hρ v).preimage hf

end Smooth

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Diagonal

theorem mem_center_levi_of_diagonal {γ : Fin n → ℕ} (x : levi F n γ) (d : Fin n → F)
    (hx : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal d)
    (hd : ∀ i j, γ i = γ j → d i = d j) : x ∈ Submonoid.center (levi F n γ) := by
  rw [Submonoid.mem_center_iff]
  intro m
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp only [Subgroup.coe_mul, Units.val_mul, hx, mul_diagonal, diagonal_mul]
  by_cases h : γ i = γ j
  · rw [hd i j h, mul_comm]
  · rw [mem_levi.1 m.2 i j h, zero_mul, mul_zero]

end Diagonal

section Block

variable {δ : Fin n → ℕ}


variable (F δ) in
def blockEmb (a : Set.range δ) : GL (Fin (blockSize δ a)) F →* levi F n δ :=
  (leviEquivPi F δ).symm.toMulEquiv.toMonoidHom.comp
    (MonoidHom.mulSingle (fun b : Set.range δ => GL (Fin (blockSize δ b)) F) a)

theorem leviEquivPi_blockEmb (a : Set.range δ) (y : GL (Fin (blockSize δ a)) F) :
    leviEquivPi F δ (blockEmb F δ a y) = Pi.mulSingle a y := by
  show leviEquivPi F δ ((leviEquivPi F δ).symm (Pi.mulSingle a y)) = _
  exact (leviEquivPi F δ).apply_symm_apply _

theorem continuous_blockEmb (a : Set.range δ) : Continuous (blockEmb F δ a) := by
  have h : Continuous fun y : GL (Fin (blockSize δ a)) F =>
      (Pi.mulSingle a y : ∀ b : Set.range δ, GL (Fin (blockSize δ b)) F) :=
    continuous_mulSingle (A := fun b : Set.range δ => GL (Fin (blockSize δ b)) F) a
  exact (leviEquivPi F δ).symm.continuous.comp h

theorem blockEmb_commute (a : Set.range δ) (y : GL (Fin (blockSize δ a)) F) (x : levi F n δ)
    (hx : leviEquivPi F δ x a = 1) : blockEmb F δ a y * x = x * blockEmb F δ a y := by
  apply (leviEquivPi F δ).injective
  rw [map_mul, map_mul, leviEquivPi_blockEmb]
  funext b
  by_cases hb : b = a
  · subst hb
    simp [hx]
  · simp [Pi.mulSingle_eq_of_ne hb]


variable (F δ) in
def blockRest (a : Set.range δ) (x : levi F n δ) : levi F n δ :=
  (leviEquivPi F δ).symm (Function.update (leviEquivPi F δ x) a 1)

theorem leviEquivPi_blockRest_self (a : Set.range δ) (x : levi F n δ) :
    leviEquivPi F δ (blockRest F δ a x) a = 1 := by
  simp [blockRest]

theorem blockEmb_mul_blockRest (a : Set.range δ) (x : levi F n δ) :
    blockEmb F δ a (leviEquivPi F δ x a) * blockRest F δ a x = x := by
  apply (leviEquivPi F δ).injective
  rw [map_mul, leviEquivPi_blockEmb]
  funext b
  by_cases hb : b = a
  · subst hb
    simp [blockRest]
  · simp [blockRest, Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]

theorem blockEmb_mem_center {a : Set.range δ} {z : GL (Fin (blockSize δ a)) F}
    (hz : z ∈ Subgroup.center (GL (Fin (blockSize δ a)) F)) :
    blockEmb F δ a z ∈ Subgroup.center (levi F n δ) := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply (leviEquivPi F δ).injective
  rw [map_mul, map_mul, leviEquivPi_blockEmb]
  funext b
  by_cases hb : b = a
  · subst hb
    simp only [Pi.mul_apply, Pi.mulSingle_eq_same]
    exact Subgroup.mem_center_iff.1 hz _
  · simp [Pi.mulSingle_eq_of_ne hb]

theorem coe_levi_apply_of_blockOf_eq (x : levi F n δ) {i j : Fin n}
    (hij : blockOf δ j = blockOf δ i) :
    ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      ((leviEquivPi F δ x (blockOf δ i) : GL (Fin (blockSize δ (blockOf δ i))) F) :
        Matrix _ _ F) ((fiberFin δ (blockOf δ i)).symm ⟨i, rfl⟩)
          ((fiberFin δ (blockOf δ i)).symm ⟨j, hij⟩) := by
  rw [leviEquivPi_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem mulSingle_scalar_apply {a : Set.range δ} {z : GL (Fin (blockSize δ a)) F} {s : F}
    (hz : ((z : GL (Fin (blockSize δ a)) F) : Matrix (Fin (blockSize δ a)) (Fin (blockSize δ a)) F) =
      Matrix.scalar (Fin (blockSize δ a)) s) (b : Set.range δ) (k l : Fin (blockSize δ b)) :
    ((Pi.mulSingle (M := fun b : Set.range δ => GL (Fin (blockSize δ b)) F) a z b :
      GL (Fin (blockSize δ b)) F) : Matrix (Fin (blockSize δ b)) (Fin (blockSize δ b)) F) k l =
      if k = l then (if b = a then s else 1) else 0 := by
  by_cases hb : b = a
  · subst hb
    rw [Pi.mulSingle_eq_same, hz, Matrix.scalar_apply, Matrix.diagonal_apply]
    simp
  · rw [Pi.mulSingle_eq_of_ne hb, Units.val_one, Matrix.one_apply]
    simp [hb]

theorem coe_blockEmb_apply_of_scalar {a : Set.range δ} {z : GL (Fin (blockSize δ a)) F} {s : F}
    (hz : ((z : GL (Fin (blockSize δ a)) F) : Matrix (Fin (blockSize δ a)) (Fin (blockSize δ a)) F) =
      Matrix.scalar (Fin (blockSize δ a)) s) :
    (((blockEmb F δ a z : levi F n δ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun i => if blockOf δ i = a then s else 1 := by
  ext i j
  by_cases hij : blockOf δ j = blockOf δ i
  · rw [coe_levi_apply_of_blockOf_eq _ hij, leviEquivPi_blockEmb, mulSingle_scalar_apply hz,
      diagonal_apply]
    have : ((fiberFin δ (blockOf δ i)).symm ⟨i, rfl⟩ =
        (fiberFin δ (blockOf δ i)).symm ⟨j, hij⟩) ↔ i = j := by
      rw [Equiv.apply_eq_iff_eq]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · rintro rfl
        rfl
    simp only [this]
  · have hne : i ≠ j := fun h => hij (h ▸ rfl)
    rw [diagonal_apply_ne _ hne]
    exact mem_levi.1 (blockEmb F δ a z).2 i j fun h => hij (Subtype.ext h.symm)

theorem blockEmb_mem_unipotentRadical {α' : Type*} [LinearOrder α'] (γ : Fin n → α')
    {a : Set.range δ} {y : GL (Fin (blockSize δ a)) F}
    (hy : y ∈ unipotentRadical F (blockSize δ a) (restrictFun δ γ a)) :
    ((blockEmb F δ a y : levi F n δ) : GL (Fin n) F) ∈ unipotentRadical F n γ := by
  rw [mem_unipotentRadical_iff_leviEquivPi, leviEquivPi_blockEmb]
  intro b
  by_cases hb : b = a
  · subst hb
    simpa using hy
  · rw [Pi.mulSingle_eq_of_ne hb]
    exact one_mem _

theorem eq_one_of_mem_unipotentRadical_const {m : ℕ} {c : ℕ} {g : GL (Fin m) F}
    (hg : g ∈ unipotentRadical F m (fun _ : Fin m => c)) : g = 1 := by
  obtain ⟨-, h⟩ := mem_unipotentRadical.1 hg
  exact Units.ext (Matrix.ext fun i j => h i j rfl)


variable (δ) in
def blockExtend (a : Set.range δ) (ε : Fin (blockSize δ a) → ℕ) : Fin n → ℕ := fun i =>
  if h : blockOf δ i = a then ε ((fiberFin δ a).symm ⟨i, h⟩) else 0

theorem restrictFun_blockExtend_self (a : Set.range δ) (ε : Fin (blockSize δ a) → ℕ) :
    restrictFun δ (blockExtend δ a ε) a = ε := by
  funext k
  simp only [restrictFun, blockExtend, dif_pos (fiberFin δ a k).2]
  congr 1
  rw [Equiv.symm_apply_eq]

theorem restrictFun_blockExtend_of_ne {a b : Set.range δ} (hb : b ≠ a)
    (ε : Fin (blockSize δ a) → ℕ) : restrictFun δ (blockExtend δ a ε) b = fun _ => 0 := by
  funext k
  simp only [restrictFun, blockExtend]
  rw [dite_eq_right]
  intro h
  exact hb ((fiberFin δ b k).2.symm.trans h)

theorem exists_split_blockExtend {a : Set.range δ} {ε : Fin (blockSize δ a) → ℕ}
    (hε : ∃ k l, ε k ≠ ε l) : ∃ i j, δ i = δ j ∧ blockExtend δ a ε i ≠ blockExtend δ a ε j := by
  obtain ⟨k, l, hkl⟩ := hε
  refine ⟨(fiberFin δ a k).1, (fiberFin δ a l).1, ?_, ?_⟩
  · exact congrArg Subtype.val ((fiberFin δ a k).2.trans (fiberFin δ a l).2.symm)
  · have hk := congrFun (restrictFun_blockExtend_self a ε) k
    have hl := congrFun (restrictFun_blockExtend_self a ε) l
    simp only [restrictFun] at hk hl
    rw [hk, hl]
    exact hkl

theorem exists_blockEmb_of_mem_unipotentRadical {a : Set.range δ} {ε : Fin (blockSize δ a) → ℕ}
    (u : levi F n δ) (hu : (u : GL (Fin n) F) ∈ unipotentRadical F n (blockExtend δ a ε)) :
    ∃ y ∈ unipotentRadical F (blockSize δ a) ε, blockEmb F δ a y = u := by
  rw [mem_unipotentRadical_iff_leviEquivPi] at hu
  have ha := hu a
  rw [restrictFun_blockExtend_self] at ha
  refine ⟨leviEquivPi F δ u a, ha, ?_⟩
  apply (leviEquivPi F δ).injective
  rw [leviEquivPi_blockEmb]
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · rw [Pi.mulSingle_eq_of_ne hb]
    have := hu b
    rw [restrictFun_blockExtend_of_ne hb] at this
    exact (eq_one_of_mem_unipotentRadical_const this).symm

end Block

end Parabolic

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.MacdonaldFormula
section
noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra Finset
open scoped ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem vPoly_ne_zero {t : ℂ} (ht : Function.Injective fun k : ℕ => t ^ k) (m : ℕ) :
    vPoly m t ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun k _ => div_ne_zero ?_ ?_
  · intro h
    have h' : t ^ (k + 1) = t ^ 0 := by rw [pow_zero]; exact (sub_eq_zero.1 h).symm
    have := ht h'
    omega
  · intro h
    have h' : t ^ 1 = t ^ 0 := by rw [pow_zero, pow_one]; exact (sub_eq_zero.1 h).symm
    have := ht h'
    omega

theorem injective_qInv_pow : Function.Injective fun k : ℕ => ((qF F : ℂ))⁻¹ ^ k := by
  have hq : 1 < qF F := Finite.one_lt_card
  have hpos : (0 : ℝ) < (qF F : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast qF_pos)
  have hne : (qF F : ℝ)⁻¹ ≠ 1 := by
    intro h
    rw [inv_eq_one] at h
    have : (1 : ℝ) < qF F := by exact_mod_cast hq
    linarith
  intro a b hab
  apply pow_right_injective₀ hpos hne
  apply Complex.ofReal_injective
  simp only at hab ⊢
  push_cast
  exact hab

theorem halfModulus_mul_recursion (Q : (Fin n → ℤ) → LaurentRing n)
    (hQ : ∀ r l, esymmL n r * Q l = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, Q (l + lamS S))
    (z : Fin n → ℂˣ) {r : ℕ} (hr : r ≤ n) (l : Fin n → ℤ) :
    sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * (halfModulus F l * evalAt z (Q l)) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        (kappa F S : ℂ) * (halfModulus F (l + lamS S) * evalAt z (Q (l + lamS S))) := by
  have h1 : evalAt z (esymmL n r) * evalAt z (Q l) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, evalAt z (Q (l + lamS S)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_mul, hQ, map_sum]
  calc _ = sqrtQ F ^ (r * (n - r)) * halfModulus F l * (evalAt z (esymmL n r) * evalAt z (Q l)) := by
        ring
    _ = _ := by
        rw [h1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [halfModulus_add, ← kappa_mul_halfModulus hr (Finset.mem_powersetCard.1 hS).2]
        ring

theorem rhoPair_add (a b : Fin n → ℤ) : rhoPair (a + b) = rhoPair a + rhoPair b := by
  simp only [rhoPair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem rhoPair_neg (a : Fin n → ℤ) : rhoPair (-a) = -rhoPair a := by
  simp only [rhoPair, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem rhoPair_comp_swap {μ : Fin n → ℤ} {i j : Fin n} (hij : (j : ℕ) = i + 1)
    (hμ : μ j = μ i + 1) : rhoPair (μ ∘ Equiv.swap i j) = rhoPair μ + 2 := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hs : μ ∘ Equiv.swap i j = μ + (Pi.single i 1 + -Pi.single j 1) := by
    funext x
    simp only [Function.comp_apply, Pi.add_apply, Pi.neg_apply, Pi.single_apply,
      Equiv.swap_apply_def]
    split_ifs <;> subst_vars <;> omega
  rw [hs, rhoPair_add, rhoPair_add, rhoPair_neg, rhoPair_single, rhoPair_single]
  push_cast [hij]
  ring

theorem halfModulus_hlR_swap (z : Fin n → ℂˣ) {μ : Fin n → ℤ} {i j : Fin n}
    (hij : (j : ℕ) = i + 1) (hμ : μ j = μ i + 1) :
    halfModulus F (μ ∘ Equiv.swap i j) * evalAt z (hlR ((qF F : ℂ))⁻¹ (μ ∘ Equiv.swap i j)) =
      halfModulus F μ * evalAt z (hlR ((qF F : ℂ))⁻¹ μ) := by
  rw [hlR_swap _ hij hμ, map_smul, smul_eq_mul, halfModulus_eq, halfModulus_eq,
    rhoPair_comp_swap hij hμ, neg_add, zpow_add₀ sqrtQ_ne_zero, ← sqrtQ_sq]
  rw [show (sqrtQ F) ^ (-2 : ℤ) = ((sqrtQ F) ^ 2)⁻¹ by rw [_root_.zpow_neg]; norm_cast]
  ring

theorem evalAt_esymmL_self_ne_zero (z : Fin n → ℂˣ) : evalAt z (esymmL n n) ≠ 0 := by
  have hp : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [evalAt_esymmL, hp, Finset.sum_singleton, monomialChar_apply]
  exact Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _

theorem schur_zero : schur (0 : Fin n → ℤ) = 1 := by
  refine altQuot_eq_of_mul ?_
  rw [mul_one, zero_add]
  rfl

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem macdonald_formula_hlR (z : Fin n → ℂˣ) {l : Fin n → ℤ} (hl : Antitone l) :
    vPoly n ((qF F : ℂ))⁻¹ * zonalSpherical μ z (torusPow F n l) =
      halfModulus F l * evalAt z (hlR ((qF F : ℂ))⁻¹ l) := by
  set t : ℂ := ((qF F : ℂ))⁻¹
  set f : (Fin n → ℤ) → ℂ := fun m =>
    vPoly n t * zonalSpherical μ z (torusPow F n m) - halfModulus F m * evalAt z (hlR t m) with hf
  have hswap : ∀ (m : Fin n → ℤ) (i j : Fin n), (j : ℕ) = i + 1 → m j = m i + 1 →
      f (m ∘ Equiv.swap i j) = f m := by
    intro m i j hij hm
    simp only [hf]
    rw [zonalSpherical_torusPow_comp, halfModulus_hlR_swap z hij hm]
  have key := eq_zero_of_recursion (fun S => (kappa F S : ℝ)) (fun S => by exact_mod_cast kappa_pos S)
    (fun r => sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r))
    (by
      rw [Nat.sub_self, mul_zero, pow_zero, one_mul]
      exact evalAt_esymmL_self_ne_zero z)
    f
    (by
      intro m hm r hr
      have h1 := zonalSpherical_recursion (μ := μ) z hm hr
      have h2 := halfModulus_mul_recursion (F := F) (hlR t) (fun r l => esymmL_mul_hlR t r l) z hr m
      simp only [hf, Complex.ofReal_natCast]
      calc _ = vPoly n t * (sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) *
              zonalSpherical μ z (torusPow F n m)) -
            sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) *
              (halfModulus F m * evalAt z (hlR t m)) := by ring
        _ = _ := by
          rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun S _ => by ring)
    (fun m hm S => Or.inr (by
      obtain ⟨σ, hσ, hfσ⟩ := exists_perm_antitone f hswap hm S
      exact ⟨σ, hσ, hfσ.symm⟩))
    (by
      simp only [hf, torusPow_zero, zonalSpherical_one, halfModulus_zero, one_mul, mul_one]
      rw [hlR_zero t injective_qInv_pow, AlgHom.commutes]
      simp)
  exact sub_eq_zero.1 (key l hl)

theorem casselman_shalika (ψ₀ : AddChar F ℂ) (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (hψ₁ : ∃ x : F, (GLnLocal.uniformizer F : F) * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) (z : Fin n → ℂˣ)
    {W : GL (Fin n) F → ℂ}
    (hWN : ∀ u ∈ unipotent F n, ∀ g, W (u * g) = Whittaker.psiN ψ₀ u * W g)
    (hWK : ∀ g, ∀ k ∈ integralGL F n, W (g * k) = W g)
    (heig : ∀ (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F),
      ∫ x, (h : HeckeAlgebra μ) x * W (g * x) ∂μ = evalAt z (satakeTransform μ h) * W g)
    (l : Fin n → ℤ) :
    W (torusPow F n l) = if Antitone l then W 1 * halfModulus F l * evalAt z (schur l) else 0 := by
  split_ifs with hl
  swap
  · exact eq_zero_of_not_antitone hψ₁ hWN hWK hl
  have hN : ∀ u ∈ unipotent F n ⊓ integralGL F n, ∀ g, W (u * g) = W g := by
    intro u hu g
    rw [hWN u hu.1, psiN_eq_one_of_mem hψ₀ hu, one_mul]
  set f : (Fin n → ℤ) → ℂ := fun m =>
    W (torusPow F n m) - W 1 * (halfModulus F m * evalAt z (schur m)) with hf
  have key := eq_zero_of_recursion (fun S => (kappa F S : ℝ)) (fun S => by exact_mod_cast kappa_pos S)
    (fun r => sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r))
    (by
      rw [Nat.sub_self, mul_zero, pow_zero, one_mul]
      exact evalAt_esymmL_self_ne_zero z)
    f
    (by
      intro m hm r hr
      have h1 := recursion_of_integral_eq (μ := μ) z hWK hN hm hr (heig _ _)
      have h2 := halfModulus_mul_recursion (F := F) schur (fun r l => esymmL_mul_schur r l) z hr m
      simp only [hf, Complex.ofReal_natCast]
      calc _ = sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * W (torusPow F n m) -
            W 1 * (sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) *
              (halfModulus F m * evalAt z (schur m))) := by ring
        _ = _ := by
          rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun S _ => by ring)
    (by
      intro m hm S
      by_cases hant : Antitone (m + lamS S)
      · exact Or.inr ⟨1, by simpa using hant, by simp⟩
      · left
        obtain ⟨i, j, hij, hmij, hiS, hjS⟩ := exists_ascent hm hant
        have hasc : (m + lamS S) j = (m + lamS S) i + 1 := by
          simp only [Pi.add_apply, lamS_apply, hiS, hjS, if_true, if_false, hmij]
          ring
        simp only [hf]
        rw [eq_zero_of_not_antitone hψ₁ hWN hWK hant, schur_eq_zero_of_ascent hij hasc, map_zero,
          mul_zero, mul_zero, sub_zero])
    (by simp only [hf, torusPow_zero, halfModulus_zero, schur_zero, map_one, mul_one, sub_self])
  have := key l hl
  simp only [hf] at this
  rw [mul_assoc]
  exact sub_eq_zero.1 this

end Spherical

end GroundTheory.Automorphic
end
end

