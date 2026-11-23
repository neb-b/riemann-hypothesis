module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.AsymExp
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem cf_sum_smul {n : ℕ} (s : Finset (Wt n)) (c : Wt n → ℂ) (g : Wt n → FR n) (y : Wt n) :
    cf (∑ x ∈ s, c x • g x) y = ∑ x ∈ s, c x * cf (g x) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cf]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ((cfBasic n).2.2.2.1 _ _ (c a) y).1,
      ((cfBasic n).2.2.2.1 (g a) 0 (c a) y).2, ih]

private theorem asym_eq_of_strictAnti {n : ℕ} {f g : FR n} (hf : ASym f) (hg : ASym g)
    (h : ∀ y : Wt n, StrictAnti y → cf f y = cf g y) (y : Wt n) : cf f y = cf g y := by
  by_cases hy : Function.Injective y
  · obtain ⟨w, hw⟩ := ((rearr n).2.1 y).2.1
    have ha : Antitone (y ∘ ⇑w) := hw ▸ ((rearr n).2.1 y).1
    have hs : StrictAnti (y ∘ ⇑w) := ha.strictAnti_of_injective (hy.comp w.injective)
    have e := h _ hs
    rw [hf w y, hg w y] at e
    have hne : sg w ≠ 0 := by
      unfold sg
      rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h1 | h1 <;> simp [h1]
    exact mul_left_cancel₀ hne e
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hy
    have hfix : y ∘ ⇑(Equiv.swap a b) = y := by
      funext i
      simp only [Function.comp_apply, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · subst h1; exact hab.symm
      · subst h2; exact hab
      · rfl
    have hsg : sg (Equiv.swap a b) = -1 := by
      simp [sg, Equiv.Perm.sign_swap hne]
    have e1 := hf (Equiv.swap a b) y
    have e2 := hg (Equiv.swap a b) y
    rw [hfix, hsg] at e1 e2
    have z1 : cf f y = 0 := by linear_combination e1 / 2
    have z2 : cf g y = 0 := by linear_combination e2 / 2
    rw [z1, z2]

theorem UpperTheory.RealTr.asymExp :
    ∀ (n : ℕ) (f : FR n), ASym f → ∃ s : Finset (Wt n), (∀ x ∈ s, StrictAnti x ∧ cf f x ≠ 0) ∧ f = ∑ x ∈ s, cf f x • alt x := by
  intro n f hf
  classical
  set s := f.coeff.support.filter (fun x => StrictAnti x) with hs
  have hmem : ∀ x, x ∈ s ↔ cf f x ≠ 0 ∧ StrictAnti x := by
    intro x
    simp [hs, cf, Finsupp.mem_support_iff]
  refine ⟨s, fun x hx => ⟨((hmem x).1 hx).2, ((hmem x).1 hx).1⟩, ?_⟩
  have hR : ASym (∑ x ∈ s, cf f x • alt x) := by
    intro w z
    rw [cf_sum_smul, cf_sum_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [(cfBasic n).2.2.2.2.2.2.2.2.1 x w z]
    ring
  apply (cfBasic n).2.2.1
  intro y
  apply asym_eq_of_strictAnti hf hR
  intro y hy
  rw [cf_sum_smul, Finset.sum_eq_single y, ((cfBasic n).2.2.2.2.2.2.2.2.2.2.2.1 y hy).1, mul_one]
  · intro x hx hxy
    rw [((cfBasic n).2.2.2.2.2.2.2.2.2.2.2.1 x ((hmem x).1 hx).2).2 y hy (Ne.symm hxy), mul_zero]
  · intro hy'
    have : cf f y = 0 := by
      by_contra hc
      exact hy' ((hmem y).2 ⟨hc, hy⟩)
    rw [this, zero_mul]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfMulSum
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private def tenPiS {J V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : J → Submodule ℂ V) : Submodule ℂ (Ten J V) where
  carrier := {x | ∀ j, x j ∈ T j}
  add_mem' {x y} hx hy j := by simpa using (T j).add_mem (hx j) (hy j)
  zero_mem' j := by simp
  smul_mem' c x hx j := by simpa using (T j).smul_mem c (hx j)

private def tenPiE {J V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : J → Submodule ℂ V) : tenPiS T ≃ₗ[ℂ] Π j, T j where
  toFun x j := ⟨x.1 j, x.2 j⟩
  invFun y := ⟨WithLp.toLp 2 fun j => (y j).1, fun j => (y j).2⟩
  map_add' x y := by ext j; simp
  map_smul' c x := by ext j; simp
  left_inv x := by ext j; simp
  right_inv y := by ext j; simp

private theorem cf_mul_sum {n : ℕ} {J : Type} (c₀ : FR n) (η : J → Wt n) (s : Finset J) (μ : Wt n) :
    cf (c₀ * ∑ j ∈ s, ex (η j)) μ = ∑ j ∈ s, cf c₀ (μ - η j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cf]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, mul_add, ((cfBasic n).2.2.2.1 _ _ 1 μ).1, ih,
      mul_comm c₀ (ex (η j)), (cfBasic n).2.2.2.2.1]

theorem UpperTheory.RealTr.tenCh :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ (J : Type) [Fintype J] [DecidableEq J] (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n), ClifMod c η → ∀ c₀, IsCh F S 1 c₀ → ∃ S' : Submodule ℂ (Ten J V), FiniteDimensional ℂ S' ∧ Stb (dg F c) S' ∧ IsCh (dg F c) S' 1 (c₀ * ∑ j, ex (η j)) := by
  intro n V _ _ F hF S hS hSt J _ _ c η hc c₀ hch
  refine ⟨tenPiS (fun _ => S), ?_, ?_, ?_⟩
  · exact Module.Finite.equiv (tenPiE (fun _ : J => S)).symm
  · intro a b x hx j
    have h : (dg F c a b x) j = F a b (x j) + ∑ k, spn c a b j k • x k := rfl
    rw [h]
    exact S.add_mem (hSt a b _ (hx j)) (S.sum_mem fun k _ => S.smul_mem _ (hx k))
  · intro μ
    have hdiag : ∀ (x : Ten J V) a j, (dg F c a a x) j = F a a (x j) + (η j a : ℂ) • x j := by
      intro x a j
      have h : (dg F c a a x) j = F a a (x j) + ∑ k, spn c a a j k • x k := rfl
      rw [h, hc.diag a]
      simp [Matrix.diagonal_apply]
    have hset : wsp (dg F c) μ ⊓ tenPiS (fun _ => S) = tenPiS (fun j => wsp F (μ - η j) ⊓ S) := by
      ext x
      constructor
      · rintro ⟨hw, hx⟩ j
        refine ⟨fun a => ?_, hx j⟩
        have h1 : (dg F c a a x) j = (μ a : ℂ) • x j := by
          have := congrArg (fun y : Ten J V => y j) (hw a)
          simpa using this
        rw [hdiag] at h1
        have h2 : F a a (x j) = (μ a : ℂ) • x j - (η j a : ℂ) • x j := eq_sub_of_add_eq h1
        rw [h2, ← sub_smul]
        simp
      · intro hx
        refine ⟨fun a => ?_, fun j => (hx j).2⟩
        ext j
        have h1 : F a a (x j) = (((μ - η j) a : ℝ) : ℂ) • x j := (hx j).1 a
        rw [hdiag, h1, ← add_smul]
        simp
    have hfin : ∀ j, FiniteDimensional ℂ ↥(wsp F (μ - η j) ⊓ S) :=
      fun j => Submodule.finiteDimensional_inf_right _ _
    have hfin' : FiniteDimensional ℂ ↥(tenPiS fun j => wsp F (μ - η j) ⊓ S) :=
      Module.Finite.equiv (tenPiE _).symm
    rw [hset, (trAdd (Ten J V) 1).2.2.2 _ hfin', LinearEquiv.finrank_eq (tenPiE _),
      Module.finrank_pi_fintype, cf_mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hch, (trAdd V 1).2.2.2 _ (hfin j)]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DivSupp
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem character_support_pairing_le_of_strict_anti {n : ℕ} (κ : Wt n) (χ : FR n) (hκ : Antitone κ)
    (h : alt (rhoV n) * χ = alt (κ + rhoV n)) (x : Wt n) (hx : StrictAnti x) (ξ : Wt n)
    (hξ : cf χ ξ ≠ 0) : ∑ a, x a * ξ a ≤ ∑ a, x a * κ a := by
  classical
  have hρ : StrictAnti (rhoV n) := (rearr n).2.2.1
  have hsupp : ∀ v, cf χ v ≠ 0 ↔ v ∈ χ.coeff.support := by
    intro v
    simp [cf, Finsupp.mem_support_iff]
  obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image χ.coeff.support
    (fun v => ∑ a, x a * v a) ⟨ξ, (hsupp ξ).1 hξ⟩
  have hμ' : cf χ μ ≠ 0 := (hsupp μ).2 hμ
  have hcoef : cf (alt (rhoV n) * χ) (rhoV n + μ) = cf χ μ := by
    rw [(cfBasic n).2.2.2.2.2.2.1, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · have e : rhoV n + μ - rhoV n ∘ ⇑(1 : Equiv.Perm (Fin n)) = μ := by
        funext a
        simp
      rw [e]
      simp [sg]
    · intro w _ hw
      have hz : cf χ (rhoV n + μ - rhoV n ∘ ⇑w) = 0 := by
        by_contra hc
        have h1 := hmax _ ((hsupp _).1 hc)
        have h2 := (rearr n).1 x (rhoV n) hx.antitone hρ.antitone w
        simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, mul_sub, mul_add,
          Finset.sum_add_distrib, Finset.sum_sub_distrib] at h1
        exact hw (h2.2 hx hρ (by linarith [h2.1]))
      rw [hz, mul_zero]
    · intro h1
      exact absurd (Finset.mem_univ _) h1
  rw [h] at hcoef
  obtain ⟨w, hw⟩ := (cfBasic n).2.2.2.2.2.2.2.2.2.2.1 (κ + rhoV n) (rhoV n + μ)
    (by rw [hcoef]; exact hμ')
  have hanti : Antitone (κ + rhoV n) := hκ.add hρ.antitone
  have h2 := ((rearr n).1 x (κ + rhoV n) hx.antitone hanti w).1
  have e : ∑ a, x a * (rhoV n + μ) a = ∑ a, x a * (κ + rhoV n) (w a) := by
    rw [hw]
    rfl
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] at e h2
  have h4 : ∑ a, x a * ξ a ≤ ∑ a, x a * μ a := hmax ξ ((hsupp ξ).1 hξ)
  linarith

private theorem character_support_pairing_le_of_antitone {n : ℕ} (κ : Wt n) (χ : FR n) (hκ : Antitone κ)
    (h : alt (rhoV n) * χ = alt (κ + rhoV n)) (x : Wt n) (hx : Antitone x) (ξ : Wt n)
    (hξ : cf χ ξ ≠ 0) : ∑ a, x a * ξ a ≤ ∑ a, x a * κ a := by
  have hρ : StrictAnti (rhoV n) := (rearr n).2.2.1
  have key : ∀ ε : ℝ, 0 < ε →
      ∑ a, x a * ξ a - ∑ a, x a * κ a ≤ ε * (∑ a, rhoV n a * κ a - ∑ a, rhoV n a * ξ a) := by
    intro ε hε
    have hs : StrictAnti (fun a => x a + ε * rhoV n a) := by
      intro a b hab
      have h1 := hρ hab
      have h2 := hx hab.le
      nlinarith
    have := character_support_pairing_le_of_strict_anti κ χ hκ h _ hs ξ hξ
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at this
    linarith
  by_contra hc
  push_neg at hc
  set A := ∑ a, x a * ξ a - ∑ a, x a * κ a with hA
  set B := ∑ a, rhoV n a * κ a - ∑ a, rhoV n a * ξ a with hB
  have hA0 : 0 < A := by rw [hA]; linarith
  have ht : 0 < |B| + 1 := by positivity
  have hε : 0 < A / (2 * (|B| + 1)) := by positivity
  have k := key _ hε
  have hle : A / (2 * (|B| + 1)) * B ≤ A / (2 * (|B| + 1)) * (|B| + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self B]) hε.le
  have heq : A / (2 * (|B| + 1)) * (|B| + 1) = A / 2 := by
    field_simp
  linarith

theorem UpperTheory.RealTr.divSupp :
    ∀ (n : ℕ) (κ : Wt n) (χ : FR n), Antitone κ → alt (rhoV n) * χ = alt (κ + rhoV n) → cf χ κ = 1 ∧ (∀ ξ, cf χ ξ ≠ 0 → Maj ξ κ) ∧
      (Sym χ → ∀ ξ, cf χ ξ ≠ 0 → nsq ξ ≤ nsq κ) := by
  intro n κ χ hκ h
  have hρ : StrictAnti (rhoV n) := (rearr n).2.2.1
  refine ⟨?_, fun ξ hξ x hx => character_support_pairing_le_of_antitone κ χ hκ h x hx ξ hξ, ?_⟩
  · have hs : StrictAnti (κ + rhoV n) := by
      intro a b hab
      have h1 := hρ hab
      have h2 := hκ hab.le
      simp only [Pi.add_apply]
      linarith
    have hcoef : cf (alt (rhoV n) * χ) (κ + rhoV n) = cf χ κ := by
      rw [(cfBasic n).2.2.2.2.2.2.1, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · have e : κ + rhoV n - rhoV n ∘ ⇑(1 : Equiv.Perm (Fin n)) = κ := by
          funext a
          simp
        rw [e]
        simp [sg]
      · intro w _ hw
        have hz : cf χ (κ + rhoV n - rhoV n ∘ ⇑w) = 0 := by
          by_contra hc
          have h1 := character_support_pairing_le_of_strict_anti κ χ hκ h (rhoV n) hρ _ hc
          have h2 := (rearr n).1 (rhoV n) (rhoV n) hρ.antitone hρ.antitone w
          simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, mul_sub, mul_add,
            Finset.sum_add_distrib, Finset.sum_sub_distrib] at h1
          exact hw (h2.2 hρ hρ (by linarith [h2.1]))
        rw [hz, mul_zero]
      · intro h1
        exact absurd (Finset.mem_univ _) h1
    rw [← hcoef, h]
    exact ((cfBasic n).2.2.2.2.2.2.2.2.2.2.2.1 _ hs).1
  · intro hS ξ hξ
    obtain ⟨w, hw⟩ := ((rearr n).2.1 ξ).2.1
    have hanti : Antitone (domC ξ) := ((rearr n).2.1 ξ).1
    have hc : cf χ (domC ξ) ≠ 0 := by
      rw [hw, hS w ξ]
      exact hξ
    have h1 := character_support_pairing_le_of_antitone κ χ hκ h (domC ξ) hanti (domC ξ) hc
    have h2 := ((rearr n).2.2.2.2.2 (domC ξ) κ (by
      simp only [nsq, sq]
      exact h1)).1
    rw [((rearr n).2.1 ξ).2.2.2.2] at h2
    exact h2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SgSmul
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem ex_prod' {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Wt n) :
    ∏ a ∈ s, ex (f a) = ex (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [(cfBasic n).2.1]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, (cfBasic n).1]

private theorem ex_pow' {n : ℕ} (x : Wt n) (k : ℕ) : ex x ^ k = ex (k • x) := by
  induction k with
  | zero => simp [(cfBasic n).2.1]
  | succ k ih => rw [pow_succ, ih, ← (cfBasic n).1, succ_nsmul]

private theorem sg_smul' {n : ℕ} (w : Equiv.Perm (Fin n)) (f : FR n) :
    sg w • f = (((Equiv.Perm.sign w : ℤ) : FR n)) * f := by
  rw [sg, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

theorem UpperTheory.RealTr.denom :
    ∀ (n : ℕ) (t : ℝ), alt (t • rhoV n) = ex (t • rhoV n) * ∏ p ∈ posP n, (1 - ex (-(t • rt p.1 p.2))) := by
  intro n t
  classical
  set Y : Fin n → FR n := fun a => ex (-(t • (Pi.single a (1 : ℝ) : Wt n))) with hY
  set c : Wt n := fun _ => t * (((n : ℝ) - 1) / 2) with hc
  have hA : alt (t • rhoV n) = ex c * (Matrix.vandermonde Y).transpose.det := by
    rw [Matrix.det_apply, Finset.mul_sum, alt]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hprod : ex c * ∏ i, (Matrix.vandermonde Y).transpose (w i) i = ex ((t • rhoV n) ∘ ⇑w) := by
      simp only [Matrix.transpose_apply, Matrix.vandermonde_apply, hY, ex_pow', ex_prod',
        ← (cfBasic n).1]
      congr 1
      funext b
      simp [Finset.sum_apply, Pi.single_apply, rhoV]
      ring
    rw [mul_smul_comm, hprod, sg_smul', Units.smul_def, zsmul_eq_mul]
  have h1 : ∀ a b : Fin n, 1 - ex (-(t • rt a b)) = ex (t • (Pi.single b (1 : ℝ) : Wt n)) * (Y b - Y a) := by
    intro a b
    rw [mul_sub, hY]
    simp only
    rw [← (cfBasic n).1, ← (cfBasic n).1, add_neg_cancel, (cfBasic n).2.1]
    congr 2
    rw [rt, smul_sub]
    abel
  have h2 : ∏ p ∈ posP n, (1 - ex (-(t • rt p.1 p.2))) =
      ∏ i, ∏ j ∈ Finset.Ioi i, (1 - ex (-(t • rt i j))) := by
    unfold posP
    rw [Finset.prod_filter, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  have h3 : ex (t • rhoV n) * ∏ i, ∏ j ∈ Finset.Ioi i, ex (t • (Pi.single j (1 : ℝ) : Wt n)) = ex c := by
    simp only [ex_prod', ← (cfBasic n).1]
    congr 1
    funext k
    simp [Finset.sum_apply, Pi.single_apply, rhoV]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio,
      Fin.card_Iio, nsmul_eq_mul, hc]
    ring
  rw [h2, hA, Matrix.det_transpose, Matrix.det_vandermonde, ← h3]
  simp_rw [h1, Finset.prod_mul_distrib]
  ring
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WeylEv
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem evT_ex' {n : ℕ} (θ x : Wt n) :
    evT θ (ex x) = Complex.exp (Complex.I * ∑ a, (θ a : ℂ) * (x a : ℂ)) := by
  simp [evT, ex, AddMonoidAlgebra.lift_single]

private theorem evT_alt' {n : ℕ} (θ x : Wt n) :
    evT θ (alt x) = (Matrix.of fun a b : Fin n => Complex.exp (Complex.I * ((θ a : ℂ) * (x b : ℂ)))).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [alt, map_sum, map_smul, evT_ex', smul_eq_mul, sg, Matrix.transpose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Complex.exp_sum, Units.smul_def, zsmul_eq_mul, Finset.mul_sum]
  rfl

private theorem den_ne {n : ℕ} (z : Fin n → ℂ) (hz : Function.Injective z) :
    (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det ≠ 0 := by
  have e : (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde z).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  rw [e, Matrix.det_permute']
  refine mul_ne_zero ?_ (Matrix.det_vandermonde_ne_zero_iff.mpr hz)
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> simp [h]

private theorem first' {n : ℕ} (lam : Fin n → ℤ) (θ : Wt n) (z : Fin n → ℂ)
    (hz : ∀ a, z a = Complex.exp (Complex.I * θ a)) (hinj : Function.Injective z) :
    weylChar lam z * evT θ (alt (rhoV n)) = evT θ (alt ((fun a => (lam a : ℝ)) + rhoV n)) := by
  set c : Fin n → ℂ := fun a => Complex.exp (Complex.I * (θ a : ℂ) * ((1 - (n : ℂ)) / 2)) with hc
  have hcast : ∀ b : Fin n, (((n - 1 - (b : ℕ) : ℕ) : ℂ)) = (n : ℂ) - 1 - ((b : ℕ) : ℂ) := by
    intro b
    have := b.isLt
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    simp
  have hD : evT θ (alt (rhoV n)) =
      (∏ a, c a) * (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det := by
    rw [evT_alt', ← Matrix.det_mul_column]
    congr 1
    ext a b
    simp only [Matrix.of_apply, hz a, rhoV, c]
    rw [← Complex.exp_nat_mul, ← Complex.exp_add, hcast b]
    congr 1
    push_cast
    ring
  have hA : evT θ (alt ((fun a => (lam a : ℝ)) + rhoV n)) =
      (∏ a, c a) * (Matrix.of fun i j : Fin n => z i ^ (lam j + ((n - 1 - (j : ℕ) : ℕ) : ℤ))).det := by
    rw [evT_alt', ← Matrix.det_mul_column]
    congr 1
    ext a b
    simp only [Matrix.of_apply, hz a, rhoV, c, Pi.add_apply]
    rw [← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    rw [hcast b]
    ring
  rw [hD, hA, weylChar]
  have hden := den_ne z hinj
  field_simp

theorem UpperTheory.RealTr.weylEv :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (θ : Wt n) (z : Fin n → ℂ), (∀ a, z a = Complex.exp (Complex.I * θ a)) →
      (Function.Injective z → weylChar lam z * evT θ (alt (rhoV n)) = evT θ (alt ((fun a => (lam a : ℝ)) + rhoV n))) ∧
      ((Function.Injective fun a => z a ^ 2) → weylChar lam (fun a => z a ^ 2) * evT θ (alt ((2 : ℝ) • rhoV n)) = evT θ (alt (twoL lam))) ∧
      ∏ a, ∏ b, (1 + z a / z b) = evT θ (∏ a, ∏ b, (1 + ex (rt a b))) ∧
      ∀ y : Fin n → ℂ, conj (weylChar lam fun a => conj (y a)) = weylChar lam y := by
  intro n lam θ z hz
  refine ⟨first' lam θ z hz, ?_, ?_, ?_⟩
  · intro hinj2
    have h := first' lam ((2 : ℝ) • θ) (fun a => z a ^ 2) (fun a => by
      rw [hz a, ← Complex.exp_nat_mul]
      congr 1
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      ring) hinj2
    have e1 : evT θ (alt ((2 : ℝ) • rhoV n)) = evT ((2 : ℝ) • θ) (alt (rhoV n)) := by
      rw [evT_alt', evT_alt']
      congr 1
      ext a b
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      congr 1
      push_cast
      ring
    have e2 : evT θ (alt (twoL lam)) = evT ((2 : ℝ) • θ) (alt ((fun a => (lam a : ℝ)) + rhoV n)) := by
      rw [evT_alt', evT_alt']
      congr 1
      ext a b
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, twoL]
      congr 1
      push_cast
      ring
    rw [e1, e2]
    exact h
  · simp only [map_prod, map_add (f := _), map_one, evT_ex']
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
    congr 1
    rw [hz a, hz b, ← Complex.exp_sub]
    congr 1
    simp only [rt, Pi.sub_apply, Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, Pi.single_apply,
      apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro y
    simp only [weylChar, map_div₀, RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1 <;> congr 1 <;> ext i j <;> simp [map_zpow₀]
end
end

