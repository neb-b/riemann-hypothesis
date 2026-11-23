module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw

@[expose] public section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.UnfoldLaw

theorem sum_reps_equiv {V K : Type} [AddCommGroup V] [Field K] [CharZero K] {M₀ M M₁ : AddSubgroup V} (S : Finset V)
    (h0 : M₀ ≤ M) (h1 : M ≤ M₁) (sep : ∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ M₀ → s = s') (cov : ∀ v ∈ M₁, ∃ s ∈ S, v - s ∈ M₀)
    (T : V ≃ V) (hT : ∀ s t, T s - T t ∈ M ↔ s - t ∈ M) (f : V → K) (inv : ∀ v, ∀ u ∈ M, f (v + u) = f v)
    (s1 : ∀ t, f t ≠ 0 → t ∈ M₁) (s2 : ∀ t, f (T t) ≠ 0 → t ∈ M₁) : ∑ t ∈ S, f (T t) = ∑ t ∈ S, f t := by
  have hle : ∀ u u', u' ∈ M₁ → (S.filter fun s => s - u ∈ M).card ≤ (S.filter fun s => s - u' ∈ M).card := by
    intro u u' hu'
    have hex : ∀ v, ∃ s, v ∈ M₁ → s ∈ S ∧ v - s ∈ M₀ := fun v => by
      by_cases hv : v ∈ M₁
      · obtain ⟨s, a, b⟩ := cov v hv
        exact ⟨s, fun _ => ⟨a, b⟩⟩
      · exact ⟨0, fun h => absurd h hv⟩
    choose ρ hρ using hex
    have key : ∀ s ∈ S.filter fun s => s - u ∈ M, ρ (s - u + u') ∈ S ∧ s - u + u' - ρ (s - u + u') ∈ M₀ := fun s hs =>
      hρ _ (add_mem (h1 (Finset.mem_filter.1 hs).2) hu')
    refine Finset.card_le_card_of_injOn (fun s => ρ (s - u + u')) (fun s hs => ?_) fun s hs s' hs' e => ?_
    · have hs := Finset.mem_coe.1 hs
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨(key s hs).1, ?_⟩)
      convert sub_mem (Finset.mem_filter.1 hs).2 (h0 (key s hs).2) using 1
      abel
    · have hs := Finset.mem_coe.1 hs
      have hs' := Finset.mem_coe.1 hs'
      refine sep s (Finset.mem_filter.1 hs).1 s' (Finset.mem_filter.1 hs').1 ?_
      have := sub_mem (key s hs).2 (key s' hs').2
      dsimp only at e
      rw [e] at this
      convert this using 1
      abel
  have hc : ∀ u ∈ M₁, (S.filter fun s => s - u ∈ M).card = (S.filter fun s => s - 0 ∈ M).card := fun u hu =>
    le_antisymm (hle _ _ (zero_mem _)) (hle _ _ hu)
  have hN : (((S.filter fun s => s - 0 ∈ M).card : ℕ) : K) ≠ 0 := by
    obtain ⟨s, a, b⟩ := cov 0 (zero_mem _)
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨s, Finset.mem_filter.2 ⟨a, by simpa using h0 b⟩⟩)
  refine mul_left_cancel₀ hN ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  have e1 : ∀ s, (((S.filter fun s => s - 0 ∈ M).card : ℕ) : K) * f (T s) = ∑ t ∈ S, if t - T s ∈ M then f t else 0 := by
    intro s
    have : ∀ t ∈ S, (if t - T s ∈ M then f t else 0) = if t - T s ∈ M then f (T s) else 0 := fun t _ => by
      split_ifs with h
      · rw [← inv (T s) _ h, add_sub_cancel]
      · rfl
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases h : f (T s) = 0
    · simp [h]
    · rw [hc _ (s1 _ h)]
  have e2 : ∀ t, (((S.filter fun s => s - 0 ∈ M).card : ℕ) : K) * f t = ∑ s ∈ S, if t - T s ∈ M then f t else 0 := by
    intro t
    obtain ⟨t, rfl⟩ := T.surjective t
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases h : f (T t) = 0
    · simp [h]
    · rw [← hc _ (s2 _ h)]
      congr 3
      refine Finset.filter_congr fun s _ => ?_
      rw [hT, ← neg_mem_iff, neg_sub]
  simp only [e1, e2]
  exact Finset.sum_comm

section Affine

variable {F : Type} [Field F] {n' c' n c : ℕ}

theorem affineFreeParam_first_sub_eq_linearPart (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (s t : Loc.FC n' c' n c → F) :
    Loc.xx1 xj s - Loc.xx1 xj t = Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart 0 (s - t) :=
  Proof.unipotentRadicals_act_affine_unfoldingSpaces.hom_ext fun a l => by
    simp only [Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply, Pi.sub_apply, linearMap_unfolding_apply_single]
    split_ifs <;> simp

theorem linPart_single (τ : Loc.FC n' c' n c → F) (s : Fin (n' + c')) (l : Fin (n + c)) :
    Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart (0 : (Fin n' → F) →ₗ[F] (Fin n → F)) τ (Pi.single s 1) l =
      if hf : Loc.IsFree n' n c l.1 s.1 then τ ⟨(l, s), hf⟩ else 0 := by
  simp only [Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply, Pi.sub_apply, linearMap_unfolding_apply_single]
  split_ifs <;> simp

theorem chArg_add_smul (x y : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)) (a : F) :
    Loc.chArg (x + a • y) = Loc.chArg x + a * Loc.chArg y := by
  unfold Loc.chArg
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.add_apply, LinearMap.smul_apply, atN_add, atN_smul]

variable {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)} {g : (Fin n → F) ≃ₗ[F] (Fin n → F)}

theorem characterArgument_first_parabolic_shift (hc : 1 ≤ c) (hc' : c' = c + 1) (hr : Loc.R1cond F n c r) (xj : (Fin n' → F) →ₗ[F] (Fin n → F))
    (t : Loc.FC n' c' n c → F) : Loc.chArg (r.toLinearMap ∘ₗ Loc.xx1 xj t) = Loc.chArg (Loc.xx1 xj t) + Loc.n1Arg r := by
  obtain ⟨-, -, h3⟩ := (Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic F n' c' n c hc hc' xj (Loc.xx1 xj t)).1 ⟨t, rfl⟩
  generalize Loc.xx1 xj t = x at h3
  have e : Loc.n1Arg r = ∑ i ∈ Finset.range c, Loc.atN (r (Loc.eN F (n + c) (n + i + 1))) (n + i) := by
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
    rw [Finset.sum_range_succ, Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.eN_eq_zero (i := n + d + 1) (by omega), map_zero]
    simp [Loc.n1Arg, Loc.atN]
  rw [e]
  unfold Loc.chArg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have b3 := atN_of_R1cond hr (h3 (i + 1))
  have b4 : Loc.atN (Loc.eN F (n + c) (n + (i + 1))) (n + i) = 0 := Proof.unfoldingCharacterArgument_comp_unipotentRadicals.atN_eN_succ _ _
  simp only [map_sub, atN_sub, b4] at b3
  change Loc.atN (r (x (Loc.eN F (n' + c') (n' + (i + 1))))) (n + i) =
    Loc.atN (x (Loc.eN F (n' + c') (n' + (i + 1)))) (n + i) + Loc.atN (r (Loc.eN F (n + c) (n + (i + 1)))) (n + i)
  linear_combination b3

theorem exists_move (hc : 1 ≤ c) (hc' : c' = c + 1) (hr : r ∈ Loc.R1 F n c)
    (hg : ∀ x, r (Loc.inX F n c x) = Loc.inX F n c (g x)) (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) :
    ∃ T : (Loc.FC n' c' n c → F) ≃ (Loc.FC n' c' n c → F),
      ∀ t, r.toLinearMap ∘ₗ Loc.xx1 xj t = Loc.xx1 (g.toLinearMap ∘ₗ xj) (T t) := by
  obtain ⟨y, T, b, h⟩ := Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic F n' c' n c hc hc' r hr 1 (one_mem _)
    (g.toLinearMap ∘ₗ xj)
  obtain rfl : y = xj := LinearMap.ext fun v => by
    have := LinearMap.congr_fun (h 0) (Loc.inX F n' c' v)
    change r (Loc.xx1 y 0 (Loc.inX F n' c' v)) = _ at this
    rw [unfoldingAffinePointMap_apply_inclusion, unfoldingAffinePointMap_apply_inclusion, hg] at this
    exact g.injective (inX_injective this)
  exact ⟨T.toEquiv.trans (Equiv.addRight b), h⟩

theorem det_first_parabolic_eq_det_block (hr : Loc.R1cond F n c r) (hg : ∀ x, r (Loc.inX F n c x) = Loc.inX F n c (g x)) :
    LinearEquiv.det r = LinearEquiv.det g := by
  apply Units.ext
  rw [LinearEquiv.coe_det, LinearEquiv.coe_det, ← LinearMap.det_toMatrix', ← LinearMap.det_toMatrix',
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  have hX : ∀ (a : Fin n) (l : Fin (n + c)), r (Pi.single (Fin.castAdd c a) 1) l = Loc.inX F n c (g (Pi.single a 1)) l := by
    intro a l
    rw [← hg, ← Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.inX_single (Fin.castAdd c a) a.2]
    rfl
  have hD : ∀ a b : Fin c, b ≤ a → r (Pi.single (Fin.natAdd n b) 1) (Fin.natAdd n a) = if a = b then 1 else 0 := by
    intro a b hab
    have := mem_Ufl.1 (hr.2.2 b.1) (Fin.natAdd n a) (by simpa using hab)
    rw [Pi.sub_apply, sub_eq_zero, Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.eN_eq_single (by omega)] at this
    refine Eq.trans this ?_
    simp [Pi.single_apply, Fin.ext_iff]
  set M := (LinearMap.toMatrix' r.toLinearMap).submatrix finSumFinEquiv finSumFinEquiv with hM
  have h21 : M.toBlocks₂₁ = 0 := by
    ext a b
    simp [hM, Matrix.toBlocks₂₁, LinearMap.toMatrix'_apply, hX, inX_apply]
  have h11 : M.toBlocks₁₁ = LinearMap.toMatrix' g.toLinearMap := by
    ext a b
    simp [hM, Matrix.toBlocks₁₁, LinearMap.toMatrix'_apply, hX, inX_castAdd]
  have h22 : M.toBlocks₂₂.det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun a _ => ?_
      simp [hM, Matrix.toBlocks₂₂, LinearMap.toMatrix'_apply, hD]
    · intro a b hab
      have : b < a := hab
      simp [hM, Matrix.toBlocks₂₂, LinearMap.toMatrix'_apply, hD a b this.le, this.ne']
  rw [← Matrix.fromBlocks_toBlocks M, h21, Matrix.det_fromBlocks_zero₂₁, h11, h22, mul_one]

end Affine

section Local

open Proof.NormalFormAtPrime Proof.boxSum_ne_zero_invariant_affineChange

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} {n' c' n c : ℕ}

theorem sclLat_bdd [StarRing E] (N : ℕ) (e : ℕ → ℤ) : ∃ k : ℕ,
    (∀ v ∈ LocE.sclLat P (qOf P) N e, IntV P ((qOf P : E) ^ k • v)) ∧
      ∀ v, IntV P v → (qOf P : E) ^ k • v ∈ LocE.sclLat P (qOf P) N e := by
  have q0 := qOf_ne_zero P
  obtain ⟨k, hk⟩ := (Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators E P N N).1 fun l => (qOf P : E) ^ e l.1
  obtain ⟨k', hk'⟩ := (Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators E P N N).1 fun l => ((qOf P : E) ^ e l.1)⁻¹
  refine ⟨max k k', fun v hv l => ?_, fun v hv => LastSteps.mem_sclLat.2 fun l => ?_⟩
  · convert (hk _ (le_max_left k k') l).mul (LastSteps.mem_sclLat.1 hv l) using 1
    have := zpow_ne_zero (e l.1) q0
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  · convert (hk' _ (le_max_right k k') l).mul (hv l) using 1
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

def movedHom {a b : ℕ} (L' : Submodule (𝓞 E) (Fin a → E)) (L : Submodule (𝓞 E) (Fin b → E))
    (h' : (Fin a → E) ≃ₗ[E] (Fin a → E)) (h : (Fin b → E) ≃ₗ[E] (Fin b → E)) : AddSubgroup ((Fin a → E) →ₗ[E] (Fin b → E)) where
  carrier := {z | ∀ v ∈ L', h.symm (z (h' v)) ∈ L}
  zero_mem' := fun v _ => by simp
  add_mem' := fun hx hy v hv => by
    rw [LinearMap.add_apply, map_add (f := _)]
    exact add_mem (hx v hv) (hy v hv)
  neg_mem' := fun hx v hv => by
    rw [LinearMap.neg_apply, map_neg]
    exact neg_mem (hx v hv)

theorem movedHom_bdd [StarRing E] {a b : ℕ} (e' e : ℕ → ℤ) (h' : (Fin a → E) ≃ₗ[E] (Fin a → E))
    (h : (Fin b → E) ≃ₗ[E] (Fin b → E)) : ∃ m : ℕ,
    (∀ z ∈ movedHom (LocE.sclLat P (qOf P) a e') (LocE.sclLat P (qOf P) b e) h' h, IntHom P ((qOf P : E) ^ m • z)) ∧
      ∀ z, IntHom P z → (qOf P : E) ^ m • z ∈ movedHom (LocE.sclLat P (qOf P) a e') (LocE.sclLat P (qOf P) b e) h' h := by
  obtain ⟨k', a1, a2⟩ := sclLat_bdd (P := P) a e'
  obtain ⟨k, b1, b2⟩ := sclLat_bdd (P := P) b e
  obtain ⟨m1, c1⟩ := (Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators E P a a).2 h'.toLinearMap
  obtain ⟨m2, c2⟩ := (Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators E P a a).2 h'.symm.toLinearMap
  obtain ⟨m3, c3⟩ := (Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators E P b b).2 h.toLinearMap
  obtain ⟨m4, c4⟩ := (Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators E P b b).2 h.symm.toLinearMap
  set j := m1 + m2 + m3 + m4
  refine ⟨k + k' + j + j, fun z hz v hv => ?_, fun z hz v hv => ?_⟩
  · convert c3 j (by omega) _ (b1 _ (hz _ (a2 _ (c2 j (by omega) v hv)))) using 1
    simp only [LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, smul_smul]
    congr 1
    ring
  · convert b2 _ (c4 j (by omega) _ (hz _ (c1 j (by omega) _ (a1 v hv)))) using 1
    simp only [LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe, smul_smul]
    congr 1
    ring

end Local

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem phiAt_mod (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) {i : ℕ} (hi : i + 2 ≤ R.m)
    (P : HeightOneSpectrum (𝓞 X.E)) :
    (∀ x, PhiAt Ch mu sharp i P x ≠ 0 → ∀ v ∈ lamYat (Pr := Pr) (R := R) i P, x v ∈ lamYat (Pr := Pr) (R := R) (i + 1) P) ∧
      ∀ x z : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)),
        (∀ v ∈ lamYat (Pr := Pr) (R := R) i P, z v ∈ lamYat (Pr := Pr) (R := R) (i + 1) P) →
          PhiAt Ch mu sharp i P (x + (qOf P : X.E) • z) = PhiAt Ch mu sharp i P x := by
  have h1 : R.k ≤ R.N i := Nat.le_add_right _ _
  have h2 : R.k ≤ R.N (i + 1) := Nat.le_add_right _ _
  have h3 : R.r + (i + 1 - 1) * R.t = R.N i + cOf R i := by
    unfold Ranks.r Ranks.N cOf
    rw [Nat.add_sub_cancel, mul_add i]
    omega
  have h4 : R.N i + cOf R i ≤ R.N (i + 1) + cOf R (i + 1) := by
    unfold Ranks.N cOf
    rw [add_mul i]
    omega
  by_cases hP : P ∈ Pr.vGs
  · unfold PhiAt lamYat
    simp only [if_pos hP]
    split_ifs
    · have := LastSteps.good_PhiGS (psi0P Ch P) (chiP Ch P) (rS := R.rS) h1 h2 h3 h4
      exact ⟨this.1, this.2.1⟩
    · have := LastSteps.good_PhiG (psi0P Ch P) (chiP Ch P) h1 h2 h3 h4
      exact ⟨this.1, this.2.1⟩
  · simp only [IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP]
    unfold PhiAt
    rw [if_neg hP]
    exact Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd X.E X.K P _ _ _ _ _ _ _ h1 h2 (by omega) (by omega)

theorem jat_le (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) :
    Jat (Pr := Pr) (R := R) sharp j P ≤ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P) := by
  intro k hk
  unfold Jat at hk
  by_cases hP : P ∈ Pr.vGs
  · unfold lamYat
    rw [if_pos hP] at hk ⊢
    split_ifs at hk
    · exact hk.1
    · exact hk.1
  · rw [if_neg hP] at hk
    intro v
    rw [IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP, IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP]
    exact (mem_stdAt_iff _).symm.trans ((hk.1 v).trans (mem_stdAt_iff _))

variable {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}

theorem chArg_depth (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu)
    (z : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)))
    (hz : z ∈ movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) (L.h i al P) (L.h (i + 1) be P)) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * Loc.chArg z) := by
  have hm := hL.hm
  have hc : cOf R i = cOf R (i + 1) + 1 := by unfold cOf; omega
  unfold Loc.chArg
  rw [Finset.mul_sum]
  refine intAt_sum _ _ fun s hs => ?_
  have hs := Finset.mem_range.1 hs
  have l1 : R.N (i + 1) + s < R.N (i + 1) + cOf R (i + 1) := by omega
  have l2 : R.N i + s + 1 < R.N i + cOf R i := by omega
  unfold Loc.atN
  rw [dite_eq_left l1, Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.eN_eq_single l2]
  by_cases hP : P.1 ∈ Pr.vGs
  · have h1 : ∀ v ∈ lamYat (Pr := Pr) (R := R) i P.1, z v ∈ lamYat (Pr := Pr) (R := R) (i + 1) P.1 := fun v hv => by
      have := (hL.stabG _ be P hP _).2 (hz _ ((inv_mem (hL.stabG _ al P hP) v).2 hv))
      rwa [LinearEquiv.apply_symm_apply, show L.h i al P ((L.h i al P)⁻¹ v) = v from LinearEquiv.apply_symm_apply _ v] at this
    unfold lamYat at h1
    simp only [if_pos hP] at h1
    have h2 := LastSteps.mem_homS_sclLat.1 h1 ⟨_, l1⟩ ⟨_, l2⟩
    have e : LocE.scE (R.N i) (fun i => i + 1) (R.N i + s + 1) - LocE.scE (R.N (i + 1)) (fun i => i + 1) (R.N (i + 1) + s) = 1 := by
      unfold LocE.scE
      rw [if_neg (by omega), if_neg (by omega)]
      dsimp only
      omega
    rw [e, zpow_one, mul_comm] at h2
    rwa [hL.depthG P hP, pow_one]
  · have hD := hL.depthQ' P hP
    have hv := (IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat (R := R) hP _).2 (intV_single P.1 ⟨_, l2⟩)
    have := (hL.boundQ _ be P hP _ (hz _ (hL.boundQ _ al P hP _ hv).1)).2
    rw [LinearEquiv.apply_symm_apply, show ∀ v, L.h i al P ((L.h i al P)⁻¹ v) = v from fun v => LinearEquiv.apply_symm_apply _ v,
      IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP] at this
    exact Proof.NormalFormAtPrime.intAt_pow_mono (A := i + 1) (by omega) (this ⟨_, l1⟩)

end Chain

end GlobalTheory.UnfoldLaw
