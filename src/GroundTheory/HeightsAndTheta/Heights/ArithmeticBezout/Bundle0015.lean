module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0030

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPolyLocalGeneratorsDiff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module

noncomputable section

variable {n : ℕ}

def polyDiff (p : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) where
  toFun f j := eval p (pderiv j f)
  map_add' f g := by ext j; simp
  map_smul' c f := by ext j; simp

theorem polyDiff_apply (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) (j : Fin n) :
    polyDiff p f j = eval p (pderiv j f) := rfl

def dotForm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ) :=
  LinearMap.mk₂ ℂ (fun w v => ∑ j, w j * v j)
    (fun w w' v => by simp [add_mul, Finset.sum_add_distrib])
    (fun c w v => by simp [mul_assoc, Finset.mul_sum])
    (fun w v v' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c w v => by simp [mul_left_comm, Finset.mul_sum])

theorem dotForm_apply (w v : Fin n → ℂ) : dotForm w v = ∑ j, w j * v j := rfl

theorem mem_polyTangent_iff (S : Set (MvPolynomial (Fin n) ℂ)) (p v : Fin n → ℂ) :
    v ∈ polyTangent S p ↔ ∀ q ∈ S, dotForm (polyDiff p q) v = 0 := Iff.rfl

theorem polyTangent_eq_of_subset (S T : Set (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hST : S ⊆ T) (h : ∀ f ∈ T, polyDiff p f ∈ Submodule.span ℂ (polyDiff p '' S)) :
    polyTangent S p = polyTangent T p := by
  ext v
  rw [mem_polyTangent_iff, mem_polyTangent_iff]
  refine ⟨fun hv f hf => ?_, fun hv f hf => hv f (hST hf)⟩
  have hle : Submodule.span ℂ (polyDiff p '' S) ≤ LinearMap.ker (dotForm.flip v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]
    exact hv g hg
  have := hle (h f hf)
  simpa only [LinearMap.mem_ker, LinearMap.flip_apply] using this

def tanLinPoly (p w : Fin n → ℂ) : MvPolynomial (Fin n) ℂ := ∑ j, C (w j) * (X j - C (p j))

theorem eval_tanLinPoly (p w : Fin n → ℂ) : eval p (tanLinPoly p w) = 0 := by
  simp [tanLinPoly]

theorem tanLinPoly_add (p w w' : Fin n → ℂ) : tanLinPoly p (w + w') = tanLinPoly p w + tanLinPoly p w' := by
  simp only [tanLinPoly, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem tanLinPoly_smul (p w : Fin n → ℂ) (c : ℂ) : tanLinPoly p (c • w) = C c * tanLinPoly p w := by
  simp only [tanLinPoly, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem tanLinPoly_zero (p : Fin n → ℂ) : tanLinPoly p 0 = 0 := by
  simp [tanLinPoly]

theorem tanLinPoly_single (p : Fin n → ℂ) (i : Fin n) :
    tanLinPoly p (Pi.single i 1) = X i - C (p i) := by
  classical
  simp only [tanLinPoly, Pi.single_apply]
  simp

theorem polyDiff_tanLinPoly (p w : Fin n → ℂ) : polyDiff p (tanLinPoly p w) = w := by
  classical
  ext i
  simp [polyDiff_apply, tanLinPoly, Pi.single_apply]

theorem X_sub_C_mem_ker (p : Fin n → ℂ) (j : Fin n) :
    X j - C (p j) ∈ RingHom.ker (eval p) := by
  simp [RingHom.mem_ker]

theorem sub_tanLinPoly_mem_sq (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    f - C (eval p f) - tanLinPoly p (polyDiff p f) ∈ RingHom.ker (eval p) ^ 2 := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h : polyDiff p (C a) = 0 := by ext j; simp [polyDiff_apply]
    simp [h, tanLinPoly_zero]
  | add f g hf hg =>
    have e : f + g - C (eval p (f + g)) - tanLinPoly p (polyDiff p (f + g)) =
        (f - C (eval p f) - tanLinPoly p (polyDiff p f)) +
          (g - C (eval p g) - tanLinPoly p (polyDiff p g)) := by
      rw [map_add (f := _), map_add (f := _), map_add (f := _), tanLinPoly_add]; ring
    rw [e]
    exact add_mem hf hg
  | mul_X f i hf =>
    have hd : polyDiff p (f * X i) = p i • polyDiff p f + eval p f • Pi.single i 1 := by
      ext j
      simp only [polyDiff_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Derivation.leibniz,
        pderiv_X, map_add]
      by_cases hij : i = j
      · subst hij
        simp only [Pi.single_eq_same, mul_one, map_mul, eval_X]
        ring
      · simp only [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij), mul_zero, map_zero,
          map_mul, eval_X, zero_add, add_zero]
    have e : f * X i - C (eval p (f * X i)) - tanLinPoly p (polyDiff p (f * X i)) =
        C (p i) * (f - C (eval p f) - tanLinPoly p (polyDiff p f)) +
          (f - C (eval p f)) * (X i - C (p i)) := by
      rw [hd, tanLinPoly_add, tanLinPoly_smul, tanLinPoly_smul, tanLinPoly_single, map_mul, eval_X, map_mul]
      ring
    rw [e]
    refine add_mem (Ideal.mul_mem_left _ _ hf) ?_
    rw [pow_two]
    refine Ideal.mul_mem_mul ?_ (X_sub_C_mem_ker p i)
    simp [RingHom.mem_ker]

theorem mem_sq_of_polyDiff_eq_zero (p : Fin n → ℂ) {f : MvPolynomial (Fin n) ℂ}
    (h0 : eval p f = 0) (h1 : polyDiff p f = 0) : f ∈ RingHom.ker (eval p) ^ 2 := by
  simpa [h0, h1, tanLinPoly_zero] using sub_tanLinPoly_mem_sq p f

theorem mem_span_sup_sq_of_polyDiff_mem (p : Fin n → ℂ) {ι : Type*} [Fintype ι]
    (h : ι → MvPolynomial (Fin n) ℂ) (hh : ∀ i, eval p (h i) = 0) {f : MvPolynomial (Fin n) ℂ}
    (hf : eval p f = 0) (hd : polyDiff p f ∈ Submodule.span ℂ (Set.range (polyDiff p ∘ h))) :
    f ∈ Ideal.span (Set.range h) ⊔ RingHom.ker (eval p) ^ 2 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hd
  have hg0 : eval p (f - ∑ i, C (c i) * h i) = 0 := by simp [hf, hh]
  have hg1 : polyDiff p (f - ∑ i, C (c i) * h i) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, C_mul', map_smul]
    rw [← hc]
    simp
  have hsum : ∑ i, C (c i) * h i ∈ Ideal.span (Set.range h) :=
    sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have e : f = (f - ∑ i, C (c i) * h i) + ∑ i, C (c i) * h i := by ring
  rw [e]
  exact add_mem (Ideal.mem_sup_right (mem_sq_of_polyDiff_eq_zero p hg0 hg1))
    (Ideal.mem_sup_left hsum)

theorem maximalIdeal_le_span_of_le_sup_sq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (T : Set R)
    (h : IsLocalRing.maximalIdeal R ≤ Ideal.span T ⊔ IsLocalRing.maximalIdeal R ^ 2) :
    IsLocalRing.maximalIdeal R ≤ Ideal.span T := by
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  rwa [Ideal.smul_eq_mul, ← pow_two]

theorem exists_polyDiff_basis (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) :
    ∃ q : Fin (n - finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p)) →
        MvPolynomial (Fin n) ℂ,
      (∀ i, q i ∈ J) ∧ LinearIndependent ℂ (polyDiff p ∘ q) ∧
        ∀ f ∈ J, polyDiff p f ∈ Submodule.span ℂ (Set.range (polyDiff p ∘ q)) := by
  set D : Submodule ℂ (Fin n → ℂ) := (J.restrictScalars ℂ).map (polyDiff p) with hDdef
  have hinj : Function.Injective (dotForm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ)) := by
    intro w w' hww
    ext j
    have := LinearMap.congr_fun hww (Pi.single j 1)
    classical
    simpa [dotForm_apply, Pi.single_apply] using this
  set W := D.map (dotForm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ))
  have hW : finrank ℂ W = finrank ℂ D :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj D)).symm
  have hco : W.dualCoannihilator = polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p := by
    ext v
    rw [Submodule.mem_dualCoannihilator, mem_polyTangent_iff]
    constructor
    · intro h q hq
      exact h _ (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem (p := J.restrictScalars ℂ) hq))
    · rintro h _ ⟨w, ⟨q, hq, rfl⟩, rfl⟩
      exact h q hq
  have hsum := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rw [hco, hW, Module.finrank_fin_fun] at hsum
  have hD : finrank ℂ D = n - finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p) := by
    omega
  let b := Module.finBasisOfFinrankEq ℂ D hD
  have hb : ∀ i, ∃ q ∈ J, polyDiff p q = (b i : Fin n → ℂ) := by
    intro i
    obtain ⟨q, hq, e⟩ := Submodule.mem_map.1 (b i).2
    exact ⟨q, hq, e⟩
  choose q hqJ hq using hb
  have hcomp : polyDiff p ∘ q = D.subtype ∘ b := funext hq
  refine ⟨q, hqJ, ?_, ?_⟩
  · rw [hcomp]
    exact b.linearIndependent.map' D.subtype (Submodule.ker_subtype D)
  · intro f hf
    have hspan : Submodule.span ℂ (Set.range (polyDiff p ∘ q)) = D := by
      rw [hcomp, Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
    rw [hspan]
    exact Submodule.mem_map_of_mem (p := J.restrictScalars ℂ) hf

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PThroughTwoPointsTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ThroughTwoPointsTrdeg.proof (hT : TrdegAdjoinLe.Statement) : ThroughTwoPointsTrdeg.Statement := by
  intro K Ω _ _ n k _ _ _ hinj x c hcx y j hyj hprop hy
  let u : Fin k × Fin n → Ω := fun im => algebraMap (MvPolynomial (Fin k × Fin n) K) Ω (X im)
  let z : Fin n → Ω := fun m => y m * (y j)⁻¹
  let x' : Fin n → Ω := fun m => algebraMap K Ω (x m)
  let c' : Fin n → Ω := fun m => algebraMap K Ω (c m)
  let s : Fin k → Ω := fun i => ∑ l, u (i, l) * x' l
  have hC : ∀ a : K, algebraMap (MvPolynomial (Fin k × Fin n) K) Ω (C a) = algebraMap K Ω a := fun a => by
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin k × Fin n) K) Ω, MvPolynomial.algebraMap_eq]

  have heq : ∀ i, ∑ m, u (i, m) * z m = s i * ∑ m, c' m * z m := by
    intro i
    have h := hy i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [genSubst, map_sub, map_mul, map_sum, hC] at h
    have h' : ∑ m, u (i, m) * y m = s i * ∑ m, c' m * y m := by
      rw [← sub_eq_zero, Finset.mul_sum, ← Finset.sum_sub_distrib, ← h]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [u, s, x', c']
      ring
    simp only [z, ← mul_assoc, ← Finset.sum_mul]
    rw [h']

  obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hcx
  have hx'p : x' p ≠ 0 := by simpa [x'] using hp
  obtain ⟨q, hD⟩ : ∃ q, x' p * z q - x' q * z p ≠ 0 := by
    by_contra h
    push Not at h
    apply hprop (y j * (z p * (x' p)⁻¹))
    funext m
    have hm := h m
    simp only [z, x'] at hm hx'p ⊢
    have hm2 : (algebraMap K Ω (x p) * y m - algebraMap K Ω (x m) * y p) * (y j)⁻¹ = 0 := by
      rw [← hm]; ring
    have hm3 := (mul_eq_zero.1 hm2).resolve_right (inv_ne_zero hyj)
    have e : y j * (y p * (y j)⁻¹ * (algebraMap K Ω (x p))⁻¹) * algebraMap K Ω (x m) =
        y p * algebraMap K Ω (x m) * (algebraMap K Ω (x p))⁻¹ := by
      rw [show y j * (y p * (y j)⁻¹ * (algebraMap K Ω (x p))⁻¹) * algebraMap K Ω (x m) =
        (y j * (y j)⁻¹) * (y p * algebraMap K Ω (x m)) * (algebraMap K Ω (x p))⁻¹ by ring,
        mul_inv_cancel₀ hyj, one_mul]
    rw [e, eq_mul_inv_iff_mul_eq₀ hx'p]
    linear_combination hm3
  set D := x' p * z q - x' q * z p with hDdef
  have hqp : q ≠ p := by
    rintro rfl
    exact hD (by simp [D])
  let E := (Finset.univ.erase p).erase q
  have hqE : q ∈ Finset.univ.erase p := Finset.mem_erase.2 ⟨hqp, Finset.mem_univ q⟩
  have hsplit : ∀ g : Fin n → Ω, ∑ m, g m = g p + g q + ∑ m ∈ E, g m := fun g => by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ hqE, add_assoc]

  let t : Fin k ⊕ (Fin k × E) → Ω := fun a => Sum.elim s (fun b => u (b.1, b.2.1)) a
  let B := Algebra.adjoin K (Set.range z ∪ Set.range t)
  have hzB : ∀ m, z m ∈ B := fun m => Algebra.subset_adjoin (Or.inl ⟨m, rfl⟩)
  have hsB : ∀ i, s i ∈ B := fun i => Algebra.subset_adjoin (Or.inr ⟨Sum.inl i, rfl⟩)
  have huB : ∀ i, ∀ m ∈ E, u (i, m) ∈ B := fun i m hm =>
    Algebra.subset_adjoin (Or.inr ⟨Sum.inr (i, ⟨m, hm⟩), rfl⟩)
  have hKB : ∀ a : K, algebraMap K Ω a ∈ B := fun a => B.algebraMap_mem a
  have hczB : ∑ m, c' m * z m ∈ B := B.sum_mem fun m _ => B.mul_mem (hKB _) (hzB m)
  have hDB : D ∈ B := B.sub_mem (B.mul_mem (hKB _) (hzB q)) (B.mul_mem (hKB _) (hzB p))
  have halg : ∀ v, D * v ∈ B → IsAlgebraic B v := fun v hv =>
    IsAlgebraic.of_mul (y := D) (mem_nonZeroDivisors_of_ne_zero hD)
      (isAlgebraic_algebraMap (⟨D, hDB⟩ : B)) (isAlgebraic_algebraMap (⟨D * v, hv⟩ : B))
  have hw : ∀ im, IsAlgebraic B (u im) := by
    rintro ⟨i, m⟩
    have hSx : ∑ m ∈ E, u (i, m) * x' m ∈ B :=
      B.sum_mem fun m hm => B.mul_mem (huB i m hm) (hKB _)
    have hSz : ∑ m ∈ E, u (i, m) * z m ∈ B :=
      B.sum_mem fun m hm => B.mul_mem (huB i m hm) (hzB m)
    have e1 := hsplit (fun m => u (i, m) * x' m)
    have e2 := hsplit (fun m => u (i, m) * z m)
    rw [heq i] at e2
    change s i = _ at e1
    by_cases hmp : m = p
    · subst hmp
      refine halg _ ?_
      have : D * u (i, m) = z q * (s i - ∑ m ∈ E, u (i, m) * x' m) -
          x' q * (s i * ∑ m, c' m * z m - ∑ m ∈ E, u (i, m) * z m) := by
        rw [hDdef]; linear_combination -z q * e1 + x' q * e2
      rw [this]
      exact B.sub_mem (B.mul_mem (hzB q) (B.sub_mem (hsB i) hSx))
        (B.mul_mem (hKB _) (B.sub_mem (B.mul_mem (hsB i) hczB) hSz))
    by_cases hmq : m = q
    · subst hmq
      refine halg _ ?_
      have : D * u (i, m) = x' p * (s i * ∑ m, c' m * z m - ∑ m ∈ E, u (i, m) * z m) -
          z p * (s i - ∑ m ∈ E, u (i, m) * x' m) := by
        rw [hDdef]; linear_combination -x' p * e2 + z p * e1
      rw [this]
      exact B.sub_mem (B.mul_mem (hKB _) (B.sub_mem (B.mul_mem (hsB i) hczB) hSz))
        (B.mul_mem (hzB p) (B.sub_mem (hsB i) hSx))
    exact isAlgebraic_algebraMap
      (⟨u (i, m), huB i m (Finset.mem_erase.2 ⟨hmq, Finset.mem_erase.2 ⟨hmp, Finset.mem_univ m⟩⟩)⟩ : B)
  have hle := hT K Ω (Set.range z) (Fin k ⊕ (Fin k × E)) t (Fin k × Fin n) u hw

  have hadj : Algebra.adjoin K (Set.range u) = (IsScalarTower.toAlgHom K (MvPolynomial (Fin k × Fin n) K) Ω).range := by
    rw [← Algebra.map_top, ← MvPolynomial.adjoin_range_X, AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  have hinj' : Function.Injective (IsScalarTower.toAlgHom K (MvPolynomial (Fin k × Fin n) K) Ω) := hinj
  have htr : Algebra.trdeg K (Algebra.adjoin K (Set.range u)) = ((k * n : ℕ) : Cardinal) := by
    rw [hadj, ← (AlgEquiv.ofInjective _ hinj').trdeg_eq, MvPolynomial.trdeg_of_isDomain]
    simp
  have hcard : Fintype.card (Fin k ⊕ (Fin k × E)) = k + k * (n - 2) := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
      Finset.card_erase_of_mem hqE, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
      Fintype.card_fin]
    rfl
  rw [htr, hcard] at hle
  have hn : 2 ≤ n := by
    have := Fin.val_ne_of_ne hqp
    omega
  rcases lt_or_ge (Algebra.trdeg K (Algebra.adjoin K (Set.range z))) Cardinal.aleph0 with hfin | hinf
  · obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.1 hfin
    rw [hd] at hle ⊢
    norm_cast at hle ⊢
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [Nat.add_sub_cancel_left] at hle
    nlinarith
  · exact (Cardinal.natCast_lt_aleph0 (n := k)).le.trans hinf

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormBirationalAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChowFormBirationalAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F))
    (g : MvPolynomial (Fin (k + 1) × Fin n) F) (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P)),
    IsProjPrime P → IsChowForm P (k + 1) g → ∑ j, c j * genPt P j = 1 →
      ∃ t : Fin n → F, (∑ l, C (t l) * pderiv (0, l) g) ∉ incIdeal P (k + 1) ∧
        ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) *
              C (∑ l, algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (t l) * genPt P l) =
            aeval (genSubst (genPt P) c) (∑ l, C (t l) * pderiv (0, l) g) * C (genPt P m)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFibreAverage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

def matGauss {m n : ℕ} (π : Fin m → Fin n → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2))

def ConeFibreAverage.Statement : Prop :=
  ∀ n m : ℕ, ∃ K : ℝ≥0∞, 0 < K ∧ K < ⊤ ∧
    ∀ (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J →
      (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
        ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
            ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
          K * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J}

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsGraphAreaIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def GraphAreaIntegral.Statement : Prop :=
  ∀ (d m n : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m) (Ω : Set (EuclideanSpace ℂ (Fin d)))
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)),
    IsOpen Ω → DifferentiableOn ℂ F Ω → ∀ A ⊆ Ω, MeasurableSet A →
    ∀ h : EuclideanSpace ℂ (Fin n) → ℝ≥0∞,
      ∫⁻ y in graphPt e F '' A, h y ∂(μH[((2 * d : ℕ) : ℝ)]) =
        ∫⁻ x in A, h (graphPt e F x) * ENNReal.ofReal (areaJacobian
          (fderiv ℝ (graphPt e F) x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)))
          ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjChowNonzero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjChowNonzero.Statement : Prop :=
  ∀ (n e : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → ComplexSets.IsFiniteProjection W A →
      eval (fun j => projPar A (.inr j))
        (Vertical.specRest (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))) f (projPar A)) ≠ 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjSecDomain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjSecDomain.Statement : Prop :=
  ∀ (n e : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    W.IsPrime → ComplexSets.IsFiniteProjection W A →
      IsDomain (Vertical.SecAlg
          (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
          (projPar A)) ∧
        Module.Finite (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
          (Vertical.SecAlg
            (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
            (projPar A))

end

end GroundTheory.Heights₂.Heights
end

