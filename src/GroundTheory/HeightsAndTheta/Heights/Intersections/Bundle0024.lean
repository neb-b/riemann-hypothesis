module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagFormDiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalFormDivisor

set_option linter.unusedSectionVars false

section Generic

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]

theorem aeval_scale (u : K → Φ) (c : (Σ k, ι k) → Φ) (s : MRing ι) (β : K → ℕ) (hs : IsMultiHomog s β) :
    aeval (fun p => u p.1 * c p) s = (∏ k, u k ^ β k) * aeval c s := by
  have h1 := congrArg (MvPolynomial.eval u) (DiagRAux.multiConeMap_of_homog c s β hs)
  have h2 : (MvPolynomial.eval u).comp (T.multiConeMap c) =
      (aeval (fun p => u p.1 * c p) : MRing ι →ₐ[ℤ] Φ).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp [T.multiConeMap]) (fun p => by simp [T.multiConeMap, mul_comm])
  rw [← RingHom.comp_apply, h2, map_mul, eval_C, map_prod] at h1
  simp only [map_pow, eval_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
  rw [h1, mul_comm]

end Generic

section Geometry

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
  [Algebra Ω Φ]

end Geometry

end DiagonalFormDivisor


end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagPivotAlgIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

namespace FlagPivotAlgIndep

variable (F : Type) [Field F] (n : ℕ)

abbrev genFrac (p : Fin n × Fin n) : FractionRing (MvPolynomial (Fin n × Fin n) F) :=
  algebraMap (MvPolynomial (Fin n × Fin n) F) _ (X p)

theorem genFrac_ne_zero (p : Fin n × Fin n) : genFrac F n p ≠ 0 := by
  simp only [genFrac, ne_eq, IsFractionRing.to_map_eq_zero_iff]
  exact X_ne_zero p

def spec (p : Fin n × Fin n) : FractionRing (MvPolynomial (Fin n × Fin n) F) :=
  if (p.2 : ℕ) < p.1 then 0
  else if h : (p.1 : ℕ) = 0 then genFrac F n p
  else genFrac F n p / genFrac F n (⟨p.1 - 1, by omega⟩, ⟨p.1 - 1, by omega⟩)

theorem prod_spec (m : ℕ) (hm : m < n) (c : Fin n) (hc : m ≤ (c : ℕ)) :
    (∏ i : Fin m, spec F n (⟨i, by omega⟩, ⟨i, by omega⟩)) * spec F n (⟨m, hm⟩, c) = genFrac F n (⟨m, hm⟩, c) := by
  induction m generalizing c with
  | zero => simp [spec]
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega) ⟨m, by omega⟩ le_rfl]
    have e : (⟨m + 1 - 1, by omega⟩ : Fin n) = ⟨m, by omega⟩ := Fin.ext (by simp)
    simp only [spec, show ¬ ((c : ℕ) < m + 1) by omega, if_false, show m + 1 ≠ 0 by omega, dif_neg, not_false_eq_true, e]
    exact mul_div_cancel₀ _ (genFrac_ne_zero F n _)

theorem spec_pivotMinor (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    aeval (spec F n) (pivotMinor (genMat F n) a b) = genFrac F n (Fin.castLE (Nat.sub_le n 1) a, b) := by
  have ha : (a : ℕ) < n := by have := a.2; omega
  unfold pivotMinor
  rw [AlgHom.map_det, Matrix.det_of_isUpperTriangular]
  · rw [Fin.prod_univ_castSucc]
    refine Eq.trans ?_ (prod_spec F n a ha b hab)
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, pivotCols, aeval_X]
      rfl
    · simp [AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, pivotCols, aeval_X]
      rfl
  · intro i j hji
    have hji' : (j : ℕ) < i := hji
    have hj : (j : ℕ) < a := by have := i.2; omega
    simp [AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, pivotCols, aeval_X, spec, hj, hji']

end FlagPivotAlgIndep

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingChartLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingChartLoc.proof : LocRingChartLoc.Statement := by
  classical
  intro K _ ι _ P W hP hW hPW hrel
  let L := FractionRing (MRing ι ⧸ P)
  let q : MRing ι →+* L := (algebraMap (MRing ι ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hq : ∀ f, f ∉ W → q f ≠ 0 := fun f hf h => hf (hPW (by
    rwa [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h))
  have hnz : ∀ v, v ∉ W → Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) := fun v hv =>
    mem_nonZeroDivisors_of_ne_zero fun h => hv (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))

  have hfrac : ∀ u v a, IsMultiHomog u a → IsMultiHomog v a → v ∉ W → q u / q v ∈ locRing P W := by
    intro u v a hu hv hvW
    refine Subring.subset_closure ⟨u, v, a, hnz v hvW, hvW, hu, hv, ?_⟩
    rw [IsFractionRing.mk'_eq_div]
    rfl
  choose c hc using hrel

  let g : (Σ k, ι k) → L := fun p => q (X p) / q (X ⟨p.1, c p.1⟩)
  let B : Subring L := Subring.closure (Set.range g)
  have hTB : Subring.closure ((Finset.univ.image g : Finset L) : Set L) = B := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hBS : B ≤ locRing P W := Subring.closure_le.mpr (by
    rintro _ ⟨p, rfl⟩
    exact hfrac _ _ _ (AvoidRing.isMultiHomog_X p.1 p.2) (AvoidRing.isMultiHomog_X p.1 (c p.1)) (hc p.1))
  let θ : MRing ι →+* L := eval₂Hom (Int.castRingHom L) g
  have hθB : ∀ f, θ f ∈ B := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => rw [eval₂Hom_C, eq_intCast]; exact intCast_mem _ r
    | add f₁ f₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul_X f p hf => rw [map_mul, eval₂Hom_X']; exact mul_mem hf (Subring.subset_closure ⟨p, rfl⟩)

  have hkey : ∀ u a, IsMultiHomog u a → q u = θ u * q (∏ k, X ⟨k, c k⟩ ^ a k) := by
    intro u a hu
    conv_lhs => rw [u.as_sum]
    conv_rhs => rw [u.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.sum_mul, map_prod]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hT : ∏ k, q (X ⟨k, c k⟩ ^ a k) = ∏ p : Σ k, ι k, q (X ⟨p.1, c p.1⟩) ^ m p := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show q (X ⟨k, c k⟩ ^ a k) = ∏ y, q (X ⟨k, c k⟩) ^ m ⟨k, y⟩
      rw [map_pow, Finset.prod_pow_eq_pow_sum, hu m hm k]
    have hθm : θ (monomial m (AddMonoidAlgebra.coeff u m)) = ((AddMonoidAlgebra.coeff u m : ℤ) : L) * ∏ p, g p ^ m p := by
      rw [show θ _ = eval₂ (Int.castRingHom L) g _ from rfl, eval₂_monomial, eq_intCast,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    have hqm : q (monomial m (AddMonoidAlgebra.coeff u m)) = ((AddMonoidAlgebra.coeff u m : ℤ) : L) * ∏ p, q (X p) ^ m p := by
      rw [monomial_eq, map_mul, map_finsuppProd, Finsupp.prod_fintype _ _ (fun _ => by simp)]
      simp only [map_pow]
      congr 1
      exact eq_intCast (q.comp C) _
    rw [hT, hθm, hqm, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← mul_pow]
    congr 1
    exact (div_mul_cancel₀ _ (hq _ (hc p.1))).symm
  refine ⟨Finset.univ.image g, hTB ▸ hBS, fun z hz => ?_⟩
  rw [hTB]
  obtain ⟨u, v, a, hu, hv, hvW, hzv⟩ := LocRingFrac.proof K ι P W hP hW hPW z hz
  have hTW := AvoidRing.coordProd_not_mem hW c hc a
  have hu' := hkey u a hu
  have hv' := hkey v a hv
  have hinv := hfrac _ v a (AvoidRing.isMultiHomog_coordProd c a) hv hvW
  have hθv : θ v ≠ 0 := fun h => hq v hvW (by rw [hv', h, zero_mul])
  refine ⟨θ u, hθB u, θ v, hθB v, hθv, ?_, ?_⟩
  · have he : (θ v)⁻¹ = q (∏ k, X ⟨k, c k⟩ ^ a k) / q v := by
      rw [eq_div_iff (hq v hvW), hv', ← mul_assoc, inv_mul_cancel₀ hθv, one_mul]
    rw [he]
    exact hinv
  · apply mul_right_cancel₀ (hq _ hTW)
    rw [mul_assoc, ← hv', ← hu']
    exact hzv

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PfAtZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem pfAt_zero (hAI3 : PushforwardArithIntersection.Statement) (I : AllFam) (hI : I.IsFamily) : PFAt I 0 := by
  intro K _ ι _ K' _ ι' _ κ v P' d G J L L' N hv hP' hP hJ hL hL' _
  have hN : (fun j => fibreDeg κ (N j).a) = (Fin.elim0 : Fin 0 → FibreBlock κ → ℤ) :=
    funext fun j => j.elim0
  have hA : Fin.append L' N = L' := funext fun j => by
    rw [Fin.append_right_nil L' N rfl]
    rfl
  rw [hN, hA]
  exact hAI3 I hI K ι K' ι' κ v P' d G J L L' hv hP' hP hJ hL hL'

theorem PushforwardProjLineFlag.proof (hAI3 : PushforwardArithIntersection.Statement) (hStep : PFStep.Statement) : PushforwardProjLineFlag.Statement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d r
  have key : ∀ r, PFAt I r := fun r =>
    Nat.rec (pfAt_zero hAI3 I hI) (fun r h => hStep I hI r h) r
  exact key r K ι K' ι' κ v P' d

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFIntZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFIntZero.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d r : ℕ)
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι')
    (A : HermLine ι') (s : MRing ι'),
    IsBlockMap κ v → IsArithVar P' (d + r + 1) → IsArithVar (imageZ v P') d →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
    arInt P' s A (Fin.append L' N) = 0

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFSecRed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFSecAt (I : AllFam) (r : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin (r + 1) → HermLine ι')
    (s : MRing ι') (a : K' → ℕ),
    IsBlockMap κ v → IsArithVar P' (d + (r + 1)) → IsArithVar (imageZ v P') d → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
    (∀ k, (N (Fin.last r)).a k = a k) → IsMultiHomog s a → s ∉ P' →
    I K' ι' P' (d + (r + 1)) (Fin.append L' N) =
      (J (fibreIdeal κ G) (r + 1) (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L

def PFSecRed.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ r : ℕ, PFSecAt I r → PFAt I (r + 1)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Inter
end

