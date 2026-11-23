module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagGrassPush
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem isSmoothHerm_fsHerm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (a : K → ℤ) :
    IsSmoothHerm (fsHerm ι a) := by
  unfold IsSmoothHerm
  have hfun : (fsHerm ι a).h = fun z => ∏ k, (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ ((a k : ℝ) / 2) := rfl
  rw [hfun]
  refine contDiffOn_prod fun k _ => ContDiffOn.rpow_const_of_ne ?_ fun z hz => ?_
  · exact (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, ι k))).contDiffOn
  · obtain ⟨i, hi⟩ := hz k
    exact (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩).ne'

theorem plToIncr_injective {j m N s : ℕ} (hs : s = j) (hN : j + m = N) :
    Function.Injective (plToIncr (m := m) hs hN) := by
  intro I I' h
  have h1 : ∀ a, I.1.orderEmbOfFin I.2 a = I'.1.orderEmbOfFin I'.2 a := by
    intro a
    have := congrArg (fun A : PlueckerData.Incr s N => A.1 (Fin.cast hs.symm a)) h
    simp only [plToIncr, Fin.cast_cast, Fin.cast_eq_self] at this
    exact Fin.cast_injective hN this
  apply Subtype.ext
  apply Finset.coe_injective
  rw [← Finset.range_orderEmbOfFin I.1 I.2, ← Finset.range_orderEmbOfFin I'.1 I'.2]
  exact congrArg Set.range (funext h1)

theorem plToIncr_surjective {j m N s : ℕ} (hs : s = j) (hN : j + m = N) :
    Function.Surjective (plToIncr (m := m) hs hN) := by
  intro A
  let g : Fin j → Fin (j + m) := fun a => Fin.cast hN.symm (A.1 (Fin.cast hs.symm a))
  have hg : StrictMono g := fun a b hab => by
    simp only [g, Fin.lt_def, Fin.val_cast]
    exact A.2 (by rw [Fin.lt_def] at hab ⊢; simpa using hab)
  have hcard : (Finset.univ.map ⟨g, hg.injective⟩).card = j := by simp
  refine ⟨⟨_, hcard⟩, ?_⟩
  have hu : g = (Finset.univ.map ⟨g, hg.injective⟩).orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard (fun x => by simp) hg
  apply Subtype.ext
  funext a
  show Fin.cast hN ((Finset.univ.map ⟨g, hg.injective⟩).orderEmbOfFin hcard (Fin.cast hs a)) = A.1 a
  rw [← hu]
  simp [g]

def plIncrEquiv {j m N s : ℕ} (hs : s = j) (hN : j + m = N) : PlIdx j m ≃ PlueckerData.Incr s N :=
  Equiv.ofBijective _ ⟨plToIncr_injective hs hN, plToIncr_surjective hs hN⟩

section Proj

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

omit [DecidableEq Ψ] in
theorem isBlockMap_grFl (hj : 1 ≤ j) (hjN : j ≤ N - 1) :
    IsBlockMap (grFlKappa Ψ N j hj hjN) (grFlV Ψ N j hj hjN) := by
  have hκ : Function.Injective (grFlKappa Ψ N j hj hjN) := fun t t' h =>
    (Fintype.equivFin Ψ).symm.injective (congrArg Prod.fst h)
  refine ⟨hκ, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨t, I⟩ ⟨t', I'⟩ h
    simp only [grFlV, Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    obtain rfl := hκ h1
    obtain rfl := plToIncr_injective _ _ (eq_of_heq h2)
    rfl
  · rintro ⟨q, A⟩ ⟨t, rfl⟩
    obtain ⟨I, hI⟩ := plToIncr_surjective (m := N - j) (N := N)
      (s := ((grFlKappa Ψ N j hj hjN t).2 : ℕ) + 1) (by show j - 1 + 1 = j; omega) (by omega) A
    exact ⟨⟨t, I⟩, congrArg (Sigma.mk _) hI⟩

theorem linDeg_muForm_apply (τ : Ψ) (i : Fin (N - 1)) :
    linDeg Ψ N (muForm Ψ N j) (τ, i) = if (i : ℕ) + 1 = j then -1 else 0 := by
  have hi := i.isLt
  unfold linDeg
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single τ (fun τ' hτ' => by
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [xDeg, Ne.symm hτ'])]
  simp only [xDeg, if_true, mul_sub]
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ a : Fin N, muForm Ψ N j (τ, a) * (if (i : ℕ) = a then 1 else 0) =
      if (i : ℕ) < j then 0 else 1 := by
    rw [Fintype.sum_eq_single ⟨i, by omega⟩]
    · simp [muForm]
    · intro a ha
      have : (i : ℕ) ≠ a := fun h => ha (Fin.ext h.symm)
      simp [this]
  have h2 : ∑ a : Fin N, muForm Ψ N j (τ, a) * (if (i : ℕ) + 1 = a then 1 else 0) =
      if (i : ℕ) + 1 < j then 0 else 1 := by
    rw [Fintype.sum_eq_single ⟨(i : ℕ) + 1, by omega⟩]
    · simp [muForm]
    · intro a ha
      have : (i : ℕ) + 1 ≠ a := fun h => ha (Fin.ext h.symm)
      simp [this]
  rw [h1, h2]
  split_ifs <;> omega

theorem linDeg_muForm (hj : 1 ≤ j) (hjN : j ≤ N - 1) :
    linDeg Ψ N (muForm Ψ N j) = pullDeg (grFlKappa Ψ N j hj hjN) (fun _ => -1) := by
  have hκ : Function.Injective (grFlKappa Ψ N j hj hjN) := (isBlockMap_grFl hj hjN).1
  funext ⟨τ, i⟩
  rw [linDeg_muForm_apply]
  unfold pullDeg
  by_cases h : (i : ℕ) + 1 = j
  · have hq : (τ, i) = grFlKappa Ψ N j hj hjN (Fintype.equivFin Ψ τ) := by
      simp only [grFlKappa, Equiv.symm_apply_apply, Prod.mk.injEq, true_and]
      exact Fin.ext (by simp; omega)
    rw [if_pos h, hq, hκ.extend_apply]
  · rw [if_neg h, Function.extend_apply']
    · rfl
    · rintro ⟨t, ht⟩
      apply h
      have := congrArg (fun q : FlBlock Ψ N => (q.2 : ℕ)) ht
      simp only [grFlKappa] at this
      omega

theorem isPullHerm_mu (hj : 1 ≤ j) (hjN : j ≤ N - 1) :
    IsPullHerm (grFlKappa Ψ N j hj hjN) (grFlV Ψ N j hj hjN)
      (fsHerm (plBlocks (Fintype.card Ψ) j (N - j)) (fun _ => -1)) (linLine Ψ N (muForm Ψ N j)) := by
  refine ⟨linDeg_muForm hj hjN, fun z => ?_⟩
  show refNorm (linDeg Ψ N (muForm Ψ N j)) z = refNorm (fun _ => (-1 : ℤ)) (fun p => z (grFlV Ψ N j hj hjN p))
  unfold refNorm
  rw [Fintype.prod_prod_type]
  refine (Equiv.prod_comp (Fintype.equivFin Ψ).symm _).symm.trans (Finset.prod_congr rfl fun t _ => ?_)
  have hlt : j - 1 < N - 1 := by omega
  rw [Fintype.prod_eq_single ⟨j - 1, hlt⟩ (fun i hi => by
    rw [linDeg_muForm_apply, if_neg (fun h => hi (Fin.ext (by simp; omega)))]
    simp)]
  rw [linDeg_muForm_apply, if_pos (by simp; omega)]
  congr 1
  exact (Equiv.sum_comp (plIncrEquiv (m := N - j) (N := N) (s := j - 1 + 1) (by omega) (by omega))
    (fun A => ‖z ⟨((Fintype.equivFin Ψ).symm t, ⟨j - 1, hlt⟩), A⟩‖ ^ 2)).symm

end Proj

section Forms

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ)

omit [DecidableEq Ψ] in
theorem linForm_muForm : linForm Ψ N (muForm Ψ N j) = muPoly Ψ N j := by
  unfold linForm muPoly muForm
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

theorem linForm_vandForm (t : VandPair Ψ N j) :
    linForm Ψ N (vandForm Ψ N j t) = X (t.1.1, t.1.2.1) - X (t.1.1, t.1.2.2) := by
  simp only [linForm, vandForm, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, sub_smul,
    Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def vandPairEquiv :
    Ψ × {ab : Fin N × Fin N // ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)} ≃ VandPair Ψ N j where
  toFun x := ⟨(x.1, x.2.1), x.2.2⟩
  invFun t := (t.1.1, ⟨t.1.2, t.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

theorem prod_vandForm :
    ∏ i : Fin (vandCount Ψ N j), linForm Ψ N (vandForm Ψ N j ((Fintype.equivFin (VandPair Ψ N j)).symm i)) =
      vandBlocks Ψ N j := by
  refine (Equiv.prod_comp (Fintype.equivFin (VandPair Ψ N j)).symm
    (fun t => linForm Ψ N (vandForm Ψ N j t))).trans ?_
  have hB : ∏ x : Ψ × {ab : Fin N × Fin N // ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)},
      (X (x.1, x.2.1.1) - X (x.1, x.2.1.2) : RootPoly Ψ N) =
      ∏ t : VandPair Ψ N j, linForm Ψ N (vandForm Ψ N j t) :=
    Fintype.prod_equiv (vandPairEquiv Ψ N j) _ (fun t => linForm Ψ N (vandForm Ψ N j t))
      (fun x => (linForm_vandForm Ψ N j (vandPairEquiv Ψ N j x)).symm)
  rw [← hB]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Finset.prod_subtype (p := fun ab : Fin N × Fin N => ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))
    (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)))
    (fun ab => by simp) (fun ab => (X (τ, ab.1) - X (τ, ab.2) : RootPoly Ψ N))]

def faForms : Fin (dimN Ψ N j + 1 + vandCount Ψ N j) → Ψ × Fin N → ℤ :=
  Fin.append (fun _ => muForm Ψ N j) (fun i => vandForm Ψ N j ((Fintype.equivFin (VandPair Ψ N j)).symm i))

theorem FA_eq_prod (cf : ℚ) : FA Ψ N j cf = C cf * ∏ i, linForm Ψ N (faForms Ψ N j i) := by
  rw [Fin.prod_univ_add]
  simp only [faForms, Fin.append_left, Fin.append_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    linForm_muForm, prod_vandForm]
  unfold FA fib
  ring

theorem linLine_faForms :
    (fun i => linLine Ψ N (faForms Ψ N j i)) =
      Fin.append (fun _ : Fin (dimN Ψ N j + 1) => linLine Ψ N (muForm Ψ N j)) (vandLine Ψ N j) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [faForms]
  · simp [faForms, vandLine]

theorem flagInt_C_mul (c : ℚ) (P : RootPoly Ψ N) : flagInt Ψ N (C c * P) = c * flagInt Ψ N P := by
  have h : antisym Ψ N (C c * P) = C c * antisym Ψ N P := by
    unfold antisym
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_mul, rename_C, mul_smul_comm]
  unfold flagInt
  rw [h, coeff_C_mul]

end Forms

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPlueckerSpan
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace PlueckerSpan

theorem sum_prod_mul_det_indicator {R : Type} [CommRing R] {s N : ℕ} (M : Matrix (Fin s) (Fin N) R)
    (t : Fin s → Fin N) :
    ∑ c : Fin s → Fin N, (∏ a, M a (c a)) *
        (Matrix.of fun a j => if c a = t j then (1 : R) else 0).det =
      (Matrix.of fun a j => M a (t j)).det := by
  classical
  have hrow : (Matrix.of fun a j => M a (t j)) =
      fun a => ∑ b, M a b • fun j => if b = t j then (1 : R) else 0 := by
    ext a j
    simp [Finset.sum_apply]
  rw [hrow]
  change _ = Matrix.detRowAlternating _
  have h1 := (Matrix.detRowAlternating (R := R) (n := Fin s)).toMultilinearMap.map_sum
    (fun a b => M a b • fun j => if b = t j then (1 : R) else 0)
  simp only [AlternatingMap.coe_multilinearMap] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h2 := (Matrix.detRowAlternating (R := R) (n := Fin s)).toMultilinearMap.map_smul_univ
    (fun a => M a (c a)) (fun a j => if c a = t j then (1 : R) else 0)
  simp only [AlternatingMap.coe_multilinearMap, smul_eq_mul] at h2
  rw [h2]
  rfl

theorem sum_prod_mul_apply_eq {Ω R E : Type} [Field Ω] [CommRing R] [Algebra Ω R] [AddCommGroup E] [Module Ω E]
    {s N : ℕ} (e : Module.Basis (Fin N) Ω E) (M : Matrix (Fin s) (Fin N) R)
    (φ : Module.Dual Ω (⋀[Ω]^s E)) :
    ∑ c : Fin s → Fin N, (∏ a, M a (c a)) * algebraMap Ω R (φ (exteriorPower.ιMulti Ω s (e ∘ c))) =
      ∑ T : Set.powersetCard (Fin N) s, algebraMap Ω R (φ (e.exteriorPower s T)) *
        (Matrix.of fun a j => M a (Set.powersetCard.ofFinEmbEquiv.symm T j)).det := by
  classical
  have hc : ∀ c : Fin s → Fin N, algebraMap Ω R (φ (exteriorPower.ιMulti Ω s (e ∘ c))) =
      ∑ T : Set.powersetCard (Fin N) s, algebraMap Ω R (φ (e.exteriorPower s T)) *
        (Matrix.of fun a j => if c a = Set.powersetCard.ofFinEmbEquiv.symm T j then (1 : R) else 0).det := by
    intro c
    conv_lhs => rw [← (e.exteriorPower s).sum_repr (exteriorPower.ιMulti Ω s (e ∘ c))]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [map_smul, smul_eq_mul, map_mul, mul_comm, exteriorPower.basis_repr_apply,
      exteriorPower.ιMultiDual_apply_ιMulti, RingHom.map_det]
    congr 2
    ext a j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Function.comp_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  simp_rw [hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← sum_prod_mul_det_indicator M, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem span_eq_top_of_dual {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {s N M : ℕ}
    (b : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω (⋀[Ω]^s E))
    (h : ∀ A : Fin s → Fin N, StrictMono A → ∃ a : Fin M → Ω, ∀ A' : Fin s → Fin N, StrictMono A' →
      ∑ m, a m * φ m (exteriorPower.ιMulti Ω s (b ∘ A')) = if A' = A then 1 else 0) :
    Submodule.span Ω (Set.range φ) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.2 fun ψ => ?_
  rw [← (b.exteriorPower s).sum_dual_apply_smul_coord ψ]
  refine Submodule.sum_mem _ fun T _ => Submodule.smul_mem _ _ ?_
  obtain ⟨a, ha⟩ := h _ (Set.powersetCard.ofFinEmbEquiv.symm T).strictMono
  have hT : (b.exteriorPower s).coord T = ∑ m, a m • φ m := by
    refine (b.exteriorPower s).ext fun T' => ?_
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, smul_eq_mul, exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    rw [ha _ (Set.powersetCard.ofFinEmbEquiv.symm T').strictMono, Finsupp.single_apply]
    have hiff : ((Set.powersetCard.ofFinEmbEquiv.symm T' : Fin s → Fin N) =
        Set.powersetCard.ofFinEmbEquiv.symm T) ↔ T' = T := by
      constructor
      · intro h'
        exact Set.powersetCard.ofFinEmbEquiv.symm.injective (DFunLike.coe_injective h')
      · rintro rfl
        rfl
    by_cases hTT : T' = T
    · rw [if_pos hTT, if_pos (hiff.2 hTT)]
    · rw [if_neg hTT, if_neg (fun h' => hTT (hiff.1 h'))]
  rw [hT]
  exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

end PlueckerSpan

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBirationalRatioClosure
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def BirationalRatioClosure.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω)
    (c : ∀ k, ι k), Birational y → (∀ k, y ⟨k, c k⟩ ≠ 0) → Subfield.closure (coneRatios y c) = ⊤

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagRatioTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def FlagRatioTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) [Fintype Ψ] (n : ℕ),
    Algebra.trdeg F (IntermediateField.adjoin F (Set.range (flagMinorRatio F Ψ n))) =
      ((Fintype.card Ψ * GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.flagDim n : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFnFieldTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def FnFieldTrdeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω)
    (d : ℕ), Birational y → IsArithVar (mCoordIdeal y) (d + 1) → Algebra.trdeg ℤ Ω = d

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsGenLeadMinorNeZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def GenLeadMinorNeZero.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) (a : Fin (n - 1)), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor (genMatFr F Ψ n τ) a ≠ 0

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagMinorTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def genMat0Fr (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (τ : Ψ) : Matrix (Fin n) (Fin n) (GenFrac F Ψ n) :=
  Matrix.of fun a b => if (a : ℕ) < j ∧ j ≤ (b : ℕ) then 0 else genMatFr F Ψ n τ a b

def flagMinorRatio0 (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (q : Ψ × Σ i : Fin (n - 1), PluckerBlocks n n i) :
    GenFrac F Ψ n :=
  flagMinor (genMat0Fr F Ψ n j q.1) q.2.1 q.2.2 / GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor (genMat0Fr F Ψ n j q.1) q.2.1

def HodgeFlagMinorTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) [Fintype Ψ] (n j : ℕ), j ≤ n →
    Algebra.trdeg F (IntermediateField.adjoin F (Set.range (flagMinorRatio0 F Ψ n j))) =
      ((Fintype.card Ψ * (j * (j - 1) / 2 + (n - j) * (n - j - 1) / 2) : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPivotMinorFlag
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def PivotMinorFlag.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n), (a : ℕ) ≤ b →
    ∃ S : PluckerBlocks n n a, pivotMinor M a b = flagMinor M a S

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRatioFieldSpan
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def RatioFieldSpan.Statement : Prop :=
  ∀ (F M : Type) [Field F] [Field M] [Algebra F M] (I J : Type) (u : I → M) (w : J → M) (v v' : M),
    Submodule.span F (Set.range u) = Submodule.span F (Set.range w) →
    v ∈ Submodule.span F (Set.range u) → v' ∈ Submodule.span F (Set.range u) → v ≠ 0 → v' ≠ 0 →
    IntermediateField.adjoin F (Set.range fun i => u i / v) = IntermediateField.adjoin F (Set.range fun j => w j / v')

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

