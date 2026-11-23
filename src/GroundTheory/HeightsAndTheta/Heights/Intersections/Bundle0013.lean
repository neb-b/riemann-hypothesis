module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0008

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ConservationDegreeFormOfExistence
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace Conservation

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem ptsIntegral_const {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs <;> simp
  · simp


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem C_not_mem {P : Ideal (MRing ι)} (hP : IsHorizontal P) {a : ℤ} (ha : a ≠ 0) : C a ∉ P := by
  intro h
  have : a ∈ P.comap (C : ℤ →+* MRing ι) := Ideal.mem_comap.mpr h
  rw [show P.comap (C : ℤ →+* MRing ι) = ⊥ from hP, Ideal.mem_bot] at this
  exact ha this


omit [Fintype K] in
theorem isMultiHomog_C (a : ℤ) : IsMultiHomog (C a : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h; simp
  · exact absurd rfl hm


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem comap_eq_of_mem {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    W.comap (C : ℤ →+* MRing ι) = Ideal.span {(p : ℤ)} := by
  have hWp : W.IsPrime := hW.1.1.1
  have hpW : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) :=
    Ideal.mem_comap.mpr (hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  have hmax := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  exact (hmax.eq_of_le (Ideal.IsPrime.comap C).ne_top
    ((Ideal.span_singleton_le_iff_mem _).mpr hpW)).symm


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem not_horizontal {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    ¬ IsHorizontal W := by
  intro h
  have := comap_eq_of_mem hp hW
  rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from h, eq_comm, Ideal.span_singleton_eq_bot] at this
  exact hp.ne_zero (by exact_mod_cast this)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem charOf_eq {P W : Ideal (MRing ι)} {p : ℕ} (hp : p.Prime) (hW : W ∈ divSupp P (C (p : ℤ))) :
    charOf W = p := by
  have h := comap_eq_of_mem hp hW
  unfold charOf
  have hg : Ideal.span {Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))} =
      Ideal.span {(p : ℤ)} := by
    rw [← h]; exact Submodule.IsPrincipal.span_singleton_generator _
  rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at hg
  simpa using hg

theorem vertR_C_prime (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) {p : ℕ} (hp : p.Prime) :
    vertR P L (C (p : ℤ)) = Real.log p * ∑ V ∈ (divSupp_finite P (C (p : ℤ))).toFinset,
      (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum n V (fun j => (L j).a) : ℝ) := by
  unfold vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Set.Finite.mem_toFinset] at hV
  rw [if_neg (not_horizontal hp hV), charOf_eq hp hV]
  ring

end Conservation

theorem Conservation.statement_holds : Conservation.Statement := by
  unfold Conservation.Statement ConservationStatement
  intro K _ ι _ I hI P n L p hP hL hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hA : IsSmoothHerm (constLine (ι := ι) (-Real.log p)) := contDiffOn_const
  have ha : ∀ k, (constLine (ι := ι) (-Real.log p)).a k = ((0 : K → ℕ) k : ℤ) := fun _ => rfl
  have hpot : (fun j z => Real.log ((L j).h z)) = pot L := rfl
  constructor
  · rw [hI.2.2 P n L _ (C (p : ℤ)) 0 hP hL hA ha (Conservation.isMultiHomog_C _)
      (Conservation.C_not_mem hP.2.2.1 (by exact_mod_cast hp.ne_zero))]
    have hlog : logNorm (constLine (ι := ι) (-Real.log p)) (C (p : ℤ)) = fun _ => 0 := by
      funext z
      show Real.log (‖eval z (map (Int.castRingHom ℂ) (C (p : ℤ)))‖ / Real.exp (-(-Real.log p))) = 0
      rw [map_C, eval_C, neg_neg, Real.exp_log hp0]
      simp [hp0.ne']
    unfold recR vertR arInt
    rw [hlog, Conservation.ptsIntegral_const, zero_mul, sub_zero]
    refine finsum_mem_congr rfl fun W hW => ?_
    rw [if_neg (Conservation.not_horizontal hp hW), if_neg (Conservation.not_horizontal hp hW)]
  · rw [hI.2.2 P n L _ (C 1) 0 hP hL hA ha (Conservation.isMultiHomog_C _)
      (Conservation.C_not_mem hP.2.2.1 one_ne_zero)]
    have hlog : logNorm (constLine (ι := ι) (-Real.log p)) (C 1) = fun _ => -Real.log p := by
      funext z
      show Real.log (‖eval z (map (Int.castRingHom ℂ) (C 1))‖ / Real.exp (-(-Real.log p))) = _
      rw [map_C, eval_C, neg_neg, Real.exp_log hp0]
      simp [Real.log_inv]
    have hempty : divSupp P (C 1 : MRing ι) = ∅ := by
      ext W
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hW
      have hle := hW.1.1.2
      rw [C_1, Ideal.span_singleton_one, sup_top_eq, top_le_iff] at hle
      exact hW.1.1.1.ne_top hle
    unfold recR arInt
    rw [hempty, finsum_mem_empty, hlog, Conservation.ptsIntegral_const, hpot]
    ring

theorem Conservation.conservation_degree_form_of_existence (hE : ThmIExists.Statement) (hC : Conservation.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Conservation.Statement := by
  intro K _ ι _ P n L p hP hL hp
  obtain ⟨I, hI⟩ := hE
  obtain ⟨h1, h2⟩ := hC K ι (I K ι) (hI K ι) P n L p hP hL hp
  have h := h1.symm.trans h2
  rw [Conservation.vertR_C_prime P L hp] at h
  exact mul_left_cancel₀ (Real.log_pos (by exact_mod_cast hp.one_lt)).ne' h

theorem Conservation.conservation_iff_degree_statement :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Conservation.Statement ↔ DegreeStatement := by
  constructor
  · intro h K _ ι _ P e L p hP hL hp
    rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)]
    exact (h K ι P e L p hP hL hp).symm
  · intro h K _ ι _ P e L p hP hL hp
    have h' := h K ι P e L p hP hL hp
    rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)] at h'
    exact h'.symm

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.DeEqZeroOfSemiPosOff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {n : ℕ}
  {A A' : HermLine ι} {s s' : MRing ι}

theorem De_eq_zero_of_semiPos (hLe : DeLeSemiPos.Statement) {L : Fin n → HermLine ι}
    (hP : IsArithVar P (n + 2)) (hL : ∀ j, IsSmoothHerm (L j)) (hLp : ∀ j, IsSemiPosHerm (L j))
    (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') (hs : IsSectionOn P A s) (hs' : IsSectionOn P A' s')
    (hnc : ∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) :
    De P L A A' s s' = 0 := by
  have h1 := hLe K ι P n L A A' s s' hP hL hLp hA hA' hs hs' hnc
  have h2 := hLe K ι P n L A' A s' s hP hL hLp hA' hA hs' hs (fun W h h' => hnc W h' h)
  rw [De_swap] at h2
  linarith

theorem De_eq_zero_of_semiPos_off (hAdd : DeSlotAdd.Statement) (hTw : SemiPosTwist.Statement)
    (hLe : DeLeSemiPos.Statement) (hP : IsArithVar P (n + 2)) (hA : IsSmoothHerm A)
    (hA' : IsSmoothHerm A') (hs : IsSectionOn P A s) (hs' : IsSectionOn P A' s')
    (hnc : ∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) (S : Finset (Fin n)) :
    ∀ L : Fin n → HermLine ι, (∀ j, IsSmoothHerm (L j)) → (∀ j, j ∉ S → IsSemiPosHerm (L j)) →
      De P L A A' s s' = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro L hL hLp
    exact De_eq_zero_of_semiPos hLe hP hL (fun j => hLp j (Finset.notMem_empty j)) hA hA' hs hs' hnc
  | @insert j S hj ih =>
    intro L hL hLp
    obtain ⟨T, hT, hTp, hLTp⟩ := hTw K ι (L j) (hL j)
    have hadd := hAdd K ι P n L j (L j) T A A' s s' hP hL (hL j) hT hA hA' hs hs' hnc
    rw [Function.update_eq_self] at hadd
    have hsm : ∀ X : HermLine ι, IsSmoothHerm X → ∀ i, IsSmoothHerm (Function.update L j X i) := by
      intro X hX i
      rcases eq_or_ne i j with rfl | hij
      · simpa using hX
      · rw [Function.update_of_ne hij]
        exact hL i
    have hpos : ∀ X : HermLine ι, IsSemiPosHerm X → ∀ i, i ∉ S →
        IsSemiPosHerm (Function.update L j X i) := by
      intro X hX i hi
      rcases eq_or_ne i j with rfl | hij
      · simpa using hX
      · rw [Function.update_of_ne hij]
        exact hLp i (by simp [Finset.mem_insert, hij, hi])
    rw [ih _ (hsm _ (isSmoothHerm_tensor (hL j) hT)) (hpos _ hLTp),
      ih _ (hsm _ hT) (hpos _ hTp)] at hadd
    linarith

theorem ProjectiveLineTwo.proof (hAdd : DeSlotAdd.Statement) (hTw : SemiPosTwist.Statement)
    (hLe : DeLeSemiPos.Statement) : SectionSpaceSymmetry := by
  intro K _ ι _ P n L A A' s s' hP hL hA hA' hs hs' hnc
  have h := De_eq_zero_of_semiPos_off hAdd hTw hLe hP hA hA' hs hs' hnc Finset.univ L hL
    (fun j hj => absurd (Finset.mem_univ j) hj)
  unfold De at h
  linarith

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ExMap
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

def pointFormEuler_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι) (n : ℕ)
    (F : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y x : Fin n → ℂ) (c : K → ℂ),
    IsSmoothHerm A → AnalyticAt ℂ F y → (∀ k, ∃ i, F y ⟨k, i⟩ ≠ 0) → fderiv ℂ F y x = bsmul c (F y) →
    cxHessian (fun y' => Real.log (A.h (F y'))) y *ᵥ star x = 0

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ExMapAlt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

def pointFormRank_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (d n : ℕ)
    (F : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y : Fin n → ℂ),
    IsArithVar Q d → d ≤ n → AnalyticAt ℂ F y → (∀ᶠ y' in 𝓝 y, F y' ∈ mcPts Q) →
    ∃ x : Fin n → ℂ, x ≠ 0 ∧ ∃ c : K → ℂ, fderiv ℂ F y x = bsmul c (F y)

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityDehomogenization_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s t : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (y : FractionRing (MRing ι ⧸ P)),
    IsMultiProjPrime P → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → IsMultiHomog t a → t ∉ W →
    y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) →
    y ∈ locRing P W ∧
      multAt (P ⊔ Ideal.span {s}) W = (Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y)).toNat

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityLocalDimension_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s →
    IsLocalRing (locRing P W) ∧ IsNoetherianRing (locRing P W) ∧ ringKrullDim (locRing P W) = 1

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityFunctionFieldNumber.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∃ hF : IsField (funField P), @NumberField (funField P) hF.toField

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityDivisorSupportClosed.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (s : MRing ι) (a : K → ℕ)
    (W : Ideal (MRing ι)),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → (W ∈ divSupp P s ↔ IsClosedPt W ∧ P ≤ W ∧ s ∈ W)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityLocalResidue_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (b : Fin 0 → K → ℤ),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → ∀ [IsLocalRing (locRing P W)],
    Finite (IsLocalRing.ResidueField (locRing P W)) ∧
      Nat.card (IsLocalRing.ResidueField (locRing P W)) = charOf W ^ (geoNum 0 W b).toNat

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityLocalCardinality_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (b : Fin 0 → K → ℤ) (y : FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → y ∈ locRing P W → y ≠ 0 →
    ((Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y)).toNat : ℝ) *
        ((geoNum 0 W b : ℝ) * Real.log (charOf W)) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W y))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityDenominator.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (x : funField P),
    IsArithVar P 1 → ∃ c : funField P, c ≠ 0 ∧ ∀ W, IsClosedPt W → P ≤ W →
      (c : FractionRing (MRing ι ⧸ P)) ∈ locRing P W ∧ ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) ∈ locRing P W

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermTensor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isSmoothHerm_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  ContDiffOn.mul hA hB

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end

