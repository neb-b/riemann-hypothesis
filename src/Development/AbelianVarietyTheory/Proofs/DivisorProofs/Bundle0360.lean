module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0329
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrismChainComplexBoundaryIdentities

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemOmAOfMemRA
section
set_option autoImplicit false

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

section DualMono

variable {k : Type} [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} {x : Fin (d + 1) → F}

theorem rA_le_of_subset {I J : Finset (Fin (d + 1))} (h : I ⊆ J) : rA k x I ≤ rA k x J := by
  refine Algebra.adjoin_mono ?_
  rintro y ⟨i, hi, j, rfl⟩
  exact ⟨i, h hi, j, rfl⟩

theorem div_mem_rA_of_mem {J : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ J) (j : Fin (d + 1)) :
    x j / x i ∈ rA k x J :=
  Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

theorem mem_omA_iff_mul {I : Finset (Fin (d + 1))} {y : F} :
    y ∈ omA k x I ↔ ∀ i ∈ I, (∏ j, x i / x j) * y ∈ rA k x I := by
  simp [omA, Submodule.mem_iInf]

theorem mul_mem_omA_of_mem_rA {J : Finset (Fin (d + 1))} {r y : F} (hr : r ∈ rA k x J) (hy : y ∈ omA k x J) :
    r * y ∈ omA k x J := by
  rw [mem_omA_iff_mul] at hy ⊢
  intro i hi
  rw [mul_left_comm]
  exact (rA k x J).mul_mem hr (hy i hi)

theorem omA_le_of_subset (hx : ∀ i, x i ≠ 0) {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (h : I ⊆ J) :
    omA k x I ≤ omA k x J := by
  obtain ⟨i₀, hi₀⟩ := hI
  intro y hy
  rw [mem_omA_iff_mul] at hy ⊢
  intro i hi
  have e : (∏ j, x i / x j) = (x i / x i₀) ^ (d + 1) * ∏ j, x i₀ / x j := by
    have hc : (x i / x i₀) ^ (d + 1) = ∏ _j : Fin (d + 1), (x i / x i₀) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hc, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    field_simp [hx i₀, hx j]
  rw [e, mul_assoc]
  exact (rA k x J).mul_mem ((rA k x J).pow_mem (div_mem_rA_of_mem (h hi₀) i) _) (rA_le_of_subset h (hy i₀ hi₀))

variable {W W' : Type} [AddCommGroup W] [Module F W] [Module k W] [IsScalarTower k F W]
  [AddCommGroup W'] [Module F W'] [Module k W'] [IsScalarTower k F W']

end DualMono

end GlobalTheory.PD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyCyclotomicPrimitiveRootsOfStrictlyHenselStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_cyclotomicPrimitiveRoots_of_strictlyHenselian : ∀ (q : ℕ) (A : Type) [CommRing A], SH A → IsUnit (q : A) → Nonempty (Prim q A) := by
  first | (exact @GlobalTheory.EtC.prim_of_strictlyHenselian) | (exact GlobalTheory.EtC.prim_of_strictlyHenselian) | (intros; apply GlobalTheory.EtC.prim_of_strictlyHenselian  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqUniformizerCharacterMulResidueCardPowEqOneStatement
section
open MeasureTheory Matrix ValuativeRel

open GlobalTheory GlobalTheory.HeisUnit in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSq_uniformizer_character_mul_residueCard_pow_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd k n d → φ0 ≠ 0 →
    ∀ (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n),
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ T T' : Fin d → GlobalTheory.SplitFlip.Res (k := k) 1, T ≠ T' →
      ∫ y, Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T') φ0 y) ∂μ = 0) →
    ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 := by
  intro k _ _ _ _ n d ι hinj Tr hTr hTrIso S hS hSiso χ hχ φ0 hφ0 hι0 hne ϖ hϖ i0 horth
  classical
  set F := ∑ T : Fin d → SplitFlip.Res (k := k) 1, Tr (cosetRep ϖ i0 T) φ0 with hF
  have hFSB : F ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k) := Submodule.sum_mem _ fun T _ => (hTr _ φ0 hφ0).1
  have hSg : S (diagAt ϖ i0) φ0 = (χ ϖ : ℂ) • F := by
    apply hinj (hS _ φ0 hφ0) (Submodule.smul_mem _ _ hFSB)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hχ _ φ0 hφ0, map_smul, map_sum, det_diagAt, hι0]
    funext Y
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, (hTr _ φ0 hφ0).2, hι0]
    have hIntInd (M : Matrix (Fin n) (Fin d) k) :
        intInd k n d M = if ∀ i j, M i j ∈ 𝒪[k] then 1 else 0 := by
      simp only [intInd, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    have hSubMem (y : k) (t : SplitFlip.Res (k := k) 1) :
        y - (ϖ : k)⁻¹ * ((Quotient.out t : 𝒪[k]) : k) ∈ 𝒪[k] ↔
          ∃ h : (ϖ : k) * y ∈ 𝒪[k], t = Ideal.Quotient.mk _ ⟨(ϖ : k) * y, h⟩ := by
      have ht : t = Ideal.Quotient.mk _ (Quotient.out t) := (Quotient.out_eq t).symm
      set a := Quotient.out t
      have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
      constructor
      · intro hc
        have hy : (ϖ : k) * y = ϖ * (y - (ϖ : k)⁻¹ * a) + a := by field_simp; ring
        have hmem : (ϖ : k) * y ∈ 𝒪[k] := hy ▸ add_mem (mul_mem hϖ.mem hc) a.2
        refine ⟨hmem, ?_⟩
        rw [ht, Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton']
        refine ⟨-⟨_, hc⟩, Subtype.ext ?_⟩
        push_cast
        field_simp
        ring
      · rintro ⟨h, e⟩
        have e' := ht.symm.trans e
        rw [Ideal.Quotient.eq, pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at e'
        obtain ⟨c, hc⟩ := e'
        have hc' : (c : k) * ϖ = a - ϖ * y := by simpa using congrArg Subtype.val hc
        have hinv : (ϖ : k)⁻¹ * ϖ = 1 := inv_mul_cancel₀ hϖ0
        have : y - (ϖ : k)⁻¹ * a = -(c : k) := by
          linear_combination (ϖ : k)⁻¹ * hc' - (y + c) * hinv
        rw [this]
        exact neg_mem c.2
    have hDiag :
        intInd k n d ((diagAt ϖ i0).valᵀ * Y) =
          ∑ T : Fin d → SplitFlip.Res (k := k) 1, intInd k n d (Y + cosetRep ϖ i0 T) := by
      have hL : ∀ i j, ((diagAt ϖ i0).valᵀ * Y) i j = (if i = i0 then (ϖ : k) else 1) * Y i j := by
        intro i j
        rw [diagAt_val, diagonal_transpose, diagonal_mul]
      have hR : ∀ (T : Fin d → SplitFlip.Res (k := k) 1) i j, (Y + cosetRep ϖ i0 T) i j =
          if i = i0 then Y i j - (ϖ : k)⁻¹ * ((Quotient.out (T j) : 𝒪[k]) : k) else Y i j := by
        intro T i j
        simp only [cosetRep, Matrix.add_apply, Matrix.of_apply]
        split_ifs <;> ring
      by_cases hQR : (∀ i j, i ≠ i0 → Y i j ∈ 𝒪[k]) ∧ ∀ j, (ϖ : k) * Y i0 j ∈ 𝒪[k]
      · obtain ⟨hQ, hRR⟩ := hQR
        let T0 : Fin d → SplitFlip.Res (k := k) 1 := fun j => Ideal.Quotient.mk _ ⟨_, hRR j⟩
        have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 1 := by
          rw [hIntInd, ite_eq_left]
          intro i j
          rw [hL]
          split_ifs with h
          · subst h; exact hRR j
          · rw [one_mul]; exact hQ i j h
        have hs : ∀ T, intInd k n d (Y + cosetRep ϖ i0 T) = if T = T0 then 1 else 0 := by
          intro T
          rw [hIntInd]
          by_cases hT : T = T0
          · rw [ite_eq_left hT, ite_eq_left]
            intro i j
            rw [hR]
            split_ifs with h
            · subst h; exact (hSubMem _ _).2 ⟨hRR j, by rw [hT]⟩
            · exact hQ i j h
          · rw [ite_eq_right hT, ite_eq_right]
            intro hm
            apply hT
            funext j
            have := hm i0 j
            rw [hR, ite_eq_left rfl] at this
            obtain ⟨_, e⟩ := (hSubMem _ _).1 this
            exact e
        rw [hl, Finset.sum_congr rfl (fun T _ => hs T), Finset.sum_ite_eq']
        simp
      · have hl : intInd k n d ((diagAt ϖ i0).valᵀ * Y) = 0 := by
          rw [hIntInd, ite_eq_right]
          intro hm
          refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
          · have := hm i j; rwa [hL, ite_eq_right h, one_mul] at this
          · have := hm i0 j; rwa [hL, ite_eq_left rfl] at this
        rw [hl]
        symm
        apply Finset.sum_eq_zero
        intro T _
        rw [hIntInd, ite_eq_right]
        intro hm
        refine hQR ⟨fun i j h => ?_, fun j => ?_⟩
        · have := hm i j; rwa [hR, ite_eq_right h] at this
        · have := hm i0 j
          rw [hR, ite_eq_left rfl] at this
          exact ((hSubMem _ _).1 this).1
    rw [hDiag]

  let _ : MeasurableSpace (Fin n × Fin d → k) := borel _
  have _ : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → k) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  have hiso := hSiso (diagAt ϖ i0) φ0 hφ0 μ hμ
  rw [hSg] at hiso
  simp only [Pi.smul_apply, smul_eq_mul, eNorm_mul, mul_pow] at hiso
  rw [lintegral_const_mul' _ _ (by simp [eNorm_eq_nnNorm])] at hiso
  obtain ⟨hFtop, hFint, -, hFi⟩ := _root_.GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self μ hμ F hFSB
  obtain ⟨h0top, h0int, h0ne, -⟩ := _root_.GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self μ hμ φ0 hφ0
  have hN0 : (∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0ne hne, h0top⟩
  have hint : ∀ T T' : Fin d → SplitFlip.Res (k := k) 1, Integrable (fun y => Tr (cosetRep ϖ i0 T) φ0 y *
      (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y)) μ := fun T T' =>
    (_root_.GlobalTheory.SBNorm.schwartzBruhat_memL2_inner_self μ hμ _ (hTr _ φ0 hφ0).1).2.2.2 _ (hTr _ φ0 hφ0).1
  have hsum : ∫ y, F y * (starRingEnd ℂ) (F y) ∂μ =
      (Fintype.card (Fin d → SplitFlip.Res (k := k) 1) : ℂ) * ∫ y, φ0 y * (starRingEnd ℂ) (φ0 y) ∂μ := by
    have hpt : ∀ y, F y * (starRingEnd ℂ) (F y) = ∑ T : Fin d → SplitFlip.Res (k := k) 1, ∑ T' : Fin d → SplitFlip.Res (k := k) 1,
        Tr (cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y) := by
      intro y
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hF, Finset.sum_apply, map_sum, Finset.sum_mul_sum]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun T _ => integrable_finsetSum _ fun T' _ => hint T T']
    simp_rw [integral_finsetSum _ fun T' _ => hint _ T']
    rw [Finset.card_univ.symm, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.sum_eq_single T (fun T' _ hT' => horth μ hμ T T' (Ne.symm hT')) (fun h => absurd (Finset.mem_univ _) h)]
    exact hTrIso μ hμ _ φ0 hφ0 φ0 hφ0
  rw [hFint, h0int] at hsum
  have hLF : (∫⁻ y, ‖F y‖ₑ ^ 2 ∂μ).toReal =
      (Fintype.card (Fin d → SplitFlip.Res (k := k) 1) : ℝ) * (∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ).toReal := by
    exact_mod_cast hsum
  have hiso' := congrArg ENNReal.toReal hiso
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_eNorm, hLF] at hiso'
  have hcard : (Fintype.card (Fin d → SplitFlip.Res (k := k) 1) : ℝ) = (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_eq_nat_card]
    have : Nat.card (SplitFlip.Res (k := k) 1) = GlobalTheory.SplitWeil.resCard k :=
      Nat.card_congr (Ideal.quotEquivOfEq (pow_one 𝓂[k])).toEquiv
    rw [this]; push_cast; ring
  rw [hcard] at hiso'
  apply mul_right_cancel₀ hN0
  linear_combination hiso'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfEtaleCohomologyEquivalenceDiagramStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.of_etaleCohomologyEquivalence_diagram : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (G G' : I ⥤ Spc) (c : Cone G) (c' : Cone G') (α : G ⟶ G') (β : c.pt ⟶ c'.pt), (∀ i, c.π.app i ≫ α.app i = β ≫ c'.π.app i) → (∀ i, Eqv R (α.app i) F) → Eqv R β F → (ContCone R F c ↔ ContCone R F c') := by
  first | (exact @GlobalTheory.EtC.ContCone.iff_of_eqv) | (exact GlobalTheory.EtC.ContCone.iff_of_eqv) | (intros; apply GlobalTheory.EtC.ContCone.iff_of_eqv  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRealGramDeterminantBoundLeProdCutoff
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.Cutoff

noncomputable section

theorem norm_entry_le_opNorm {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (Z : Matrix m n ℂ) (a : m) (b : n) :
    ‖Z a b‖ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)‖ := by
  set v : EuclideanSpace ℂ n := EuclideanSpace.single b (1 : ℂ)
  have h1 := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)).le_opNorm v
  have hv : ‖v‖ = 1 := by simp [v]
  rw [hv, mul_one] at h1
  have h2 := PiLp.norm_apply_le (Matrix.toEuclideanLin Z v) a
  have h3 : (Matrix.toEuclideanLin Z v) a = Z a b := by
    simp [v, Matrix.toLpLin_apply, Matrix.mulVec_single]
  rw [h3] at h2
  exact h2.trans h1

theorem gB_nonneg {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : 0 ≤ gB p0 w :=
  Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem zOf_mem_cut (X : Data E r) {z : V (nd X)} (hz : z ∈ Om X) (τ : X.Ψ) :
    zOf X z τ ∈ {w : Low r → ℂ | ∀ p : Low r, (p.1.2 : ℕ) < X.p0 → X.p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1} := by
  intro p hb ha
  have he : zOf X z τ p = zBlock X z τ ⟨p.1.1, ha⟩ ⟨p.1.2, hb⟩ := by
    simp [zBlock, nmat, zOf, p.2]
  rw [he]
  exact ((norm_entry_le_opNorm _ _ _).trans (hz τ).le)

theorem ofReal_bnd_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (z : V (nd X)), z ∈ Om X → ENNReal.ofReal (bnd X z) ≤ ∏ τ, hB X.p0 (zOf X z τ) := by
  intro E _ _ _ r X z hz
  rw [bnd, ENNReal.ofReal_prod_of_nonneg (fun τ _ => gB_nonneg _ _)]
  refine le_of_eq (Finset.prod_congr rfl fun τ _ => ?_)
  rw [hB, Set.indicator_of_mem (zOf_mem_cut X hz τ)]

end

end GlobalTheory.IntBall.Cutoff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagBlockNormContInv
section
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem offDiagBlockNorm_cont_inv : ∀ (n : ℕ) (ε : Fin n → Bool), (Continuous fun g : UJ ε => ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) ∧ ∀ (k k' : KG ε) (g : UJ ε), ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM ((k : UJ ε) * g * (k' : UJ ε))) z.1.1 z.1.2‖ ^ 2 = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 := by
  intro n ε
  refine ⟨?_, ?_⟩
  · have hM : Continuous fun g : UJ ε => toM g :=
      Units.continuous_val.comp continuous_subtype_val
    refine continuous_finsetSum _ fun z _ => ?_
    exact ((continuous_apply z.1.2).comp ((continuous_apply z.1.1).comp hM)).norm.pow 2
  · intro k k' g
    have hk : toM (k : UJ ε) ∈ Kset ε := k.2
    have hk' : toM (k' : UJ ε) ∈ Kset ε := k'.2
    have hmul : toM ((k : UJ ε) * g * (k' : UJ ε)) = toM (k : UJ ε) * toM g * toM (k' : UJ ε) := rfl
    rw [hmul]
    refine _root_.GlobalTheory.offDiag_sum_sq_norm_unitary_invariant n ε _ _ _ ?_ hk.2 ?_ hk'.2
    · exact Matrix.mem_unitaryGroup_iff'.mp hk.1
    · exact Matrix.mem_unitaryGroup_iff'.mp hk'.1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingCuspidalCharacterGLRootPowerSumCharacterStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_cuspidalCharacterGL_rootPowerSumCharacter : ∀ (F : Type) [Field F] [Finite F], ∀ (θ : AlgebraicClosure F →* ℂ) (m : ℕ) (e : ℕ → ℕ) (ε : ℤ), (∀ i, ∑ᶠ x, cusp θ m (e i) x = 0) → ∀ N : ℕ, (∀ i j, i < N → j < N → ∑ᶠ x, cusp θ m (e i) x * star (chG (rootSum θ (e j)) m x) = if i = j then (ε : ℂ) * (Nat.card (GL (Fin m) F) : ℂ) else 0) → ∀ (L : List ℕ) (T : Finset ℕ), L.Nodup → (∀ i ∈ L, i < N) → (∀ j ∈ T, j < N) → T.card ≤ L.length → ∀ n, n = m * L.length → ∑ᶠ x, J θ (L.map fun i => (m, e i)) n x * star (chG (fun P => ∏ j ∈ T, rootSum θ (e j) P) n x) = if T = L.toFinset then (ε : ℂ) ^ L.length * (Nat.card (GL (Fin n) F) : ℂ) else 0 := by
  first | (exact @GlobalTheory.Shin.pair_J_prod_rootSum) | (exact GlobalTheory.Shin.pair_J_prod_rootSum) | (intros; apply GlobalTheory.Shin.pair_J_prod_rootSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParFunSiegMul
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem GlobalTheory.KSp.parFun_sieg_mul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), (∀ φ : Matrix α ν E → ℂ, parFun c ψ χ Q (mat c (1 : UG c (stdJ ν E))) φ = φ) ∧ ∀ p ∈ sieg c ν, ∀ q ∈ sieg c ν, ∀ φ : Matrix α ν E → ℂ, parFun c ψ χ Q (mat c (p * q)) φ = parFun c ψ χ Q (mat c p) (parFun c ψ χ Q (mat c q) φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψ0 χ hχ hres
  obtain ⟨β, hβ, hsymm, -, hadj, -⟩ := _root_.GlobalTheory.KSp.pr_alg F E c δ hE α ν Q hQ
  obtain ⟨hsc1, hscmul, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
  refine ⟨?_, ?_⟩
  · intro φ
    funext x
    have h1 : mat c (1 : UG c (stdJ ν E)) = 1 := rfl
    have h11 : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₁ = 1 := by
      ext i j
      by_cases h : i = j <;> simp [toBlocks₁₁, Matrix.one_apply, h]
    have h12 : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₂ = 0 := by
      ext i j; simp [toBlocks₁₂, one_apply]
    have hp0 : pr c Q x 0 = 0 := by rw [← hβ]; simp
    simp only [parFun, h1, h11, h12, det_one, hsc1, Matrix.mul_one, Matrix.mul_zero, hp0, mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · intro p hp q hq φ
    funext x
    have hmul : mat c (p * q) = mat c p * mat c q := rfl
    obtain ⟨hq1, -, -⟩ := _root_.GlobalTheory.KSp.sieg_blocks F E c δ hE ν q hq
    have hP : mat c p = fromBlocks (mat c p).toBlocks₁₁ (mat c p).toBlocks₁₂ 0 (mat c p).toBlocks₂₂ := by
      rw [← (mem_sieg c).mp hp]; exact (fromBlocks_toBlocks _).symm
    have hQ' : mat c q = fromBlocks (mat c q).toBlocks₁₁ (mat c q).toBlocks₁₂ 0 (mat c q).toBlocks₂₂ := by
      rw [← (mem_sieg c).mp hq]; exact (fromBlocks_toBlocks _).symm
    set A := (mat c p).toBlocks₁₁
    set B := (mat c p).toBlocks₁₂
    set A' := (mat c q).toBlocks₁₁
    set B' := (mat c q).toBlocks₁₂
    set D' := (mat c q).toBlocks₂₂
    have e11 : (mat c (p * q)).toBlocks₁₁ = A * A' := by
      rw [hmul, hP, hQ', fromBlocks_multiply]; simp
    have e12 : (mat c (p * q)).toBlocks₁₂ = A * B' + B * D' := by
      rw [hmul, hP, hQ', fromBlocks_multiply]; simp
    have hcc : ∀ M : Matrix ν ν E, (M.map c).map c = M := fun M => by ext; simp [hE.invol]
    have hDA : D' * (A'.map c)ᵀ = 1 := by
      have h := congrArg (fun M : Matrix ν ν E => (M.map c)ᵀ) hq1
      have hm : ∀ M N : Matrix ν ν E, (M * N).map c = M.map c * N.map c := fun M N => by
        ext i j; simp [Matrix.mul_apply, map_sum, map_mul]
      have h1c : ((1 : Matrix ν ν E).map c)ᵀ = 1 := by
        rw [Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
      simp only [hm, Matrix.transpose_map, hcc, transpose_mul, transpose_transpose, h1c] at h
      exact h
    have hadd : ∀ u v w : Matrix α ν E, pr c Q u (v + w) = pr c Q u v + pr c Q u w := by
      intro u v w; rw [← hβ, ← hβ, ← hβ, map_add (f := _)]
    have hkey : pr c Q (x * A * A') (x * B * D') = pr c Q (x * A) (x * B) := by
      rw [← hβ, ← hβ, hadj, Matrix.mul_assoc (x * B), hDA, Matrix.mul_one]
    simp only [parFun, e11, e12, det_mul, hscmul, Matrix.mul_add, ← Matrix.mul_assoc, hadd, hkey, mul_add,
      AddChar.map_add_eq_mul]
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichChartsStatement
section
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodClass_injective_of_rich_charts : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ per per' : Λ →+ Hol F.V, K.perCl per = K.perCl per' → per = per' := by
  first | exact @GlobalTheory.AnPer.Charts.perCl_injective | exact GlobalTheory.AnPer.Charts.perCl_injective | (intros; apply GlobalTheory.AnPer.Charts.perCl_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyGLHarishChandraRecursioStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion : ∀ (F : Type) [Field F] [Finite F], ∀ (S : F[X] → ℂ) (n : ℕ) (x : GL (Fin n) F), psiG S n x = chG S n x - ∑ a ∈ Finset.range n, hc a (n - a) (psiG S a) (fun _ => 1) n x := by
  first | (exact @GlobalTheory.ShinPsiRec.psiG_eq_chG_sub_hc) | (exact GlobalTheory.ShinPsiRec.psiG_eq_chG_sub_hc) | (intros; apply GlobalTheory.ShinPsiRec.psiG_eq_chG_sub_hc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], (∀ ζ : Prim q A, ζ.1 ^ q = 1) ∧ (∀ (ζ : Prim q A) (a : ℕ), Nat.Coprime a q → ∃ ξ : Prim q A, ξ.1 = ζ.1 ^ a) ∧ (∀ (ζ : Prim q A) (a b : ℕ), ¬ a ≡ b [MOD q] → IsUnit (ζ.1 ^ a - ζ.1 ^ b)) ∧ (∀ (ζ : Prim q A) (x : A), x ^ q = 1 → ∏ a ∈ Finset.range q, (x - ζ.1 ^ a) = 0) ∧ (∀ (ζ ξ : Prim q A), ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (ξ.1 - ζ.1 ^ a) = 0) ∧ ∀ (r : ℕ), r ∣ q → ∀ ζ : Prim q A, ∃ ξ : Prim r A, ξ.1 = ζ.1 ^ (q / r) := by
  first | (exact @GlobalTheory.EtC.PrimBasic.prim_basic) | (exact GlobalTheory.EtC.PrimBasic.prim_basic) | (intros; apply GlobalTheory.EtC.PrimBasic.prim_basic  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrismChainComplexBoundaryIdentitiesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prism_chain_complex_boundary_identities : (∀ N (c : Pr N →₀ ℤ), Pr.d N (Pr.d N c) = 0) ∧ (∀ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) c, Pr.d M (Pr.push θ c) = Pr.push θ (Pr.d N c)) ∧ (∀ N k (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.Deg k (Pr.d N c)) ∧ (∀ N k (c : Pr N →₀ ℤ), Pr.Deg k c → Pr.Deg k (Pr.bd c)) ∧ (∀ N (c : Pr N →₀ ℤ), Pr.bd (Pr.bd c) = 0) ∧ (∀ N (c : Pr N →₀ ℤ), Pr.d (N + 1) (Pr.bd c) = Pr.bd (Pr.d N c)) ∧ ∀ N, Pr.Deg N (Pr.aw N) ∧ Pr.Deg N (Pr.wa N) := by
  first | (exact @GlobalTheory.EtC.PrCx.pr_complex) | (exact GlobalTheory.EtC.PrCx.pr_complex) | (intros; apply GlobalTheory.EtC.PrCx.pr_complex  <;> assumption)
end

