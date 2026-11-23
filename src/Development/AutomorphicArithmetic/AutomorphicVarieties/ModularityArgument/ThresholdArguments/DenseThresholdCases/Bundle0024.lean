module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.SumTwoG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ArithmeticPointDecomposition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuProdT
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.UnitaryBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem locProd_sum {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {ε : EpsFamily A} (L : LawsV a ha ε rc) :
    ∀ {c n : ℕ} {N : Fin c → ℕ} (hn : ∑ i, N i = n) (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
      (τ : SmIrr (GL (Fin n) (w.adicCompletion E))), Nonempty (τ.ρ.Equiv (locProd hn w σ)) →
      rc (cl τ) = sumList (List.ofFn fun i => rc (cl (σ i))) := by
  intro c
  induction c with
  | zero =>
    intro n N hn σ τ e
    obtain rfl : n = 0 := by simpa using hn.symm
    obtain ⟨e⟩ := e
    obtain ⟨φ⟩ := SupportRing.nonempty_equiv_unit (k := w.adicCompletion E) (stdBlocks N hn) fun i => (σ i).ρ
    have h1 := L.det 0 1 isSmoothChar_one
    simp only [List.range_zero, List.map_nil] at h1
    rw [List.ofFn_zero]
    refine (congrArg rc (IrrGL.of_eq_of.2 ⟨e.trans φ⟩)).trans h1
  | succ s ih =>
    intro n N hn σ τ e
    obtain rfl : n = N 0 + ∑ i : Fin s, N i.succ := hn.symm.trans (Fin.sum_univ_succ N)
    obtain ⟨e⟩ := e
    obtain ⟨E₁⟩ := MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := w.adicCompletion E) N hn fun i => (σ i).ρ
    have hs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => N i.succ) rfl) fun i : Fin s => (σ i.succ).ρ) :=
      isSmooth_parInd _ _
    have hi := _root_.GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ _ _ _ _ _ _ (σ 0).ρ _ τ.ρ (σ 0).smooth (σ 0).irred hs τ.irred ⟨e.trans E₁.symm⟩
    let σ' : SmIrr (GL (Fin (∑ i : Fin s, N i.succ)) (w.adicCompletion E)) := ⟨_, _, hs, hi⟩
    have h1 := L.prod (N 0) _ (ParLaws.toRep (σ 0)) (ParLaws.toRep σ') (ParLaws.toRep τ) ⟨e.trans E₁.symm⟩
    have h2 := ih (N := fun i : Fin s => N i.succ) rfl (fun i => σ i.succ) σ' ⟨.refl _⟩
    rw [List.ofFn_succ]
    exact h1.trans (congrArg _ h2)
theorem UpperTheory.V.Z.Win.Gu.prodT_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ExtraV → ProdT := by
  intro _ X E Ω _ _ _ _ _ n c N hn w σ _ τ e A h rc hrc
  obtain ⟨a, ha, ε, L⟩ := X E Ω A w h rc hrc
  exact locProd_sum L hn σ τ e
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuSpehT
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.CuspRep GlobalTheory.DefiniteBC UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem segSum_nu {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (hnu : ∀ x (s : ℝ), rc (x.nu s) = (rc x).lpTw s)
    (l : List (Segment (w.adicCompletion E))) (c : ℝ) :
    segSum rc (l.map fun Γ => Γ.nu (c : ℂ)) = (segSum rc l).lpTw c := by
  simp only [segSum]
  rw [← GlobalTheory.NuShift.sumList_lpTw, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun Γ _ => ?_
  show ((rc (Γ.first.nu (c : ℂ))).lpTw _).lpChar _ = _
  rw [hnu, WD.lpTw_add, add_comm, ← WD.lpTw_add, GlobalTheory.NuShift.lpChar_lpTw]
  rfl
private theorem rec_spehQuotT {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : IsRecT h rc) (hTZ : GlobalTheory.Published.GenericUnitaryDualGL)
    (hLM : GlobalTheory.Published.StandardCosocleGL) (a d n : ℕ) (hd : ∑ _ : Fin d, a = n) (σ : LocIrr w a) (σ' : LocIrr w n)
    (hu : IsUnitarisable σ.ρ) (hg : IsGeneric σ.ρ) (hq : IsSpehQuot hd σ σ') :
    rc (cls (ParLaws.toRep σ')) =
      sumList ((List.range d).map fun k : ℕ => (rc (cls (ParLaws.toRep σ))).lpTw (((d : ℝ) - 1) / 2 - k)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨m, δ, Δ, s, hΔ, hδu, hs, hd0, hφ⟩ := hTZ.exists_prod σ.smooth σ.irred hu hg
  have hA := GlobalTheory.T.isLanglandsQuotient_of_irreducible_unitary_segment_product _ (GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le _) a _ σ.ρ σ.irred m δ Δ s hΔ hδu hs hd0 hφ
  have hB := GlobalTheory.T.langlandsQuotient_of_speh_type_product_isL _ hLM (GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le _) (GlobalTheory.T.parabolicInduction_in_stages_product_of_products _) a _ σ.ρ m δ Δ s hΔ hδu hs hd0 hφ d n hd _ σ'.ρ σ'.irred hq
  obtain ⟨a', ha', L⟩ := hrc
  rw [L.langlands _ _ (GlobalTheory.SpehRec.isL_of_equiv hB (equivRep (ParLaws.toRep σ'))),
    L.langlands _ _ (GlobalTheory.SpehRec.isL_of_equiv hA (equivRep (ParLaws.toRep σ)))]
  simp only [segSum]
  rw [List.map_flatMap, GlobalTheory.SpehRec.sumList_flatMap]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact segSum_nu L.nu _ _
theorem UpperTheory.V.Z.Win.Gu.spehT_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ExtraV → SpehT := by
  intro H _ E Ω _ _ _ _ _ _ a d P w ρ σ _ _ hP hu hS A h rc hrc
  have L := H.litN.loc
  have hd : ∑ _ : Fin d, a = d * a := by simp
  exact rec_spehQuotT hrc (_root_.PositivityTheory.Gud.generic_unitary_dual_GL trivial L.sq L.gen L.multi L.cos) L.cos a d _ hd ρ σ hu
    (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E a P w ρ hP)
    (GlobalTheory.DiscreteSpectrumCM.isSpehQuot_of_isSpeh hd ρ σ hS)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuSumTwoG
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open Module TensorProduct GlobalTheory.Pst.DpstMap
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section Split
variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
  {V₀ V₁ V₂ : Type} [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀]
  [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁]
  [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂]
  {ρ₀ : Representation ↥LL.1 ↥(GK K) V₀} {ρ₁ : Representation ↥LL.1 ↥(GK K) V₁}
  {ρ₂ : Representation ↥LL.1 ↥(GK K) V₂}
private theorem tensV_section (p : V₁ →ₗ[↥LL.1] V₂) (s : V₂ →ₗ[↥LL.1] V₁) (hps : ∀ v, p (s v) = v)
    (x : V₂ ⊗[ℚ_[l]] Bst P) : tensV P p (tensV P s x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [tensV, hps]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
variable [FiniteDimensional ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₂]
private theorem isPst_split {AI : LocAinf l P} (T : LocTied l P AI) {i : V₀ →ₗ[↥LL.1] V₁} {p : V₁ →ₗ[↥LL.1] V₂}
    {s : V₂ →ₗ[↥LL.1] V₁} (hi : ∀ g v, i (ρ₀ g v) = ρ₁ g (i v)) (hp : ∀ g v, p (ρ₁ g v) = ρ₂ g (p v))
    (hs : ∀ g v, s (ρ₂ g v) = ρ₁ g (s v)) (h1 : Function.Injective i) (h2 : Function.Exact i p)
    (hps : ∀ v, p (s v) = v) (hV₀ : IsPst P ρ₀) (hV₂ : IsPst P ρ₂) : IsPst P ρ₁ := by
  obtain ⟨hdom, hfrac, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V₀ := Module.Finite.trans ↥LL.1 V₀
  haveI : FiniteDimensional ℚ_[l] V₁ := Module.Finite.trans ↥LL.1 V₁
  haveI : FiniteDimensional ℚ_[l] V₂ := Module.Finite.trans ↥LL.1 V₂
  have b₁ := _root_.GlobalTheory.PstRank.rank_DpstUr_le P hdom hfrac ρ₁
  haveI f₁ : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₁) :=
    Module.rank_lt_aleph0_iff.mp (b₁.trans_lt (Cardinal.natCast_lt_aleph0))
  obtain ⟨f₀, c₀⟩ := (isPst_iff P ρ₀).1 hV₀
  obtain ⟨f₂, c₂⟩ := (isPst_iff P ρ₂).1 hV₂
  obtain ⟨hinj, hex⟩ := UpperTheory.V.Loc.PstExact.dmap_exact P hi hp h1 h2
  have inj : Function.Injective (UpperTheory.V.Loc.PstExact.dUr P hi) := fun x y h => hinj h
  have sur : Function.Surjective (UpperTheory.V.Loc.PstExact.dUr P hp) := fun y =>
    ⟨toUr P ρ₁ (dmap P hs ((toUr P ρ₂).symm y)), Subtype.ext (tensV_section P p s hps _)⟩
  have ex : Function.Exact (UpperTheory.V.Loc.PstExact.dUr P hi) (UpperTheory.V.Loc.PstExact.dUr P hp) := fun y => hex y
  have e := (UpperTheory.V.Loc.PstExact.dUr P hp).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 sur, finrank_top, LinearMap.exact_iff.mp ex, LinearMap.finrank_range_of_inj inj] at e
  have e' := (p.restrictScalars ℚ_[l]).finrank_range_add_finrank_ker
  have exq : Function.Exact (i.restrictScalars ℚ_[l]) (p.restrictScalars ℚ_[l]) := h2
  rw [LinearMap.exact_iff.mp exq, LinearMap.finrank_range_of_inj (f := i.restrictScalars ℚ_[l]) h1,
    LinearMap.range_eq_top.2 (show Function.Surjective (p.restrictScalars ℚ_[l]) from fun v => ⟨s v, hps v⟩),
    finrank_top] at e'
  exact (isPst_iff P ρ₁).2 ⟨f₁, by omega⟩
end Split
section Sum
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a b : ℕ}
private theorem isPst_sum (T : LocTied l P AI) {L : FinExt l} (s : ↥Gw →* GL (Fin a) ↥L.1) (s' : ↥Gw →* GL (Fin b) ↥L.1)
    (h : IsPst P (Bw.repE L s)) (h' : IsPst P (Bw.repE L s')) : IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) := by
  let e : (Fin (a + b) → ↥L.1) ≃ₗ[↥L.1] (Fin a → ↥L.1) × (Fin b → ↥L.1) :=
    (LinearEquiv.funCongrLeft ↥L.1 ↥L.1 finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ ↥L.1 ↥L.1)
  have he : ∀ g v, e (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s') g v) =
      (Bw.repE L s g (e v).1, Bw.repE L s' g (e v).2) := by
    intro g v
    rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, GlobalTheory.BCGal.sumRep_val]
    ext i <;>
      simp [e, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft] <;> rfl
  have he' : ∀ g x, e.symm (Bw.repE L s g x.1, Bw.repE L s' g x.2) =
      Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s') g (e.symm x) := by
    intro g x
    apply e.injective
    rw [he, e.apply_symm_apply, e.apply_symm_apply]
  refine isPst_split P T (i := e.symm.toLinearMap ∘ₗ LinearMap.inl ↥L.1 _ _)
    (p := LinearMap.snd ↥L.1 _ _ ∘ₗ e.toLinearMap) (s := e.symm.toLinearMap ∘ₗ LinearMap.inr ↥L.1 _ _)
    (ρ₀ := Bw.repE L s) (ρ₂ := Bw.repE L s') (fun g v => ?_) (fun g v => ?_) (fun g v => ?_) ?_ ?_ ?_ h h'
  · have := he' g (v, 0)
    simpa using this
  · simp [he]
  · have := he' g (0, v)
    simpa using this
  · intro x y hxy
    simpa using hxy
  · intro y
    constructor
    · intro hy
      refine ⟨(e y).1, ?_⟩
      apply e.injective
      have hy' : (e y).2 = 0 := hy
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply, e.apply_symm_apply]
      exact Prod.ext rfl hy'.symm
    · rintro ⟨x, rfl⟩
      simp
  · intro v
    simp
private theorem isPstAt_sum (T : LocTied l P AI) {r : ↥Gw →* GL (Fin a) (Om l)} {r' : ↥Gw →* GL (Fin b) (Om l)}
    (h : IsPstAt P Bw r) (h' : IsPstAt P Bw r') : IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
  obtain ⟨L₁, r₁, m₁, p₁⟩ := h
  obtain ⟨L₂, r₂, m₂, p₂⟩ := h'
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have n₁ := m₁.enlarge l₁
  have n₂ := m₂.enlarge l₂
  exact ⟨supExt L₁ L₂, _, ⟨n₁.1, by rw [GlobalTheory.Pst.SumParam.mapRep_sumRep, n₁.2, n₂.2]⟩,
    isPst_sum Bw T _ _ (_root_.GlobalTheory.PstExt.isPst_enlarge P Bw l₁ r₁ p₁) (_root_.GlobalTheory.PstExt.isPst_enlarge P Bw l₂ r₂ p₂)⟩
end Sum
theorem UpperTheory.V.Z.Win.Gu.sumTwoG_of_printsH_gdLaws_sumAway_sumHTAt :
    _root_.UpperTheory.V.Af.HypothesesH' → GdLaws → SumAway → SumHTAt → SumTwoG := by
  intro _ hG hA hT E Ω _ _ _ _ _ l _ ι a b r r' p p' HT HT' C C'
  obtain ⟨T⟩ := Loc.tiedP l
  have hv := GlobalTheory.BCGal.cont_sumRep r r' (Units.continuous_val.comp C.cont) (Units.continuous_val.comp C'.cont)
  have hc : Continuous (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
    refine Units.continuous_iff.2 ⟨hv, ?_⟩
    simp only [← map_inv]
    exact hv.comp continuous_inv
  refine ⟨hc, GlobalTheory.BCGal.ss_sumRep r r' C.ss C'.ss, fun w hg => ?_, fun w A h rc hrc => ?_⟩
  · exact hT E Ω l a b r r' C.cont C'.cont HT HT' w
      (C.ht w fun A h rc hrc => (((hG E Ω A w h).1 _ _).1 (hg A h rc hrc)).1)
      (C'.ht w fun A h rc hrc => (((hG E Ω A w h).1 _ _).1 (hg A h rc hrc)).2)
  · obtain ⟨a1, b1⟩ := C.par w A h rc hrc
    obtain ⟨a2, b2⟩ := C'.par w A h rc hrc
    have sp := ((hG E Ω A w h).1 (p w A h rc) (p' w A h rc)).1
    refine And.intro (fun hw => ?_) (fun O _ _ _ Bw hj hg => ?_)
    · obtain ⟨x, hx, kx⟩ := a1 hw
      obtain ⟨x', hx', kx'⟩ := a2 hw
      refine Exists.intro (x.lpSum x') (And.intro (hA E Ω l ι a b r r' C.cont C'.cont w hw A h _ _ hx hx') fun g => ?_)
      rw [kx (sp g).1, kx' (sp g).2]
    · obtain ⟨p1, e1⟩ := b1 O Bw hj (sp hg).1
      obtain ⟨p2, e2⟩ := b2 O Bw hj (sp hg).2
      have e : (Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (Dec (F := E) A).subtype =
          Formalism.MainNotions.SumRepresentations.At.sumRep (r.comp (Dec (F := E) A).subtype) (r'.comp (Dec (F := E) A).subtype) := by
        ext g i j
        rfl
      have p3 := isPstAt_sum Bw T p1 p2
      rw [e]
      exact ⟨p3, by rw [GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l _ _ ⟨T⟩ ι E Ω A w O Bw h hj a b _ _ p1 p2 p3, e1, e2]⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KFinal
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.ZK
theorem lemmaK_litN_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : ∃ CK, LemmaK CK := _root_.UpperTheory.V.ZK.lemmaK_of_litN_alt hN bOdd
end UpperTheory.V.ZK
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KeepIrrOpenW
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr UpperTheory.V.CA Formalism.MainNotions.N
namespace UpperTheory.V.J
theorem irrOpenW_alt : _root_.UpperTheory.V.J.IrrOpenAlt := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B ι J hn hE x hx
  have irr_iff_span {Γ : Type} [Group Γ] (r : Γ →* GL (Fin n) (Qbar l)) :
      IsIrr r ↔ Submodule.span (Qbar l) (Set.range (mat r)) = ⊤ := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [← UpperTheory.V.AlgebraTools.Det.irrIffSpan]
    constructor
    · intro h N hN
      obtain ⟨-, -, hIrr⟩ := h
      exact hIrr N le_top fun g v hv => hN g v hv
    · intro h
      exact ⟨top_ne_bot, fun g v _ => Submodule.mem_top, fun N _ hN => h N fun g v hv => hN g v hv⟩
  have gram_at {A G H K : Type} [CommRing A] [Group G] [Group H] [CommRing K]
      (D : GDet n A G) (f : A →+* K) (φ : H →* G) (ρ : H →* Matrix (Fin n) (Fin n) K)
      (h : (D.map f).comap φ = GDet.ofRep ρ) (g : Fin n × Fin n → H) :
      f (Matrix.det (Matrix.of fun a b => D.tr (MonoidAlgebra.single (φ (g a * g b)) 1))) =
        Matrix.det (Matrix.of fun a b => (ρ (g a) * ρ (g b)).trace) := by
    have trace_at (a : H) : f (D.tr (MonoidAlgebra.single (φ a) 1)) = (ρ a).trace := by
      have hmap : f (D.tr (MonoidAlgebra.single (φ a) 1)) =
          (D.map f).tr (MonoidAlgebra.single (φ a) 1) := by
        have hcoeff := ((d_gmap D).2.2.1 f (MonoidAlgebra.single (φ a) 1)).2 1
        simpa [GDet.tr, MonoidAlgebra.coeff_mapRingHom] using hcoeff.symm
      have hcomap : ((D.map f).comap φ).tr (MonoidAlgebra.single a 1) =
          (D.map f).tr (MonoidAlgebra.single (φ a) 1) := by
        have hchi : ((D.map f).comap φ).chi (MonoidAlgebra.single a 1) =
            (D.map f).chi (MonoidAlgebra.single (φ a) 1) := by
          show (D.map f).D (Polynomial K) (MonoidAlgebra.mapDomainRingHom (Polynomial K) φ
            (MonoidAlgebra.single 1 Polynomial.X -
              MonoidAlgebra.mapRingHom H Polynomial.C (MonoidAlgebra.single a 1))) = _
          congr 1
          rw [map_sub]
          simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
        simp only [GDet.tr, GDet.lam, hchi]
      rw [hmap, ← hcomap, h, ← (d_toDet _ _).2.2.1, d_toDet_ofRep.1 ρ,
        (d_ofRep _ _ _).2.2.1 hn, GDet.repAlg, MonoidAlgebra.lift_single, one_smul]
      congr 1
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rw [trace_at, map_mul]
  obtain ⟨ρ, -, hρ, hirr⟩ := hx
  obtain ⟨m, hm, hdet⟩ := (g_gram _ _ _).1 ((irr_iff_span ρ).1 hirr)
  choose g hg using hm
  refine ⟨Matrix.det (Matrix.of fun a b => B.u.D.tr (MonoidAlgebra.single (V.pr (g a * g b)) 1)), ?_, ?_⟩
  · intro h0
    refine hdet ?_
    have h1 := gram_at B.u.D (x : B.B →+* Qbar l) V.pr (mat ρ) hρ g
    have h2 := h1.symm.trans h0
    simpa only [hg] using h2
  · intro y w hJ hy hy0
    have hA : y.Arith w := ⟨hy.1, fun v j => by
      obtain ⟨ph, hph, -⟩ := hy.2 v
      exact ⟨ph j, hph j⟩⟩
    obtain ⟨ρ', hc', -, hρ', -⟩ := _root_.UpperTheory.GalN.V.end1W' hE y w hJ hA
    refine ⟨ρ', hc', hρ', (irr_iff_span ρ').2 ((g_gram _ _ _).2 ⟨fun a => mat ρ' (g a), fun a => ⟨_, rfl⟩, fun h => hy0 ?_⟩)⟩
    have h1 := gram_at B.u.D (y : B.B →+* Qbar l) V.pr (mat ρ') hρ' g
    exact h1.trans h
end UpperTheory.V.J
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocK
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.local_k_of_printed_rec_compat_sph_frob :
    _root_.UpperTheory.V.Af.Hypotheses' → RecTExists → CompatT → PlainRec → WinPt → RecSph → RecFrob → LocK := by
  intro P hRec hC hPR hW hSph hFrob K Ω _ _ _ _ _ _ l _ hl ι e he r π hc hreg hpol hatt w A κ hlw hA hex hplain
  obtain ⟨hfl, hI⟩ := hex
  have hAl : A.valuation (l : Ω) < 1 := by simpa using (hA _).2 hlw
  let m : Fin 2 → ℤ := ![(e : ℤ), -(e : ℤ)]
  have hκm : ∀ i (s : ↥(Dec (F := K) A)), (s : G K Ω) ∈ Ine (F := K) A →
      κ i s = cycBar K Ω l s ^ m i * (1 : G K Ω →* (Qbar l)ˣ) s := by
    intro i s hs
    fin_cases i
    · simpa [m] using (hI s hs).1
    · simpa [m] using (hI s hs).2
  have hor : ∀ i j, κ i ≠ κ j * (cycBar K Ω l).comp (Dec (F := K) A).subtype := by
    intro i j hij
    obtain ⟨s, hs, hne⟩ := UpperTheory.V.Ws.Pt.cycIne K Ω l A hAl (m i - m j - 1) (by
      fin_cases i <;> fin_cases j <;> simp [m] <;> omega)
    have h1 := congrArg (fun f => f ⟨s, Ine_le_Dec A hs⟩) hij
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1
    rw [hκm i _ hs, hκm j _ hs] at h1
    apply hne
    simp only [MonoidHom.one_apply, mul_one] at h1
    rw [zpow_sub, zpow_sub, h1, zpow_one]
    group
  have hfa : FlagAt 1 m r A κ := ⟨fun _ => 1, fun _ _ _ => rfl, hfl, hκm⟩
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K 2 π w
  obtain ⟨rc, hrc⟩ := hRec K Ω A w hA
  obtain ⟨t, ht⟩ := hW K 2 (by norm_num) π
  obtain ⟨hpl, htor, hmono⟩ := hPR K Ω A w hA rc hrc 2 π t (ht w hplain) σ hσ
  have hgd : Gd (rc (algNorm σ)) := ⟨htor, hmono⟩
  obtain ⟨j, L0, hj0, hB⟩ := GlobalTheory.PlaceBridge.exists_locBridge l K Ω w A hlw hA
  obtain ⟨Bw, hBj, -⟩ := hB L0 le_rfl
  have hj : Induces Bw := fun x => by rw [hBj]; exact hj0 x
  obtain ⟨HT, -, hcomp⟩ := hC K Ω l ι 2 (by norm_num) r π hc hreg hpol hatt
  obtain ⟨hpst, hwd⟩ := ((hcomp w σ hσ).1 A hA rc hrc).2 _ Bw hj hgd
  have hlev : IsLevelWD 1 2 (rc (algNorm σ)) := by
    rw [← hwd]
    exact _root_.UpperTheory.V.Af.weil_deligne_above_of_printed_results P K Ω l hl ι 2 1 le_rfl m r hc w A hA _ Bw hj κ hfa hpst (Or.inl hor)
  have hK : HasFixed σ.ρ (GlobalTheory.LFun.KGL w (n := 2)) := hSph K Ω A w hA rc hrc 2 σ hpl hlev
  have hsat := _root_.UpperTheory.V.Af.satake_local_of_printed_results P K 2 w σ
  refine ⟨?_, fun B hBs τ hτ => ?_⟩
  · obtain ⟨B, hB'⟩ := hsat.1 hK
    exact ⟨B, (hsat.2 _ π.finPart (hiso σ hσ) B).2 hB'⟩
  · have hBσ := (hsat.2 _ π.finPart (hiso σ hσ) B).1 hBs
    let φ : ↥(Weil hA) := ⟨τ, mem_Weil_of_isFrob hA hτ⟩
    have hd : deg φ = 1 := deg_eq_one_iff.2 hτ
    have h1 := GlobalTheory.T.weilDeligne_frobenius_eigenvalue_of_full_flag K Ω l ι 2 1 le_rfl m r hc w A hA _ Bw hj κ hfa hpst 0 φ hd
    rw [hwd] at h1
    obtain ⟨b, hb, hzb⟩ := hFrob K Ω A w hA rc hrc 2 σ B hpl hBσ φ hd _ h1
    refine ⟨b, hb, ?_⟩
    exact hzb
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MPTauEx
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
private theorem ce_char {l : ℕ} [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (ka : Γ →* (PadicAlgCl l)ˣ) (h : Continuous ka) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ g, (ka g).val ∈ E ∧ ‖(ka g).val‖ ≤ 1 := by
  have hc : Continuous fun g => (ka g).val := Units.continuous_val.comp h
  let r : Γ →* GL (Fin 1) (PadicAlgCl l) :=
    (Units.map (Matrix.scalar (Fin 1) : PadicAlgCl l →+* _).toMonoidHom).comp ka
  have hr : ∀ (g : Γ) (i j : Fin 1), (r g).val i j = (ka g).val := by
    intro g i j
    obtain rfl : i = j := Subsingleton.elim _ _
    simp [r]
  obtain ⟨E, hE, hm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ 1 r
    (fun i j => by simp only [hr]; exact hc)
  refine ⟨E, hE, fun g => ⟨hr g 0 0 ▸ hm g 0 0, ?_⟩⟩
  obtain ⟨C, hC⟩ := (isCompact_range hc.norm).bddAbove
  by_contra hg
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C (not_le.1 hg)
  have := hC ⟨g ^ N, rfl⟩
  simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  exact absurd hN (not_lt.2 this)
theorem tauEx' (h1 : _root_.UpperTheory.V.Cu2.KapExAlt) (h2 : TauOf) : _root_.UpperTheory.V.Cu.TauExAlt := by
  intro hP Ω _ _ _ l _ ι K' _ hl2 hK hTC hdisc hdec hcc g0 hg0
  obtain ⟨m, κ, hκ⟩ := h1 hP Ω l ι K' hl2 hK hTC hdisc hdec hcc
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : IsGalois K' Ω := IsGalois.tower_top_of_isGalois ℚ K' Ω
  haveI : CompactSpace (G K' Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[K'] Ω))
  haveI : T2Space (G K' Ω) := inferInstanceAs (T2Space (Ω ≃ₐ[K'] Ω))
  have hc : Continuous κ := by simpa using (hκ 1 le_rfl).cont
  obtain ⟨E, hE, hmE⟩ := ce_char (G K' Ω) κ hc
  haveI := hE
  obtain ⟨c₁, hc₁⟩ := UpperTheory.V.X.So.coefOf l E
  refine ⟨m, c₁, κ, fun c₂ hc₂ j hj => ?_⟩
  refine h2 Ω l ι K' hl2 hK hdec g0 hg0 (m * j) (κ ^ j) (hκ j hj) c₂ fun h => ?_
  have e : (((κ ^ j) h : (Qbar l)ˣ) : Qbar l) = ((κ h : (Qbar l)ˣ) : Qbar l) ^ j := by
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
  rw [e]
  exact pow_mem (hc₂ ((hc₁ _).2 (hmE h))) j
end UpperTheory.V.Cu2
end
end
end

