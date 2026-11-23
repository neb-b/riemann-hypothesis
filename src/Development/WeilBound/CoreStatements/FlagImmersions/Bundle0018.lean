module

public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0010
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushUnit
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0014
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0015
public import Development.WeilBound.CoreStatements.FlagImmersions.ExistsUnitMetric
public import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormNotInCoordIdeal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0179

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.AevalEqZeroOfMem
section
noncomputable section

namespace RootFieldNumerics.Sq

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp SheetDecomposition
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

omit [CharZero Ω] [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_eq_zero_of_mem {y : (Σ k, ι k) → Ω} {f : MRing ι} (hf : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  have h : ((aeval fun _ : K => (1 : Ω)).restrictScalars ℤ).comp (mConeMap y) = aeval y :=
    algHom_ext fun p => by simp [mConeMap]
  rw [← h, AlgHom.comp_apply, show mConeMap y f = 0 from hf, map_zero]

theorem valEq_of_lineIso {y : (Σ k, ι k) → Ω} (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) {a b : K → ℤ} {f g : MRing ι}
    (h : IsLineIso (mCoordIdeal y) a b f g) : ValEq ℚ y a y b := by
  classical
  obtain ⟨⟨α, γ, hf, hg, hd⟩, hfP, hgP, hU⟩ := h
  have hne : ∀ {s : MRing ι} {d : K → ℕ}, IsMultiHomog s d → s ∉ mCoordIdeal y → aeval y s ≠ 0 := fun hs hP h0 =>
    hP (by rw [mCoordIdeal, RingHom.mem_ker, ConeTrdeg.mConeMap_of_isMultiHomog y hs, h0, map_zero, zero_mul])
  refine ⟨aeval y f / aeval y g, div_ne_zero (hne hf hfP) (hne hg hgP), fun O _ => ?_⟩
  have hex : ∀ k, ∃ c : ι k, ∀ i, O.valuation (y ⟨k, i⟩) ≤ O.valuation (y ⟨k, c⟩) := fun k => by
    obtain ⟨i, -⟩ := hy k
    obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ (fun i => O.valuation (y ⟨k, i⟩)) ⟨i, Finset.mem_univ _⟩
    exact ⟨c, fun i => hc i (Finset.mem_univ _)⟩
  choose c hc using hex
  have hc0 : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i, hi⟩ := hy k
    have := hc k i
    rw [h0, map_zero] at this
    exact hi ((Valuation.zero_iff _).1 (le_antisymm this zero_le))
  have hO : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ O := fun k i => by
    rw [← O.valuation_le_one_iff, map_div₀, div_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (hc0 k)))]
    exact hc k i
  let w : (Σ k, ι k) → O := fun p => ⟨ratioPt y c p, hO p.1 p.2⟩
  let φ : MRing ι →+* O := eval₂Hom (Int.castRingHom O) w
  have hφ : ∀ s, (φ s : Ω) = aeval (ratioPt y c) s := fun s => by
    have : O.subtype.comp φ = (aeval (ratioPt y c) : MRing ι →ₐ[ℤ] Ω) :=
      ringHom_ext (fun r => by simp) fun p => by simp [φ, w]
    exact DFunLike.congr_fun this s
  have hP : ∀ s ∈ mCoordIdeal y, φ s = 0 := fun s hs => Subtype.ext <| by
    rw [hφ]
    exact aeval_eq_zero_of_mem (mCoordIdeal_ratioPt y c hc0 ▸ hs)
  obtain ⟨u, v, hu, hv, huv⟩ := hU ((IsLocalRing.maximalIdeal O).comap φ) (Ideal.comap_isPrime _ _)
    (fun s hs => by rw [Ideal.mem_comap, hP s hs]; exact zero_mem _) fun k => ⟨c k, fun h => by
      have e : φ (X ⟨k, c k⟩) = 1 := Subtype.ext (by rw [hφ]; simp [ratioPt, hc0])
      rw [Ideal.mem_comap, e] at h
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h)⟩
  have h1 : ∀ s, s ∉ (IsLocalRing.maximalIdeal O).comap φ → O.valuation (φ s) = 1 := fun s hs =>
    (O.valuation_eq_one_iff _).1 (IsLocalRing.notMem_maximalIdeal.1 hs)
  have h2 : O.valuation (aeval (ratioPt y c) f) = O.valuation (aeval (ratioPt y c) g) := by
    have e := congrArg (fun t : O => (t : Ω)) (hP _ huv)
    simp only [map_sub, map_mul] at e
    push_cast at e
    have e' := congrArg O.valuation (sub_eq_zero.1 e)
    rwa [map_mul, map_mul, h1 u hu, h1 v hv, one_mul, one_mul, hφ, hφ] at e'
  have h3 : ∀ {s : MRing ι} {d : K → ℕ}, IsMultiHomog s d →
      aeval y s = (∏ k, y ⟨k, c k⟩ ^ d k) * aeval (ratioPt y c) s := fun hs => by
    rw [← HilbertSamuel.LiftBirationalNef.aeval_scale (fun k => y ⟨k, c k⟩) hs]
    congr 2
    funext p
    rw [ratioPt, mul_div_cancel₀ _ (hc0 _)]
  have h4 : O.valuation (aeval (ratioPt y c) g) ≠ 0 := by
    rw [map_ne_zero]
    exact right_ne_zero_of_mul (h3 hg ▸ hne hg hgP)
  rw [UnitZ.vdeg_chart O y c hc0 hO, UnitZ.vdeg_chart O y c hc0 hO, h3 hf, h3 hg, map_div₀, map_mul, map_mul, h2,
    mul_div_mul_right _ _ h4, ← map_div₀, ← map_mul, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (hc0 k), ← zpow_add₀ (hc0 k), hd, sub_add_cancel]

variable {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]

theorem exists_ratio (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (L : Type) (_ : Field L) (_ : CharZero L) (φ : L →+* Ω) (z : (Σ k, ι k) → L), (∀ p, φ (z p) = y p / y ⟨p.1, c p.1⟩) ∧
      (∀ t, t ∈ blockFnField y ↔ ∃ x, φ x = t) ∧ Birational z ∧ mCoordIdeal z = mCoordIdeal y := by
  refine ⟨ratioField y c, inferInstance, inferInstance, algebraMap (ratioField y c) Ω, ratioPtL y c, fun _ => rfl, fun t => ?_,
    birational y c hc, mCoordIdeal_ratioPtL y c hc⟩
  rw [← ratioField_eq_blockFnField y c hc]
  exact ⟨fun h => ⟨⟨t, h⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩

variable {L : Type} [Field L] [CharZero L]

theorem finrank_ratio {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {φ : L →+* Ω} {z : (Σ k, ι k) → L}
    (hφ : ∀ p, φ (z p) = y p / y ⟨p.1, c p.1⟩) (hr : ∀ t, t ∈ blockFnField y ↔ ∃ x, φ x = t) {κ : K₁ → K}
    {v : (Σ k, ι₁ k) → Σ k, ι k} (hv : IsBlockMap κ v) :
    Module.finrank (fnField ℚ (z ∘ v)) L = IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) := by
  have h1 : (fnField ℚ (z ∘ v)).map φ.toRatAlgHom = blockFnField (y ∘ v) := by
    rw [fnField, IntermediateField.adjoin_map, blockFnField]
    congr 1
    have e : ∀ p q : Σ k, ι₁ k, p.1 = q.1 → φ.toRatAlgHom ((z ∘ v) p / (z ∘ v) q) = (y ∘ v) p / (y ∘ v) q := fun p q h => by
      have h' : (⟨(v p).1, c (v p).1⟩ : Σ k, ι k) = ⟨(v q).1, c (v q).1⟩ :=
        congrArg (fun k => (⟨k, c k⟩ : Σ k, ι k)) ((hv.2.2.1 p).trans ((congrArg κ h).trans (hv.2.2.1 q).symm))
      show φ (z (v p) / z (v q)) = y (v p) / y (v q)
      rw [map_div₀, hφ, hφ, h', div_div_div_cancel_right₀ (hc _)]
    ext t
    constructor
    · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
      exact ⟨p, q, h, e p q h⟩
    · rintro ⟨p, q, h, rfl⟩
      exact ⟨_, ⟨p, q, h, rfl⟩, e p q h⟩
  have h2 : (⊤ : IntermediateField ℚ L).map φ.toRatAlgHom = blockFnField y := by
    ext t
    rw [hr, IntermediateField.mem_map]
    exact ⟨fun ⟨x, _, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩⟩
  rw [← h1, ← h2, IntermediateField.relfinrank_map_map, IntermediateField.relfinrank_top_right]

open Classical in
theorem num_pull (hP : NumPull) {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → L} (hI : mCoordIdeal z = mCoordIdeal y) {κ : K₁ → K}
    {v : (Σ k, ι₁ k) → Σ k, ι k} (hv : IsBlockMap κ v) {d : ℕ} (hz : IsPt ℚ z d) {e : ℕ}
    (hf : Module.finrank (fnField ℚ (z ∘ v)) L = e) (he : e ≠ 0) (a : Fin d → K₁ → ℤ) :
    num ℚ z (fun j => pullDeg κ (a j)) =
      (e : ℤ) * NumbersDVR.intNum ℚ ((mCoordIdeal (y ∘ v)).map (MvPolynomial.map (Int.castRingHom ℚ))) a := by
  have hzv : IsPt ℚ (z ∘ v) d := by
    refine ⟨fun b => ?_, Module.finite_of_finrank_pos (by rw [hf]; exact Nat.pos_of_ne_zero he), hz.2.2⟩
    obtain ⟨i, hi⟩ := hz.1 (κ b)
    obtain ⟨⟨b', j⟩, hp⟩ := hv.2.2.2 ⟨κ b, i⟩ ⟨b, rfl⟩
    obtain rfl : b' = b := hv.1 ((hv.2.2.1 ⟨b', j⟩).symm.trans (congrArg Sigma.fst hp))
    exact ⟨j, by rwa [Function.comp_apply, hp]⟩
  have hI' : mCoordIdeal (z ∘ v) = mCoordIdeal (y ∘ v) := by
    rw [← JoinBlock.imageZ_coord κ v _ hv.1 hv.2.2.1, ← JoinBlock.imageZ_coord κ v _ hv.1 hv.2.2.1, hI]
  rw [hP ℚ _ _ _ _ _ κ v _ d a hv hz hzv, num, hf, inum, pointIdeal_rat, hI']

theorem isPt_of_birational {z : (Σ k, ι k) → L} (hb : Birational z) {d : ℕ} (hz : IsArithVar (mCoordIdeal z) (d + 1)) :
    IsPt ℚ z d := by
  have h0 : 0 < Module.finrank (RingHom.id L).fieldRange L := by
    rw [show (RingHom.id L).fieldRange = ⊤ from RingHom.fieldRange_eq_top_iff.2 Function.surjective_id]
    have : Module.Finite (⊤ : Subfield L) L :=
      Module.Finite.of_surjective (Algebra.linearMap (⊤ : Subfield L) L) fun x => ⟨⟨x, trivial⟩, rfl⟩
    exact Module.finrank_pos
  exact (numMap L L (RingHom.id L) K ι z d hb hz h0).1


open Classical in
theorem intNum_cmp (hP : NumPull) {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] (y : (Σ k, ι k) → Ω)
    {κ₁ : K₁ → K} {v₁ : (Σ k, ι₁ k) → Σ k, ι k} {κ₂ : K₂ → K} {v₂ : (Σ k, ι₂ k) → Σ k, ι k} (h₁ : IsBlockMap κ₁ v₁)
    (h₂ : IsBlockMap κ₂ v₂) {d : ℕ} (hy : IsArithVar (mCoordIdeal y) (d + 1))
    (e₁ : IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) ≠ 0)
    (e₂ : IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) ≠ 0) (a₁ : Fin d → K₁ → ℤ) (a₂ : Fin d → K₂ → ℤ)
    (h : ∀ j, ∃ f g, IsLineIso (mCoordIdeal y) (pullDeg κ₁ (a₁ j)) (pullDeg κ₂ (a₂ j)) f g) :
    (IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) : ℤ) *
        NumbersDVR.intNum ℚ ((mCoordIdeal (y ∘ v₁)).map (MvPolynomial.map (Int.castRingHom ℚ))) a₁ =
      (IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) : ℤ) *
        NumbersDVR.intNum ℚ ((mCoordIdeal (y ∘ v₂)).map (MvPolynomial.map (Int.castRingHom ℚ))) a₂ := by
  choose c hc using ne_of_arith hy
  obtain ⟨L, _, _, φ, z, hφ, hr, hb, hI⟩ := exists_ratio y c hc
  rw [← hI] at hy h
  have hz : IsPt ℚ z d := isPt_of_birational hb hy
  refine (num_pull hP hI h₁ hz (finrank_ratio hc hφ hr h₁) e₁ a₁).symm.trans
    (Eq.trans ?_ (num_pull hP hI h₂ hz (finrank_ratio hc hφ hr h₂) e₂ a₂))
  refine numEq ptDim hP (unitZero ptDim) ℚ L K ι K ι z z d _ _ hz hz fun j => ?_
  obtain ⟨f, g, hfg⟩ := h j
  exact valEq_of_lineIso hz.1 hfg


open Classical MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M in
theorem degNum_eq (hI : PB.Inputs) {d : ℕ} {σ : Type} {S : PB.AnSys d σ} {P : Ideal (MRing ι)} (Re : PB.Realis S P)
    (w : Fin d → σ) :
    (Re.deg : ℝ) * S.degNum w =
      (NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) fun j => (Re.ref (w j)).a : ℤ) := by
  have href : mInt Re.R.A (fun j => potOf Re.R (Re.ref (w j))) (fun _ => 1) = Re.deg * S.degNum w := by
    have hth : ∀ a, IsPotential S.A (S.th a) := fun a => (S.sing a).1
    have hpb : ∀ a, IsPotential Re.R.A ((S.th a).pullback Re.π Re.holo.1) := fun a =>
      isPotentialPullback S.A Re.R.A Re.π Re.holo (S.th a) (hth a)
    have hC2 (a : σ) (x : Re.R.X) : PB.IsTwiceDifferentiableAt Re.R.A ((S.th a).pullback Re.π Re.holo.1) x := by
      intro j hj
      let P' := (S.th a).pullback Re.π Re.holo.1
      let chart := Re.R.A.chart j
      have hx : chart x ∈ chart.target ∩ chart.symm ⁻¹' P'.U x :=
        ⟨chart.map_source hj, by
          rw [Set.mem_preimage, chart.left_inv hj]
          exact P'.mem_U x⟩
      exact (contDiffAt_of_isPotential Re.R.A P' (hpb a) x j hx).of_le (by simp)
    rw [(_root_.GlobalTheory.CompanionTheory.Ar.PB.mInt_congr_samePot d Re.R.X Re.R.A Set.univ
      (fun j => potOf Re.R (Re.ref (w j))) (fun j => (S.th (w j)).pullback Re.π Re.holo.1)
      (fun _ => 1) (fun _ => 1) (fun j => by simp) (fun j => Re.ref_pot (w j))
      (fun j x _ => hC2 (w j) x) (fun _ _ => rfl)).1]
    let Φ : Fin d → LocPot S.X := fun j => S.th (w j)
    let Ψ : Fin d → LocPot Re.R.X := fun j => (Φ j).pullback Re.π Re.holo.1
    change mInt Re.R.A Ψ (fun _ => 1) = Re.deg * mInt S.A Φ (fun _ => 1)
    rcases isEmpty_or_nonempty S.X with hX | hX
    · have hY : IsEmpty Re.R.X := ⟨fun y => hX.false (Re.π y)⟩
      have hA : ∀ k, (S.A.chart k).target = ∅ := fun k => by
        rw [← (S.A.chart k).image_source_eq_target, Set.eq_empty_of_isEmpty (S.A.chart k).source, Set.image_empty]
      have hB : ∀ k, (Re.R.A.chart k).target = ∅ := fun k => by
        rw [← (Re.R.A.chart k).image_source_eq_target, Set.eq_empty_of_isEmpty (Re.R.A.chart k).source, Set.image_empty]
      simp [mInt, integralWith, hA, hB]
    · let : MeasurableSpace S.X := borel S.X
      have : BorelSpace S.X := ⟨rfl⟩
      let : MeasurableSpace Re.R.X := borel Re.R.X
      have : BorelSpace Re.R.X := ⟨rfl⟩
      obtain ⟨A⟩ := existsPartition S.A
      obtain ⟨B⟩ := existsPartition Re.R.A
      obtain ⟨E, V, k, W, j, hEm, hEd, hEU, hEV, hsh⟩ := exists_sheet_partition Re.holo Re.degree
      have hΦ := mIntegrableCont S.A Φ (fun j => hth (w j)) (fun _ => 1) continuous_const
      have hΨ := mIntegrableCont Re.R.A Ψ (fun j => hpb (w j)) (fun _ => 1) continuous_const
      have hXsum := dI_hasSum S.A A Φ (fun _ => 1) (integrableOn_weight S.A A Φ _ hΦ) E hEm hEd Re.br
        (analyticNull S.A Re.br Re.degree.1 Re.degree.2.1) hEU
      have hYsum := dI_hasSum Re.R.A B Ψ (fun _ => 1) (integrableOn_weight Re.R.A B Ψ _ hΨ)
        (fun m => Re.π ⁻¹' E m) (fun m => Re.holo.1.measurable (hEm m))
        (fun m n hmn => (hEd hmn).preimage Re.π) (Re.π ⁻¹' Re.br)
        (analyticNull Re.R.A _ Re.degree.2.2.1 Re.degree.2.2.2.1)
        (by rw [← Set.preimage_iUnion, hEU, Set.preimage_compl])
      have hp (m : ℕ) : integralWith Re.R.A B Ψ ((Re.π ⁻¹' E m).indicator (fun _ => 1)) =
          Re.deg * integralWith S.A A Φ ((E m).indicator (fun _ => 1)) := by
        rw [show (Re.π ⁻¹' E m).indicator (fun _ => (1 : ℝ)) = fun y => (E m).indicator (fun _ => 1) (Re.π y) from
          funext fun y => Set.indicator_comp_right Re.π (s := E m) (g := fun _ => (1 : ℝ)) (x := y)]
        obtain ⟨hV, hVk, hW, hdis, hpre, hbij⟩ := hsh m
        exact (degree_piece Re.holo Φ (fun j => hth (w j)) A B (hEm m) (hEV m) hV hVk hW hdis hpre hbij _ hΦ).2
      simp only [hp] at hYsum
      rw [mIntEq Re.R.A B Ψ (fun j => hpb (w j)) _ hΨ, mIntEq S.A A Φ (fun j => hth (w j)) _ hΦ]
      exact HasSum.unique hYsum (hXsum.mul_left _)
  rw [← href, ← ptsIntegral_one_eq_mInt hI.resExists resBridge Re.R Re.arith fun j => Re.ref_smooth _]
  exact Giv.degreeGeneric_of_degree hI.degree K ι P d _ Re.arith fun j => Re.ref_smooth _

end RootFieldNumerics.Sq
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.UnitAtOfSpan
section
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
  GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

namespace RootFieldNumerics.RF

namespace Smooth

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem mem_genFibre (z : Spec (CommRingCat.of ℂ) ⟶ X) (hc : genPt ξ ⤳ centre z) :
    (⟨centre z, hc⟩ : Cpt ξ) ∈ genFibre ℤ ξ := by
  intro o ho
  have h1 : ValAt ξ z (o : Ω) (o : ℂ) := LiesOver.valAt_int hc o
  have h2 := CxVal.inv h1 (by exact_mod_cast ho)
  have h3 := CxVal.mul h1 h2
  have h0 : (o : Ω) ≠ 0 := by
    intro h
    have h4 : ValAt ξ z (0 : Ω) (0 : ℂ) := by simpa using LiesOver.valAt_int hc 0
    rw [h] at h1
    exact ho (by exact_mod_cast CxVal.unique h1 h4)
  obtain ⟨_, s, e, -⟩ := h1
  obtain ⟨_, s', e', -⟩ := h2
  exact ⟨by simpa using h0, ⟨s, by simpa using e⟩, ⟨s', by simpa using e'⟩⟩

theorem val_ne_zero {z : Spec (CommRingCat.of ℂ) ⟶ X} {hc : genPt ξ ⤳ centre z} {u : Ω} {r : ℂ}
    (hu : unitAt ξ ⟨centre z, hc⟩ u) (hr : ValAt ξ z u r) : r ≠ 0 := by
  obtain ⟨s, hs⟩ := hu.2.2
  have h1 := CxVal.mul hr (⟨hc, s, hs, rfl⟩ : ValAt ξ z u⁻¹ _)
  rw [mul_inv_cancel₀ hu.1] at h1
  exact left_ne_zero_of_mul_eq_one (CxVal.unique h1 (CxVal.one hc))

theorem unitAt_of_span {p : Cpt ξ} {s t : Ω} (hs : s ≠ 0) (ht : t ≠ 0)
    (h : Submodule.span (regAt ξ p) {s} = Submodule.span (regAt ξ p) {t}) : unitAt ξ p (s / t) := by
  have key : ∀ {s t : Ω}, t ≠ 0 → s ∈ Submodule.span (regAt ξ p) {t} → s / t ∈ regAt ξ p := by
    intro s t ht hm
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hm
    have : s / t = r := by
      rw [← hr]
      exact mul_div_cancel_right₀ _ ht
    rw [this]
    exact r.2
  refine ⟨div_ne_zero hs ht, key ht (h ▸ Submodule.mem_span_singleton_self s), ?_⟩
  rw [inv_div]
  exact key hs (h ▸ Submodule.mem_span_singleton_self t)

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem pres_on (hT : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) {L : Lat ξ Ω} {a : K → ℤ} {e₀ c₀ : Ω}
    (hD : L.IsDegOn Set.univ y a e₀) (hg : ∀ p ∈ genFibre ℤ ξ, L.IsGenAt p (c₀ * e₀))
    {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y)) :
    ∃ g h dg dh, Pres y a c₀ g h dg dh ∧ evC w g ≠ 0 ∧ evC w h ≠ 0 := by
  classical
  obtain ⟨z, hz, hco⟩ := SheetDecomposition.ChartForm.exists_point hT w
    (fun k => (hw.1 k).imp fun _ h => IsUnit.mk0 _ h) (fun g hg => by rw [← evC_eq]; exact hw.2 g hg)
  choose c hc using hco.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hco.2 k _ (hc k)).1
  have hY : ∀ m : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
  have hW : ∀ m : K → ℕ, (∏ k, w ⟨k, c k⟩ ^ m k) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k).ne_zero
  have hxc : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  let p : Cpt ξ := ⟨centre z, hz⟩
  have hch : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p := by
    refine ⟨hxc, fun c' => ?_⟩
    show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ ∈ _
    rw [← Finset.prod_div_distrib]
    refine Subring.prod_mem _ fun k _ => ?_
    obtain ⟨r, ⟨_, s, e, -⟩, -⟩ := (hco.2 k _ (hc k)).2 (c' k)
    exact ⟨s, e⟩
  have hYa : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have hgen := hg p (mem_genFibre z hz)
  have hu : unitAt ξ p (c₀ / ∏ k, y ⟨k, c k⟩ ^ a k) := by
    have := unitAt_of_span hgen.1 (mul_ne_zero hYa hD.1) (hgen.2.symm.trans (hD.2 p trivial c hch))
    rwa [mul_div_mul_right _ _ hD.1] at this
  obtain ⟨U, hU, hmem⟩ := hT.affine c hxc
  have hpU : p.1 ∈ U := (hmem _).2 ⟨hz, hch⟩
  have hgU : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, CoordBase.inChart_gen hT hxc⟩
  obtain ⟨s, hs⟩ := hu.2.1
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p.1, hpU⟩ : U)
  have hloc := hU.isLocalization_stalk ⟨p.1, hpU⟩
  obtain ⟨⟨t, f⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨p.1, hpU⟩).asIdeal.primeCompl s
  have e' : s * X.presheaf.germ U p.1 hpU f.1 = X.presheaf.germ U p.1 hpU t := e
  have hfu : IsUnit (X.presheaf.germ U p.1 hpU f.1) := IsLocalization.map_units (X.presheaf.stalk p.1) f
  have h2 := congrArg (genMap ξ p) e'
  rw [map_mul, hs, CoordBase.genMap_germ_val U hgU p hpU, CoordBase.genMap_germ_val U hgU p hpU] at h2
  have hfu' : unitAt ξ p (CoordBase.val U hgU f.1) := by
    rw [← CoordBase.genMap_germ_val U hgU p hpU]
    obtain ⟨v, hv⟩ := hfu
    rw [← hv]
    exact ⟨(v.isUnit.map _).ne_zero, ⟨_, rfl⟩, ⟨v⁻¹.val, map_units_inv _ v⟩⟩
  have htu : unitAt ξ p (CoordBase.val U hgU t) := h2 ▸ ZUnit.mul hu hfu'
  have hin : ∀ b : Γ(X, U), CoordBase.val U hgU b ∈ chartRingZ y c := fun b => by
    rw [← CptIn.Intr.segre_chart y c hy]
    exact (CoordBase.mem_adjoin_iff hT hxc hU hmem hgU _).2 ⟨b, rfl⟩
  obtain ⟨δt, Gt, ht1, ht2, ht3⟩ := LiesOver.exists_form_valAt hz hco c hy hc (hin t)
  obtain ⟨δf, Gf, hf1, hf2, hf3⟩ := LiesOver.exists_form_valAt hz hco c hy hc (hin f.1)
  have nt : evC w Gt ≠ 0 := fun h => val_ne_zero htu ht3 (by rw [h, zero_div])
  have nf : evC w Gf ≠ 0 := fun h => val_ne_zero hfu' hf3 (by rw [h, zero_div])
  have hm : ∀ m : K → ℕ, evC w (cMon c m) ≠ 0 := fun m => by
    rw [evC_eq, aeval_cMon]
    exact hW m
  refine ⟨Gt * cMon c δf * cMon c fun k => (a k).toNat, Gf * cMon c δt * cMon c fun k => (-a k).toNat, _, _,
    ⟨homog_mul (homog_mul ht1 (homog_cMon _ _)) (homog_cMon _ _),
      homog_mul (homog_mul hf1 (homog_cMon _ _)) (homog_cMon _ _), fun k => ?_, ?_⟩, ?_, ?_⟩
  · simp only [Pi.add_apply]
    omega
  · have ea : (∏ k, y ⟨k, c k⟩ ^ (a k).toNat) = (∏ k, y ⟨k, c k⟩ ^ a k) * ∏ k, y ⟨k, c k⟩ ^ (-a k).toNat := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k)]
      congr 1
      omega
    simp only [map_mul, aeval_cMon, ht2, hf2]
    rw [ea, ← h2]
    field_simp
  · rw [evC_mul, evC_mul]; exact mul_ne_zero (mul_ne_zero nt (hm _)) (hm _)
  · rw [evC_mul, evC_mul]; exact mul_ne_zero (mul_ne_zero nf (hm _)) (hm _)

end Smooth

open Smooth in
theorem smoothLine : SmoothLine := by
  intro X Ω _ ξ K _ J _ y F' _ _ ψ L a e₀ c₀ cinf n _ hT _ hO _ hvar hD hg hpos hconj
  obtain ⟨A₀, ha, hsm, hcj, hn⟩ := exists_unit_metric y a c₀ fun w hw => by
    by_cases h : w ∈ mcPts (mCoordIdeal y)
    · exact pres_on hT hD hg h
    · exact pres_off hvar.2.1.2.1 a c₀ hw h
  obtain ⟨u, hu, huc⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K J Ω F' y ψ (fun σ => Real.log (cinf σ)) hO
  have huc' := huc fun σ => by simp only [hconj]
  refine ⟨hu.shift A₀, ?_, ?_, fun z => ?_, ?_, fun w hw => ?_⟩
  · show A₀.a + 0 = a
    rw [add_zero, ha]
  · exact ContDiffOn.mul hsm hu.smooth.neg.exp
  · show A₀.h _ * Real.exp (-u _) = A₀.h z * Real.exp (-u z)
    rw [hcj z, huc' z]
  · intro σ z g h dg dh hz h1 h2 h3 h4
    have h3' : ∀ k, (dg k : ℤ) - dh k = a k := fun k => by
      rw [h3 k]
      show (A₀.a + 0) k = a k
      rw [add_zero, ha]
    rw [hn z hz.1 g h dg dh ⟨h1, h2, h3', h4⟩]
    show _ = cinf σ * (A₀.h z * Real.exp (-u z)) * _
    rw [(hu.near σ z hz).self_of_nhds, Real.exp_neg, Real.exp_log (hpos σ)]
    have := (hpos σ).ne'
    field_simp
  · obtain ⟨g, h, dg, dh, hP, -, hh⟩ := pres_on hT hD hg hw
    exact ⟨g, h, dg, dh, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2, hh⟩

end RootFieldNumerics.RF
end
end

