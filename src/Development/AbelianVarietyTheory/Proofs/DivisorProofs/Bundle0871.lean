module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactNormalSubgroupDescentInvariants
section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

noncomputable section

namespace GlobalTheory.Cusp.Shear

theorem exists_measurable_addSection : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N : Subgroup G) [DiscreteTopology Γ]
    (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    (Λ : AddSubgroup V) (s : V → G) (π : N → V), Continuous s → (∀ v w, s (v + w) = s v * s w) → (∀ v, s v ∈ N) →
    (∀ (a : N) (v : V), (a : G) = s v → π a = v) → (∀ v ∈ Λ, s v ∈ Γ) →
    ∃ B : Set V, MeasurableSet B ∧ ∀ v : V, ∃! w : Λ, (w : V) + v ∈ B := by
  intro G _ _ _ _ _ _ Γ N _ V _ _ _ _ Λ s π hsc hmul hs hπs hsΓ
  let s' : V → N := fun v => ⟨s v, hs v⟩
  have hπs' : ∀ v, π (s' v) = v := fun v => hπs _ v rfl
  have hs'add : ∀ v w, s' (v + w) = s' v * s' w := fun v w => Subtype.ext (hmul v w)
  have hs0 : s' 0 = 1 := by
    have h := hs'add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)

  let H : Subgroup N :=
    { carrier := {n | n = s' (π n) ∧ π n ∈ Λ}
      one_mem' := by
        have h1 : π 1 = 0 := by rw [← hs0, hπs']
        exact ⟨by rw [h1, hs0], by rw [h1]; exact Λ.zero_mem⟩
      mul_mem' := fun {a b} ha hb => by
        have e : a * b = s' (π a + π b) := by rw [hs'add, ← ha.1, ← hb.1]
        have hp : π (a * b) = π a + π b := by rw [e, hπs']
        exact ⟨by rw [hp]; exact e, by rw [hp]; exact Λ.add_mem ha.2 hb.2⟩
      inv_mem' := fun {a} ha => by
        have h1 : s' (π a) * s' (-π a) = 1 := by rw [← hs'add, add_neg_cancel, hs0]
        have e : a⁻¹ = s' (-π a) :=
          (congrArg (·⁻¹) ha.1).trans (eq_inv_of_mul_eq_one_right h1).symm
        have hp : π a⁻¹ = -π a := by rw [e, hπs']
        exact ⟨by rw [hp]; exact e, by rw [hp]; exact Λ.neg_mem ha.2⟩ }
  have hH : ∀ h : H, ((h : N) : G) ∈ Γ := fun h => by
    have e : ((h : N) : G) = s (π h) := congrArg Subtype.val h.2.1
    rw [e]; exact hsΓ _ h.2.2
  haveI : DiscreteTopology H :=
    .of_continuous_injective (f := fun h : H => (⟨((h : N) : G), hH h⟩ : Γ))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      fun a b e => Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) e))
  refine ⟨s' ⁻¹' stdDom H, (hsc.subtype_mk hs).measurable (measurableSet_stdDom H), fun v => ?_⟩
  obtain ⟨h, hh, hu⟩ := existsUnique_stdDom H (s' v)
  refine ⟨⟨π h, h.2.2⟩, ?_, fun w hw => ?_⟩
  · show s' (π h + v) ∈ stdDom H
    rw [hs'add, ← h.2.1]
    exact hh
  · have hmem : s' w ∈ H := ⟨by rw [hπs'], by rw [hπs']; exact w.2⟩
    have e := hu ⟨s' w, hmem⟩ (by
      show s' w * s' v ∈ stdDom H
      rw [← hs'add]
      exact hw)
    apply Subtype.ext
    show (w : V) = π h
    rw [← e]
    exact (hπs' w).symm

theorem integral_section_eq_constTermOn : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ]
    [LocallyCompactSpace N] [LocallyCompactSpace N'], N' ≤ N → (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [MeasurableSpace V] [BorelSpace V] (Λ : AddSubgroup V) (s : V → G) (π : N → V),
      Continuous s → (∀ v w, s (v + w) = s v * s w) → (∀ v, s v ∈ N) → Continuous π →
      (∀ a b : N, π (a * b) = π a + π b) → (∀ (a : N) (v : V), (a : G) = s v → π a = v) →
      (∀ a : N, π a = 0 ↔ (a : G) ∈ N') → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ φ : G → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv Γ φ → Continuous φ → (∀ m ∈ N', ∀ g, φ (m * g) = φ g) →
      ∀ (μ : MeasureTheory.Measure V) (𝓕 : Set V), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Λ 𝓕 μ →
        ∀ x : G, ∫ v in 𝓕, φ (s v * x) ∂μ = μ.real 𝓕 • GlobalTheory.Cusp.constTermOn Γ N φ x := by
  intro G _ _ _ _ _ _ _ _ Γ N N' _ _ _ hle hn hc hc' V _ _ _ _ _ _ Λ s π hsc hmul hs hπc hπmul hπs hker hsΓ hπΓ
    φ hφ hφc hN' μ 𝓕 hμ h𝓕 x

  let s' : V → N := fun v => ⟨s v, hs v⟩
  have hs'c : Continuous s' := hsc.subtype_mk _
  have hleft : Function.LeftInverse π s' := fun v => hπs _ v rfl
  have hemb : Topology.IsEmbedding s' := hleft.isEmbedding hπc hs'c
  haveI : SecondCountableTopology V := hemb.secondCountableTopology
  haveI : T2Space V := hemb.t2Space
  haveI : Countable Λ := Function.Injective.countable (f := fun w : Λ => (⟨s w, hsΓ _ w.2⟩ : Γ)) fun a b h =>
    Subtype.ext (hleft.injective (Subtype.ext (congrArg Subtype.val h : s a = s b)))
  let e := prodHomeo hle hs hsc hπc hπmul hπs hker
  let ν : Measure N := ((Measure.haar : Measure N').prod μ).map e
  haveI : ν.IsHaarMeasure := _root_.GlobalTheory.Cusp.Shear.isHaarMeasure_map_prodHomeo G Γ N N' hle hn hc hc' V s π hs hsc hπc hπmul hπs hker hmul μ hμ
  obtain ⟨B, hBm, hB⟩ := exists_measurable_addSection G Γ N V Λ s π hsc hmul hs hπs hsΓ
  let A := stdDom (Γ.subgroupOf N')
  have hAm : MeasurableSet A := measurableSet_stdDom _
  have hD : IsFundamentalDomain (Γ.subgroupOf N) (e '' (A ×ˢ B)) ν :=
    _root_.GlobalTheory.Cusp.Shear.isFundamentalDomain_image_prod G Γ N N' hle hn V Λ s π hs hsc hπc hπmul hπs hker hmul hsΓ hπΓ A B hAm hBm
      (existsUnique_stdDom _) hB ν
  have hep : MeasurePreserving e ((Measure.haar : Measure N').prod μ) ν := ⟨e.continuous.measurable, rfl⟩
  have hemb' : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding

  have hI : ∫ n in e '' (A ×ˢ B), φ (n * x) ∂ν =
      (Measure.haar : Measure N').real A • ∫ v in B, φ (s v * x) ∂μ := by
    rw [hep.setIntegral_image_emb hemb', ← Measure.prod_restrict]
    have h1 : ∀ z : N' × V, φ ((e z : G) * x) = φ (s z.2 * x) := fun z => by
      rw [prodHomeo_apply, mul_assoc]; exact hN' _ z.1.2 _
    simp only [h1]
    rw [integral_fun_snd (fun v => φ (s v * x)), measureReal_restrict_apply_univ]
  have hM : ν (e '' (A ×ˢ B)) = Measure.haar A * μ B := by
    change ((Measure.haar : Measure N').prod μ).map e _ = _
    rw [hemb'.map_apply, e.preimage_image, Measure.prod_prod]
  have hA0 : (Measure.haar : Measure N') A ≠ 0 := (isFundamentalDomain_stdDom _ _).measure_ne_zero (NeZero.ne _)
  have hAt : (Measure.haar : Measure N') A ≠ ⊤ := hc'.measure_ne_top (isFundamentalDomain_stdDom _ _)
  have hDt := hc.measure_ne_top hD
  have hD0 := hD.measure_ne_zero (NeZero.ne ν)
  rw [hM] at hDt hD0
  have hBt : μ B ≠ ⊤ := fun h => hDt (by rw [h, ENNReal.mul_top hA0])
  have hB0 : μ B ≠ 0 := fun h => hD0 (by rw [h, mul_zero])

  have hBF : IsAddFundamentalDomain Λ B μ := .mk' hBm.nullMeasurableSet fun v => by
    simpa [AddSubgroup.vadd_def, vadd_eq_add] using hB v
  have hf : ∀ (w : Λ) (v : V), φ (s ((w : V) + v) * x) = φ (s v * x) := fun w v => by
    rw [hmul, mul_assoc]; exact hφ _ (hsΓ _ w.2) _
  rw [h𝓕.setIntegral_eq hBF (fun w v => hf w v), measureReal_def, h𝓕.measure_eq hBF, constTermOn_eq hD hφ x, hI,
    measureReal_def, hM, measureReal_def, ENNReal.toReal_mul, smul_smul, smul_smul]
  have ha : ((Measure.haar : Measure N') A).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hA0, hAt⟩
  have hb : (μ B).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hB0, hBt⟩
  rw [show (μ B).toReal * (((Measure.haar : Measure N') A).toReal * (μ B).toReal)⁻¹ *
      ((Measure.haar : Measure N') A).toReal = 1 by field_simp, one_smul]

end GlobalTheory.Cusp.Shear

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionIntegralOfLimitSteps
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.Incl

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

theorem subst_expAlong {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    {κ : Type} [Fintype κ] {ι : κ → Type} [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin d → C)
    (A : κ → Matrix (Fin d) (Fin d) C) (t : κ → C) (hA : ∀ b a, (A b).mulVec (u b a) = t b • u b a) (i : Fin d) :
    subst (expAlong (fun _ : κ => G) u)
        (expPt G (∑ b, mv (A b) (lgPt G fun e => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : κ, Fin d) C))) i) =
      subst (fun e : Fin d => ∑ ℓ : (Σ b, ι b), (t ℓ.1 * u ℓ.1 ℓ.2 e) • (X ℓ : MvPowerSeries (Σ b, ι b) C))
        (expOf G i) := by
  have hu : ∀ (b : κ) (e : Fin d),
      constantCoeff (∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) = 0 := fun b e => by simp
  have hE : ∀ (b : κ), (fun e : Fin d => expAlong (fun _ : κ => G) u ⟨b, e⟩) =
      expPt G (fun e => ∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) := fun b => rfl
  have hs : HasSubst (expAlong (fun _ : κ => G) u) :=
    hasSubst_of_constantCoeff_zero fun q => cc_expPt G (hu q.1) q.2
  have hX : ∀ (b : κ) (e : Fin d), constantCoeff (X ⟨b, e⟩ : MvPowerSeries (Σ _ : κ, Fin d) C) = 0 := by simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [subst_expPt G hs (fun e => by
    rw [Finset.sum_apply, map_sum]
    exact Finset.sum_eq_zero fun b _ => cc_mv _ (cc_lgPt G (hX b)) e)]
  unfold expPt
  congr 1
  funext e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_apply, ← coe_substAlgHom hs, map_sum, coe_substAlgHom, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [subst_mv hs]
  have h1 : (fun e' => subst (expAlong (fun _ : κ => G) u)
      (lgPt G (fun e => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : κ, Fin d) C)) e')) =
      fun e => ∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C) := by
    funext e'
    rw [subst_lgPt G hs (hX b)]
    simp only [subst_X hs]
    rw [hE b, lgPt_expPt G (hu b)]
  rw [h1]
  simp only [mv, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  exact congrFun (hA b a) e

theorem isotropic_blocks {O : Type} [CommRing O] [StarRing O] (I : Ideal O) {φ : Type} {r m : φ → ℕ} {n : ℕ}
    (blk : (Σ f : φ, Fin (m f)) ↪ Fin n) (ε : φ → O) (x : ∀ f, Fin (r f) → Fin n → O)
    (h0 : ∀ f b j, j ∉ Set.range (fun j => blk ⟨f, j⟩) → x f b j = 0)
    (hiso : ∀ f b b', ∑ j, x f b j * star (x f b' j) ∈ I) (b b' : Σ f, Fin (r f)) :
    ∑ j, star (ε b.1 * x b.1 b.2 j) * (ε b'.1 * x b'.1 b'.2 j) ∈ I := by
  obtain ⟨f, β⟩ := b
  obtain ⟨f', β'⟩ := b'
  by_cases hf : f = f'
  · subst hf
    have e : ∑ j, star (ε f * x f β j) * (ε f * x f β' j) =
        (star (ε f) * ε f) * ∑ j, x f β' j * star (x f β j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul]; ring
    rw [e]
    exact I.mul_mem_left _ (hiso f β' β)
  · refine Ideal.sum_mem _ fun j _ => ?_
    by_cases h1 : j ∈ Set.range (fun j => blk ⟨f, j⟩)
    · by_cases h2 : j ∈ Set.range (fun j => blk ⟨f', j⟩)
      · obtain ⟨j1, h1⟩ := h1
        obtain ⟨j2, h2⟩ := h2
        exact absurd (congrArg Sigma.fst (blk.injective (h1.trans h2.symm))) hf
      · simp [h0 f' β' j h2]
    · simp [h0 f β j h1]

theorem inclSt_of_lim (hAct : LimActSt) (hPt : LimPtSt) (hFr : LimFrameSt) : InclSt := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y Ch p _ Y cx n B hB
  obtain ⟨blk, hblk⟩ := hB
  choose x hx0 hxB hxiso using fun (f : {f : Lt1 Dw // cx f ≠ 0}) (N : ℕ) => (hblk f).2.2 N
  choose ε hε using fun τ : E →+* ℂ => hAct E H Dw l Xo c hstar T io y Ch p Y τ
  choose A hAapp hAlie using fun (b : Col cx) (j : Fin n) =>
    hε b.1.1.1 (B b.1.1 b.2 j) (fun N => x b.1 N b.2 j) (fun N => hxB b.1 N b.2 j)
  letI := io.toAlgebra
  letI : Algebra T.Fr Y.C := Y.ιF.toAlgebra
  have hw : ∀ b : Col cx, IntLog (fglOf (isIntFB_chart Ch Y)) (lgPt (fgl Ch Y)
      fun e => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) Y.C)) :=
    fun b => intLog_lgPt_X (fgl Ch Y) (fun e => (⟨b, e⟩ : Σ _ : Col cx, Fin (chD Ch.ch)))
  have hint := fun j : Fin n => hPt Y.C (vX_vp Y) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch Y) _ (Col cx) _ hw
    (fun b => A b j) (fun N b => ε b.1.1.1 N * x b.1 N b.2 j) (fun N b => hAapp b j N)
  refine ⟨fun q => expPt (fgl Ch Y) (∑ b, mv (A b q.1) (lgPt (fgl Ch Y) fun e => X ⟨b, e⟩)) q.2,
    fun q => cc_expPt _ (hint q.1).1 q.2, fun q => (hint q.1).2 q.2, fun q => ?_, ?_⟩
  · exact subst_expAlong (fgl Ch Y) (fun b : Col cx => frame Ch Y b.1.1) (fun b => A b q.1)
      (fun b => jX Y (B b.1.1 b.2 q.1)) (fun b a => hAlie b q.1 _) q.2
  · exact hFr Y.C (vX_vp Y) p (vX_vp_p Y) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch Y) _ (gauge_chart Ch Y) _ (Col cx) _
      hw H.w0 n A (fun N b j => ε b.1.1.1 N * x b.1 N b.2 j) (fun N b j => hAapp b j N)
      (fun N => isotropic_blocks _ blk (fun f => ε f.1.1 N) (fun f => x f N) (fun f => hx0 f N)
        (fun f b b' => by simpa only [hstar] using hxiso f N b b'))

end GlobalTheory.IsoTriv.Incl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionRetractionOfLimitSteps
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

theorem mv_sum_smul_X {C : Type} [Field C] {d : ℕ} {σ : Type} [Fintype σ] (A : Matrix (Fin d) (Fin d) C)
    (s : σ → C) (g : σ → Fin d → C) (e : Fin d) :
    mv A (fun e' => ∑ ℓ, (s ℓ * g ℓ e') • (MvPowerSeries.X ℓ : MvPowerSeries σ C)) e =
      ∑ ℓ, (s ℓ * A.mulVec (g ℓ) e) • (MvPowerSeries.X ℓ : MvPowerSeries σ C) := by
  simp only [mv, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun e' _ => ?_
  rw [mul_left_comm]

theorem subst_expPt_sum_mv {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d n : ℕ} {σ κ : Type} [Fintype κ]
    (G : LogFGL v d) (w : Fin n → Fin d → MvPowerSeries σ C) (hw : ∀ j e, constantCoeff (w j e) = 0)
    (r : κ → Fin n) (A : κ → Matrix (Fin d) (Fin d) C) (i : Fin d) :
    subst (fun q : Fin n × Fin d => expPt G (w q.1) q.2)
        (expPt G (∑ b, mv (A b) (lgPt G fun e => (MvPowerSeries.X (r b, e) : MvPowerSeries (Fin n × Fin d) C))) i) =
      expPt G (fun e => ∑ b, mv (A b) (w (r b)) e) i := by
  have ht : HasSubst (fun q : Fin n × Fin d => expPt G (w q.1) q.2) :=
    hasSubst_of_constantCoeff_zero fun q => cc_expPt G (hw q.1) q.2
  have hl : ∀ b e, constantCoeff
      (lgPt G (fun e => (MvPowerSeries.X (r b, e) : MvPowerSeries (Fin n × Fin d) C)) e) = 0 :=
    fun b => cc_lgPt G (by simp)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [subst_expPt G ht (fun e => by
    rw [Finset.sum_apply, map_sum]; exact Finset.sum_eq_zero fun b _ => cc_mv _ (hl b) e)]
  congr 1
  funext e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_apply, ← coe_substAlgHom ht, map_sum, coe_substAlgHom]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [subst_mv ht]
  congr 1
  funext e'
  rw [subst_lgPt G ht (by simp)]
  simp only [subst_X ht]
  exact congrFun (lgPt_expPt G (hw (r b))) e'

theorem retrSt_of : LimActSt → LimPtSt → InvSt → RetrSt := by
  intro hAct hPt hInv E _ _ _ H Dw l Xo c _ hstar T io y Ch p _ X cx n B hB
  classical
  obtain ⟨blk, hblk⟩ := hB
  have key : ∀ f : {f : Lt1 Dw // cx f ≠ 0}, ∃ ρf : Fin (rk f.1) → Fin (chD Ch.ch) → PS X.C n (chD Ch.ch),
      (∀ β i, constantCoeff (ρf β i) = 0) ∧ (∀ β i, MvIsInt (vX_vp X) (ρf β i)) ∧
      ∀ β i, subst (colPt Ch X cx B) (ρf β i) = expH Ch X cx ⟨⟨f, β⟩, i⟩ := by
    intro f
    obtain ⟨hS, ⟨r, hr⟩, hx⟩ := hblk f
    obtain ⟨φ, hφ⟩ := GlobalTheory.IsoCols.exists_lift T (io.comp (embK c f.1.1))
    have inj := IsFractionRing.injective T.V T.Fr
    have hp0 : (p : T.V) ≠ 0 := fun h => by
      have h1 := congrArg (jX X) h
      rw [map_natCast, map_zero] at h1
      exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h1)
    have hM : ∀ b b' (N : ℕ), ∃ a z,
        φ a = (Matrix.of fun b b' => B f.1 b (r b')) b b' + φ (p : 𝓞 E) ^ N * z := fun b b' N => by
      obtain ⟨x, -, hx2, -⟩ := hx N
      obtain ⟨z, hz⟩ := hx2 b (r b')
      exact ⟨x b (r b'), z, inj (by rw [hφ, map_natCast φ]; exact hz)⟩
    obtain ⟨M', hMM', hM'⟩ := hInv (𝓞 E) T.V φ (p : 𝓞 E) (by rw [map_natCast]; exact hp0)
      (by rw [map_natCast]; exact not_isUnit_p X) (rk f.1) _ hr hM
    obtain ⟨ε, hε⟩ := hAct E H Dw l Xo c hstar T io y Ch p X f.1.1
    choose x z hxz using hM'
    choose A hA1 hA2 using fun β' β => hε (M' β' β) (x β' β) fun N =>
      ⟨z β' β N, by rw [← map_natCast φ p, ← hxz, hφ]; rfl⟩
    have hint : ∀ β, IntLog (fgl Ch X) (∑ β', mv (A β' β)
        (lgPt (fgl Ch X) fun e => (MvPowerSeries.X (r β', e) : PS X.C n (chD Ch.ch)))) := fun β => by
      letI := io.toAlgebra
      letI : Algebra T.Fr X.C := X.ιF.toAlgebra
      exact hPt X.C (vX_vp X) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch X) _ (Fin (rk f.1)) _
        (fun β' => intLog_lgPt_X (fgl Ch X) fun e => (r β', e)) (fun β' => A β' β)
        (fun N β' => ε N * x β' β N) fun N β' => hA1 β' β N
    have hz : ∀ f' : {f : Lt1 Dw // cx f ≠ 0}, f' ≠ f → ∀ b β', B f'.1 b (r β') = 0 := fun f' hf b β' => by
      refine (hblk f').1 b _ fun ⟨j', hj'⟩ => ?_
      by_cases hm : r β' ∈ Set.range fun j => blk ⟨f, j⟩
      · obtain ⟨j, hj⟩ := hm
        exact hf (congrArg Sigma.fst (blk.injective (hj'.trans hj.symm)))
      · rw [Matrix.det_eq_zero_of_column_eq_zero β' fun b => hS b _ hm] at hr
        exact not_isUnit_zero hr
    refine ⟨fun β => expPt (fgl Ch X) _, fun β => cc_expPt _ (hint β).1, fun β => (hint β).2, fun β i => ?_⟩
    refine (subst_expPt_sum_mv (fgl Ch X) (fun j e => ∑ ℓ : Let cx,
      (jX X (B ℓ.1.1.1 ℓ.1.2 j) * frame Ch X ℓ.1.1.1 ℓ.2 e) • (MvPowerSeries.X ℓ : MvPowerSeries (Let cx) X.C))
      (fun j e => by simp) r (fun β' => A β' β) i).trans ?_
    show expPt _ _ i = expPt (fgl Ch X) (fun e => ∑ a, frame Ch X f.1 a e •
      (MvPowerSeries.X ⟨⟨f, β⟩, a⟩ : MvPowerSeries (Let cx) X.C)) i
    congr 1
    funext e
    simp_rw [mv_sum_smul_X]
    have hc : ∀ (b : Fin (rk f.1)) (a : Fin (rk f.1)),
        ∑ β', jX X (B f.1 b (r β')) * (A β' β).mulVec (frame Ch X f.1 a) e =
          if b = β then frame Ch X f.1 a e else 0 := fun b a => by
      have h1 := congrArg (jX X) (congrFun (congrFun hMM' b) β)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum, Matrix.one_apply] at h1
      simp only [frame, hA2, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Finset.sum_mul, ← map_mul]
      rw [show ∑ β', jX X (B f.1 b (r β') * M' β' β) = _ from h1]
      split_ifs <;> simp
    rw [Finset.sum_comm, Fintype.sum_sigma, Finset.sum_eq_single (⟨f, β⟩ : Col cx)]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_smul, hc, if_pos rfl]
    · rintro ⟨f', b⟩ - hne
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [← Finset.sum_smul]
      by_cases hf : f' = f
      · subst hf
        rw [hc, if_neg fun h => hne (by rw [show b = β from h]), zero_smul]
      · simp [hz f' hf]
    · exact fun h => absurd (Finset.mem_univ _) h
  choose ρf h1 h2 h3 using key
  exact ⟨fun q => ρf q.1.1 q.1.2 q.2, fun q => h1 _ _ _, fun q => h2 _ _ _, fun q => h3 _ _ _⟩

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactHighestWeightUniqueOfIrreducible
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HDUniq

noncomputable def height (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i : Fin n, ((i : ℕ) : ℝ) • LinearMap.proj i

theorem height_apply {n : ℕ} (u : Fin n → ℝ) : height n u = ∑ i : Fin n, ((i : ℕ) : ℝ) * u i := by
  simp [height, LinearMap.sum_apply]

theorem height_root {n : ℕ} (a b : Fin n) : height n (PI.UpqRep.root a b) = (a : ℝ) - (b : ℝ) := by
  rw [height_apply]
  simp [PI.UpqRep.root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

theorem height_cdom {n : ℕ} {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h : PI.UpqRep.CDom ε μ Λ) :
    height n (Λ - μ) ≤ 0 ∧ (height n (Λ - μ) = 0 → Λ = μ) := by
  obtain ⟨c, hc, e⟩ := h
  have hval : height n (Λ - μ) = ∑ a, ∑ b, (c a b : ℝ) * ((a : ℝ) - (b : ℝ)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]; refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, height_root, smul_eq_mul]
  have term : ∀ a b, (c a b : ℝ) * ((a : ℝ) - (b : ℝ)) ≤ 0 ∧
      ((c a b : ℝ) * ((a : ℝ) - (b : ℝ)) = 0 → c a b = 0) := by
    intro a b
    by_cases h0 : c a b = 0
    · simp [h0]
    · have hab : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast (hc a b h0).1
      have hpos : (0 : ℝ) < c a b := by exact_mod_cast Nat.pos_of_ne_zero h0
      refine ⟨mul_nonpos_of_nonneg_of_nonpos hpos.le (by linarith), fun h => ?_⟩
      exact absurd h (mul_neg_of_pos_of_neg hpos (by linarith)).ne
  refine ⟨?_, fun h0 => ?_⟩
  · rw [hval]; exact Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => (term a b).1
  · rw [hval] at h0
    have hz : ∀ a b, c a b = 0 := by
      intro a b
      have h1 := (Finset.sum_eq_zero_iff_of_nonpos fun a _ =>
        Finset.sum_nonpos fun b _ => (term a b).1).1 h0 a (Finset.mem_univ _)
      exact (term a b).2 ((Finset.sum_eq_zero_iff_of_nonpos fun b _ => (term a b).1).1 h1 b
        (Finset.mem_univ _))
    rw [← sub_eq_zero, e]
    simp [hz]

theorem cdom_antisymm {n : ℕ} {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h : PI.UpqRep.CDom ε μ Λ)
    (h' : PI.UpqRep.CDom ε Λ μ) : μ = Λ := by
  have a := height_cdom h
  have b := height_cdom h'
  have hn : height n (μ - Λ) = - height n (Λ - μ) := by rw [← map_neg, neg_sub]
  exact (a.2 (by linarith [a.1, b.1])).symm

theorem khighest_weight_unique : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), KRel ε E → KUnit ε E → ∀ L : Submodule ℂ V, FiniteDimensional ℂ L →
    KStab ε E L → (∀ L' ≤ L, KStab ε E L' → L' = ⊥ ∨ L' = L) → ∀ (Λ : Fin n → ℝ) (v : V), v ∈ L → v ≠ 0 →
    KHighest ε E Λ v → (∀ ν : Fin n → ℝ, ∀ x ∈ L, x ≠ 0 → KHighest ε E ν x → ν = Λ) := by
  intro n ε V _ _ E hR hU L hfin hst hirr Λ v hvL hv0 hv ν x hxL hx0 hx
  have dom : ∀ (μ : Fin n → ℝ) (y : V) (μ' : Fin n → ℝ) (z : V), y ∈ L → y ≠ 0 → KHighest ε E μ y →
      z ∈ L → z ≠ 0 → IsWeight E μ' z → PI.UpqRep.CDom ε μ' μ := by
    intro μ y μ' z hyL hy0 hy hzL hz0 hz
    obtain ⟨L₁, hle, hyL₁, hst₁, -, hdom, -⟩ :=
      CompanionTheory.D.DSIC.hLowSpan n ε V E μ y L hR hU hy0 hy hfin hst hyL
    have hL₁ : L₁ = L := by
      rcases hirr L₁ hle hst₁ with h | h
      · exact absurd (by simpa [h] using hyL₁) hy0
      · exact h
    exact hdom μ' z (hL₁ ▸ hzL) hz0 hz
  exact cdom_antisymm (dom Λ v ν x hvL hv0 hv hxL hx0 hx.1) (dom ν x Λ v hxL hx0 hx hvL hv0 hv.1)

end GlobalTheory.HDUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionEqSumKFiniteModule
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HolomorphicDiscreteSeriesDecomposition

theorem dRepC_eq_sum : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), IsKMod ε σ D E → ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (v : D), GlobalTheory.SmVec.dRepC (Jm ε) σ Z v = ((∑ a, ∑ b, Z a b • E a b v : D) : H) := by
  intro n ε H _ _ σ D E hK Z v
  have hG : IsUnit (Jm ε) := IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)
  obtain ⟨h1, h2⟩ := GlobalTheory.SmVec.parts_mem hG (Formalism.REAL.Jm_conjTranspose ε) Z
  have key : ∀ X, inG ε X → Formalism.L2.Theta.dRep σ X (v : H) = ∑ a, ∑ b, X a b • (E a b v : H) := fun X hX => by
    have := hK.real X hX v
    simp only [Complex.coe_smul] at this
    exact this.deriv
  unfold GlobalTheory.SmVec.dRepC
  rw [key _ h1, key _ h2]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.smul_sum, ← Finset.sum_add_distrib, smul_smul, ← add_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  field_simp
  ring

end GlobalTheory.HolomorphicDiscreteSeriesDecomposition
end

