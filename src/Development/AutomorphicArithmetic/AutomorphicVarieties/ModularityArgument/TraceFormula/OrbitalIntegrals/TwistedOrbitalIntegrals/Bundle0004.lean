module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotAlong
section
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.quotAlong :
    UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotAlong := by
  intro _ _ G _ _ _ _ _ _ _ _ H _ _ _ _ _ _ _ _ j hj μG hμ T S hT hc hS ν hν
  subst hS
  let e₀ : T ≃* T.map j := T.equivMapOfInjective j hj.injective
  have c1 : Continuous e₀ := (hj.continuous.comp continuous_subtype_val).subtype_mk _
  have c2 : Continuous e₀.symm := by
    rw [(hj.isInducing.comp IsInducing.subtypeVal).continuous_iff]
    have : (j ∘ Subtype.val) ∘ e₀.symm = Subtype.val := funext fun x => congrArg Subtype.val (e₀.apply_symm_apply x)
    exact continuous_subtype_val.congr fun x => (congrFun this x).symm
  let e : T ≃ₜ* T.map j := ⟨e₀, c1, c2⟩
  have he : Measurable (e : T → T.map j) := c1.measurable
  refine ⟨ν.map e, e.isHaarMeasure_map ν, Measure.map_map (g := fun x : T.map j => (x : G)) measurable_subtype_coe he, fun F _ _ => ?_⟩
  have hp : PositivityTheory.Rg.Tf.Geo.IsNormAlong id (fun t : T => j t) ν = IsQuotNormaliser (T.map j) (ν.map e) := by
    funext ρ
    refine propext (and_congr_right fun hρ => forall_congr' fun g => ?_)
    rw [lintegral_map (f := fun h : T.map j => ρ (h * g)) (hρ.comp (measurable_subtype_coe.mul_const g)) he]
    rfl
  have gen : ∀ p q : (G → ℝ≥0∞) → Prop, p = q → ∀ [Decidable (∃ ρ, p ρ)] [Decidable (∃ ρ, q ρ)],
      (if h : ∃ ρ, p ρ then ∫ x, F x * ((h.choose x).toReal : ℂ) ∂μG else 0) =
      (if h : ∃ ρ, q ρ then ∫ x, F x * ((h.choose x).toReal : ℂ) ∂μG else 0) := by
    rintro p _ rfl _ _
    congr
  exact @gen _ _ hp (Classical.propDecidable _) (Classical.propDecidable _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotReal
section
open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

private theorem UpperTheory.V.Z.Tf.Orb.quotReal_ae_fin {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μG : Measure G) [μG.IsMulLeftInvariant] [SFinite μG]
    (H : Subgroup G) (μ : Measure H) [SFinite μ] {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μ ρ) :
    ∀ᵐ g ∂μG, ρ g < ∞ := by
  have hmul : Measurable fun p : G × H => (p.2 : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
  have hset : MeasurableSet {p : G × H | ρ ((p.2 : G) * p.1) < ∞} :=
    measurableSet_lt (hρ.1.comp hmul) measurable_const
  have h1 : ∀ᵐ g ∂μG, ∀ᵐ h : H ∂μ, ρ ((h : G) * g) < ∞ := by
    refine Filter.Eventually.of_forall fun g => ?_
    refine ae_lt_top (hρ.1.comp (measurable_subtype_coe.mul_const g)) ?_
    rw [hρ.2 g]; exact ENNReal.one_ne_top
  have h2 : ∀ᵐ h : H ∂μ, ∀ᵐ g ∂μG, ρ ((h : G) * g) < ∞ :=
    (Measure.ae_ae_comm (p := fun (g : G) (h : H) => ρ ((h : G) * g) < ∞) hset).1 h1
  have hne : μ ≠ 0 := by
    intro h0
    have := hρ.2 1
    rw [h0, lintegral_zero_measure] at this
    exact zero_ne_one this
  haveI : (ae μ).NeBot := ae_neBot.2 hne
  obtain ⟨h, hh⟩ := h2.exists
  have h3 := (measurePreserving_mul_left μG ((h : G)⁻¹)).quasiMeasurePreserving.ae hh
  simpa using h3

theorem UpperTheory.V.Z.Tf.Orb.quotReal :
    UpperTheory.V.Z.Tf.Orb.QuotReal := by
  intro G _ _ _ _ μG _ _ H μ _ A hA
  unfold quotIntegral quotLIntegral
  split_ifs with hex
  · have hρ := hex.choose_spec
    set ρ := hex.choose
    have hfin := UpperTheory.V.Z.Tf.Orb.quotReal_ae_fin μG H μ hρ
    have hm : Measurable fun g => A.indicator (1 : G → ℝ≥0∞) g * ρ g :=
      (measurable_one.indicator hA).mul hρ.1
    rw [← integral_toReal hm.aemeasurable, ← integral_complex_ofReal]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      by_cases hg : g ∈ A <;> simp [hg]
    · filter_upwards [hfin] with g hg
      by_cases hgA : g ∈ A <;> simp [hgA, hg]
  · simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.TwCentImg
section
open PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.twCentImg :
    UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.TwCentImg := by
  intro hC k E _ _ _ _ _ σ hσ n δ γ hγ hN
  have hp : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  have hsep : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := by
    have : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (γ : Matrix (Fin n) (Fin n) k).map (algebraMap k E) := rfl
    rw [this, Matrix.charpoly_map]
    exact hγ.map
  have hfix : ∀ y : GL (Fin n) k, sigmaGL σ (incl y : GL (Fin n) E) = incl y := fun y => by
    ext i j
    exact σ.commutes _
  have hcomm : ∀ a b : GL (Fin n) E, a * incl γ = incl γ * a → b * incl γ = incl γ * b → a * b = b * a := fun a b ha hb =>
    Units.ext (hC E n _ a.val b.val hsep (congrArg Units.val ha) (congrArg Units.val hb))
  have hδ : δ * incl γ = incl γ * δ := by
    have h := map_twNorm_of_pow_eq_one (sigmaGL σ) hp δ
    change sigmaGL σ (normGL σ δ) = δ⁻¹ * normGL σ δ * δ at h
    rw [hN, hfix] at h
    calc δ * incl γ = δ * (δ⁻¹ * incl γ * δ) := by rw [← h]
      _ = incl γ * δ := by group
  refine ⟨by rw [IsTwRegSemisimple, hN]; exact hsep, Subgroup.ext fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have h1 : x * incl γ = incl γ * x := hN ▸ twCent_commute_twNorm _ hp δ hx
    have h2 : x⁻¹ * δ * sigmaGL σ x = δ := hx
    have h3 : sigmaGL σ x = x := by
      calc sigmaGL σ x = δ⁻¹ * x * (x⁻¹ * δ * sigmaGL σ x) := by group
        _ = δ⁻¹ * (x * δ) := by rw [h2, mul_assoc]
        _ = x := by rw [hcomm x δ h1 hδ]; group
    have h4 : ∀ i j, ∃ c, algebraMap k E c = (x : Matrix (Fin n) (Fin n) E) i j := fun i j => by
      have hs : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) ((x : Matrix (Fin n) (Fin n) E) i j) :=
        congrArg (fun y : GL (Fin n) E => (y : Matrix (Fin n) (Fin n) E) i j) h3
      have := (IsGalois.mem_bot_iff_fixed ((x : Matrix (Fin n) (Fin n) E) i j)).mpr fun τ =>
        (Subgroup.zpowers_le.mpr hs) (hσ τ)
      rwa [IntermediateField.mem_bot] at this
    choose M hM using h4
    have e : (algebraMap k E).mapMatrix (Matrix.of M) = (x : Matrix (Fin n) (Fin n) E) := by
      ext i j
      exact hM i j
    have hd : (Matrix.of M).det ≠ 0 := fun h0 => by
      have h1 := RingHom.map_det (algebraMap k E) (Matrix.of M)
      rw [h0, map_zero, e] at h1
      exact (Matrix.GeneralLinearGroup.det x).ne_zero h1.symm
    have e' : incl (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd) = x := Units.ext e
    refine ⟨_, Subgroup.mem_centralizer_singleton_iff.2 ?_, e'⟩
    have hinj : Function.Injective (incl : GL (Fin n) k → GL (Fin n) E) := fun a b h => by
      ext i j
      exact (algebraMap k E).injective (congrArg (fun y : GL (Fin n) E => (y : Matrix (Fin n) (Fin n) E) i j) h)
    apply hinj
    rw [map_mul, map_mul, e', h1]
  · rintro ⟨t, ht, rfl⟩
    have h1 : (incl t : GL (Fin n) E) * incl γ = incl γ * incl t := by
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 ht]
    rw [mem_twCent, hfix, mul_assoc, ← hcomm _ δ h1 hδ]
    group
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.UnitMatch
section
open MeasureTheory NumberField IsDedekindDomain PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Z.Tf.Orb
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)
open scoped ENNReal

private theorem cent_facts (hCC : CentComm) {k : Type} [Field k] [TopologicalSpace k] {n : ℕ} [T2Space (GL (Fin n) k)]
    [ContinuousMul (GL (Fin n) k)] {γ : GL (Fin n) k} (hγ : IsRegSemisimple γ) :
    IsClosed ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) ∧
    ∀ a ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)), ∀ b ∈ (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)),
        Commute a b := by
  refine ⟨?_, fun a ha b hb => ?_⟩
  · have : ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = {x | x * γ = γ * x} := by
      ext x; simp [Subgroup.mem_centralizer_singleton_iff, Commute, SemiconjBy]
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  · rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
    exact Units.ext (hCC k n γ a b hγ (congrArg Units.val ha) (congrArg Units.val hb))

private theorem ind_comp {X Y M : Type} [Zero M] [One M] (u : X → Y) (A : Set Y) :
    (fun x => A.indicator (1 : Y → M) (u x)) = (u ⁻¹' A).indicator 1 := by
  funext x
  by_cases h : u x ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show x ∈ u ⁻¹' A from h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show x ∉ u ⁻¹' A from h)]

theorem UpperTheory.V.Z.Tf.Orb.unitMatch :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.TwCent → UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.QuotReal → UpperTheory.V.Z.Tf.Orb.UnitSB → UpperTheory.V.Z.Tf.Orb.UnitMatch := by
  intro hT hC hCC hTw hH hQ hU hB k E _ _ _ _ _ _ _ _ _ _ _ _ _ hur σ hσ n _ _ _ _ μE μk hE hk vE vk
  obtain ⟨a1, a2, a3, -⟩ := hT E n
  obtain ⟨b1, b2, b3, -⟩ := hT k n
  have hσc : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E) := ((hC k E).2.2 n).2 σ
  obtain ⟨h1, h2⟩ := hB k E hur σ hσ n μE μk hE hk vE vk
  have hk' : ∀ (γ : GL (Fin n) k) (μγ : Measure (Subgroup.centralizer {γ})), IsRegSemisimple γ → μγ.IsHaarMeasure →
      orbIntegralC μk γ μγ (unitFnC k) = ((orbIntegral μk γ μγ (unitFn k)).toReal : ℂ) := fun γ μγ hγ hμ => by
    obtain ⟨c1, c2⟩ := cent_facts hCC hγ
    obtain ⟨s1, -, -⟩ := hH _ _ c1 c2 μγ hμ
    unfold orbIntegralC orbIntegral unitFnC unitFn
    rw [ind_comp (fun g : GL (Fin n) k => g⁻¹ * γ * g), ind_comp (fun g : GL (Fin n) k => g⁻¹ * γ * g)]
    exact hQ _ μk _ μγ _ (((hU k n).1.preimage ((continuous_inv.mul continuous_const).mul continuous_id)).measurableSet)
  refine ⟨fun δ γ h μδ μγ hδ hN hμδ hμγ hm => ?_, fun γ μγ hγ hn hμ => ?_⟩
  · have hγ : IsRegSemisimple γ := by
      have e : ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
          (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) := by
        rw [hN, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, ← Matrix.charpoly_map]
        rfl
      have := hδ
      unfold IsTwRegSemisimple at this
      rw [e] at this
      exact (Polynomial.separable_map _).1 this
    obtain ⟨c1, c2⟩ := hTw k E σ hσ n δ hδ
    obtain ⟨s1, -, -⟩ := hH _ _ c1 c2 μδ hμδ
    rw [hk' γ μγ hγ hμγ, ← h1 δ γ h μδ μγ hδ hN hμδ hμγ hm]
    unfold twOrbIntegralC twOrbIntegral unitFnC unitFn
    rw [ind_comp (fun g : GL (Fin n) E => twConj (sigmaGL σ) g δ), ind_comp (fun g : GL (Fin n) E => twConj (sigmaGL σ) g δ)]
    exact hQ _ μE _ μδ _ (((hU E n).1.preimage ((continuous_inv.mul continuous_const).mul hσc)).measurableSet)
  · rw [hk' γ μγ hγ hμ, h2 γ μγ hγ hn hμ]
    simp
end

