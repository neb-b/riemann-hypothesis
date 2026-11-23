module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PTwoVanish
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.CV.SecondVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV

theorem hcs_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X × Y → ℂ} (hf : HasCompactSupport f) (g : X) : HasCompactSupport fun y => f (g, y) := by
  refine HasCompactSupport.intro (IsCompact.image hf continuous_snd) fun y hy => ?_
  by_contra h
  exact hy ⟨(g, y), subset_tsupport _ (Function.mem_support.2 h), rfl⟩

theorem hcs_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    {f : X × Y → ℂ} (hf : HasCompactSupport f) (g : Y) : HasCompactSupport fun y => f (y, g) := by
  refine HasCompactSupport.intro (IsCompact.image hf continuous_fst) fun y hy => ?_
  by_contra h
  exact hy ⟨(y, g), subset_tsupport _ (Function.mem_support.2 h), rfl⟩

theorem vp_bdd_on {X : Type*} [TopologicalSpace X] {m : ℕ} {V : ((Fin m → SignType) → ℝ) → ℂ} (hV : VP V)
    {q : X → (Fin m → SignType) → ℝ} (hq : Continuous q) {K : Set X} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ‖V (q x)‖ ≤ B := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hq.continuousOn
  obtain ⟨B, hB⟩ := hV.bdd R
  refine ⟨max B 0, le_max_right _ _, fun x hx => (hB (q x) fun e => ?_).trans (le_max_left _ _)⟩
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm (q x) e).trans (hR x hx)

theorem tor2 {n m : ℕ} {d₁ d₂ : GL (Fin n) ℂ} {V : ((Fin m → SignType) → ℝ) → ℂ}
    {p₁ p₂ : GL (Fin n) ℂ → (Fin m → SignType) → ℝ} (h₁ : LocFam d₁ V p₁) (h₂ : LocFam d₂ V p₂)
    {t₁ t₂ : GL (Fin n) ℂ} (ht₁ : t₁ ∈ twCent (thC n) d₁) (ht₂ : t₂ ∈ twCent (thC n) d₂) (x₁ x₂ : GL (Fin n) ℂ)
    (z : (Fin m → SignType) → ℝ) : V (p₁ (t₁ * x₁) + p₂ (t₂ * x₂) + z) = V (p₁ x₁ + p₂ x₂ + z) := by
  rw [add_assoc, h₁.tor t₁ ht₁, add_left_comm (p₁ x₁), h₂.tor t₂ ht₂, add_left_comm (p₂ x₂), ← add_assoc]

end PositivityTheory.Rg.BcB.CV.SecondVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV PositivityTheory.Rg.BcB.CV.SecondVanishing in
theorem PositivityTheory.Rg.BcB.CV.pf_TwoVanish : PositivityTheory.Rg.BcB.LocVanish → PositivityTheory.Rg.BcB.D4.LocProper → PositivityTheory.Rg.BcB.CV.LocTor → PositivityTheory.Rg.BcB.CV.QInt → PositivityTheory.Rg.BcB.CV.QAdd → PositivityTheory.Rg.BcB.CV.QProd → PositivityTheory.Rg.BcB.CV.OneVanish → PositivityTheory.Rg.BcB.CV.TwoVanish := by
  intro hLV hLP hLT hQI hQA hQP hOV n m _ _ μ _ d₁ d₂ ν _ _ f V p₁ p₂ z hm hd₁ hd₂ hfc hfs hcu₁ hcu₂ hV hF₁ hF₂ hz
  obtain ⟨hcl₁, hcomm₁, hθ, hlc, hsc⟩ := hLT n d₁ hd₁
  obtain ⟨hcl₂, hcomm₂, -, -, -⟩ := hLT n d₂ hd₂
  have := hlc
  have := hsc
  have hc₁ : Continuous fun x => twConj (thC n) x d₁ := by
    show Continuous fun x => x⁻¹ * d₁ * thC n x
    exact (continuous_inv.mul continuous_const).mul hθ
  have hc₂ : Continuous fun x => twConj (thC n) x d₂ := by
    show Continuous fun x => x⁻¹ * d₂ * thC n x
    exact (continuous_inv.mul continuous_const).mul hθ
  have hΦc : Continuous fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) :=
    hfc.comp ((hc₁.comp continuous_fst).prodMk (hc₂.comp continuous_snd))
  have hΦinv : ∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x : GL (Fin n) ℂ × GL (Fin n) ℂ,
      f (twConj (thC n) (t * x).1 d₁, twConj (thC n) (t * x).2 d₂) = f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) := by
    intro t ht x
    rw [Prod.fst_mul, Prod.snd_mul, twConj_mul_left _ _ (Subgroup.mem_prod.1 ht).1,
      twConj_mul_left _ _ (Subgroup.mem_prod.1 ht).2]
  obtain ⟨C₁, hC₁, hsub₁⟩ := hLP n d₁ hd₁ (Prod.fst '' tsupport f) (IsCompact.image hfs continuous_fst)
  obtain ⟨C₂, hC₂, hsub₂⟩ := hLP n d₂ hd₂ (Prod.snd '' tsupport f) (IsCompact.image hfs continuous_snd)
  obtain ⟨Bf, hBf⟩ := hfc.bounded_above_of_compact_support hfs
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hBf (1, 1))
  have hclosed : IsClosed (((twCent (thC n) d₁).prod (twCent (thC n) d₂) : Subgroup _) :
      Set (GL (Fin n) ℂ × GL (Fin n) ℂ)) := by
    rw [Subgroup.coe_prod]; exact hcl₁.prod hcl₂
  obtain ⟨A₀, -, hA₀⟩ := hQI (GL (Fin n) ℂ × GL (Fin n) ℂ) (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
    (C₁ ×ˢ C₂) hclosed (hC₁.prod hC₂)
  have hint : ∀ h : GL (Fin n) ℂ × GL (Fin n) ℂ → ℂ, Measurable h →
      (∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x, h (t * x) = h x) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C₁ ×ˢ C₂, ‖h x‖ ≤ B) →
      quotLIntegral (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
        (fun x => ‖f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * h x‖ₑ) ≠ ⊤ := by
    intro h hm hinv ⟨B, hB0, hB⟩
    refine (hA₀ (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * h x) (Bf * B) (mul_nonneg hBf0 hB0)
      (hΦc.measurable.mul hm) (fun t ht x => by rw [hΦinv t ht x, hinv t ht x]) ?_ ?_).1
    · intro x hx
      have hfx : f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) ≠ 0 := left_ne_zero_of_mul hx
      have hts : (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) ∈ tsupport f :=
        subset_tsupport _ (Function.mem_support.2 hfx)
      obtain ⟨a₁, ha₁, b₁, hb₁, e₁⟩ := Set.mem_mul.1 (hsub₁ (show twConj (thC n) x.1 d₁ ∈ Prod.fst '' tsupport f from ⟨_, hts, rfl⟩))
      obtain ⟨a₂, ha₂, b₂, hb₂, e₂⟩ := Set.mem_mul.1 (hsub₂ (show twConj (thC n) x.2 d₂ ∈ Prod.snd '' tsupport f from ⟨_, hts, rfl⟩))
      exact Set.mem_mul.2 ⟨(a₁, a₂), Subgroup.mem_prod.2 ⟨ha₁, ha₂⟩, (b₁, b₂), ⟨hb₁, hb₂⟩, Prod.ext e₁ e₂⟩
    · intro x hx
      rw [norm_mul]
      exact mul_le_mul (hBf _) (hB x hx) (norm_nonneg _) hBf0
  have hq : Continuous fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => p₁ x.1 + p₂ x.2 + z :=
    ((hF₁.cont.comp continuous_fst).add (hF₂.cont.comp continuous_snd)).add continuous_const
  have hq' : Continuous fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => p₁ x.1 := hF₁.cont.comp continuous_fst
  have hmF : Measurable fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => V (p₁ x.1 + p₂ x.2 + z) := hV.meas.comp hq.measurable
  have hmB : Measurable fun x : GL (Fin n) ℂ × GL (Fin n) ℂ => V (p₁ x.1) := hV.meas.comp hq'.measurable
  have hiF : ∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x : GL (Fin n) ℂ × GL (Fin n) ℂ,
      V (p₁ (t * x).1 + p₂ (t * x).2 + z) = V (p₁ x.1 + p₂ x.2 + z) := fun t ht x =>
    tor2 hF₁ hF₂ (Subgroup.mem_prod.1 ht).1 (Subgroup.mem_prod.1 ht).2 x.1 x.2 z
  have hiB : ∀ t ∈ (twCent (thC n) d₁).prod (twCent (thC n) d₂), ∀ x : GL (Fin n) ℂ × GL (Fin n) ℂ,
      V (p₁ (t * x).1) = V (p₁ x.1) := fun t ht x => by
    simpa using hF₁.tor t.1 (Subgroup.mem_prod.1 ht).1 x.1 0
  have hIF := hint _ hmF hiF (vp_bdd_on hV hq (hC₁.prod hC₂))
  have hIB := hint _ hmB hiB (vp_bdd_on hV hq' (hC₁.prod hC₂))
  have hsplit := (hQA (GL (Fin n) ℂ × GL (Fin n) ℂ) (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν).2.1
    (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1 + p₂ x.2 + z))
    (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1))
    (hΦc.measurable.mul hmF) (hΦc.measurable.mul hmB) hIF hIB

  have hA : quotIntegral (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
      (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1 + p₂ x.2 + z) -
        f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1)) = 0 := by
    refine hQP _ _ μ μ _ _ ν _ hcl₁ hcl₂ hcomm₁ hcomm₂
      ((hΦc.measurable.mul hmF).sub (hΦc.measurable.mul hmB))
      (fun t ht x => by simp only [hΦinv t ht x, hiF t ht x, hiB t ht x]) (Or.inl fun ν₁ _ _ x₂ => ?_)
    have h1 := hOV n m μ d₁ ν₁ (fun y => f (y, twConj (thC n) x₂ d₂)) V p₁ (p₂ x₂ + z) hd₁
      (hfc.comp (continuous_id.prodMk continuous_const)) (hcs_right hfs _) (hcu₁ _) hV hF₁
      (by rw [Pi.add_apply, hF₂.zero, hz, add_zero])
    calc _ = quotIntegral μ (twCent (thC n) d₁) ν₁ (fun x => f (twConj (thC n) x d₁, twConj (thC n) x₂ d₂) *
          (V (p₁ x + (p₂ x₂ + z)) - V (p₁ x))) := by
          congr 1; funext x; dsimp only; rw [add_assoc]; ring
      _ = 0 := h1

  have hB : quotIntegral (μ.prod μ) ((twCent (thC n) d₁).prod (twCent (thC n) d₂)) ν
      (fun x => f (twConj (thC n) x.1 d₁, twConj (thC n) x.2 d₂) * V (p₁ x.1)) = 0 := by
    refine hQP _ _ μ μ _ _ ν _ hcl₁ hcl₂ hcomm₁ hcomm₂ (hΦc.measurable.mul hmB)
      (fun t ht x => by simp only [hΦinv t ht x, hiB t ht x]) (Or.inr fun ν₂ _ _ x₁ => ?_)
    have hne : (fun _ : Fin m => (1 : SignType)) ≠ 0 := by
      intro h
      have := congrFun h ⟨0, Nat.pos_of_ne_zero hm⟩
      simp at this
    obtain ⟨W₁, W₂, hW, -⟩ := hF₂.nil _ hne
    have h1 := hLV n μ (fun y => f (twConj (thC n) x₁ d₁, y)) (fun _ => 1) d₂ ν₂ W₁ W₂
      (hfc.comp (continuous_const.prodMk continuous_id)) (hcs_left hfs _) (hcu₂ _) hd₂ hW.1 hW.2.1 hW.2.2.1 hW.2.2.2
      measurable_const (fun _ _ => ⟨1, fun _ _ => by simp⟩) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    calc _ = quotIntegral μ (twCent (thC n) d₂) ν₂ (fun x => V (p₁ x₁) *
          (f (twConj (thC n) x₁ d₁, twConj (thC n) x d₂) * (fun _ => (1 : ℂ)) x)) := by
          congr 1; funext x; dsimp only; ring
      _ = V (p₁ x₁) * quotIntegral μ (twCent (thC n) d₂) ν₂ (fun x =>
          f (twConj (thC n) x₁ d₁, twConj (thC n) x d₂) * (fun _ => (1 : ℂ)) x) := (hQA _ μ _ ν₂).2.2 _ _
      _ = 0 := by rw [h1, mul_zero]
  rw [hA, hB] at hsplit
  linear_combination -hsplit
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PfQMap
section
open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal NNReal

noncomputable section

namespace PositivityTheory.Rg.BcB.CV.QuotientMapAlt

def subEquiv {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    (e : G ≃ₜ* G') (T : Subgroup G) : T ≃ₜ* T.map e.toMonoidHom where
  toFun t := ⟨e t, Subgroup.mem_map.2 ⟨t, t.2, rfl⟩⟩
  invFun t := ⟨e.symm t, by
    obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.1 t.2
    have h : e.symm (t : G') = s := by
      rw [← hst]
      exact e.symm_apply_apply s
    rw [h]
    exact hs⟩
  left_inv t := Subtype.ext (e.symm_apply_apply (t : G))
  right_inv t := Subtype.ext (e.apply_symm_apply (t : G'))
  map_mul' s t := Subtype.ext (map_mul e (s : G) (t : G))
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

end PositivityTheory.Rg.BcB.CV.QuotientMapAlt

open PositivityTheory.Rg.BcB.CV.QuotientMapAlt in
theorem PositivityTheory.Rg.BcB.CV.pf_QMap : PositivityTheory.Rg.BcB.D4.NormEq → PositivityTheory.Rg.BcB.CV.QMap := by
  intro hN G _ _ _ _ _ _ _ _ G' _ _ _ _ _ _ _ _ e μ _ μ' _ T T' ν _ _ ν' _ _ F hTc hT hF hFT h0
  subst hT
  have hT'c : IsClosed ((T.map e.toMonoidHom : Subgroup G') : Set G') := by
    rw [Subgroup.coe_map]
    exact e.toHomeomorph.isClosedMap _ hTc
  have : SecondCountableTopology T := inferInstanceAs (SecondCountableTopology (T : Set G))
  have : SecondCountableTopology (T.map e.toMonoidHom) :=
    inferInstanceAs (SecondCountableTopology ((T.map e.toMonoidHom : Subgroup G') : Set G'))
  have : LocallyCompactSpace T := hTc.locallyCompactSpace
  have : LocallyCompactSpace (T.map e.toMonoidHom) := hT'c.locallyCompactSpace
  by_cases hex : ∃ ρ, IsQuotNormaliser T ν ρ
  swap
  · rw [quotIntegral, dite_eq_right hex]
  rw [quotIntegral, dite_eq_left hex]
  have hρ : IsQuotNormaliser T ν hex.choose := hex.choose_spec
  set ρ := hex.choose

  let φ := subEquiv e T
  let c : ℝ≥0 := Measure.haarScalarFactor (Measure.map φ.symm ν') ν
  have hc : Measure.map φ.symm ν' = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : (0 : ℝ≥0) < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hcne : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0.ne'
  let ρ' : G' → ℝ≥0∞ := fun x => (c : ℝ≥0∞)⁻¹ * ρ (e.symm x)
  have hρ' : IsQuotNormaliser (T.map e.toMonoidHom) ν' ρ' := by
    refine ⟨measurable_const.mul (hρ.1.comp e.symm.continuous.measurable), fun x => ?_⟩
    have hk : Measurable fun t : T => ρ ((t : G) * e.symm x) :=
      hρ.1.comp (measurable_subtype_coe.mul_const _)
    have h1 : ∫⁻ h : T.map e.toMonoidHom, ρ' ((h : G') * x) ∂ν' =
        (c : ℝ≥0∞)⁻¹ * ∫⁻ t, ρ ((t : G) * e.symm x) ∂(Measure.map φ.symm ν') := by
      rw [lintegral_map hk (show Measurable (⇑φ.symm) from φ.symm.continuous.measurable),
        ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hcne)]
      refine lintegral_congr fun h => ?_
      show (c : ℝ≥0∞)⁻¹ * ρ (e.symm ((h : G') * x)) = _
      rw [map_mul]
      rfl
    rw [h1, hc, lintegral_smul_measure, hρ.2, ENNReal.smul_def, smul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel hcne ENNReal.coe_ne_top

  let eM : G' ≃ᵐ G := e.symm.toHomeomorph.toMeasurableEquiv
  have hH : (Measure.map eM μ').IsHaarMeasure :=
    (inferInstance : (Measure.map e.symm μ').IsHaarMeasure)
  let a : ℝ≥0 := Measure.haarScalarFactor (Measure.map eM μ') μ
  have ha : Measure.map eM μ' = a • μ := Measure.isMulLeftInvariant_eq_smul _ _
  have ha0 : (0 : ℝ≥0) < a := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hF' : Measurable fun x => F (e.symm x) := hF.comp e.symm.continuous.measurable
  have hFT' : ∀ h ∈ T.map e.toMonoidHom, ∀ x, F (e.symm (h * x)) = F (e.symm x) := by
    intro h hh x
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hh
    show F (e.symm (e t * x)) = _
    rw [map_mul, e.symm_apply_apply]
    exact hFT t ht _
  have hex' : ∃ ρ, IsQuotNormaliser (T.map e.toMonoidHom) ν' ρ := ⟨ρ', hρ'⟩
  rw [quotIntegral, dite_eq_left hex', hN G' μ' _ ν' _ _ ρ' hF' hFT' hex'.choose_spec hρ'] at h0
  have key : a • ∫ g, F g * ((((c : ℝ≥0∞)⁻¹ * ρ g).toReal : ℝ) : ℂ) ∂μ = 0 := by
    rw [← integral_smul_nnreal_measure, ← ha, integral_map_equiv]
    exact h0
  have key2 : ∫ g, F g * ((((c : ℝ≥0∞)⁻¹ * ρ g).toReal : ℝ) : ℂ) ∂μ = 0 := by
    have := congrArg (fun z : ℂ => (a⁻¹ : ℝ≥0) • z) key
    simpa [smul_smul, inv_mul_cancel₀ ha0.ne'] using this
  have hcr : ((c : ℝ≥0∞)⁻¹).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top, ENNReal.inv_ne_top.2 hcne⟩
  have key3 : ∫ g, F g * ((((c : ℝ≥0∞)⁻¹ * ρ g).toReal : ℝ) : ℂ) ∂μ =
      (((c : ℝ≥0∞)⁻¹).toReal : ℂ) * ∫ g, F g * (((ρ g).toReal : ℝ) : ℂ) ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [ENNReal.toReal_mul, Complex.ofReal_mul]
    ring
  rw [key3] at key2
  exact (mul_eq_zero.1 key2).resolve_left (by exact_mod_cast hcr)
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.QuotIntegralMulRight
section
noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace PositivityTheory.Rg.BcB.CV.VolumeFunction

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

theorem gam_abs_le {m : ℕ} (y : (Fin m → SignType) → ℝ) (a : Fin m → ℝ) :
    |gam y a| ≤ (Fintype.card (Finset (Fin m → SignType)) : ℝ) := by
  classical
  unfold gam gamOn
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 ?_).trans ?_
  · intro s _
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun e _ => by split_ifs <;> simp)
  · rw [nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_le_univ _

theorem map_count_equiv {H : Type*} [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H]
    (e : H ≃ H) : Measure.map e (Measure.count : Measure H) = Measure.count := by
  ext s hs
  rw [Measure.map_apply (measurable_of_countable _) hs]
  have h : e ⁻¹' s = e.symm '' s := Set.ext fun x => ⟨fun hx => ⟨e x, hx, e.symm_apply_apply x⟩, by
    rintro ⟨y, hy, rfl⟩
    show e (e.symm y) ∈ s
    rw [e.apply_symm_apply]; exact hy⟩
  rw [h, Measure.count_injective_image e.symm.injective]

theorem count_isHaar {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H]
    [MeasurableSingletonClass H] [Countable H] : (Measure.count : Measure H).IsHaarMeasure where
  lt_top_of_isCompact := fun _ hK => Measure.count_apply_lt_top.2 hK.finite_of_discrete
  map_mul_left_eq_self := fun g => map_count_equiv (Equiv.mulLeft g)
  open_pos := fun _ _ hU => by rw [Ne, Measure.count_eq_zero_iff]; exact hU.ne_empty

theorem count_isInv {H : Type*} [Group H] [MeasurableSpace H]
    [MeasurableSingletonClass H] [Countable H] : (Measure.count : Measure H).IsInvInvariant :=
  ⟨map_count_equiv (Equiv.inv H)⟩

theorem quotIntegral_mul_right (hNE : NormEq) {T : Type} [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
    [LocallyCompactSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (ν : Measure T) [ν.IsHaarMeasure] (hcomm : ∀ s t : T, s * t = t * s) (Γ : Subgroup T) (μΓ : Measure Γ)
    [SFinite μΓ] [μΓ.IsInvInvariant] (F : T → ℂ) (hF : Measurable F) (hinv : ∀ g ∈ Γ, ∀ t, F (g * t) = F t)
    (s : T) : quotIntegral ν Γ μΓ (fun t => F (t * s)) = quotIntegral ν Γ μΓ F := by
  unfold quotIntegral
  by_cases hρ : ∃ ρ, IsQuotNormaliser Γ μΓ ρ
  · rw [dif_pos hρ, dif_pos hρ]
    have hρn := hρ.choose_spec
    have : ν.IsMulRightInvariant := ⟨fun g => by
      have h : (fun x => x * g) = (fun x => g * x) := funext fun x => hcomm x g
      rw [h]; exact map_mul_left_eq_self ν g⟩
    have hρ' : IsQuotNormaliser Γ μΓ (fun t => hρ.choose (t * s⁻¹)) := by
      refine ⟨hρn.1.comp (measurable_mul_const _), fun g => ?_⟩
      show ∫⁻ h, hρ.choose ((h : T) * g * s⁻¹) ∂μΓ = 1
      simp only [mul_assoc]
      exact hρn.2 _
    have h1 := integral_mul_right_eq_self (μ := ν) (fun t => F t * ((hρ.choose (t * s⁻¹)).toReal : ℂ)) s
    simp only [mul_inv_cancel_right] at h1
    rw [h1]
    exact hNE T ν Γ μΓ F _ _ hF hinv hρ' hρn
  · rw [dif_neg hρ, dif_neg hρ]

end PositivityTheory.Rg.BcB.CV.VolumeFunction

namespace PositivityTheory.Rg.BcB.CV

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV.VolumeFunction

theorem pf_Vfun : PositivityTheory.Rg.BcB.ChainSum → PositivityTheory.Rg.BcB.D4.RatDisc → PositivityTheory.Rg.BcB.D4.NormEq → PositivityTheory.Rg.BcB.CV.QInt →
    PositivityTheory.Rg.BcB.CV.QAdd → PositivityTheory.Rg.BcB.CV.Vfun := by
  intro hCS hRD hNE hQI hQA T _ _ _ _ _ _ _ _ ν _ Γ m a hcomm hdisc hac hadd hΓ hprop
  have := hdisc
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hcl : IsClosed (Γ : Set T) := Subgroup.isClosed_of_discrete
  have : (Measure.count : Measure Γ).IsHaarMeasure := count_isHaar
  have : (Measure.count : Measure Γ).IsInvInvariant := count_isInv
  have hmeasF : ∀ y : (Fin m → SignType) → ℝ, Measurable fun t => (gam y (a t) : ℂ) := fun y =>
    Complex.measurable_ofReal.comp (((hCS m).2.2.1 y).comp hac.measurable)
  have hinv : ∀ y : (Fin m → SignType) → ℝ, ∀ g ∈ Γ, ∀ t, (gam y (a (g * t)) : ℂ) = (gam y (a t) : ℂ) := by
    intro y g hg t
    rw [hadd, hΓ g hg, zero_add]
  set K : ℝ := (Fintype.card (Finset (Fin m → SignType)) : ℝ) with hKdef
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have key : ∀ M : ℝ, ∃ B : ℝ, ∀ y : (Fin m → SignType) → ℝ, (∀ e, |y e| ≤ M) →
      quotLIntegral ν Γ Measure.count (fun t => ‖(gam y (a t) : ℂ)‖ₑ) ≠ ⊤ ∧
        ‖quotIntegral ν Γ Measure.count (fun t => (gam y (a t) : ℂ))‖ ≤ B := by
    intro M
    obtain ⟨C, hC, hCm⟩ := hprop (2 * M)
    obtain ⟨A, _, hA⟩ := hQI T ν Γ Measure.count C hcl hC
    refine ⟨A * K, fun y hy => hA _ K hK0 (hmeasF y) (hinv y) ?_ ?_⟩
    · intro t ht
      apply hCm
      intro i
      exact (hCS m).2.1 y M (a t) hy (fun h => ht (by rw [h, Complex.ofReal_zero])) i
    · intro x _
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact gam_abs_le _ _
  have hfin : ∀ y : (Fin m → SignType) → ℝ,
      quotLIntegral ν Γ Measure.count (fun t => ‖(gam y (a t) : ℂ)‖ₑ) ≠ ⊤ := by
    intro y
    obtain ⟨B, hB⟩ := key (∑ e, |y e|)
    exact (hB y fun e => Finset.single_le_sum (f := fun e => |y e|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ e)).1
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · by_cases hρ : ∃ ρ, IsQuotNormaliser Γ (Measure.count : Measure Γ) ρ
    · simp only [quotIntegral, dif_pos hρ]
      have h2 : Measurable fun p : ((Fin m → SignType) → ℝ) × T => (p.1, a p.2) :=
        measurable_fst.prodMk (hac.measurable.comp measurable_snd)
      have hj : Measurable fun p : ((Fin m → SignType) → ℝ) × T =>
          (gam p.1 (a p.2) : ℂ) * ((hρ.choose p.2).toReal : ℂ) :=
        (Complex.measurable_ofReal.comp ((hRD.2 m).comp h2)).mul
          (Complex.measurable_ofReal.comp ((hρ.choose_spec.1.ennreal_toReal).comp measurable_snd))
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    · simp only [quotIntegral, dif_neg hρ]
      exact measurable_const
  · intro M
    obtain ⟨B, hB⟩ := key M
    exact ⟨B, fun y hy => (hB y hy).2⟩
  · intro y y' e s t h
    have hsub : ∀ u v : (Fin m → SignType) → ℝ,
        quotIntegral ν Γ Measure.count (fun x => (gam u (a x) : ℂ)) -
          quotIntegral ν Γ Measure.count (fun x => (gam v (a x) : ℂ)) =
        quotIntegral ν Γ Measure.count (fun x => ((gam u (a x) - gam v (a x) : ℝ) : ℂ)) := by
      intro u v
      rw [← (hQA T ν Γ Measure.count).2.1 _ _ (hmeasF u) (hmeasF v) (hfin u) (hfin v)]
      simp only [Complex.ofReal_sub]
    rw [hsub, hsub]
    congr 1
    funext x
    rw [(hCS m).2.2.2.2 y y' e s t (a x) h]
  · intro y s
    have hrew : ∀ t, (gam (fun e => y e - sdot e (a s)) (a t) : ℂ) = (gam y (a (t * s)) : ℂ) := by
      intro t
      have h := (hCS m).2.2.2.1 (fun e => y e - sdot e (a s)) (a t) (a s)
      simp only [sub_add_cancel] at h
      rw [hadd, h]
    simp only [hrew]
    exact quotIntegral_mul_right hNE ν hcomm Γ Measure.count _ (hmeasF y) (hinv y) s

end PositivityTheory.Rg.BcB.CV

end
end

