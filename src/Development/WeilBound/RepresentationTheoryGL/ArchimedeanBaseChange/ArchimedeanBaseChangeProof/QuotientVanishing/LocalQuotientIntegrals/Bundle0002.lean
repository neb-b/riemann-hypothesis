module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.IsClosedEmbeddingSlice
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.Glob2Aux

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV

theorem exists_haar_map {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (e : G ≃ₜ* H) (S : Subgroup G) (ν : Measure S) [ν.IsHaarMeasure] [ν.IsInvInvariant] (T : Subgroup H)
    (hT : S.map e.toMonoidHom = T) : ∃ ν' : Measure T, ν'.IsHaarMeasure ∧ ν'.IsInvInvariant := by
  subst hT
  have hinv : ∀ y : S.map e.toMonoidHom, e.symm y ∈ S := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
    rw [← hxy]
    change e.symm (e x) ∈ S
    rw [e.symm_apply_apply]
    exact hx
  let ψ : S ≃ₜ* S.map e.toMonoidHom :=
    { toFun := fun x => ⟨e x, Subgroup.mem_map.2 ⟨x, x.2, rfl⟩⟩
      invFun := fun y => ⟨e.symm y, hinv y⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y)
      map_mul' := fun x y => Subtype.ext (map_mul e (x : G) y)
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk hinv }
  refine ⟨ν.map ψ, ContinuousMulEquiv.isHaarMeasure_map ν ψ, ⟨?_⟩⟩
  have hψ : Measurable ψ := ψ.continuous.measurable
  have hi : Measurable (Inv.inv : S → S) := continuous_inv.measurable
  have hi' : Measurable (Inv.inv : S.map e.toMonoidHom → S.map e.toMonoidHom) := continuous_inv.measurable
  show Measure.map Inv.inv (ν.map ψ) = ν.map ψ
  rw [Measure.map_map hi' hψ]
  have : (Inv.inv ∘ ψ) = ψ ∘ Inv.inv := funext fun x => (map_inv ψ x).symm
  rw [this, ← Measure.map_map hψ hi, Measure.map_inv_eq_self]

theorem isClosedEmbedding_slice {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] (c : Y) :
    Topology.IsClosedEmbedding (fun x : X => (x, c)) := by
  refine ⟨isEmbedding_prodMkLeft c, ?_⟩
  have : Set.range (fun x : X => (x, c)) = Set.univ ×ˢ {c} := by
    ext p; constructor
    · rintro ⟨x, rfl⟩; exact ⟨trivial, rfl⟩
    · rintro ⟨-, hp⟩; exact ⟨p.1, Prod.ext rfl (Set.mem_singleton_iff.1 hp).symm⟩
  rw [this]; exact isClosed_univ.prod isClosed_singleton

end PositivityTheory.Rg.BcB.CV.Glob2Aux

namespace PositivityTheory.Rg.BcB.CV

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 Glob2Aux

theorem pf_Glob2 : PositivityTheory.Rg.BcB.D4.SplitAt2 → PositivityTheory.Rg.BcB.CV.LocTor → PositivityTheory.Rg.BcB.CV.QMap → PositivityTheory.Rg.BcB.CV.QProd → PositivityTheory.Rg.BcB.CV.TwoVanish → PositivityTheory.Rg.BcB.CV.Ploc → PositivityTheory.Rg.BcB.CV.FamAt → PositivityTheory.Rg.BcB.CV.AdTop → PositivityTheory.Rg.BcB.CV.Glob2 := by
  intro hS hLT hQM hQP hTV hPl hFA hAT
  intro E _ _ _ _ n m _ _ μ _ d ν _ _ Wof a V τ φ hm hP hV hVa hφ hVC
  obtain ⟨v₁, v₂, hv⟩ := exists_pair_ne (InfinitePlace E)
  obtain ⟨G', iG, iT, iTG, iLC, iSC, iM, iB, iMGL, iBGL, e, μ₁, μ₂, θ', hμ₁, hμ₂, -, he1, hev1, hev2, heθ, hcent⟩ :=
    hS E n v₁ v₂ hv μ
  have := hμ₁
  have := hμ₂
  obtain ⟨hLCA, hT2A, hSCA, hθc, hdegm, -⟩ := hAT E n
  have := hLCA
  have := hT2A
  have := hSCA
  have hmem : ∀ g, g ∈ adCent d ↔ e g ∈ ((twCent (thC n) (locGL v₁ d)).prod (twCent (thC n) (locGL v₂ d))).prod
      (twCent θ' (e (ratGL E n d)).2) := by
    intro g
    rw [← hcent d, Subgroup.mem_map]
    constructor
    · intro h; exact ⟨g, h, rfl⟩
    · rintro ⟨x, hx, hxg⟩
      change e x = e g at hxg
      have : x = g := by rw [← e.symm_apply_apply x, hxg, e.symm_apply_apply]
      rwa [← this]
  have hE1 : ∀ t ∈ twCent (thC n) (locGL v₁ d), embInf n v₁ t ∈ adCent d := fun t ht =>
    (hmem _).2 (by rw [hev1]; exact Subgroup.mem_prod.2 ⟨Subgroup.mem_prod.2 ⟨ht, one_mem _⟩, one_mem _⟩)
  have hE2 : ∀ t ∈ twCent (thC n) (locGL v₂ d), embInf n v₂ t ∈ adCent d := fun t ht =>
    (hmem _).2 (by rw [hev2]; exact Subgroup.mem_prod.2 ⟨Subgroup.mem_prod.2 ⟨one_mem _, ht⟩, one_mem _⟩)
  obtain ⟨hsep₁, hL₁⟩ := hFA E n m d Wof a V v₁ hP hVa hE1
  obtain ⟨hsep₂, hL₂⟩ := hFA E n m d Wof a V v₂ hP hVa hE2
  obtain ⟨hcl₁, hcomm₁, -, hLC, hSC⟩ := hLT n _ hsep₁
  obtain ⟨hcl₂, hcomm₂, -, -, -⟩ := hLT n _ hsep₂
  have := hLC
  have := hSC
  have : T2Space ((GL (Fin n) ℂ × GL (Fin n) ℂ) × G') := e.symm.toHomeomorph.isEmbedding.t2Space
  have : T2Space G' := (isEmbedding_prodMkRight ((1 : GL (Fin n) ℂ × GL (Fin n) ℂ))).t2Space

  have hclP : IsClosed (((twCent (thC n) (locGL v₁ d)).prod (twCent (thC n) (locGL v₂ d)) : Subgroup _) :
      Set (GL (Fin n) ℂ × GL (Fin n) ℂ)) := by
    rw [Subgroup.coe_prod]; exact hcl₁.prod hcl₂
  have hcommP : ∀ s ∈ (twCent (thC n) (locGL v₁ d)).prod (twCent (thC n) (locGL v₂ d)),
      ∀ t ∈ (twCent (thC n) (locGL v₁ d)).prod (twCent (thC n) (locGL v₂ d)), s * t = t * s := by
    intro s hs t ht
    rw [Subgroup.mem_prod] at hs ht
    exact Prod.ext (hcomm₁ _ hs.1 _ ht.1) (hcomm₂ _ hs.2 _ ht.2)
  have hcl3 : IsClosed (twCent θ' (e (ratGL E n d)).2 : Set G') := by
    have hA : IsClosed ((((twCent (thC n) (locGL v₁ d)).prod (twCent (thC n) (locGL v₂ d))).prod
        (twCent θ' (e (ratGL E n d)).2) : Subgroup _) : Set ((GL (Fin n) ℂ × GL (Fin n) ℂ) × G')) := by
      rw [← hcent d, Subgroup.coe_map]
      exact e.toHomeomorph.isClosedMap _ hP.closed
    have h2 := hA.preimage (f := fun g : G' => ((1 : GL (Fin n) ℂ × GL (Fin n) ℂ), g))
      (continuous_const.prodMk continuous_id)
    convert h2 using 1
    ext g
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_prod, one_mem, and_self, true_and]
  have hcomm3 : ∀ s ∈ twCent θ' (e (ratGL E n d)).2, ∀ t ∈ twCent θ' (e (ratGL E n d)).2, s * t = t * s := by
    intro s hs t ht
    have hs' : e.symm ((1, 1), s) ∈ adCent d := (hmem _).2 (by
      rw [e.apply_symm_apply]; exact Subgroup.mem_prod.2 ⟨Subgroup.mem_prod.2 ⟨one_mem _, one_mem _⟩, hs⟩)
    have ht' : e.symm ((1, 1), t) ∈ adCent d := (hmem _).2 (by
      rw [e.apply_symm_apply]; exact Subgroup.mem_prod.2 ⟨Subgroup.mem_prod.2 ⟨one_mem _, one_mem _⟩, ht⟩)
    have h := congrArg e (hP.comm _ hs' _ ht')
    rw [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply] at h
    exact congrArg Prod.snd h
  have : SigmaFinite μ₁ := inferInstance
  have : SigmaFinite μ₂ := inferInstance
  have : (μ₁.prod μ₁).IsHaarMeasure := inferInstance
  have : ((μ₁.prod μ₁).prod μ₂).IsHaarMeasure := inferInstance
  obtain ⟨ν', hν'1, hν'2⟩ := exists_haar_map e (adCent d) ν _ (hcent d)
  have := hν'1
  have := hν'2

  have hFm : Measurable fun x => φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x) := by
    have h1 : Continuous fun x : GA E n => twConj (thetaA E n) x (ratGL E n d) :=
      (continuous_inv.mul continuous_const).mul hθc
    refine (hφ.cont.comp h1).measurable.mul (hV.meas.comp (Measurable.of_eval fun e' => ?_))
    have := hdegm (Wof e')
    rw [← BorelSpace.measurable_eq] at this
    exact measurable_const.sub this
  have hFi : ∀ t ∈ adCent d, ∀ x, φ (twConj (thetaA E n) (t * x) (ratGL E n d)) * V (yOf τ Wof (t * x)) =
      φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x) := by
    intro t ht x
    have ht' : t⁻¹ * ratGL E n d * thetaA E n t = ratGL E n d := ht
    have h1 : twConj (thetaA E n) (t * x) (ratGL E n d) = twConj (thetaA E n) x (ratGL E n d) := by
      calc (t * x)⁻¹ * ratGL E n d * thetaA E n (t * x)
          = x⁻¹ * (t⁻¹ * ratGL E n d * thetaA E n t) * thetaA E n x := by rw [map_mul]; group
        _ = x⁻¹ * ratGL E n d * thetaA E n x := by rw [ht']
    have h2 : yOf τ Wof (t * x) = fun e' => yOf τ Wof x e' - sdot e' (a t) := by
      funext e'
      simp only [yOf, hP.degT t ht x e']
      ring
    rw [h1, h2, hVa t ht]
  refine hQM (GA E n) ((GL (Fin n) ℂ × GL (Fin n) ℂ) × G') e μ ((μ₁.prod μ₁).prod μ₂) (adCent d) _ ν ν'
    (fun x => φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x)) hP.closed (hcent d) hFm hFi ?_
  refine hQP (GL (Fin n) ℂ × GL (Fin n) ℂ) G' (μ₁.prod μ₁) μ₂ _ _ ν' _ hclP hcl3 hcommP hcomm3
    (hFm.comp e.symm.continuous.measurable) ?_ (Or.inl ?_)
  · intro t ht x
    show _ * _ = _ * _
    rw [map_mul]
    exact hFi _ ((hmem _).2 (by rw [e.apply_symm_apply]; exact ht)) _
  intro ν₁ _ _ x'

  have hPl7 : ∀ v, GeneralLinearGroup.map (cV v) (ratGL E n d) = locGL v d := fun v =>
    (hPl E n v ⊥).2.2.2.2.2.2.1 d
  have hδ : e (ratGL E n d) = ((locGL v₁ d, locGL v₂ d), (e (ratGL E n d)).2) := by
    have h := he1 (ratGL E n d)
    rw [hPl7 v₁, hPl7 v₂] at h
    exact Prod.ext h rfl
  have hproj : ∀ y : (GL (Fin n) ℂ × GL (Fin n) ℂ) × G',
      GeneralLinearGroup.map (cV v₁) (e.symm y) = y.1.1 ∧ GeneralLinearGroup.map (cV v₂) (e.symm y) = y.1.2 := by
    intro y
    have h := he1 (e.symm y)
    rw [e.apply_symm_apply] at h
    exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩
  set g' := twConj θ' x' (e (ratGL E n d)).2 with hg'
  set g0 := e.symm (((1 : GL (Fin n) ℂ), (1 : GL (Fin n) ℂ)), x') with hg0
  set f : GL (Fin n) ℂ × GL (Fin n) ℂ → ℂ := fun g => φ (e.symm (g, g')) with hf
  set z : (Fin m → SignType) → ℝ := fun e' => yOf τ Wof g0 e' - pAt Wof v₁ 1 e' - pAt Wof v₂ 1 e' with hz
  have hsplit : ∀ x₁ x₂ : GL (Fin n) ℂ, e.symm ((x₁, x₂), x') = embInf n v₁ x₁ * (embInf n v₂ x₂ * g0) := by
    intro x₁ x₂
    rw [← e.symm_apply_apply (embInf n v₁ x₁ * (embInf n v₂ x₂ * g0))]
    congr 1
    rw [map_mul, map_mul, hev1, hev2, hg0, e.apply_symm_apply]
    simp
  have hφpart : ∀ x₁ x₂ : GL (Fin n) ℂ, twConj (thetaA E n) (e.symm ((x₁, x₂), x')) (ratGL E n d) =
      e.symm ((twConj (thC n) x₁ (locGL v₁ d), twConj (thC n) x₂ (locGL v₂ d)), g') := by
    intro x₁ x₂
    rw [← e.symm_apply_apply (twConj (thetaA E n) (e.symm ((x₁, x₂), x')) (ratGL E n d))]
    congr 1
    simp only [twConj, map_mul, map_inv, heθ, e.apply_symm_apply]
    rw [hδ, hg']
    rfl
  have hVpart : ∀ x₁ x₂ : GL (Fin n) ℂ, yOf τ Wof (e.symm ((x₁, x₂), x')) = pAt Wof v₁ x₁ + pAt Wof v₂ x₂ + z := by
    intro x₁ x₂
    funext e'
    have hh : e (embInf n v₂ x₂ * g0) = ((1, x₂), x') := by
      rw [map_mul, hev2, hg0, e.apply_symm_apply]; simp
    have hc1 : GeneralLinearGroup.map (cV v₁) (embInf n v₂ x₂ * g0) = 1 := by
      have h := (hproj (e (embInf n v₂ x₂ * g0))).1
      rw [e.symm_apply_apply, hh] at h
      exact h
    have hc0 : GeneralLinearGroup.map (cV v₂) g0 = 1 := (hproj _).2
    have h8a := (hPl E n v₁ (Wof e')).2.2.2.2.2.2.2 x₁ (embInf n v₂ x₂ * g0)
    have h8b := (hPl E n v₂ (Wof e')).2.2.2.2.2.2.2 x₂ g0
    rw [hc1, mul_one] at h8a
    rw [hc0, mul_one] at h8b
    rw [hsplit]
    simp only [yOf, pAt, Pi.add_apply, hz]
    linarith
  have hkey : (fun x₁ : GL (Fin n) ℂ × GL (Fin n) ℂ =>
      φ (twConj (thetaA E n) (e.symm (x₁, x')) (ratGL E n d)) * V (yOf τ Wof (e.symm (x₁, x')))) =
      fun x => f (twConj (thC n) x.1 (locGL v₁ d), twConj (thC n) x.2 (locGL v₂ d)) *
        V (pAt Wof v₁ x.1 + pAt Wof v₂ x.2 + z) := by
    funext x
    obtain ⟨x₁, x₂⟩ := x
    rw [hφpart, hVpart]
  have hz0 : z 0 = 0 := by
    have hr : Module.finrank E (Wof 0) = 0 := by rw [hP.zero]; exact finrank_bot E _
    have h1 := (hPl E n v₁ (Wof 0)).2.2.2.1 hP.zero
    have h2 := (hPl E n v₂ (Wof 0)).2.2.2.1 hP.zero
    simp only [hz, yOf, pAt, prof, hr, h1.1, h2.1, h1.2 g0]
    simp
  have hfc : Continuous f := hφ.cont.comp (e.symm.continuous.comp (continuous_id.prodMk continuous_const))
  have hfs : HasCompactSupport f :=
    hφ.supp.comp_isClosedEmbedding (e.symm.toHomeomorph.isClosedEmbedding.comp (isClosedEmbedding_slice g'))
  have hvc1 : ∀ g, VeryCusp fun x => f (x, g) := by
    intro g
    have h := hVC v₁ (e.symm ((1, g), g')) (hproj _).1
    have heq : (fun x => f (x, g)) = fun x => φ (embInf n v₁ x * e.symm ((1, g), g')) := by
      funext x
      simp only [hf]
      congr 1
      rw [← e.symm_apply_apply (embInf n v₁ x * e.symm ((1, g), g')), map_mul, hev1, e.apply_symm_apply]
      simp
    rw [heq]; exact h
  have hvc2 : ∀ g, VeryCusp fun x => f (g, x) := by
    intro g
    have h := hVC v₂ (e.symm ((g, 1), g')) (hproj _).2
    have heq : (fun x => f (g, x)) = fun x => φ (embInf n v₂ x * e.symm ((g, 1), g')) := by
      funext x
      simp only [hf]
      congr 1
      rw [← e.symm_apply_apply (embInf n v₂ x * e.symm ((g, 1), g')), map_mul, hev2, e.apply_symm_apply]
      simp
    rw [heq]; exact h
  exact (congrArg (quotIntegral (μ₁.prod μ₁) _ ν₁) hkey).trans
    (hTV n m μ₁ (locGL v₁ d) (locGL v₂ d) ν₁ f V (pAt Wof v₁) (pAt Wof v₂) z hm hsep₁ hsep₂ hfc hfs hvc1 hvc2 hV
      hL₁ hL₂ hz0)

end PositivityTheory.Rg.BcB.CV
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.LintegralIndicatorNeTop
section
noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped Pointwise ENNReal

namespace PositivityTheory.Rg.BcB.CV

namespace QuotientIntegral

theorem enorm_ofReal_toReal_le (r : ℝ≥0∞) : ‖((r.toReal : ℝ) : ℂ)‖ₑ ≤ r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem lintegral_indicator_ne_top (μ : Measure G) [μ.IsHaarMeasure]
    (T : Subgroup G) (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant] {C : Set G}
    (hT : IsClosed (T : Set G)) (hC : IsCompact C) {ρ0 : G → ℝ≥0∞}
    (h0 : IsQuotNormaliser T ν ρ0) :
    ∫⁻ g, ((T : Set G) * C).indicator 1 g * ρ0 g ∂μ ≠ ⊤ := by
  classical
  have : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology (T : Set G)
  have : SigmaCompactSpace T := inferInstance
  have : SFinite ν := inferInstance
  have hmcoe : Measurable (fun h : T => (h : G)) := measurable_subtype_coe
  have : ν.IsMulRightInvariant := by
    have : ν.inv.IsMulRightInvariant := inferInstance
    rwa [Measure.inv_eq_self] at this
  obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : G)
  set K : Set G := U * C with hKdef
  have hKc : IsCompact K := hUc.mul hC
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  set S : Set G := (T : Set G) * C with hSdef
  have hSm : MeasurableSet S := (hT.mul_right_of_isCompact hC).measurableSet
  have hSinv : ∀ t ∈ T, ∀ x, t * x ∈ S ↔ x ∈ S := by
    intro t ht x
    constructor
    · rintro ⟨s, hs, c, hc, hsc⟩
      exact ⟨t⁻¹ * s, T.mul_mem (T.inv_mem ht) hs, c, hc, by
        show t⁻¹ * s * c = x
        rw [mul_assoc, show s * c = t * x from hsc, inv_mul_cancel_left]⟩
    · rintro ⟨s, hs, c, hc, rfl⟩
      exact ⟨t * s, T.mul_mem ht hs, c, hc, mul_assoc _ _ _⟩
  have hKind : Measurable (K.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hKm
  set I : G → ℝ≥0∞ := fun g => ∫⁻ h : T, K.indicator 1 ((h : G) * g) ∂ν with hIdef
  have hIm : Measurable I := by
    have : Measurable (fun p : G × T => K.indicator (1 : G → ℝ≥0∞) ((p.2 : G) * p.1)) :=
      hKind.comp ((hmcoe.comp measurable_snd).mul measurable_fst)
    exact this.lintegral_prod_right'
  have hIT : ∀ t ∈ T, ∀ g, I (t * g) = I g := by
    intro t ht g
    have := lintegral_mul_right_eq_self (μ := ν)
      (fun h : T => K.indicator (1 : G → ℝ≥0∞) ((h : G) * g)) ⟨t, ht⟩
    simp only [hIdef]
    rw [← this]
    refine lintegral_congr fun h => ?_
    simp [mul_assoc]
  set V : Set T := (fun h : T => (h : G)) ⁻¹' interior U with hVdef
  have hVm : MeasurableSet V := hmcoe measurableSet_interior
  have hVpos : ν V ≠ 0 := by
    have hVo : IsOpen V := isOpen_interior.preimage continuous_subtype_val
    have h1 : (1 : T) ∈ V := by
      show ((1 : T) : G) ∈ interior U
      simpa using mem_interior_iff_mem_nhds.mpr hU1
    exact (hVo.measure_pos ν ⟨1, h1⟩).ne'
  have hIC : ∀ g ∈ S, ν V ≤ I g := by
    rintro _ ⟨t, ht, c, hc, rfl⟩
    rw [hIT t ht c, ← lintegral_indicator_one hVm]
    refine lintegral_mono fun h => ?_
    by_cases hh : h ∈ V
    · have hK : (h : G) * c ∈ K := Set.mul_mem_mul (interior_subset hh) hc
      simp [hh, hK]
    · simp [Set.indicator_apply, hh]
  have hIfin : ∀ g, I g ≠ ⊤ := by
    intro g
    have hemb : Topology.IsClosedEmbedding (fun h : T => (h : G) * g) :=
      (Homeomorph.mulRight g).isClosedEmbedding.comp hT.isClosedEmbedding_subtypeVal
    have hmeas : Measurable (fun h : T => (h : G) * g) := hmcoe.mul_const g
    have : I g = ν ((fun h : T => (h : G) * g) ⁻¹' K) := by
      rw [← lintegral_indicator_one (hmeas hKm)]
      rfl
    rw [this]
    exact ((hemb.isCompact_preimage hKc).measure_lt_top).ne
  set ρ : G → ℝ≥0∞ := S.piecewise (fun g => K.indicator 1 g * (I g)⁻¹) ρ0 with hρdef
  have hρ : IsQuotNormaliser T ν ρ := by
    refine ⟨Measurable.piecewise hSm (hKind.mul hIm.inv) h0.1, fun g => ?_⟩
    by_cases hg : g ∈ S
    · have hmem : ∀ h : T, (h : G) * g ∈ S := fun h => (hSinv _ h.2 g).2 hg
      calc ∫⁻ h : T, ρ ((h : G) * g) ∂ν = ∫⁻ h : T, K.indicator 1 ((h : G) * g) * (I g)⁻¹ ∂ν := by
            refine lintegral_congr fun h => ?_
            simp only [hρdef, Set.piecewise_eq_of_mem _ _ _ (hmem h), hIT _ h.2]
        _ = I g * (I g)⁻¹ := lintegral_mul_const _ (hKind.comp (hmcoe.mul_const g))
        _ = 1 := ENNReal.mul_inv_cancel
              (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hVpos) (hIC g hg))) (hIfin g)
    · have hmem : ∀ h : T, (h : G) * g ∉ S := fun h hh => hg ((hSinv _ h.2 g).1 hh)
      rw [← h0.2 g]
      refine lintegral_congr fun h => ?_
      simp only [hρdef, Set.piecewise_eq_of_notMem _ _ _ (hmem h)]
  have hF1 : Measurable (S.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hSm
  have hFinv : ∀ h ∈ T, ∀ g, S.indicator (1 : G → ℝ≥0∞) (h * g) = S.indicator 1 g := by
    intro h hh g
    simp only [Set.indicator_apply, hSinv h hh g, Pi.one_apply]
  rw [lintegral_normaliser_eq hF1 hFinv h0 hρ]
  refine ne_of_lt (lt_of_le_of_lt (b := ∫⁻ g, K.indicator 1 g * (ν V)⁻¹ ∂μ)
    (lintegral_mono fun g => ?_) ?_)
  · by_cases hg : g ∈ S
    · simp only [Set.indicator_of_mem hg, Pi.one_apply, one_mul, hρdef,
        Set.piecewise_eq_of_mem _ _ _ hg]
      gcongr
      exact hIC g hg
    · simp [hg]
  · rw [lintegral_mul_const _ hKind, lintegral_indicator_one hKm]
    exact ENNReal.mul_lt_top hKc.measure_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hVpos))

theorem main (μ : Measure G) [μ.IsHaarMeasure] (T : Subgroup G) (ν : Measure T) [ν.IsHaarMeasure]
    [ν.IsInvInvariant] (C : Set G) (hT : IsClosed (T : Set G)) (hC : IsCompact C) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (F : G → ℂ) (B : ℝ), 0 ≤ B → Measurable F →
      (∀ t ∈ T, ∀ x, F (t * x) = F x) → (∀ x, F x ≠ 0 → x ∈ (T : Set G) * C) →
      (∀ x ∈ C, ‖F x‖ ≤ B) → quotLIntegral μ T ν (fun x => ‖F x‖ₑ) ≠ ⊤ ∧
        ‖quotIntegral μ T ν F‖ ≤ A * B := by
  classical
  by_cases hex : ∃ ρ, IsQuotNormaliser T ν ρ
  · have h0 : IsQuotNormaliser T ν hex.choose := hex.choose_spec
    set S : Set G := (T : Set G) * C with hSdef
    have hL : ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ ≠ ⊤ :=
      lintegral_indicator_ne_top μ T ν hT hC h0
    refine ⟨(∫⁻ g, S.indicator 1 g * hex.choose g ∂μ).toReal, ENNReal.toReal_nonneg,
      fun F B hB hF hFT hFS hFC => ?_⟩
    have hbound : ∀ g, ‖F g‖ₑ ≤ ENNReal.ofReal B * S.indicator 1 g := by
      intro g
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg, Pi.one_apply, mul_one]
        obtain ⟨t, ht, c, hc, rfl⟩ := hg
        rw [hFT t ht c, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hFC c hc)
      · have : F g = 0 := by
          by_contra h
          exact hg (hFS g h)
        simp [this]
    have hle : ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ ≤
        ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ := by
      calc ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ
          ≤ ∫⁻ g, ENNReal.ofReal B * (S.indicator 1 g * hex.choose g) ∂μ :=
            lintegral_mono fun g => by
              rw [← mul_assoc]
              gcongr
              exact hbound g
        _ = ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hne : ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL
    have hfin : ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ ≠ ⊤ := ne_top_of_le_ne_top hne hle
    refine ⟨by rw [quotLIntegral, dite_eq_left hex]; exact hfin, ?_⟩
    rw [quotIntegral, dite_eq_left hex]
    calc ‖∫ g, F g * ((hex.choose g).toReal : ℂ) ∂μ‖
        = ‖∫ g, F g * ((hex.choose g).toReal : ℂ) ∂μ‖ₑ.toReal := (toReal_enorm _).symm
      _ ≤ (∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ).toReal := by
          refine ENNReal.toReal_mono hfin ((enorm_integral_le_lintegral_enorm _).trans
            (lintegral_mono fun g => ?_))
          rw [enorm_mul]
          gcongr
          exact enorm_ofReal_toReal_le _
      _ ≤ (ENNReal.ofReal B * ∫⁻ g, S.indicator 1 g * hex.choose g ∂μ).toReal :=
          ENNReal.toReal_mono hne hle
      _ = (∫⁻ g, S.indicator 1 g * hex.choose g ∂μ).toReal * B := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB, mul_comm]
  · refine ⟨0, le_rfl, fun F B _ _ _ _ _ => ?_⟩
    simp [quotLIntegral, quotIntegral, hex]

end QuotientIntegral

theorem pf_QInt : QInt := by
  intro G _ _ _ _ _ _ _ _ μ _ T ν _ _ C hT hC
  exact QuotientIntegral.main μ T ν C hT hC

end PositivityTheory.Rg.BcB.CV
end
end

