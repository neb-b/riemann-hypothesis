module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.CVEmbInfSelf
section
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped ComplexOrder

namespace PositivityTheory.Rg.BcB.CV.LocalPlacePositivity

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cV_alg (v : InfinitePlace E) (x : E) : cV v (algebraMap E (Ad E) x) = v.embedding x :=
  pInf_algebraMap x v

open Classical in
theorem cV_embInf (v w : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (cV w) (embInf n v y) = if w = v then y else 1 := by
  ext i j
  change (GeneralLinearGroup.map (pInf E) (embInf n v y)) i j w = _
  unfold embInf
  rw [MonoidHom.comp_apply, pInf_infGL]
  change (MonoidHom.mulSingle (fun _ : InfinitePlace E => GL (Fin n) ℂ) v y w).val i j = _
  by_cases h : w = v
  · subst h
    simp
  · simp [h]

theorem cV_embInf_self (v : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (cV v) (embInf n v y) = y := by
  classical
  rw [cV_embInf, if_pos rfl]

theorem pFin_embInf (v : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (pFin E) (embInf n v y) = 1 := by
  unfold embInf
  exact pFin_infGL _

theorem cW_embInf (w : HeightOneSpectrum (𝓞 E)) (v : InfinitePlace E) (y : GL (Fin n) ℂ) :
    GeneralLinearGroup.map (cW w) (embInf n v y) = 1 := by
  have e : GeneralLinearGroup.map (cW w) (embInf n v y) =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (embInf n v y)) := rfl
  rw [e, pFin_embInf, map_one]

theorem cV_ratGL (v : InfinitePlace E) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (ratGL E n d) = locGL v d := by
  ext i j
  exact pInf_algebraMap (d i j) v

theorem map_inv_val {R : Type} [CommRing R] (f : Ad E →+* R) (x : GA E n) :
    ((x⁻¹ : GA E n).val).map f = ((GeneralLinearGroup.map f x)⁻¹ : GL (Fin n) R).val := by
  rw [← map_inv]; rfl

theorem frame_map_eq {R : Type} [CommRing R] (f : Ad E →+* R) (x y : GA E n)
    (h : GeneralLinearGroup.map f x = GeneralLinearGroup.map f y) {r : ℕ} (M : Matrix (Fin n) (Fin r) E) :
    (frame x M).map f = (frame y M).map f := by
  rw [frame, frame, Matrix.map_mul, Matrix.map_mul, map_inv_val, map_inv_val, h]

theorem frame_map (v : InfinitePlace E) (x : GA E n) {r : ℕ} (M : Matrix (Fin n) (Fin r) E) :
    (frame x M).map (cV v) = ((GeneralLinearGroup.map (cV v) x)⁻¹ : GL (Fin n) ℂ).val * M.map v.embedding := by
  have h : (M.map (algebraMap E (Ad E))).map (cV v) = M.map v.embedding := by
    ext i j
    exact cV_alg v (M i j)
  rw [frame, Matrix.map_mul, h, map_inv_val]

theorem lognInf_eq (v : InfinitePlace E) (x : GA E n) {r : ℕ} (M : Matrix (Fin n) (Fin r) E) :
    lognInf v (frame x M) = ploc (M.map v.embedding) (GeneralLinearGroup.map (cV v) x) := by
  rw [lognInf, frame_map, ploc]

theorem exists_ginv {K : Type} [Field K] {r m : ℕ} (A : Matrix (Fin r) (Fin m) K) :
    ∃ B : Matrix (Fin m) (Fin r) K, A * B * A = A := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective A.mulVecLin.rangeRestrict
    (LinearMap.range_rangeRestrict _)
  obtain ⟨h, hh⟩ := LinearMap.exists_extend g
  refine ⟨LinearMap.toMatrix' h, ?_⟩
  apply Matrix.mulVec_injective
  funext z
  have hz : A *ᵥ z ∈ LinearMap.range A.mulVecLin := ⟨z, rfl⟩
  have h1 : h (A *ᵥ z) = g ⟨A *ᵥ z, hz⟩ := LinearMap.congr_fun hh ⟨A *ᵥ z, hz⟩
  have h2 : A *ᵥ g ⟨A *ᵥ z, hz⟩ = A *ᵥ z :=
    congrArg Subtype.val (LinearMap.congr_fun hg ⟨A *ᵥ z, hz⟩)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, h1, h2]

theorem exists_left (v : InfinitePlace E) (W : Submodule E (Fin n → E)) :
    ∃ L : Matrix (Fin (Module.finrank E W)) (Fin n) ℂ, L * (basisMat W).map v.embedding = 1 := by
  obtain ⟨B, hB⟩ := exists_ginv (basisMat W)
  have hinj : Function.Injective (basisMat W).mulVec := by
    refine Matrix.mulVec_injective_iff.2 ?_
    exact (Module.finBasis E W).linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hBM : B * basisMat W = 1 := by
    apply Matrix.mulVec_injective
    funext c
    apply hinj
    rw [Matrix.one_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hB]
  refine ⟨B.map v.embedding, ?_⟩
  rw [← Matrix.map_mul, hBM, Matrix.map_one _ (map_zero _) (map_one _)]

theorem gram_re_pos {r : ℕ} (B : Matrix (Fin n) (Fin r) ℂ) (L : Matrix (Fin r) (Fin n) ℂ) (hL : L * B = 1) :
    0 < (Bᴴ * B).det.re := by
  have hps : (Bᴴ * B).PosSemidef := posSemidef_conjTranspose_mul_self B
  have h0 : (Bᴴ * B).det ≠ 0 := by
    intro h
    obtain ⟨w, hw, hw0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    apply hw
    have h1 : B *ᵥ w = 0 := (conjTranspose_mul_self_mulVec_eq_zero B w).1 hw0
    calc w = (L * B) *ᵥ w := by rw [hL, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  have hpos : 0 < (Bᴴ * B).det := lt_of_le_of_ne hps.det_nonneg (Ne.symm h0)
  exact (Complex.pos_iff.1 hpos).1

theorem ploc_re_pos (v : InfinitePlace E) (W : Submodule E (Fin n → E)) (g : GL (Fin n) ℂ) :
    0 < ((((g⁻¹ : GL (Fin n) ℂ).val * (basisMat W).map v.embedding)ᴴ *
      ((g⁻¹ : GL (Fin n) ℂ).val * (basisMat W).map v.embedding)).det).re := by
  obtain ⟨L, hL⟩ := exists_left v W
  refine gram_re_pos _ (L * g.val) ?_
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc g.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, hL]

theorem ploc_cont (v : InfinitePlace E) (W : Submodule E (Fin n → E)) :
    Continuous (ploc ((basisMat W).map v.embedding)) := by
  have hB : Continuous fun g : GL (Fin n) ℂ => (g⁻¹ : GL (Fin n) ℂ).val * (basisMat W).map v.embedding :=
    Units.continuous_coe_inv.matrix_mul continuous_const
  have hd : Continuous fun g : GL (Fin n) ℂ => ((((g⁻¹ : GL (Fin n) ℂ).val * (basisMat W).map v.embedding)ᴴ *
      ((g⁻¹ : GL (Fin n) ℂ).val * (basisMat W).map v.embedding)).det).re :=
    Complex.continuous_re.comp (hB.matrix_conjTranspose.matrix_mul hB).matrix_det
  exact (hd.log fun g => (ploc_re_pos v W g).ne').congr fun g => rfl

theorem ploc_mul_k {r : ℕ} (M : Matrix (Fin n) (Fin r) ℂ) (x k : GL (Fin n) ℂ) (hk : thC n k = k) :
    ploc M (x * k) = ploc M x := by
  have hk' : ((k⁻¹ : GL (Fin n) ℂ).val)ᴴ = k.val := by
    have h := congrArg Units.val hk
    rw [thetaR_val] at h
    refine Eq.trans ?_ h
    ext i j
    simp [Matrix.conjTranspose_apply]
  have e : ∀ B : Matrix (Fin n) (Fin r) ℂ,
      ((k⁻¹ : GL (Fin n) ℂ).val * B)ᴴ * ((k⁻¹ : GL (Fin n) ℂ).val * B) = Bᴴ * B := fun B => by
    rw [Matrix.conjTranspose_mul, hk', Matrix.mul_assoc, ← Matrix.mul_assoc k.val, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul]
  unfold ploc
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, e]

theorem ploc_empty {r : ℕ} (M : Matrix (Fin n) (Fin r) ℂ) (hr : r = 0) (g : GL (Fin n) ℂ) : ploc M g = 0 := by
  subst hr
  simp [ploc]

theorem degM_empty {r : ℕ} (x : GA E n) (M : Matrix (Fin n) (Fin r) E) (hr : r = 0) : degM x M = 0 := by
  subst hr
  exact degM_zero x M

theorem deg_embInf (v : InfinitePlace E) (W : Submodule E (Fin n → E)) (g : GL (Fin n) ℂ) (x : GA E n) :
    deg (embInf n v g * x) W + ploc ((basisMat W).map v.embedding) (g * GeneralLinearGroup.map (cV v) x) =
      deg x W + ploc ((basisMat W).map v.embedding) (GeneralLinearGroup.map (cV v) x) := by
  classical
  have hfin : ∀ w, lognFin w (frame (embInf n v g * x) (basisMat W)) = lognFin w (frame x (basisMat W)) :=
    fun w => by
      unfold lognFin
      rw [frame_map_eq (cW w) _ x (by rw [map_mul, cW_embInf, one_mul])]
  have hinf : ∀ w, lognInf w (frame (embInf n v g * x) (basisMat W)) = lognInf w (frame x (basisMat W)) +
      if w = v then ploc ((basisMat W).map v.embedding) (g * GeneralLinearGroup.map (cV v) x) -
        ploc ((basisMat W).map v.embedding) (GeneralLinearGroup.map (cV v) x) else 0 := fun w => by
    by_cases h : w = v
    · subst h
      rw [if_pos rfl, lognInf_eq, lognInf_eq, map_mul, cV_embInf_self]
      ring
    · rw [if_neg h, add_zero]
      unfold lognInf
      rw [frame_map_eq (cV w) _ x (by rw [map_mul, cV_embInf, if_neg h, one_mul])]
  simp only [deg, degM, hfin, hinf, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

end PositivityTheory.Rg.BcB.CV.LocalPlacePositivity

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 in
theorem PositivityTheory.Rg.BcB.CV.pf_Ploc : PositivityTheory.Rg.BcB.CV.Ploc := by
  intro E _ _ _ n v W
  refine ⟨fun x => LocalPlacePositivity.lognInf_eq v x _, LocalPlacePositivity.ploc_cont v W, fun x k hk => LocalPlacePositivity.ploc_mul_k _ x k hk,
    fun hW => ?_, LocalPlacePositivity.cV_embInf_self v, fun v' hv' g => ?_, fun d => LocalPlacePositivity.cV_ratGL v d,
    fun g x => LocalPlacePositivity.deg_embInf v W g x⟩
  · subst hW
    exact ⟨fun x => LocalPlacePositivity.ploc_empty _ (by simp) x, fun x => LocalPlacePositivity.degM_empty x _ (by simp)⟩
  · classical
    rw [LocalPlacePositivity.cV_embInf, if_neg hv']
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.EnormOfRealToRealLe
section
noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace PositivityTheory.Rg.BcB.CV

namespace QuotientIntegral

theorem enorm_ofReal_toReal_le' (r : ℝ≥0∞) : ‖((r.toReal : ℝ) : ℂ)‖ₑ ≤ r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

theorem integrable_mul {G : Type*} [MeasurableSpace G] {μ : Measure G} {F : G → ℂ}
    {ρ : G → ℝ≥0∞} (hF : Measurable F) (hρ : Measurable ρ) (h : ∫⁻ g, ‖F g‖ₑ * ρ g ∂μ ≠ ⊤) :
    Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μ := by
  refine ⟨(hF.mul (Complex.measurable_ofReal.comp hρ.ennreal_toReal)).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) h.lt_top
  rw [enorm_mul]
  gcongr
  exact enorm_ofReal_toReal_le' _

end QuotientIntegral

theorem pf_QAdd : QAdd := by
  intro G _ _ μ T ν
  classical
  by_cases hex : ∃ ρ, IsQuotNormaliser T ν ρ
  · have hL : ∀ F : G → ℂ, quotLIntegral μ T ν (fun x => ‖F x‖ₑ) =
        ∫⁻ g, ‖F g‖ₑ * hex.choose g ∂μ := fun F => by rw [quotLIntegral, dite_eq_left hex]
    have hI : ∀ F : G → ℂ, quotIntegral μ T ν F =
        ∫ g, F g * ((hex.choose g).toReal : ℂ) ∂μ := fun F => by rw [quotIntegral, dite_eq_left hex]
    have hint : ∀ F : G → ℂ, Measurable F → quotLIntegral μ T ν (fun x => ‖F x‖ₑ) ≠ ⊤ →
        Integrable (fun g => F g * ((hex.choose g).toReal : ℂ)) μ := fun F hF h =>
      QuotientIntegral.integrable_mul hF hex.choose_spec.1 (by rwa [hL] at h)
    refine ⟨fun ι s F hF => ?_, fun F F' hF hF' h h' => ?_, fun c F => ?_⟩
    · simp only [hI, Finset.sum_mul]
      exact integral_finsetSum s fun i hi => hint _ (hF i hi).1 (hF i hi).2
    · simp only [hI, sub_mul]
      exact integral_sub (hint _ hF h) (hint _ hF' h')
    · simp only [hI, mul_assoc]
      exact integral_const_mul c _
  · refine ⟨fun _ _ _ _ => ?_, fun _ _ _ _ _ _ => ?_, fun _ _ => ?_⟩ <;>
      simp [quotIntegral, hex]

end PositivityTheory.Rg.BcB.CV
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.ExistsMeasure
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.Glob1Aux

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

theorem emb_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (v : InfinitePlace E) (x : E) :
    v.embedding (conjE E x) = starRingEnd ℂ (v.embedding x) :=
  IsCMField.complexEmbedding_complexConj E v.embedding x

theorem locGL_theta {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (thetaE E n d) = thC n (locGL v d) := by
  apply Units.ext
  have h1 : (locGL v (thetaE E n d)).val = ((thetaR (conjE E) n d).val).map v.embedding := rfl
  have h2 : (locGL v d⁻¹).val = (d⁻¹ : GL (Fin n) E).val.map v.embedding := rfl
  rw [h1, thetaR_val, thetaR_val, ← map_inv, h2]
  ext i j
  simp [emb_conj]

theorem locGL_nrm {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (nrm d) = locGL v d * thC n (locGL v d) := by
  rw [nrm, map_mul, locGL_theta]

theorem sep {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) (hd : IsRegD d) : (locGL v d * thC n (locGL v d)).val.charpoly.Separable := by
  rw [← locGL_nrm]
  have : (locGL v (nrm d)).val = (nrm d).val.map v.embedding := rfl
  rw [this, Matrix.charpoly_map]
  exact hd.map

theorem exists_measure {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (e : G ≃ₜ* H) (T : Subgroup G) (T' : Subgroup H) (hT : T.map e.toMonoidHom = T') (ν : Measure T)
    [ν.IsHaarMeasure] [ν.IsInvInvariant] : ∃ ν' : Measure T', ν'.IsHaarMeasure ∧ ν'.IsInvInvariant := by
  have h1 : ∀ t : T, e t ∈ T' := fun t => by
    rw [← hT]; exact Subgroup.mem_map_of_mem _ t.2
  have h2 : ∀ s : T', e.symm s ∈ T := fun s => by
    have hs : (s : H) ∈ T.map e.toMonoidHom := by rw [hT]; exact s.2
    obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.1 hs
    rw [← hts]
    show e.symm (e t) ∈ T
    rw [e.symm_apply_apply]
    exact ht
  let f : T ≃ₜ* T' :=
    { toFun := fun t => ⟨e t, h1 t⟩
      invFun := fun s => ⟨e.symm s, h2 s⟩
      left_inv := fun t => Subtype.ext (e.symm_apply_apply t)
      right_inv := fun s => Subtype.ext (e.apply_symm_apply s)
      map_mul' := fun a b => Subtype.ext (map_mul e (a : G) (b : G))
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨ν.map f, inferInstance, ⟨?_⟩⟩
  have hf : Measurable f := f.continuous.measurable
  have hinv : Measurable (fun t : T => t⁻¹) := continuous_inv.measurable
  have hν : Measure.map (fun t : T => t⁻¹) ν = ν := Measure.IsInvInvariant.inv_eq_self
  show Measure.map (fun s : T' => s⁻¹) (Measure.map f ν) = Measure.map f ν
  rw [Measure.map_map continuous_inv.measurable hf]
  conv_rhs => rw [← hν, Measure.map_map hf hinv]
  congr 1
  funext t
  exact (map_inv f t).symm

end PositivityTheory.Rg.BcB.CV.Glob1Aux

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV.Glob1Aux in
theorem PositivityTheory.Rg.BcB.CV.pf_Glob1 : PositivityTheory.Rg.BcB.D4.SplitAt → PositivityTheory.Rg.BcB.D4.NonEllFlag → PositivityTheory.Rg.BcB.LocVanish → PositivityTheory.Rg.BcB.CV.LocTor → PositivityTheory.Rg.BcB.CV.QMap → PositivityTheory.Rg.BcB.CV.QProd → PositivityTheory.Rg.BcB.CV.Ploc → PositivityTheory.Rg.BcB.CV.AdTop → PositivityTheory.Rg.BcB.CV.Glob1 := by
  intro hSA hNEF hLV hLT hQM hQP hPl hAT E _ _ _ n _ _ μ _ d ν _ _ φ hreg hne hcomm hcl hφ hvc
  obtain ⟨v, W₁, W₂, hW0, hW12, hp1, hp2⟩ := hNEF E n d hreg hne
  obtain ⟨G', _, _, _, _, _, _, _, _, _, e, μ₁, μ₂, θ', hμ₁, hμ₂, -, he1, hemb, hθ, hcent⟩ := hSA E n v μ
  have hsep := sep v d hreg
  obtain ⟨hT1c, hT1m, -, hLC, hSC⟩ := hLT n (locGL v d) hsep
  obtain ⟨hLCA, hT2A, hSCA, hθA, -, -⟩ := hAT E n
  have := hLC; have := hSC; have := hLCA; have := hT2A; have := hSCA; have := hμ₁; have := hμ₂
  have : T2Space (GL (Fin n) ℂ × G') := e.symm.toHomeomorph.isEmbedding.t2Space
  have : T2Space (GL (Fin n) ℂ) :=
    T2Space.of_injective_continuous (f := fun g : GL (Fin n) ℂ => (g, (1 : G')))
      (fun a b h => (Prod.ext_iff.1 h).1) (continuous_id.prodMk continuous_const)
  have : T2Space G' :=
    T2Space.of_injective_continuous (f := fun b : G' => ((1 : GL (Fin n) ℂ), b))
      (fun a b h => (Prod.ext_iff.1 h).2) (continuous_const.prodMk continuous_id)
  have he1' : (e (ratGL E n d)).1 = locGL v d := by
    rw [he1]; exact (hPl E n v ⊥).2.2.2.2.2.2.1 d
  have hmem : ∀ p, p ∈ (twCent (thC n) (locGL v d)).prod (twCent θ' (e (ratGL E n d)).2) ↔
      p ∈ e '' (adCent d : Set (GA E n)) := by
    intro p; rw [← hcent d]; exact Iff.rfl
  have hT2c : IsClosed (twCent θ' (e (ratGL E n d)).2 : Set G') := by
    have hc : IsClosed (e '' (adCent d : Set (GA E n))) := e.toHomeomorph.isClosedMap _ hcl
    have : (twCent θ' (e (ratGL E n d)).2 : Set G') =
        (fun b => ((1 : GL (Fin n) ℂ), b)) ⁻¹' (e '' (adCent d : Set (GA E n))) := by
      ext b
      rw [Set.mem_preimage, ← hmem, Subgroup.mem_prod]
      exact ⟨fun h => ⟨Subgroup.one_mem _, h⟩, fun h => h.2⟩
    rw [this]
    exact hc.preimage (continuous_const.prodMk continuous_id)
  have hT2m : ∀ s ∈ twCent θ' (e (ratGL E n d)).2, ∀ t ∈ twCent θ' (e (ratGL E n d)).2, s * t = t * s := by
    intro s hs t ht
    obtain ⟨x, hx, hxs⟩ := (hmem (1, s)).1 (Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, hs⟩)
    obtain ⟨y, hy, hyt⟩ := (hmem (1, t)).1 (Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, ht⟩)
    have h := congrArg (fun p => (e p).2) (hcomm x hx y hy)
    simp only [map_mul, Prod.snd_mul, hxs, hyt] at h
    exact h
  obtain ⟨ν', hν'1, hν'2⟩ := exists_measure e (adCent d) _ (hcent d) ν
  have := hν'1; have := hν'2
  have hFc : Continuous fun x : GA E n => φ (twConj (thetaA E n) x (ratGL E n d)) :=
    hφ.cont.comp ((continuous_inv.mul continuous_const).mul hθA)
  refine hQM (GA E n) (GL (Fin n) ℂ × G') e μ (μ₁.prod μ₂) (adCent d) _ ν ν' _ hcl (hcent d) hFc.measurable
    (fun t ht x => congrArg φ (twConj_mul_left (thetaA E n) (ratGL E n d) ht x)) ?_
  refine hQP (GL (Fin n) ℂ) G' μ₁ μ₂ _ _ ν' _ hT1c hT2c hT1m hT2m (hFc.comp e.symm.continuous).measurable ?_ (Or.inl ?_)
  · intro t ht x
    obtain ⟨s, hs, rfl⟩ := (hmem t).1 ht
    show φ (twConj (thetaA E n) (e.symm (e s * x)) (ratGL E n d)) = φ (twConj (thetaA E n) (e.symm x) (ratGL E n d))
    rw [map_mul, e.symm_apply_apply]
    exact congrArg φ (twConj_mul_left (thetaA E n) (ratGL E n d) hs _)
  · intro ν₁ _ _ x₂
    have key : ∀ x₁ : GL (Fin n) ℂ, twConj (thetaA E n) (e.symm (x₁, x₂)) (ratGL E n d) =
        e.symm (twConj (thC n) x₁ (locGL v d), twConj θ' x₂ (e (ratGL E n d)).2) := by
      intro x₁
      apply e.injective
      rw [e.apply_symm_apply]
      simp only [twConj, map_mul, map_inv, hθ, e.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · simp [he1']
      · simp
    have hf : VeryCusp fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2)) := by
      have h := hvc v (e.symm (1, twConj θ' x₂ (e (ratGL E n d)).2)) (by rw [← he1, e.apply_symm_apply])
      have : (fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2))) =
          fun g => φ (embInf n v g * e.symm (1, twConj θ' x₂ (e (ratGL E n d)).2)) := by
        funext g
        have hg : embInf n v g = e.symm (g, 1) := by rw [← hemb g, e.symm_apply_apply]
        rw [hg, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
      rw [this]; exact h
    have hfc : Continuous fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2)) :=
      hφ.cont.comp (e.symm.continuous.comp (continuous_id.prodMk continuous_const))
    have hfs : HasCompactSupport fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2)) := by
      have hK : IsCompact (e '' tsupport φ) := hφ.supp.image e.continuous
      refine IsCompact.of_isClosed_subset (hK.image continuous_fst) (isClosed_tsupport _) ?_
      have hcl' : IsClosed {g : GL (Fin n) ℂ | (g, twConj θ' x₂ (e (ratGL E n d)).2) ∈ e '' tsupport φ} :=
        hK.isClosed.preimage (continuous_id.prodMk continuous_const)
      refine (closure_minimal ?_ hcl').trans ?_
      · intro g hg
        exact ⟨_, subset_tsupport _ hg, e.apply_symm_apply _⟩
      · intro g hg
        exact ⟨_, hg, rfl⟩
    have hLV' := hLV n μ₁ _ (fun _ => 1) (locGL v d) ν₁ W₁ W₂ hfc hfs hf hsep hW0 hW12 hp1 hp2 measurable_const
      (fun _ _ => ⟨1, fun _ _ => by simp⟩) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    refine Eq.trans ?_ hLV'
    congr 1
    funext x₁
    show φ (twConj (thetaA E n) (e.symm (x₁, x₂)) (ratGL E n d)) = _
    rw [key, mul_one]
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.PFamAt
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.FamilyAtPlace

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

theorem emb_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (v : InfinitePlace E) (x : E) :
    v.embedding (conjE E x) = starRingEnd ℂ (v.embedding x) :=
  IsCMField.complexEmbedding_complexConj E v.embedding x

theorem locGL_theta {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (thetaE E n d) = thC n (locGL v d) := by
  apply Units.ext
  have h1 : (locGL v (thetaE E n d)).val = ((thetaR (conjE E) n d).val).map v.embedding := rfl
  have h2 : (locGL v d⁻¹).val = (d⁻¹ : GL (Fin n) E).val.map v.embedding := rfl
  rw [h1, thetaR_val, thetaR_val, ← map_inv, h2]
  ext i j
  simp [emb_conj]

theorem locGL_nrm {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (nrm d) = locGL v d * thC n (locGL v d) := by
  rw [nrm, map_mul, locGL_theta]

theorem perp_anti {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {W W' : Submodule K (Fin n → K)} (h : W ≤ W') :
    perp σ W' ≤ perp σ W := fun _ hy x hx => hy x (h hx)

theorem perpD_anti {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (d : GL (Fin n) K) {W W' : Submodule K (Fin n → K)}
    (h : W ≤ W') : perpD σ d W' ≤ perpD σ d W :=
  Submodule.map_mono (perp_anti σ h)

end PositivityTheory.Rg.BcB.CV.FamilyAtPlace

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV.FamilyAtPlace in
theorem PositivityTheory.Rg.BcB.CV.pf_FamAt : PositivityTheory.Rg.BcB.D4.LocFlag → PositivityTheory.Rg.BcB.CV.Ploc → PositivityTheory.Rg.BcB.CV.FamAt := by
  intro hLF hP E _ _ _ n m d Wof a V v hPar hV hemb
  refine ⟨?_, ?_⟩
  · rw [← locGL_nrm]
    have : (locGL v (nrm d)).val = (nrm d).val.map v.embedding := rfl
    rw [this, Matrix.charpoly_map]
    exact hPar.reg.map
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact continuous_pi fun e => (hP E n v (Wof e)).2.1
    · intro x
      exact ((hP E n v (Wof 0)).2.2.2.1 hPar.zero).1 x
    · intro x k hk
      funext e
      exact (hP E n v (Wof e)).2.2.1 x k hk
    · intro t ht x z
      have hs := hemb t ht
      have key : ∀ e, pAt Wof v (t * x) e = pAt Wof v x e - sdot e (a (embInf n v t)) := by
        intro e
        have h1 := (hP E n v (Wof e)).2.2.2.2.2.2.2 t (embInf n v x)
        rw [(hP E n v (Wof e)).2.2.2.2.1 x, hPar.degT _ hs] at h1
        simp only [pAt]
        linarith
      have : pAt Wof v (t * x) + z = fun e => (pAt Wof v x + z) e - sdot e (a (embInf n v t)) := by
        funext e
        simp only [Pi.add_apply, key]
        ring
      rw [this, hV _ hs]
    · intro e he
      have hW : Wof e ≠ ⊥ := by
        intro h
        obtain ⟨e0, _, hu⟩ := hPar.uniq ⊥ (hPar.zero ▸ hPar.iso 0)
        exact he ((hu e h).trans (hu 0 hPar.zero).symm)
      obtain ⟨h1, h2, h3, h4, h5⟩ := hLF E n d (Wof e) v (hPar.iso e) hW (hPar.perp e)
      refine ⟨_, _, ⟨h1, h2, h3, h4⟩, ?_⟩
      intro u hu x e' he'
      have hW' : Wof e' ≤ Wof e ∨ (Wof e ≤ Wof e' ∧ Wof e' ≤ perpD (conjE E) d (Wof e)) := by
        rcases he' with h | h
        · exact Or.inr ⟨hPar.mono _ _ h, (hPar.iso e').2.trans (perpD_anti _ _ (hPar.mono _ _ h))⟩
        · exact Or.inl (hPar.mono _ _ h)
      have c1 := (hP E n v (Wof e')).1 (embInf n v u * embInf n v x)
      have c2 := (hP E n v (Wof e')).1 (embInf n v x)
      rw [map_mul, (hP E n v (Wof e')).2.2.2.2.1 u, (hP E n v (Wof e')).2.2.2.2.1 x] at c1
      rw [(hP E n v (Wof e')).2.2.2.2.1 x] at c2
      simp only [pAt]
      rw [← c1, ← c2]
      exact h5 (embInf n v x) u hu (Wof e') hW'
end
end

