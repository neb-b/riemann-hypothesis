module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0008
public import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
section
open MeasureTheory Set GlobalTheory.AdelicU GlobalTheory.OpTrace NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open scoped ENNReal NNReal Topology ComplexConjugate ContDiff InnerProductSpace Matrix

noncomputable section

namespace GlobalTheory.Orb

section Operators

variable {H H' V W : Type} [Group H] [Group H'] [MeasurableSpace H] [MeasurableSpace H']
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem repOp_congr {π : H →* (V →L[ℂ] V)} {π' : H' →* (V →L[ℂ] V)} {μ : Measure H} {μ' : Measure H'} {f : H → ℂ}
    {f' : H' → ℂ} (h : ∀ T, IsRepOp π μ f T ↔ IsRepOp π' μ' f' T) : repOp π μ f = repOp π' μ' f' := by
  by_cases hT : ∃ T, IsRepOp π μ f T
  · obtain ⟨T, hT⟩ := hT
    rw [hT.repOp_eq, ((h T).1 hT).repOp_eq]
  · rw [repOp, repOp, dite_eq_right hT, dite_eq_right fun ⟨T, h'⟩ => hT ⟨T, (h T).2 h'⟩]

theorem IsUnitEquiv.symm {π : H →* (V →L[ℂ] V)} {π' : H →* (W →L[ℂ] W)} (h : IsUnitEquiv π π') :
    IsUnitEquiv π' π := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A.symm, fun g v => A.injective (by simp [hA])⟩

theorem IsUnitEquiv.trans {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] {π : H →* (V →L[ℂ] V)}
    {π' : H →* (W →L[ℂ] W)} {π'' : H →* (U →L[ℂ] U)} (h : IsUnitEquiv π π') (h' : IsUnitEquiv π' π'') :
    IsUnitEquiv π π'' := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨B, hB⟩ := h'
  exact ⟨A.trans B, fun g v => by simp [hA, hB]⟩

variable [CompleteSpace V] [CompleteSpace W]

theorem isRepOp_conj {π : H →* (V →L[ℂ] V)} {π' : H →* (W →L[ℂ] W)} (A : V ≃ₗᵢ[ℂ] W)
    (hA : ∀ g v, A (π g v) = π' g (A v)) {μ : Measure H} {f : H → ℂ} {T : V →L[ℂ] V} (h : IsRepOp π μ f T) :
    IsRepOp π' μ f ((A.toContinuousLinearEquiv : V →L[ℂ] W) ∘L T ∘L
      (A.toContinuousLinearEquiv.symm : W →L[ℂ] V)) := fun w => by
  obtain ⟨h1, h2⟩ := h (A.symm w)
  have e : ∀ g, f g • π' g w = (A.toContinuousLinearEquiv : V →L[ℂ] W) (f g • π g (A.symm w)) := fun g => by
    simp [hA]
  simp only [e]
  refine ⟨ContinuousLinearMap.integrable_comp _ h1, ?_⟩
  rw [ContinuousLinearMap.integral_comp_comm _ h1, ← h2]
  rfl

theorem IsUnitEquiv.hasTrace {π : H →* (V →L[ℂ] V)} {π' : H →* (W →L[ℂ] W)} (h : IsUnitEquiv π π') {μ : Measure H}
    {f : H → ℂ} {c : ℂ} (ht : HasTrace (repOp π μ f) c) : HasTrace (repOp π' μ f) c := by
  by_cases hT : ∃ T, IsRepOp π μ f T
  · obtain ⟨T, hT⟩ := hT
    obtain ⟨A, hA⟩ := h
    rw [hT.repOp_eq] at ht
    rw [(isRepOp_conj A hA hT).repOp_eq]
    exact ⟨ht.1.comp_comp _ _, (ht.1.trace_conj _).trans ht.2⟩
  · obtain ⟨A, hA⟩ := h.symm
    rw [repOp, dite_eq_right hT] at ht
    rw [repOp, dite_eq_right fun ⟨T, h'⟩ => hT ⟨_, isRepOp_conj A hA h'⟩]
    exact ⟨isTraceClass_zero, trace_zero.trans (trace_zero.symm.trans ht.2)⟩

end Operators

section Transport

variable {H H' n V W : Type} [Group H] [Group H'] [TopologicalSpace H] [TopologicalSpace H'] [Fintype n]
  [DecidableEq n] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (e : H ≃ₜ* H') {ι : H →* Matrix n n ℂ} {ι' : H' →* Matrix n n ℂ} {a : Matrix n n ℂ}

variable {e}

theorem conj_symm (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) (g : H') :
    ι (e.symm g) = a⁻¹ * ι' g * a⁻¹⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 ha
  obtain ⟨g, rfl⟩ := e.surjective g
  rw [hι, e.symm_apply_apply, Matrix.nonsing_inv_nonsing_inv _ hd]
  simp only [mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd, mul_one]

theorem comp_mem_ccMat (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {f' : H' → ℂ} (h : f' ∈ CcMat ι') :
    f' ∘ e ∈ CcMat ι := by
  obtain ⟨hc, Φ, hΦ, hf⟩ := h
  refine ⟨hc.comp_homeomorph e.toHomeomorph, Φ ∘ fun y i j => ∑ l, (∑ k, a i k * y k l) * a⁻¹ l j,
    hΦ.comp (by fun_prop), fun g => (hf _).trans (congrArg Φ ?_)⟩
  funext i j
  simp only [matCoord, hι, Matrix.mul_apply]

theorem isRegSS_conj_iff (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) (s : H) :
    IsRegSS (ι' (e s)) ↔ IsRegSS (ι s) := by
  rw [IsRegSS, IsRegSS, hι, Matrix.charpoly_mul_comm,
    Matrix.nonsing_inv_mul_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 ha)]


variable (e) in
theorem isCompact_cent_iff (s : H) : IsCompact (cent (e s) : Set H') ↔ IsCompact (cent s : Set H) := by
  rw [isCompact_iff_compactSpace, isCompact_iff_compactSpace]
  exact ⟨fun _ => (centEquiv e s rfl).toHomeomorph.symm.compactSpace,
    fun _ => (centEquiv e s rfl).toHomeomorph.compactSpace⟩

variable [MeasurableSpace H] [BorelSpace H] [MeasurableSpace H'] [BorelSpace H'] (e)

theorem measurableEmbedding_equiv : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding

theorem map_symm_map (μ' : Measure H') : (μ'.map e.symm).map e = μ' := by
  rw [Measure.map_map (map_continuous e).measurable (map_continuous e.symm).measurable]
  convert Measure.map_id using 2
  ext x; simp

theorem repOp_map (π' : H' →* (V →L[ℂ] V)) (μ : Measure H) (f' : H' → ℂ) :
    repOp π' (μ.map e) f' = repOp (π'.comp (e : H →* H')) μ (f' ∘ e) :=
  repOp_congr fun T => forall_congr' fun v => and_congr (measurableEmbedding_equiv e).integrable_map_iff
    (by rw [(measurableEmbedding_equiv e).integral_map]; rfl)

theorem isTempered_map_iff (π' : H' →* (V →L[ℂ] V)) (μ : Measure H) :
    IsTempered (μ.map e) π' ↔ IsTempered μ (π'.comp (e : H →* H')) :=
  exists_congr fun _ => and_congr_right fun _ => forall₂_congr fun _ _ =>
    (measurableEmbedding_equiv e).integrable_map_iff

variable {e} [CompleteSpace V]

theorem IsCharFn.of_map (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {μ : Measure H}
    {π' : H' →* (V →L[ℂ] V)} {Θ : H' → ℂ} (h : IsCharFn ι' (μ.map e) π' Θ) :
    IsCharFn ι μ (π'.comp (e : H →* H')) (Θ ∘ e) := by
  refine ⟨(locallyIntegrable_map_homeomorph e.toHomeomorph).1 h.1, fun s hs =>
    ContinuousAt.comp (h.2.1 _ ((isRegSS_conj_iff ha hι s).2 hs)) (map_continuous e).continuousAt, fun f hf => ?_⟩
  have := h.2.2 _ (comp_mem_ccMat (conj_symm ha hι) hf)
  rw [repOp_map, (measurableEmbedding_equiv e).integral_map] at this
  convert this using 2 <;> ext x <;> simp

variable [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H]
  [IsTopologicalGroup H'] [SecondCountableTopology H'] [LocallyCompactSpace H'] [T2Space H']

theorem IsPseudoCoeff.of_map (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {μ : Measure H} [μ.IsHaarMeasure]
    {D' : H' →* (V →L[ℂ] V)} {f' : H' → ℂ} (h : IsPseudoCoeff ι' (μ.map e) D' f') :
    IsPseudoCoeff ι μ (D'.comp (e : H →* H')) (f' ∘ e) := by
  obtain ⟨Θ, hΘ, hO⟩ := h.orb_compact
  refine ⟨comp_mem_ccMat hι h.mem, repOp_map e D' μ f' ▸ h.trace_self, fun U _ _ _ π h1 h2 h3 h4 => ?_,
    fun s hs hT dt _ _ => ?_, Θ ∘ e, hΘ.of_map ha hι, fun s hs hT dt _ _ => ?_⟩
  · obtain ⟨π', rfl⟩ : ∃ π' : H' →* (U →L[ℂ] U), π = π'.comp (e : H →* H') :=
      ⟨π.comp (e.symm : H' →* H), MonoidHom.ext fun x => by simp⟩
    rw [← repOp_map]
    refine h.trace_other U π' ⟨fun g v => ?_, fun v => ?_⟩ ⟨h2.1, fun S hS => h2.2 S ⟨hS.1, fun g => hS.2 _⟩⟩
      ((isTempered_map_iff e π' μ).2 h3) fun ⟨A, hA⟩ => h4 ⟨A, fun g => hA _⟩
    · simpa using h1.1 (e.symm g) v
    · simpa [Function.comp_def] using (h1.2 v).comp (map_continuous e.symm)
  · exact (hasOrbInt_map e rfl f' _).1.1 (h.orb_noncompact _ ((isRegSS_conj_iff ha hι s).2 hs)
      (mt (isCompact_cent_iff e s).1 hT) _)
  · have := hO _ ((isRegSS_conj_iff ha hι s).2 hs) ((isCompact_cent_iff e s).2 hT) (dt.map (centEquiv e s rfl))
    rw [map_measureReal_apply (map_continuous _).measurable MeasurableSet.univ, preimage_univ] at this
    exact (hasOrbInt_map e rfl f' _).1.1 this

theorem IsPseudoCoeff.comp (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {μ' : Measure H'} [μ'.IsHaarMeasure]
    {D' : H' →* (V →L[ℂ] V)} {f' : H' → ℂ} (h : IsPseudoCoeff ι' μ' D' f') :
    IsPseudoCoeff ι (μ'.map e.symm) (D'.comp (e : H →* H')) (f' ∘ e) :=
  IsPseudoCoeff.of_map ha hι (by rwa [map_symm_map])

theorem isPseudoCoeff_map_iff (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {μ : Measure H} [μ.IsHaarMeasure]
    {D' : H' →* (V →L[ℂ] V)} {f' : H' → ℂ} :
    IsPseudoCoeff ι' (μ.map e) D' f' ↔ IsPseudoCoeff ι μ (D'.comp (e : H →* H')) (f' ∘ e) := by
  refine ⟨IsPseudoCoeff.of_map ha hι, fun h => ?_⟩
  convert h.comp (e := e.symm) (Matrix.isUnit_nonsing_inv_iff.2 ha) (conj_symm ha hι) using 1
  · rfl
  · exact MonoidHom.ext fun x => by simp
  · ext x; simp

end Transport

section Scaling

variable {H n V W : Type} [Group H] [TopologicalSpace H] [Fintype n] [DecidableEq n] [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [MeasurableSpace H]
  {ι : H →* Matrix n n ℂ} {μ : Measure H} {c : ℝ≥0}


variable [CompleteSpace V] [CompleteSpace W]

variable [BorelSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H]
  [μ.IsHaarMeasure]

end Scaling

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem exists_frameMat_eq (ρ : D.what₂.Tau) {x : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hx : x ∈ UJset (M.ε ρ)) :
    ∃ g, frameMat M ρ g = x := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
  have e : M.fr ρ * ((M.fr ρ)⁻¹ * x * M.fr ρ) * (M.fr ρ)⁻¹ = x := by
    rw [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul, mul_assoc, Matrix.mul_nonsing_inv _ hd, mul_one]
  obtain ⟨g, hg⟩ := exists_archEquiv_eq V (embOverOf D ρ) rfl ((conj_mem_UJset_iff M ρ _).1 (e.symm ▸ hx))
  exact ⟨g, (congrArg (M.fr ρ * · * (M.fr ρ)⁻¹) hg).trans e⟩

theorem isEmbedding_frameMat (ρ : D.what₂.Tau) : Topology.IsEmbedding (frameMat M ρ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
  have h : Topology.IsEmbedding fun x : Matrix (Fin V.rank) (Fin V.rank) ℂ => M.fr ρ * x * (M.fr ρ)⁻¹ :=
    Function.LeftInverse.isEmbedding (f := fun x => (M.fr ρ)⁻¹ * x * M.fr ρ) (fun x => by
      simp only [mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd, mul_one])
      ((continuous_const.mul continuous_id).mul continuous_const)
      ((continuous_const.mul continuous_id).mul continuous_const)
  exact h.comp (isEmbedding_archMat V.gram (isCMExt_host D) (embOverOf D ρ))

def frameHom (ρ : D.what₂.Tau) : GArch D.sp.cm.sig V.gram (placeOf D ρ) →* Formalism.REAL.UJ (M.ε ρ) :=
  (frameMat M ρ).toHomUnits.codRestrict _ (frameMat_mem M ρ)

theorem frameHom_bijective (ρ : D.what₂.Tau) : Function.Bijective (frameHom M ρ) :=
  ⟨fun _ _ h => (isEmbedding_frameMat M ρ).injective (congrArg (ujMat (M.ε ρ)) h), fun x => by
    obtain ⟨g, hg⟩ := exists_frameMat_eq M ρ (x := ujMat (M.ε ρ) x) x.2
    exact ⟨g, Subtype.ext (Units.ext hg)⟩⟩

theorem isEmbedding_ujMat {m : ℕ} (ε : Fin m → Bool) : Topology.IsEmbedding (ujMat ε) :=
  (Formalism.REAL.isClosedEmbeddingMatrix m ε).1.isEmbedding

def frameEquiv (ρ : D.what₂.Tau) : GArch D.sp.cm.sig V.gram (placeOf D ρ) ≃ₜ* Formalism.REAL.UJ (M.ε ρ) :=
  { MulEquiv.ofBijective _ (frameHom_bijective M ρ) with
    continuous_toFun := (isEmbedding_ujMat _).continuous_iff.2 (isEmbedding_frameMat M ρ).continuous
    continuous_invFun := (isEmbedding_frameMat M ρ).continuous_iff.2 ((isEmbedding_ujMat _).continuous.congr
      fun x => congrArg (ujMat (M.ε ρ))
        ((MulEquiv.ofBijective _ (frameHom_bijective M ρ)).apply_symm_apply x).symm) }

theorem ujMat_frameEquiv_eq_conj (ρ : D.what₂.Tau) (g : GArch D.sp.cm.sig V.gram (placeOf D ρ)) :
    ujMat (M.ε ρ) (frameEquiv M ρ g) = M.fr ρ * matAt V ρ g * (M.fr ρ)⁻¹ := rfl

theorem isPseudoCoeff_dsRep_iff (ρ : D.what₂.Tau) (μ : Measure (GArch D.sp.cm.sig V.gram (placeOf D ρ)))
    [μ.IsHaarMeasure] (f : Formalism.REAL.UJ (M.ε ρ) → ℂ) : haveI := (M.ds ρ).1
    IsPseudoCoeff (ujMat (M.ε ρ)) (μ.map (frameEquiv M ρ)) (ujRep (M.ds ρ).2.2.1) f ↔
      IsPseudoCoeff (matAt V ρ) μ (dsRep M ρ) (f ∘ frameEquiv M ρ) :=
  haveI := (M.ds ρ).1
  isPseudoCoeff_map_iff (M.fr_unit ρ) (ujMat_frameEquiv_eq_conj M ρ)

end Record

end GlobalTheory.Orb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueCharIsOfFinOrder
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelCharOrder

theorem prod_isOfFinOrder {ι M : Type} [CommMonoid M] (s : Finset ι) (f : ι → M) (h : ∀ i ∈ s, IsOfFinOrder (f i)) :
    IsOfFinOrder (∏ i ∈ s, f i) :=
  Finset.prod_induction f IsOfFinOrder (fun _ _ ha hb => ha.mul hb) IsOfFinOrder.one h

theorem residue_char_isOfFinOrder {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E)
    (χ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (u : (Formalism.L2.DIV.kP PP)ˣ) : IsOfFinOrder (χ u) := by
  have : Finite (Formalism.L2.DIV.kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  exact χ.isOfFinOrder (isOfFinOrder_of_finite u)

theorem levFn_flag1_isOfFinOrder {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (x : GL (Fin V.rank) (Lev.EAf D)) :
    IsOfFinOrder (Formalism.L2.DIV.levFn β (flag1L L) x) := by
  have h1 : Formalism.L2.DIV.ext1 (flag1L L).P.H (flag1L L).P.chi (Formalism.L2.DIV.rTup β (flag1L L) x) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold Formalism.L2.DIV.levFn
  rw [h1]
  refine (IsOfFinOrder.one.mul ?_).mul ?_
  · exact prod_isOfFinOrder _ _ fun PP _ => prod_isOfFinOrder _ _ fun c _ => residue_char_isOfFinOrder PP _ _
  · exact prod_isOfFinOrder _ _ fun PP _ => residue_char_isOfFinOrder PP _ _

theorem levEnv_chi_isOfFinOrder : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J), IsOfFinOrder ((levEnv V β L).χ k) := by
  intro D V β L k
  exact levFn_flag1_isOfFinOrder V β L _

end GlobalTheory.LevelCharOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignFrameUnitaryIso
section
open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.FrameIsoReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

theorem cT_star (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; rfl

theorem signFrame_map (h : IsCMExt F E σ) (τ : EmbOver E w) {ε : Fin n → Bool}
    {b : GL (Fin n) (w.Completion ⊗[F] E)} (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) :
    (b.1.map (infEmb τ))ᴴ * J.map τ.1 * b.1.map (infEmb τ) = Formalism.REAL.Jm ε := by
  have h1 : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1 * JR w.Completion J * b.1).map (infEmb τ) =
      (Matrix.diagonal fun i => if ε i then (1 : w.Completion ⊗[F] E) else -1).map (infEmb τ) :=
    congrArg (fun M => M.map (infEmb τ)) hb
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero _)] at h1
  have h2 : (JR w.Completion J).map (infEmb τ) = J.map τ.1 := by ext r s; simp [JR, inclR]
  have h3 : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1).map (infEmb τ) =
      (b.1.map (infEmb τ))ᴴ := by
    ext i j; exact (infEmb_sigR h τ _).symm
  rw [h2, h3] at h1
  rw [h1, Formalism.REAL.Jm]
  congr 1; funext i; split_ifs <;> simp

section Frame

variable (σ J) (h : IsCMExt F E σ) (τ : EmbOver E w) (ε : Fin n → Bool) (b : GL (Fin n) (w.Completion ⊗[F] E))

abbrev fB : Matrix (Fin n) (Fin n) ℂ := b.1.map (infEmb τ)

abbrev fBi : Matrix (Fin n) (Fin n) ℂ := (b⁻¹).1.map (infEmb τ)

theorem fBi_mul : fBi τ b * fB τ b = 1 := by
  rw [fBi, fB, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem fB_mul : fB τ b * fBi τ b = 1 := by
  rw [fBi, fB, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem inFrame_eq (g : GArch σ J w) :
    GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g = fBi τ b * (archEquiv J h τ g).1.1 * fB τ b := by
  rw [archEquiv_val]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame, Units.val_mul, Matrix.map_mul]

include h in
theorem isEmbedding_inFrame : Topology.IsEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b) := by
  have e : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b =
      (fun x : Matrix (Fin n) (Fin n) ℂ => fBi τ b * x * fB τ b) ∘ GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ) := by
    funext g
    exact (inFrame_eq σ J h τ b g).trans rfl
  have hc : Topology.IsEmbedding fun x : Matrix (Fin n) (Fin n) ℂ => fBi τ b * x * fB τ b :=
    Function.LeftInverse.isEmbedding (f := fun x => fB τ b * x * fBi τ b) (fun x => by
      simp only [← mul_assoc, fB_mul, one_mul]; rw [mul_assoc, fB_mul, mul_one])
      ((continuous_const.mul continuous_id).mul continuous_const)
      ((continuous_const.mul continuous_id).mul continuous_const)
  rw [e]
  exact hc.comp (GlobalTheory.Orb.isEmbedding_archMat J h τ)

variable {ε}

include h in
theorem inFrame_mem (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) (g : GArch σ J w) :
    Formalism.REAL.inUJ ε (GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g) := by
  have hS : (fB τ b)ᴴ * J.map τ.1 * fB τ b = Formalism.REAL.Jm ε := signFrame_map h τ hb
  have hA : ((archEquiv J h τ g).1.1)ᴴ * J.map τ.1 * (archEquiv J h τ g).1.1 = J.map τ.1 := by
    rw [← cT_star]; exact (archEquiv J h τ g).2
  rw [Formalism.REAL.inUJ, inFrame_eq σ J h]
  set A := (archEquiv J h τ g).1.1
  set T := J.map τ.1
  set B := fB τ b
  set Bi := fBi τ b
  have hT : Biᴴ * (Bᴴ * T * B) * Bi = T := by
    have : Biᴴ * (Bᴴ * T * B) * Bi = (B * Bi)ᴴ * T * (B * Bi) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, fB_mul, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  calc (Bi * A * B)ᴴ * Formalism.REAL.Jm ε * (Bi * A * B)
      = Bᴴ * Aᴴ * (Biᴴ * (Bᴴ * T * B) * Bi) * A * B := by
        rw [← hS]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Bᴴ * (Aᴴ * T * A) * B := by rw [hT]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hA, hS]

def hom0 : GArch σ J w →* (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  (Units.map (infEmb τ).mapMatrix.toMonoidHom).comp ((MulAut.conj b⁻¹).toMonoidHom.comp (matHom _ σ J))

theorem coe_archimedeanFrameConjMatrixHom (g : GArch σ J w) : ((hom0 σ J τ b g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
    GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g := by
  simp [hom0, GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame, MulAut.conj_apply]

include h in
theorem exists_inFrame_eq (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) (a : Formalism.REAL.UJ ε) :
    ∃ g : GArch σ J w, GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g = ((a : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
  have hS : (fB τ b)ᴴ * J.map τ.1 * fB τ b = Formalism.REAL.Jm ε := signFrame_map h τ hb
  let bU : (Matrix (Fin n) (Fin n) ℂ)ˣ := Units.map (infEmb τ).mapMatrix.toMonoidHom b
  have hbU : (bU : Matrix (Fin n) (Fin n) ℂ) = fB τ b := rfl
  have hbUi : ((bU⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = fBi τ b := by
    rw [← map_inv]; rfl
  let yU : (Matrix (Fin n) (Fin n) ℂ)ˣ := bU * (a : (Matrix (Fin n) (Fin n) ℂ)ˣ) * bU⁻¹
  set x := ((a : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  have hx : xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε := a.2
  have hy : (yU : Matrix (Fin n) (Fin n) ℂ) = fB τ b * x * fBi τ b := by
    simp only [yU, Units.val_mul, hbU, hbUi, x]
  set T := J.map τ.1
  set B := fB τ b
  set Bi := fBi τ b
  have hT : Biᴴ * (Bᴴ * T * B) * Bi = T := by
    have : Biᴴ * (Bᴴ * T * B) * Bi = (B * Bi)ᴴ * T * (B * Bi) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, fB_mul, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hmem : yU ∈ Formalism.UG.UJ (starRingEnd ℂ) T := by
    change Formalism.UG.cT (starRingEnd ℂ) (yU : Matrix (Fin n) (Fin n) ℂ) * T * (yU : Matrix (Fin n) (Fin n) ℂ) = T
    rw [cT_star, hy]
    calc (B * x * Bi)ᴴ * T * (B * x * Bi) = Biᴴ * (xᴴ * (Bᴴ * T * B) * x) * Bi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = T := by rw [hS, hx, ← hS, hT]
  refine ⟨(archEquiv J h τ).symm ⟨yU, hmem⟩, ?_⟩
  rw [inFrame_eq σ J h, MulEquiv.apply_symm_apply]
  change Bi * (yU : Matrix (Fin n) (Fin n) ℂ) * B = x
  rw [hy]
  simp only [← Matrix.mul_assoc, fBi_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, fBi_mul, Matrix.mul_one, Matrix.one_mul]

def frameHom (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) : GArch σ J w →* Formalism.REAL.UJ ε :=
  (hom0 σ J τ b).codRestrict _ fun g => by
    change Formalism.REAL.inUJ ε _
    rw [coe_archimedeanFrameConjMatrixHom]; exact inFrame_mem σ J h τ b hb g

theorem frameHom_val (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) (g : GArch σ J w) :
    Formalism.REAL.coeMatrixAlt ε (frameHom σ J h τ b hb g) = GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g := coe_archimedeanFrameConjMatrixHom σ J τ b g

theorem frameHom_bijective (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) : Function.Bijective (frameHom σ J h τ b hb) := by
  refine ⟨fun g g' e => (isEmbedding_inFrame σ J h τ b).injective ?_, fun a => ?_⟩
  · rw [← frameHom_val σ J h τ b hb, ← frameHom_val σ J h τ b hb, e]
  · obtain ⟨g, hg⟩ := exists_inFrame_eq σ J h τ b hb a
    exact ⟨g, Formalism.REAL.injective_coeMatrix ε ((frameHom_val σ J h τ b hb g).trans hg)⟩

def frameEquiv (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) : GArch σ J w ≃ₜ* Formalism.REAL.UJ ε :=
  { MulEquiv.ofBijective _ (frameHom_bijective σ J h τ b hb) with
    continuous_toFun := ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding).continuous_iff.2
      ((isEmbedding_inFrame σ J h τ b).continuous.congr fun g => (frameHom_val σ J h τ b hb g).symm)
    continuous_invFun := (isEmbedding_inFrame σ J h τ b).continuous_iff.2 ((Formalism.REAL.continuous_coeMatrix ε).congr fun x => by
      have := frameHom_val σ J h τ b hb ((MulEquiv.ofBijective _ (frameHom_bijective σ J h τ b hb)).symm x)
      exact (congrArg (Formalism.REAL.coeMatrixAlt ε)
        ((MulEquiv.ofBijective _ (frameHom_bijective σ J h τ b hb)).apply_symm_apply x).symm).trans this) }

end Frame

end GlobalTheory.FrameIsoReal
end
end

