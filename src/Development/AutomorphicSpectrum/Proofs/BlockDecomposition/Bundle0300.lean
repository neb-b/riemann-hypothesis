module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InductionReindexEquiv
section
set_option maxSynthPendingDepth 1

noncomputable section

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.CompanionTheory.SmGLBridge

namespace GlobalTheory.CompanionTheory.ParIndReindex

section Generic

variable {G G' V V' W : Type} [Group G] [Group G']
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]

theorem twKer_map (r : G ≃* G') (L : V ≃ₗ[ℂ] V') {π : Representation ℂ G V}
    {π' : Representation ℂ G' V'} (hL : ∀ g v, L (π g v) = π' (r g) (L v))
    {N : Subgroup G} {N' : Subgroup G'} (hN : ∀ g, g ∈ N ↔ r g ∈ N') :
    (twKer π N 1).map (L : V →ₗ[ℂ] V') = twKer π' N' 1 := by
  delta GlobalTheory.PRep.twKer
  rw [Submodule.map_span]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨n, v, rfl⟩, rfl⟩
    exact ⟨⟨r n, (hN n).1 n.2⟩, L v, by simp [hL]⟩
  · rintro ⟨n', v', rfl⟩
    refine ⟨_, ⟨⟨r.symm n', (hN _).2 (by simpa using n'.2)⟩, L.symm v', rfl⟩, ?_⟩
    simp [hL]

def jacquetEquiv (r : G ≃* G') (L : V ≃ₗ[ℂ] V') {π : Representation ℂ G V}
    {π' : Representation ℂ G' V'} (hL : ∀ g v, L (π g v) = π' (r g) (L v))
    {N : Subgroup G} {N' : Subgroup G'} (hN : ∀ g, g ∈ N ↔ r g ∈ N') :
    Jacquet π N ≃ₗ[ℂ] Jacquet π' N' :=
  Submodule.Quotient.equiv _ _ L (twKer_map r L hL hN)

def pullFun (r : G ≃* G') {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) (f : indSpace H' σ') : indSpace H σ :=
  ⟨fun x => f.1 (r x), fun h g => by
    show f.1 (r (h * g)) = σ h (f.1 (r g))
    rw [map_mul, ← hσ h]
    exact f.2 ⟨r h, hH h⟩ (r g)⟩

theorem ind_pullFun (r : G ≃* G') {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) (f : indSpace H' σ') (g : G) :
    ind H σ g (pullFun r hH hσ f) = pullFun r hH hσ (ind H' σ' (r g) f) := by
  apply Subtype.ext
  funext x
  show f.1 (r (x * g)) = f.1 (r x * r g)
  rw [map_mul]

theorem pullFun_eq_iff (r : G ≃* G') {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) (f f' : indSpace H' σ') :
    pullFun r hH hσ f = pullFun r hH hσ f' ↔ f = f' := by
  constructor
  · intro h
    apply Subtype.ext
    funext y
    have h1 : f.1 (r (r.symm y)) = f'.1 (r (r.symm y)) :=
      congrArg (fun p : indSpace H σ => p.1 (r.symm y)) h
    simpa using h1
  · rintro rfl
    rfl

variable [TopologicalSpace G] [TopologicalSpace G'] [IsTopologicalGroup G] [IsTopologicalGroup G']

def pull (r : G ≃* G') (hr : Continuous r) {H : Subgroup G} {H' : Subgroup G'}
    (hH : ∀ h : H, r h ∈ H') {σ : Representation ℂ H W} {σ' : Representation ℂ H' W}
    (hσ : ∀ h : H, σ' ⟨r h, hH h⟩ = σ h) :
    smoothPart (ind H' σ') →ₗ[ℂ] smoothPart (ind H σ) where
  toFun f := ⟨pullFun r hH hσ f.1, by
    have hset : {g : G | ind H σ g (pullFun r hH hσ f.1) = pullFun r hH hσ f.1} =
        r ⁻¹' {g' : G' | ind H' σ' g' f.1 = f.1} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_preimage, ind_pullFun, pullFun_eq_iff]
    show IsOpen {g : G | ind H σ g (pullFun r hH hσ f.1) = pullFun r hH hσ f.1}
    rw [hset]
    exact IsOpen.preimage hr f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def indEquiv (r : G ≃* G') (hr : Continuous r) (hs : Continuous r.symm) {H : Subgroup G}
    {H' : Subgroup G'} (hH : ∀ g, g ∈ H ↔ r g ∈ H') {σ : Representation ℂ H W}
    {σ' : Representation ℂ H' W} (hσ : ∀ h : H, σ' ⟨r h, (hH h).1 h.2⟩ = σ h) :
    smoothPart (ind H σ) ≃ₗ[ℂ] smoothPart (ind H' σ') :=
  LinearEquiv.ofLinear
    (pull r.symm hs (fun h' => (hH _).2 (by simp)) (fun h' => by
      rw [← hσ ⟨r.symm h', (hH _).2 (by simp)⟩]
      congr 1
      exact Subtype.ext (by simp)))
    (pull r hr (fun h => (hH h).1 h.2) hσ)
    (LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
      show f.1.1 (r (r.symm x)) = _
      simp)))
    (LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
      show f.1.1 (r.symm (r x)) = _
      simp)))

end Generic

section Reindex

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {N : ℕ}

theorem glReindex_apply (ι : n ≃ Fin N) (g : GL n k) (i j : n) :
    ((glReindex ι g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (ι i) (ι j) =
      (g : Matrix n n k) i j := by
  show (Matrix.reindexAlgEquiv k k ι (g : Matrix n n k)) (ι i) (ι j) = (g : Matrix n n k) i j
  simp [Matrix.coe_reindexAlgEquiv]

theorem mem_parab_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : GL n k) :
    g ∈ parab k e ↔ glReindex ι g ∈ parab k (e.trans ι) := by
  show (g : Matrix n n k).BlockTriangular (blk e) ↔
    ((glReindex ι g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).BlockTriangular (blk (e.trans ι))
  constructor
  · intro h i j hij
    have h2 := @h (ι.symm i) (ι.symm j) (by simpa [blk] using hij)
    have e1 := glReindex_apply ι g (ι.symm i) (ι.symm j)
    simp only [Equiv.apply_symm_apply] at e1
    rw [e1]
    exact h2
  · intro h i j hij
    have h2 := @h (ι i) (ι j) (by simpa [blk] using hij)
    rw [glReindex_apply] at h2
    exact h2

private theorem leviProj_glReindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : GL n k)
    (h : g ∈ parab k e) (h' : glReindex ι g ∈ parab k (e.trans ι)) :
    leviProj k (e.trans ι) ⟨glReindex ι g, h'⟩ = leviProj k e ⟨g, h⟩ := by
  funext a
  apply Units.ext
  ext i j
  show ((glReindex ι g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (ι (e ⟨a, i⟩)) (ι (e ⟨a, j⟩)) =
    (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩)
  exact glReindex_apply ι g _ _

theorem mem_unipRad_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : GL n k) :
    g ∈ unipRad k e ↔ glReindex ι g ∈ unipRad k (e.trans ι) := by
  show g ∈ Subgroup.map (parab k e).subtype (leviProj k e).ker ↔
    glReindex ι g ∈ Subgroup.map (parab k (e.trans ι)).subtype (leviProj k (e.trans ι)).ker
  simp only [Subgroup.mem_map, MonoidHom.mem_ker]
  constructor
  · rintro ⟨⟨p, hp'⟩, hp, rfl⟩
    refine ⟨⟨glReindex ι p, (mem_parab_reindex e ι p).1 hp'⟩, ?_, rfl⟩
    rw [leviProj_glReindex e ι p hp']
    exact hp
  · rintro ⟨⟨p, hp'⟩, hp, hpg⟩
    simp only [Subgroup.coe_subtype] at hpg
    subst hpg
    have hg : g ∈ parab k e := (mem_parab_reindex e ι g).2 hp'
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [leviProj_glReindex e ι g hg hp'] at hp
    exact hp

theorem leviProj_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (p : parab k e) :
    leviProj k (e.trans ι) ⟨glReindex ι p, (mem_parab_reindex (k := k) e ι p.1).1 p.2⟩ = leviProj k e p := by
  exact leviProj_glReindex e ι p.1 p.2 _

theorem leviEmb_reindex (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (g : Levi k m) :
    glReindex ι (leviEmb k e g) = leviEmb k (e.trans ι) g := by
  apply Units.ext
  ext i j
  have h1 := glReindex_apply (k := k) ι (leviEmb k e g) (ι.symm i) (ι.symm j)
  simp only [Equiv.apply_symm_apply] at h1
  rw [h1]
  rfl

theorem continuous_glReindex_symm (ι : n ≃ Fin N) :
    Continuous (glReindex (k := k) ι).symm := by
  have h1 : ⇑(glReindex (k := k) ι).symm = ⇑(glReindex (k := k) ι.symm) :=
    funext (glReindex_symm ι)
  rw [h1]
  exact continuous_glReindex ι.symm

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def parIndEquiv (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (ρ : Representation ℂ (Levi k m) W) :
    IndSp e ρ ≃ₗ[ℂ] IndSp (e.trans ι) ρ :=
  indEquiv (glReindex ι) (continuous_glReindex ι) (continuous_glReindex_symm ι)
    (mem_parab_reindex e ι) (fun h => by
      show (twist ρ (deltaHalf k m)) (leviProj k (e.trans ι) _) = (twist ρ (deltaHalf k m)) (leviProj k e h)
      rw [leviProj_reindex])

theorem parIndEquiv_apply (e : (Σ i, m i) ≃ n) (ι : n ≃ Fin N) (ρ : Representation ℂ (Levi k m) W)
    (g : GL n k) (f : IndSp e ρ) :
    parIndEquiv e ι ρ (parInd e ρ g f) = parInd (e.trans ι) ρ (glReindex ι g) (parIndEquiv e ι ρ f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext y
  show f.1.1 ((glReindex ι).symm y * g) = f.1.1 ((glReindex ι).symm (y * glReindex ι g))
  rw [map_mul, MulEquiv.symm_apply_apply]

end Reindex

theorem jac_parInd_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' n : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ n) (e' : (Σ j, m' j) ≃ n) {N : ℕ} (ι : n ≃ Fin N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((jac e' (parInd e ρ)).Equiv (jac (e'.trans ι) (parInd (e.trans ι) ρ))) := by
  intro k _ _ _ _ α β' n _ _ _ _ _ _ m _ _ m' _ _ e e' N ι W _ _ ρ
  refine ⟨Representation.Equiv.mk
    (jacquetEquiv (glReindex (k := k) ι) (parIndEquiv e ι ρ) (parIndEquiv_apply e ι ρ)
      (mem_unipRad_reindex e' ι)) (fun l => ?_)⟩
  apply LinearMap.ext
  intro y
  obtain ⟨v, rfl⟩ := Quot.exists_rep y
  have h1 := parIndEquiv_apply e ι ρ (leviEmb k e' l) v
  rw [leviEmb_reindex] at h1
  have h2 : parIndEquiv e ι ρ ((((deltaHalf k m')⁻¹ l : ℂˣ) : ℂ) • parInd e ρ (leviEmb k e' l) v) =
      (((deltaHalf k m')⁻¹ l : ℂˣ) : ℂ) •
        parInd (e.trans ι) ρ (leviEmb k (e'.trans ι) l) (parIndEquiv e ι ρ v) := by
    rw [LinearEquiv.map_smul, h1]
  exact congrArg (Quot.mk _) h2

end GlobalTheory.CompanionTheory.ParIndReindex
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq
section
noncomputable section

open MeasureTheory Filter
open scoped ENNReal
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotNorm

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG]
  {H : Subgroup G} {μH : Measure H} [SFinite μH] [μH.IsInvInvariant]

theorem ae_lt_top_of_normaliser {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) :
    ∀ᵐ g ∂μG, ρ g < ∞ := by
  have hmulH : Measurable fun p : H × G => (p.1 : G) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul measurable_snd
  set E : Set G := {g | ρ g = ∞} with hEdef
  have hE : MeasurableSet E := hρ.1 (measurableSet_singleton ∞)
  have hind : Measurable (E.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hE
  have hzero : ∀ g : G, ∫⁻ h : H, E.indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μH = 0 := by
    intro g
    have hm : Measurable fun h : H => ρ ((h : G) * g) :=
      hρ.1.comp (measurable_subtype_coe.mul_const g)
    have hfin : ∀ᵐ h : H ∂μH, ρ ((h : G) * g) < ∞ :=
      ae_lt_top hm (by rw [hρ.2 g]; exact ENNReal.one_ne_top)
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hfin] with h hh
    simp [hEdef, Set.indicator, hh.ne]
  have key : ∫⁻ h : H, ∫⁻ g, E.indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μG ∂μH = 0 := by
    rw [lintegral_lintegral_swap]
    · simp [hzero]
    · exact (hind.comp hmulH).aemeasurable
  have h2 : ∀ h : H, ∫⁻ g, E.indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μG = μG E := fun h => by
    rw [lintegral_mul_left_eq_self (E.indicator (1 : G → ℝ≥0∞)) (h : G),
      lintegral_indicator_one hE]
  simp only [h2, lintegral_const] at key
  have hne : μH Set.univ ≠ 0 := by
    intro h0
    have h1 := hρ.2 1
    rw [Measure.measure_univ_eq_zero.1 h0] at h1
    simp at h1
  have hE0 : μG E = 0 := (mul_eq_zero.1 key).resolve_right hne
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hE0] with g hg
  exact lt_top_iff_ne_top.2 hg

theorem integral_nonneg_normaliser_eq {f : G → ℝ} (hf : Measurable f) (hf0 : ∀ g, 0 ≤ f g)
    (hfH : ∀ h ∈ H, ∀ g, f (h * g) = f g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    ∫ g, f g * (ρ g).toReal ∂μG = ∫ g, f g * (ρ' g).toReal ∂μG := by
  have aux : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      ∫ g, f g * (σ g).toReal ∂μG = (∫⁻ g, ENNReal.ofReal (f g) * σ g ∂μG).toReal := by
    intro σ hσ
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun g => mul_nonneg (hf0 g) ENNReal.toReal_nonneg)
      (hf.mul hσ.1.ennreal_toReal).aestronglyMeasurable]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top_of_normaliser (μG := μG) hσ] with g hg
    rw [ENNReal.ofReal_mul (hf0 g), ENNReal.ofReal_toReal hg.ne]
  rw [aux hρ, aux hρ', lintegral_normaliser_eq (F := fun g => ENNReal.ofReal (f g))
    hf.ennreal_ofReal (fun h hh g => by simp only [hfH h hh g]) hρ hρ']

theorem integrable_normaliser_iff {F : G → ℂ} (hF : Measurable F)
    (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μG ↔
      Integrable (fun g => F g * ((ρ' g).toReal : ℂ)) μG := by
  have aux : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      ∫⁻ g, ‖F g * ((σ g).toReal : ℂ)‖ₑ ∂μG = ∫⁻ g, ‖F g‖ₑ * σ g ∂μG := by
    intro σ hσ
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top_of_normaliser (μG := μG) hσ] with g hg
    rw [enorm_mul, ← ofReal_norm_eq_enorm ((σ g).toReal : ℂ), Complex.norm_real,
      Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hg.ne]
  have hm : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      AEStronglyMeasurable (fun g => F g * ((σ g).toReal : ℂ)) μG := fun hσ =>
    (hF.mul (Complex.measurable_ofReal.comp hσ.1.ennreal_toReal)).aestronglyMeasurable
  have heq := lintegral_normaliser_eq (μG := μG) (F := fun g => ‖F g‖ₑ) hF.enorm
    (fun h hh g => by simp only [hFH h hh g]) hρ hρ'
  simp only [Integrable, hm hρ, hm hρ', true_and, hasFiniteIntegral_iff_enorm, aux hρ, aux hρ', heq]

theorem integral_real_normaliser_eq {f : G → ℝ} (hf : Measurable f)
    (hfH : ∀ h ∈ H, ∀ g, f (h * g) = f g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ')
    (hi : Integrable (fun g => f g * (ρ g).toReal) μG)
    (hi' : Integrable (fun g => f g * (ρ' g).toReal) μG) :
    ∫ g, f g * (ρ g).toReal ∂μG = ∫ g, f g * (ρ' g).toReal ∂μG := by
  have part : ∀ {σ : G → ℝ≥0∞} {u : G → ℝ}, IsQuotNormaliser H μH σ → Measurable u →
      (∀ g, |u g| ≤ |f g|) → Integrable (fun g => f g * (σ g).toReal) μG →
      Integrable (fun g => u g * (σ g).toReal) μG := by
    intro σ u hσ hu hle h
    refine h.mono (hu.mul hσ.1.ennreal_toReal).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hle g) (abs_nonneg _)
  have hp : Measurable fun g => max (f g) 0 := hf.max measurable_const
  have hn : Measurable fun g => max (-f g) 0 := hf.neg.max measurable_const
  have hpl : ∀ g, |max (f g) 0| ≤ |f g| := fun g => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hnl : ∀ g, |max (-f g) 0| ≤ |f g| := fun g => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have dec : ∀ {σ : G → ℝ≥0∞}, IsQuotNormaliser H μH σ →
      Integrable (fun g => f g * (σ g).toReal) μG →
      ∫ g, f g * (σ g).toReal ∂μG =
        ∫ g, max (f g) 0 * (σ g).toReal ∂μG - ∫ g, max (-f g) 0 * (σ g).toReal ∂μG := by
    intro σ hσ h
    rw [← integral_sub (part hσ hp hpl h) (part hσ hn hnl h)]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    have : f g = max (f g) 0 - max (-f g) 0 := (max_zero_sub_max_neg_zero_eq_self (f g)).symm
    simp only
    rw [← sub_mul, ← this]
  rw [dec hρ hi, dec hρ' hi',
    integral_nonneg_normaliser_eq hp (fun g => le_max_right _ _)
      (fun h hh g => by simp only [hfH h hh g]) hρ hρ',
    integral_nonneg_normaliser_eq hn (fun g => le_max_right _ _)
      (fun h hh g => by simp only [hfH h hh g]) hρ hρ']

theorem integral_normaliser_eq_of {F : G → ℂ} (hF : Measurable F)
    (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g) {ρ ρ' : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    ∫ g, F g * ((ρ g).toReal : ℂ) ∂μG = ∫ g, F g * ((ρ' g).toReal : ℂ) ∂μG := by
  have hiff := integrable_normaliser_iff (μG := μG) hF hFH hρ hρ'
  by_cases hi : Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μG
  · have hi' := hiff.1 hi
    have ere : ∀ {σ : G → ℝ≥0∞}, Integrable (fun g => F g * ((σ g).toReal : ℂ)) μG →
        Integrable (fun g => (F g).re * (σ g).toReal) μG ∧
          (∫ g, F g * ((σ g).toReal : ℂ) ∂μG).re = ∫ g, (F g).re * (σ g).toReal ∂μG := by
      intro σ h
      have h1 := Complex.reCLM.integrable_comp h
      have h2 := Complex.reCLM.integral_comp_comm h
      simp only [Complex.reCLM_apply, Complex.re_mul_ofReal] at h1 h2
      exact ⟨h1, h2.symm⟩
    have eim : ∀ {σ : G → ℝ≥0∞}, Integrable (fun g => F g * ((σ g).toReal : ℂ)) μG →
        Integrable (fun g => (F g).im * (σ g).toReal) μG ∧
          (∫ g, F g * ((σ g).toReal : ℂ) ∂μG).im = ∫ g, (F g).im * (σ g).toReal ∂μG := by
      intro σ h
      have h1 := Complex.imCLM.integrable_comp h
      have h2 := Complex.imCLM.integral_comp_comm h
      simp only [Complex.imCLM_apply, Complex.im_mul_ofReal] at h1 h2
      exact ⟨h1, h2.symm⟩
    apply Complex.ext
    · rw [(ere hi).2, (ere hi').2]
      exact integral_real_normaliser_eq (Complex.measurable_re.comp hF)
        (fun h hh g => by simp only [Function.comp, hFH h hh g]) hρ hρ' (ere hi).1 (ere hi').1
    · rw [(eim hi).2, (eim hi').2]
      exact integral_real_normaliser_eq (Complex.measurable_im.comp hF)
        (fun h hh g => by simp only [Function.comp, hFH h hh g]) hρ hρ' (eim hi).1 (eim hi').1
  · rw [integral_undef hi, integral_undef (fun h => hi (hiff.2 h))]

theorem quotIntegral_eq {F : G → ℂ} (hF : Measurable F)
    (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g) {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) :
    quotIntegral μG H μH F = ∫ g, F g * ((ρ g).toReal : ℂ) ∂μG := by
  have hex : ∃ ρ, IsQuotNormaliser H μH ρ := ⟨ρ, hρ⟩
  rw [quotIntegral, dite_eq_left hex]
  exact integral_normaliser_eq_of hF hFH hex.choose_spec hρ

theorem integral_normaliser_eq : PositivityTheory.Rg.BcB.D4.NormEq := by
  intro G _ _ _ _ _ _ _ μ _ H μH _ _ F ρ₁ ρ₂ hF hFH hρ₁ hρ₂
  exact integral_normaliser_eq_of (μG := μ) hF hFH hρ₁ hρ₂

end GlobalTheory.CompanionTheory.QuotNorm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerOpsComm
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.UV

variable {X : Scheme.{0}} {k : ℕ} (M : ℕ → X.Modules) (T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1))

def kerSeq (e : ℕ) : X.Modules := kernel (T (Fin.last k) e)

def cokSeq (e : ℕ) : X.Modules := cokernel (T (Fin.last k) e)

variable {M T}

def kerOps (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i : Fin k) (e : ℕ) :
    kerSeq M T e ⟶ kerSeq M T (e + 1) :=
  kernel.map (T (Fin.last k) e) (T (Fin.last k) (e + 1)) (T i.castSucc e) (T i.castSucc (e + 1))
    (hc _ _ e)

def cokOps (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i : Fin k) (e : ℕ) :
    cokSeq M T e ⟶ cokSeq M T (e + 1) :=
  cokernel.map (T (Fin.last k) e) (T (Fin.last k) (e + 1)) (T i.castSucc e) (T i.castSucc (e + 1))
    (hc _ _ e)

theorem kerOps_comm (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i j : Fin k) (e : ℕ) :
    kerOps hc i e ≫ kerOps hc j (e + 1) = kerOps hc j e ≫ kerOps hc i (e + 1) := by
  dsimp only [kerOps, kerSeq]
  apply equalizer.hom_ext
  simp only [kernel.map, Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
  rw [hc i.castSucc j.castSucc e]

theorem cokOps_comm (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i j : Fin k) (e : ℕ) :
    cokOps hc i e ≫ cokOps hc j (e + 1) = cokOps hc j e ≫ cokOps hc i (e + 1) := by
  dsimp only [cokOps, cokSeq]
  apply coequalizer.hom_ext
  simp only [cokernel.map, Category.assoc, cokernel.π_desc, cokernel.π_desc_assoc]
  simp only [← Category.assoc, hc i.castSucc j.castSucc (e + 1)]

end GlobalTheory.CompanionTheory.GE.UV
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRefinementBlockOrder
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.CellCompare

theorem mem_relParab_iff_leviEmb_mem_blockUpper :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ}
      {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β' → Type}
      [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N)
      (f : ∀ i, (Σ j, c i j) ≃ m i) (δ : Fin N → ℕ)
      (hδ : ∀ i j j' (t : c i j) (t' : c i j'),
        δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j') (x : Levi k m),
      x ∈ relParab k f ↔ leviEmb k e x ∈ blockUpper k N δ := by
  intro k _ _ _ _ α β' _ _ _ _ N m _ _ c _ _ e f δ hδ x
  unfold relParab
  rw [Subgroup.mem_pi]
  change _ ↔ (leviEmb k e x : Matrix (Fin N) (Fin N) k).BlockTriangular δ
  constructor
  · intro hx p q hpq
    obtain ⟨⟨a, u⟩, rfl⟩ := e.surjective p
    obtain ⟨⟨b, v⟩, rfl⟩ := e.surjective q
    by_cases hab : a = b
    · subst hab
      obtain ⟨⟨j, t⟩, rfl⟩ := (f a).surjective u
      obtain ⟨⟨j', t'⟩, rfl⟩ := (f a).surjective v
      rw [leviEmb_apply_same]
      exact mem_parab_iff.1 (hx a trivial) j j' t t' ((hδ a j' j t' t).1 hpq)
    · exact leviEmb_apply_ne k e x hab u v
  · intro hx i _
    rw [mem_parab_iff]
    intro j j' t t' hjj
    have h := hx ((hδ i j' j t' t).2 hjj)
    rwa [leviEmb_apply_same] at h

end GlobalTheory.CompanionTheory.CellCompare
end

