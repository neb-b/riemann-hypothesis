module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0503
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0533
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialGrowthUpperHalfLog
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCurry
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

noncomputable section

namespace GlobalTheory.FlagFibre

theorem measurePreserving_curry (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  have h : (volume : Measure (ι × κ → ℂ)) =
      (volume : Measure (ι → κ → ℂ)).map (MeasurableEquiv.curry ι κ ℂ).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
      ext f; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  refine ⟨(MeasurableEquiv.curry ι κ ℂ).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} (X : Data E r) (hj : j ≤ r) {Tau : Type}
  [Fintype Tau] (κ : Tau ≃ X.Ψ)

theorem mem_OmF_of_proj (hp : X.p0 = r - j) {z : V (nd X)} (hz : proj X hj κ z ∈ DomFlat Tau j (r - j)) :
    z ∈ OmF X (x0F X) := by
  intro τ
  obtain ⟨t, rfl⟩ := κ.surjective τ
  refine ⟨?_, fun i => ?_⟩
  · have e : mat (cpt X (x0F X) z) (κ t) = mat (x0F X) (κ t) * uni (coords X κ z t) := rfl
    rw [e, det_mul, det_uni, mul_one]
    exact det_x0F X _
  · rw [dmin_cpt X κ z t i, hp]
    refine _root_.GlobalTheory.FlagFibre.signs_over_dom r j (r - j) (idx hj) (isBlockOrderedSumEquiv_trueIndex hj) _ (reindex_sgn hj) _ ?_ i
    have h := hz t
    have e : unflat (proj X hj κ z) t = toMat (base (idx hj) (coords X κ z t)) := by
      ext a b; exact proj_eq X hj κ z t (a, b)
    rwa [e] at h

theorem inter_OmF (hp : X.p0 = r - j) {S : Set (Tau × Fin j × Fin (r - j) → ℂ)} (hD : S ⊆ DomFlat Tau j (r - j)) :
    proj X hj κ ⁻¹' S ∩ OmF X (x0F X) = proj X hj κ ⁻¹' S :=
  Set.inter_eq_left.2 fun _ hz => mem_OmF_of_proj X hj κ hp (hD hz)

theorem densF_eq (z : V (nd X)) :
    densF X (x0F X) z = ∏ t, dens (sgnMat r X.p0) (coords X κ z t) := by
  rw [densF, ← κ.prod_comp]
  exact Finset.prod_congr rfl fun t _ => Finset.prod_congr rfl fun i _ => by rw [dmin_cpt X κ z t]

theorem muF_preimage (hp : X.p0 = r - j) {S : Set (Tau × Fin j × Fin (r - j) → ℂ)} (hS : MeasurableSet S)
    (hD : S ⊆ DomFlat Tau j (r - j)) :
    muF X (x0F X) (proj X hj κ ⁻¹' S) =
      ENNReal.ofReal ((flagConst j * flagConst (r - j))⁻¹ ^ Fintype.card Tau) * muD Tau j (r - j) S := by
  have hS' := measurable_proj X hj κ hS
  set c := MeasurableEquiv.curry Tau (Fin j × Fin (r - j)) ℂ with hc
  set φ : (Tau → Fin j × Fin (r - j) → ℂ) → ℝ≥0∞ := (c.symm ⁻¹' S).indicator 1 with hφ
  have hφm : Measurable φ := measurable_one.indicator (c.symm.measurable hS)
  have hDm : Measurable fun y => ENNReal.ofReal (dens (sgnMat r (r - j)) y) := (measurable_dens _).ennreal_ofReal
  have key := _root_.GlobalTheory.ProdFibre.lintegral_pi_fibre Tau _ _ _ (glue (idx hj)) (base (idx hj)) _ φ (GlobalTheory.T.measurePreserving_glueLowerUnitriangularBlocks _ _ _ _ (isBlockOrderedSumEquiv_trueIndex hj))
    (measurable_base _) (base_glue (isBlockOrderedSumEquiv_trueIndex hj)) hDm hφm
  have hm : Measurable fun y : Tau → Low r → ℂ => φ (fun t => base (idx hj) (y t)) *
      ∏ t, ENNReal.ofReal (dens (sgnMat r (r - j)) (y t)) :=
    (hφm.comp (Measurable.of_eval fun t => (measurable_base _).comp (measurable_pi_apply t))).mul
      (Finset.measurable_prod _ fun t _ => hDm.comp (measurable_pi_apply t))
  rw [← (_root_.GlobalTheory.FlagFibre.measurePreserving_coords_sorted E r X Tau κ).lintegral_comp hm,
    ← (measurePreserving_curry Tau (Fin j × Fin (r - j))).lintegral_comp_emb c.measurableEmbedding] at key
  rw [muF, muD, withDensity_apply _ hS', withDensity_apply _ hS, Measure.restrict_restrict hS',
    Measure.restrict_restrict hS, Set.inter_eq_left.2 hD,
    inter_OmF X hj κ hp hD, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator hS', ← lintegral_indicator hS]
  refine Eq.trans (lintegral_congr fun z => ?_) (key.trans (lintegral_congr fun v => ?_))
  · have e : c.symm (fun t => base (idx hj) (coords X κ z t)) = proj X hj κ z :=
      funext fun s => (proj_eq X hj κ z s.1 s.2).symm
    by_cases h : proj X hj κ z ∈ S
    · rw [Set.indicator_of_mem (show z ∈ proj X hj κ ⁻¹' S from h), hφ,
        Set.indicator_of_mem (by rwa [Set.mem_preimage, e]), Pi.one_apply, one_mul, densF_eq X κ, hp,
        ENNReal.ofReal_prod_of_nonneg fun _ _ => dens_nonneg _ _]
    · rw [Set.indicator_of_notMem (show z ∉ proj X hj κ ⁻¹' S from h), hφ,
        Set.indicator_of_notMem (by rwa [Set.mem_preimage, e]), zero_mul]
  · by_cases h : v ∈ S
    · rw [Set.indicator_of_mem h, hφ, Set.indicator_of_mem (show c v ∈ c.symm ⁻¹' S from h), Pi.one_apply, one_mul]
      have hc0 : 0 < flagConst j * flagConst (r - j) := mul_pos (flagConst_pos _) (flagConst_pos _)
      have hv : ∀ t, toMat (c v t) ∈ hcDom j (r - j) := hD h
      have hpos : ∀ t, 0 ≤ (hQ (toMat (c v t))).det.re ^ (-((j + (r - j) : ℕ) : ℤ)) := fun t =>
        zpow_nonneg (Complex.pos_iff.1 (PosDef.det_pos (hv t))).1.le _
      rw [Finset.prod_congr rfl fun t _ => _root_.GlobalTheory.FlagFibreInt.lintegral_dens_glue r j (r - j) (idx hj) (isBlockOrderedSumEquiv_trueIndex hj) (sgnMat r (r - j))
        (reindex_sgn hj) (c v t) (hv t), ← ENNReal.ofReal_prod_of_nonneg fun t _ => div_nonneg (hpos t) hc0.le,
        ← ENNReal.ofReal_mul (by positivity), Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
        div_eq_inv_mul, inv_pow]
      rfl
    · rw [Set.indicator_of_notMem h, hφ, Set.indicator_of_notMem (show c v ∉ c.symm ⁻¹' S from h), zero_mul]

theorem covol_eq_muD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r)
    (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ F, IsFD (gammaU X hj κ) F →
    muD Tau j (r - j) F < ⊤ ∧
      covol X = grassConst j (r - j) ^ Fintype.card Tau * (muD Tau j (r - j) F).toReal := by
  intro E _ _ _ r j X hj Tau _ κ hp F hF
  obtain ⟨F', hm, hsub, h0, hfs⟩ := GlobalTheory.T.isFundamentalSet_chart_preimage_fundamentalDomain E r j X hj Tau κ hp (_root_.GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq E r j X hj Tau κ hp)
    (fun N hN hD h => by rw [muF_preimage X hj κ hp hN hD, h, mul_zero]) F hF
  have hD := hsub.trans hF.2.1
  rw [inter_OmF X hj κ hp hD] at hfs
  obtain ⟨h1, h2⟩ := covol_eq X (isOrth_x0F X) hfs
  have e : muD Tau j (r - j) F' = muD Tau j (r - j) F := (measure_eq_measure_of_null_diff hsub h0)
  have hc0 : 0 < flagConst j * flagConst (r - j) := mul_pos (flagConst_pos _) (flagConst_pos _)
  rw [muF_preimage X hj κ hp hm hD, e] at h1 h2
  refine ⟨?_, ?_⟩
  · refine lt_top_iff_ne_top.2 fun h => h1.ne ?_
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
  · have e1 : flagConst r = grassConst j (r - j) * (flagConst j * flagConst (r - j)) := by
      rw [← mul_assoc, ← flagConst_add, Nat.add_sub_cancel' hj]
    have e2 : X.Ψ.card = Fintype.card Tau := by rw [Fintype.card_congr κ, Fintype.card_coe]
    rw [h2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), e1, e2, mul_pow, inv_pow]
    field_simp

end GlobalTheory.FlagFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalizationBlowupIsIsoDense
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.BlowOpen

theorem exists_specializes_of_dense {X : Type} [TopologicalSpace X] [QuasiSober X] [NoetherianSpace X] (S : Set X)
    (hSo : IsOpen S) (hSd : Dense S) (x : X) : ∃ w ∈ S, w ⤳ x := by
  classical
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have hCi : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hCc : IsClosed (irreducibleComponent x) := isClosed_of_mem_irreducibleComponents _ hC
  have hη : IsGenericPoint hCi.genericPoint (irreducibleComponent x) := by
    simpa [hCc.closure_eq] using hCi.isGenericPoint_genericPoint_closure
  let F := ⋃ C' ∈ (irreducibleComponents X \ {irreducibleComponent x}), C'
  have hFc : IsClosed F := (NoetherianSpace.finite_irreducibleComponents.diff).isClosed_biUnion
    (fun C' h => isClosed_of_mem_irreducibleComponents C' h.1)
  have hηF : hCi.genericPoint ∉ F := by
    simp only [F, Set.mem_iUnion]
    rintro ⟨C', ⟨hC', hne⟩, hηC'⟩
    have hsub : irreducibleComponent x ⊆ C' := fun y hy =>
      (hη.specializes hy).mem_closed (isClosed_of_mem_irreducibleComponents C' hC') hηC'
    exact hne (Set.mem_singleton_iff.2 (hC.eq_of_le hC'.1 hsub).symm)
  obtain ⟨w, hwF, hwS⟩ := hSd.inter_open_nonempty Fᶜ hFc.isOpen_compl ⟨_, hηF⟩
  have hwC : w ∈ irreducibleComponent x := by
    by_contra h
    apply hwF
    simp only [F, Set.mem_iUnion]
    refine ⟨irreducibleComponent w, ⟨irreducibleComponent_mem_irreducibleComponents w, fun e => h ?_⟩,
      mem_irreducibleComponent⟩
    rw [← Set.mem_singleton_iff.1 e]; exact mem_irreducibleComponent
  exact ⟨_, (hη.specializes hwC).mem_open hSo hwS, hη.specializes mem_irreducibleComponent⟩

theorem exists_specializes_of_dense_scheme (N : Scheme.{0}) [IsLocallyNoetherian N] (W : Set N) (hWo : IsOpen W)
    (hWd : Dense W) (n : N) : ∃ w ∈ W, w ⤳ n := by
  obtain ⟨_, ⟨O, hO, rfl⟩, hnO, -⟩ := N.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ n) isOpen_univ
  haveI : IsNoetherianRing Γ(N, O) := IsLocallyNoetherian.component_noetherian ⟨O, hO⟩
  obtain ⟨w, hw, hwn⟩ := @exists_specializes_of_dense (O : Set N) _ O.isOpen.isOpenEmbedding_subtypeVal.quasiSober
    (noetherianSpace_of_isAffineOpen O hO) (Subtype.val ⁻¹' W : Set (O : Set N)) (hWo.preimage continuous_subtype_val)
    (hWd.preimage O.isOpen.isOpenMap_subtype_val) ⟨n, hnO⟩
  exact ⟨w, hw, hwn.map continuous_subtype_val⟩

end GlobalTheory.BlowOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFamilyChartDomain
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

noncomputable section

namespace GlobalTheory.RiemSmooth

def stdR (g : ℕ) : Module.Basis (Σ _ : Fin g, Fin 2) ℝ (Fin g → ℂ) :=
  Pi.basis fun _ => Complex.basisOneI

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm y w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    imForm Hm z w = (hermForm Hm z w).im := rfl

theorem entry_eq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (p q : Fin g) :
    Hm p q = ((imForm Hm (stdR g ⟨p, 1⟩) (stdR g ⟨q, 0⟩) : ℝ) : ℂ) +
      ((imForm Hm (stdR g ⟨p, 0⟩) (stdR g ⟨q, 0⟩) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [imForm_apply, stdR, hermForm, Pi.basis_apply]

end GlobalTheory.RiemSmooth

namespace GlobalTheory.RiemSmooth

def coordMat {g : ℕ} (u : (Σ _ : Fin g, Fin 2) → (Fin g → ℂ)) :
    Matrix (Σ _ : Fin g, Fin 2) (Σ _ : Fin g, Fin 2) ℝ :=
  Matrix.of fun a k => (stdR g).repr (u k) a

theorem std_eq_sum {g : ℕ} (u : (Σ _ : Fin g, Fin 2) → (Fin g → ℂ)) (hM : (coordMat u).det ≠ 0)
    (a : Σ _ : Fin g, Fin 2) :
    stdR g a = ∑ k, ((coordMat u)⁻¹ k a) • u k := by
  apply (stdR g).repr.injective
  ext a'
  have h1 : coordMat u * (coordMat u)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hM)
  have h2 : ∑ k, coordMat u a' k * (coordMat u)⁻¹ k a = if a = a' then 1 else 0 := by
    rw [← Matrix.mul_apply, h1, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.smul_apply, Finset.sum_apply', smul_eq_mul,
    Module.Basis.repr_self, Finsupp.single_apply]
  rw [← h2]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem imForm_std {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (u : (Σ _ : Fin g, Fin 2) → (Fin g → ℂ))
    (hM : (coordMat u).det ≠ 0) (F : (Σ _ : Fin g, Fin 2) → (Σ _ : Fin g, Fin 2) → ℝ)
    (hF : ∀ k l, (hermForm Hm (u k) (u l)).im = F k l) (a c : Σ _ : Fin g, Fin 2) :
    imForm Hm (stdR g a) (stdR g c) =
      ∑ k, ∑ l, (coordMat u)⁻¹ k a * (coordMat u)⁻¹ l c * F k l := by
  rw [std_eq_sum u hM a, std_eq_sum u hM c]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    imForm_apply, hF]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem contDiffOn_det_real {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : X → Matrix ι ι ℝ} {s : Set X} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => M x a b) s) :
    ContDiffOn ℝ ∞ (fun x => (M x).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem contDiffOn_inv_entry {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : X → Matrix ι ι ℝ} {s : Set X} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => M x a b) s)
    (hdet : ∀ x ∈ s, (M x).det ≠ 0) (k a : ι) :
    ContDiffOn ℝ ∞ (fun x => (M x)⁻¹ k a) s := by
  have hadj : ContDiffOn ℝ ∞ (fun x => (M x).adjugate k a) s := by
    simp only [Matrix.adjugate_apply]
    refine contDiffOn_det_real fun i j => ?_
    by_cases hi : i = a
    · subst hi; simpa [Matrix.updateRow_apply] using contDiffOn_const
    · simpa [Matrix.updateRow_apply, hi] using h i j
  refine ((contDiffOn_det_real h).inv hdet |>.mul hadj).congr fun x hx => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp [smul_eq_mul]

end GlobalTheory.RiemSmooth

namespace GlobalTheory.RiemSmooth

theorem contDiffOn_of_im_eq {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {L : Type} [AddCommGroup L] {g : ℕ}
    {B : Set X} (hB : IsOpen B) (P : X → (L →+ (Fin g → ℂ))) (F : L → L → ℝ)
    (hP : ∀ v, ContDiffOn ℝ ∞ (fun b => P b v) B)
    (hspan : ∀ b ∈ B, Submodule.span ℝ (Set.range (P b)) = ⊤)
    (Hm : X → Matrix (Fin g) (Fin g) ℂ)
    (hH : ∀ b ∈ B, ∀ x y, (hermForm (Hm b) (P b x) (P b y)).im = F x y) (p q : Fin g) :
    ContDiffOn ℝ ∞ (fun b => Hm b p q) B := by
  refine contDiffOn_of_locally_contDiffOn fun b₀ hb₀ => ?_
  obtain ⟨t, ht, hts, hli⟩ := exists_linearIndependent ℝ (Set.range (P b₀))
  rw [hspan b₀ hb₀] at hts
  let bt : Module.Basis t ℝ (Fin g → ℂ) := Module.Basis.mk hli (by rw [Subtype.range_coe, hts])
  let e := bt.indexEquiv (stdR g)
  have hv : ∀ k, ∃ v, P b₀ v = bt (e.symm k) := fun k => by
    obtain ⟨v, hv⟩ := ht (e.symm k).2
    exact ⟨v, by rw [hv, Module.Basis.mk_apply]⟩
  choose v hv using hv
  let M : X → Matrix (Σ _ : Fin g, Fin 2) (Σ _ : Fin g, Fin 2) ℝ := fun b => coordMat fun k => P b (v k)
  have hMs : ∀ a k, ContDiffOn ℝ ∞ (fun b => M b a k) B := fun a k => by
    let ℓ : (Fin g → ℂ) →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap ((Finsupp.lapply a).comp (stdR g).repr.toLinearMap)
    exact ℓ.contDiff.comp_contDiffOn (hP (v k))
  have hdet0 : (M b₀).det ≠ 0 := by
    have : M b₀ = (stdR g).toMatrix (bt.reindex e) := by
      ext a k
      simp [M, coordMat, Module.Basis.toMatrix_apply, hv]
    rw [this, ← Module.Basis.det_apply]
    exact ((stdR g).isUnit_det _).ne_zero
  have hcont : ContinuousAt (fun b => (M b).det) b₀ :=
    (contDiffOn_det_real hMs).continuousOn.continuousAt (hB.mem_nhds hb₀)
  obtain ⟨U, hU, hUo, hb₀U⟩ := eventually_nhds_iff.1 (hcont.eventually_ne hdet0)
  refine ⟨U, hUo, hb₀U, ?_⟩
  have hdet : ∀ b ∈ B ∩ U, (M b).det ≠ 0 := fun b hb => hU b hb.2
  have hN := contDiffOn_inv_entry (fun a k => (hMs a k).mono Set.inter_subset_left) hdet
  have hsum : ∀ a c, ContDiffOn ℝ ∞ (fun b => ∑ k, ∑ l, (M b)⁻¹ k a * (M b)⁻¹ l c * F (v k) (v l)) (B ∩ U) :=
    fun a c => ContDiffOn.sum fun k _ => ContDiffOn.sum fun l _ =>
      ((hN k a).mul (hN l c)).mul contDiffOn_const
  refine ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hsum ⟨p, 1⟩ ⟨q, 0⟩)).add
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hsum ⟨p, 0⟩ ⟨q, 0⟩)).mul (contDiffOn_const (c := Complex.I)))).congr
    fun b hb => ?_
  have hF : ∀ k l, (hermForm (Hm b) (P b (v k)) (P b (v l))).im = F (v k) (v l) :=
    fun k l => hH b hb.1 _ _
  have h1 := entry_eq (Hm b) p q
  rw [imForm_std (Hm b) _ (hdet b hb) _ hF, imForm_std (Hm b) _ (hdet b hb) _ hF] at h1
  exact h1

theorem exists_riem_contDiffOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (d : ℕ) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B → (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → ∃ Hm : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin g) (Fin g) ℂ, (∀ b ∈ B, IsRiem Fu i (P b) (Hm b)) ∧ ∀ p q, ContDiffOn ℝ ∞ (fun b => Hm b p q) B := by
  intro E _ _ _ H Dw l Xo c σ g ty Fu i d B P hB hper hhol
  classical
  let Hm : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin g) (Fin g) ℂ :=
    fun b => if h : b ∈ B then Classical.choose (hper b h).2.2.2.2 else 0
  have hHm : ∀ b (h : b ∈ B), Hm b = Classical.choose (hper b h).2.2.2.2 := fun b h => dif_pos h
  have hR : ∀ b ∈ B, IsRiem Fu i (P b) (Hm b) := fun b h => by
    rw [hHm b h]
    exact Classical.choose_spec (hper b h).2.2.2.2
  refine ⟨Hm, hR, fun p q => ?_⟩
  refine contDiffOn_of_im_eq hB P (fun x y => ((Fu.Di i).EF x y : ℝ)) (fun v => ?_)
    (fun b h => (hper b h).2.2.2.1) Hm (fun b h x y => (hR b h).2.2 x y) p q
  exact contDiffOn_pi.2 fun j =>
    GlobalTheory.ChartGlue.contDiffOn_real hB ((differentiableOn_pi.1 (hhol v)) j)

end GlobalTheory.RiemSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixPolynomialGrowthPuncturedPolydisc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem period_growth_mono_bound (x C : ℝ) (k K : ℕ) (hx : 0 ≤ x) (hk : k ≤ K) :
    C * (1 + x) ^ k ≤ max C 0 * (1 + x) ^ K := by
  have h1 : (1:ℝ) ≤ 1 + x := by linarith
  calc C * (1 + x) ^ k ≤ max C 0 * (1 + x) ^ k :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 + x) ^ K :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hk) (le_max_right _ _)

theorem period_matrix_polynomial_growth : ∀ (n a d : ℕ) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (c : Fin d → Fin d → ℂ), DifferentiableOn ℂ τ (logDom n a) → (∀ s ∈ logDom n a, ∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im) → (∀ s ∈ logDom n a, ∀ i j, τ s i j - τ s j i = c i j) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n a d τ c hτ hpos hc

  have key : ∀ v : Fin d → ℝ, v ≠ 0 → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 →
      (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) →
      ‖∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)‖ ≤ C * (1 + ‖s‖) ^ k := by
    intro v hv
    apply GlobalTheory.upper_half_growth n a
    · have hij : ∀ i j, DifferentiableOn ℂ (fun s => τ s i j) (logDom n a) :=
        fun i j => differentiableOn_pi.1 (differentiableOn_pi.1 hτ i) j
      fun_prop
    · intro s hs; exact hpos s hs v hv
  have e1 : ∀ (M : Fin d → Fin d → ℂ) (i : Fin d),
      ∑ i', ∑ j', (((Pi.single i (1:ℝ) : Fin d → ℝ) i' : ℝ) : ℂ) * M i' j' * (((Pi.single i (1:ℝ) : Fin d → ℝ) j' : ℝ) : ℂ) = M i i := by
    intro M i
    simp [Pi.single_apply, apply_ite Complex.ofReal, ite_mul, mul_ite, Finset.sum_ite_eq']
  have e2 : ∀ (M : Fin d → Fin d → ℂ) (i j : Fin d),
      ∑ i', ∑ j', ((((Pi.single i (1:ℝ) + Pi.single j 1 : Fin d → ℝ)) i' : ℝ) : ℂ) * M i' j' * ((((Pi.single i (1:ℝ) + Pi.single j 1 : Fin d → ℝ)) j' : ℝ) : ℂ) = M i i + M j j + M i j + M j i := by
    intro M i j
    simp [Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib, apply_ite Complex.ofReal, ite_mul, mul_ite, Finset.sum_ite_eq']
    ring
  have ne1 : ∀ i : Fin d, (Pi.single i (1:ℝ) : Fin d → ℝ) ≠ 0 := by
    intro i h
    have := congrFun h i
    simp at this
  have ne2 : ∀ i j : Fin d, (Pi.single i (1:ℝ) + Pi.single j 1 : Fin d → ℝ) ≠ 0 := by
    intro i j h
    have := congrFun h i
    simp [Pi.single_apply] at this
    split_ifs at this <;> linarith

  have entry : ∀ i j : Fin d, ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 →
      (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖τ s i j‖ ≤ C * (1 + ‖s‖) ^ k := by
    intro i j
    obtain ⟨C1, k1, h1⟩ := key _ (ne2 i j)
    obtain ⟨C2, k2, h2⟩ := key _ (ne1 i)
    obtain ⟨C3, k3, h3⟩ := key _ (ne1 j)
    refine ⟨(max C1 0 + max C2 0 + max C3 0 + ‖c i j‖) / 2, max k1 (max k2 k3), by positivity, ?_⟩
    intro s hs hl him
    set K := max k1 (max k2 k3)
    have hx : 0 ≤ ‖s‖ := norm_nonneg _
    have b1 := (h1 s hs hl him).trans (period_growth_mono_bound ‖s‖ C1 k1 K hx (by omega))
    have b2 := (h2 s hs hl him).trans (period_growth_mono_bound ‖s‖ C2 k2 K hx (by omega))
    have b3 := (h3 s hs hl him).trans (period_growth_mono_bound ‖s‖ C3 k3 K hx (by omega))
    rw [e2] at b1
    rw [e1] at b2 b3
    have hP : 1 ≤ (1 + ‖s‖) ^ K := one_le_pow₀ (by linarith)
    have hcc : ‖c i j‖ ≤ ‖c i j‖ * (1 + ‖s‖) ^ K := le_mul_of_one_le_right (norm_nonneg _) hP
    have hid : (2:ℂ) * τ s i j = (τ s i i + τ s j j + τ s i j + τ s j i) - τ s i i - τ s j j + c i j := by
      rw [← hc s hs i j]; ring
    have h2n : ‖(2:ℂ) * τ s i j‖ ≤ ‖τ s i i + τ s j j + τ s i j + τ s j i‖ + ‖τ s i i‖ + ‖τ s j j‖ + ‖c i j‖ := by
      rw [hid]
      refine (norm_add_le _ _).trans ?_
      gcongr
      refine (norm_sub_le _ _).trans ?_
      gcongr
      exact norm_sub_le _ _
    rw [norm_mul] at h2n
    norm_num at h2n
    nlinarith
  choose Ce ke hCe hke using entry
  refine ⟨∑ i, ∑ j, Ce i j, Finset.univ.sup (fun p : Fin d × Fin d => ke p.1 p.2), ?_⟩
  intro s hs hl him
  set K := Finset.univ.sup (fun p : Fin d × Fin d => ke p.1 p.2)
  have hx : 0 ≤ ‖s‖ := norm_nonneg _
  have hP : 0 ≤ (1 + ‖s‖) ^ K := by positivity
  have hS : 0 ≤ ∑ i, ∑ j, Ce i j := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hCe i j
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have hk : ke i j ≤ K := Finset.le_sup (f := fun p : Fin d × Fin d => ke p.1 p.2) (Finset.mem_univ (i, j))
  have b := (hke i j s hs hl him).trans (period_growth_mono_bound ‖s‖ (Ce i j) (ke i j) K hx hk)
  rw [max_eq_left (hCe i j)] at b
  have hle : Ce i j ≤ ∑ i, ∑ j, Ce i j :=
    (Finset.single_le_sum (f := fun j => Ce i j) (fun j _ => hCe i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, Ce i j) (fun i _ => Finset.sum_nonneg fun j _ => hCe i j) (Finset.mem_univ i))
  exact b.trans (mul_le_mul_of_nonneg_right hle hP)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationScaledMultiple
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TorRef.Scale

variable {X : Scheme.{0}}

theorem idlAlong_nsmul (D : EffCartierData X) (n : ℕ) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) :
    idlAlong (D.nsmul n).idealSheaf ξ = idlAlong D.idealSheaf ξ ^ n := by
  obtain ⟨i, hi⟩ := D.exists_mem (ξ (IsLocalRing.closedPoint R))
  have h1 := (D.nsmul n).stalkId_idealSheaf i _ hi
  have h2 := D.stalkId_idealSheaf i _ hi
  have h3 : (X.presheaf.germ ((D.nsmul n).U i) (ξ (IsLocalRing.closedPoint R)) hi).hom ((D.nsmul n).f i) =
      ((X.presheaf.germ (D.U i) (ξ (IsLocalRing.closedPoint R)) hi).hom (D.f i)) ^ n :=
    map_pow _ _ _
  unfold idlAlong
  rw [h1, h3, h2, ← Ideal.map_pow, Ideal.span_singleton_pow]

end GlobalTheory.TorRef.Scale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilPairingExpModelFiberEqAlternatingFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_expModelFiber_eq_alternatingForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → ∀ (k : ℕ) (a b : (Fu.Di i).La) (ζ : ℂˣ), 0 < k → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Fu.Di i).EF a b : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P a)) (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P b)) (unitOn ζ) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.pushEx_cubWeil | exact GlobalTheory.ShFam.Hor.LogCh.pushEx_cubWeil | (intros; apply GlobalTheory.ShFam.Hor.LogCh.pushEx_cubWeil <;> assumption)
end

