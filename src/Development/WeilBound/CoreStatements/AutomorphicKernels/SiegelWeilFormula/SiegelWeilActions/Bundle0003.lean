module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.LagrangianCondition
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0013
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.UpperBlockRankOneUpdate

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOfParts
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act

def IndepDom : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (L : LD d), ∀ s₁ f, IsSec d.K d.χ s₁ f → ∀ z : ℂ,
  (∀ nb lam 𝓖 𝓖₀, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖₀ →
    ∀ uM ν 𝓤 𝓤₀, L.UData uM ν 𝓤 → L.UData uM ν 𝓤₀ → ∀ T T', L.IsSub T T' → ∀ x,
      ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T (uM u * x) ∂ν =
        ∫ u in 𝓤₀, fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM u * x) ∂ν) ∧
  ∀ nb' lam' 𝓖' 𝓖'₀, CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖'₀ →
    ∀ T' x, first L f s₁ z nb' lam' 𝓖' T' x = first L f s₁ z nb' lam' 𝓖'₀ T' x

def CptDom : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ),
  (∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 →
    ∃ 𝓖₀, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖₀ ∧ IsCompact (closure 𝓖₀)) ∧
  ∀ L : LD d, ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∃ 𝓤₀, L.UData uM ν 𝓤₀ ∧ IsCompact (closure 𝓤₀)

def AbsConv : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (L : LD d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ (T : nF σ d.Y d.b) (x : d.G),
    (∀ q : Cs d, Integrable (kq L f s₁ z nb T uM (rep q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖))) ∧
    Summable fun q : Cs d => ∫ p, ‖kq L f s₁ z nb T uM (rep q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖))

def FirstEq : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (L : LD d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → IsCompact (closure 𝓖') →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ T T', L.IsSub T T' → ∀ x,
    ∑' q : {q : Cs d // LagrangianCondition L (rep q)}, tm L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep q.1) x = first L f s₁ z nb' lam' 𝓖' T' x


variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} in
structure CLaw {d : SD σ} (R : RD d) (L : LD d) (w₁ : d.G) (cM : (Fin L.n → AE F E) × AF F → d.G)
    (κ : Measure ((Fin L.n → AE F E) × AF F)) : Prop where
  comm : ∀ w (τ : ℝ) (y : GR d.n) (g : G2 σ L.Y), IsDil (Pi.single L.i₀ 1) τ y → L.j g * R.ι w y = R.ι w y * L.j g
  wdil : ∀ w (τ : ℝ) (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y → ∃ p t, IsPar p t ∧
    (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = Real.exp (-(2 * τ)) ∧
    (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = 1 ∧ w₁ * R.ι w y = p * w₁
  cdil : ∀ w (τ : ℝ) (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y →
    ∃ sc : ((Fin L.n → AE F E) × AF F) ≃ᵐ ((Fin L.n → AE F E) × AF F), (∀ c, cM c * R.ι w y = R.ι w y * cM (sc c)) ∧
      κ.map sc = ENNReal.ofReal (Real.exp (2 * d.n * τ)) • κ

def SecUnf : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) (L : LD d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ →
  ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ T T', L.IsSub T T' →
  ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → IsCompact (closure 𝓖') →
  ∃ w₁ cM κ, CLaw R L w₁ cM κ ∧ ∃ K : ℂ, ∀ x,
    sec2 L f s₁ z nb lam 𝓖 T uM ν 𝓤 x = K * ∑' q' : Cs L.sd, ∫ β in 𝓖',
      (∫ c, phz d f s₁ z (w₁ * (cM c * (L.j (rep q' * nb' β) * x))) ∂κ) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β.1)))) ∂lam'

def SecLaw : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) (L : LD d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ →
  ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ T T', L.IsSub T T' →
  ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → IsCompact (closure 𝓖') →
  ∀ w (τ : ℝ) (y : GR d.n) x, IsDil (Pi.single L.i₀ 1) τ y →
    sec2 L f s₁ z nb lam 𝓖 T uM ν 𝓤 (R.ι w y * x) = Complex.exp (τ * (d.n - 2 * z)) * sec2 L f s₁ z nb lam 𝓖 T uM ν 𝓤 x


variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} in
theorem phz_par {d : SD σ} {f : d.G → ℂ} {s₁ : ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {τ : ℝ} {p : d.G} {t : GL (Fin d.n) (AE F E)}
    (hp : IsPar p t) (ha : (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = Real.exp (-(2 * τ)))
    (hχ : (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = 1) (g : d.G) :
    phz d f s₁ z (p * g) = Complex.exp (-(τ * (2 * z + d.n))) * phz d f s₁ z g := by
  have hH : ((d.Ht (p * g) : ℝ) : ℂ) = (Real.exp (-(2 * τ)) : ℂ) * ((d.Ht g : ℝ) : ℂ) := by
    simp only [SD.Ht]
    rw [d.ok.hgt.mul hp, ha, Real.toNNReal_mul (Real.exp_pos _).le, NNReal.coe_mul, Real.coe_toNNReal _ (Real.exp_pos _).le,
      Complex.ofReal_mul]
  have he : ∀ w : ℂ, ((Real.exp (-(2 * τ)) : ℝ) : ℂ) ^ w = Complex.exp (-(2 * τ) * w) := by
    intro w
    rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp] <;> push_cast <;> simp [Real.pi_pos, Real.pi_pos.le]
  unfold phz
  rw [hH, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos _).le NNReal.zero_le_coe, hf.law p t g hp, hχ, ha, he, he,
    ← mul_assoc]
  have : Complex.exp (-(τ * (2 * z + d.n))) = Complex.exp (-(2 * τ) * (z - s₁)) * Complex.exp (-(2 * τ) * (s₁ + d.n / 2)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this]; ring

theorem secLaw_of : SecUnf → SecLaw := by
  intro hU F E _ _ _ _ _ σ d R L s₁ f hf he
  obtain ⟨t, ht⟩ := hU F E σ d R L s₁ f hf he
  refine ⟨t, fun z hz nb lam 𝓖 hc hcG uM ν 𝓤 hUd hcU T T' hTT' nb' lam' 𝓖' hc' hcG' w τ y x hy => ?_⟩
  obtain ⟨w₁, cM, κ, hL, K, hK⟩ := ht z hz nb lam 𝓖 hc hcG uM ν 𝓤 hUd hcU T T' hTT' nb' lam' 𝓖' hc' hcG'
  obtain ⟨p, tp, hp, ha, hχ, hw⟩ := hL.wdil w τ y hy
  obtain ⟨sc, hsc, hκ⟩ := hL.cdil w τ y hy
  have key : ∀ h : G2 σ L.Y, ∫ c, phz d f s₁ z (w₁ * (cM c * (L.j h * (R.ι w y * x)))) ∂κ =
      Complex.exp (τ * (d.n - 2 * z)) * ∫ c, phz d f s₁ z (w₁ * (cM c * (L.j h * x))) ∂κ := by
    intro h
    have h1 : ∀ c, w₁ * (cM c * (L.j h * (R.ι w y * x))) = p * (w₁ * (cM (sc c) * (L.j h * x))) := by
      intro c
      rw [← mul_assoc (L.j h), hL.comm w τ y h hy, mul_assoc, ← mul_assoc (cM c), hsc c, mul_assoc, ← mul_assoc w₁, hw,
        mul_assoc]
    simp_rw [h1, phz_par hf z hp ha hχ]
    rw [integral_const_mul, ← integral_map_equiv sc (fun c => phz d f s₁ z (w₁ * (cM c * (L.j h * x)))), hκ,
      integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul, ← mul_assoc]
    congr 1
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hK, hK]
  simp_rw [key, mul_assoc (Complex.exp _), integral_const_mul]
  rw [tsum_mul_left]; ring


variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} in
theorem lhs_eq_tsum {d : SD σ} (L : LD d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b))
    (𝓖 : Set (nA σ d.Y d.b)) (T : nF σ d.Y d.b) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E))
    (𝓤 : Set (Fin L.n → AE F E)) (hν : ν 𝓤 = 1) (hlam : lam 𝓖 = 1) (x : d.G)
    (hi : ∀ q : Cs d, Integrable (kq L f s₁ z nb T uM (rep q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖)))
    (hs : Summable fun q : Cs d => ∫ p, ‖kq L f s₁ z nb T uM (rep q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖))) :
    Summable (fun q : Cs d => tm L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep q) x) ∧
      ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T (uM u * x) ∂ν = ∑' q : Cs d, tm L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep q) x := by
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (Cs d) := Quotient.countable
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by simp [hν])
  have : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by simp [hlam])
  obtain ⟨h1, h2⟩ := exch (fun q : Cs d => kq L f s₁ z nb T uM (rep q) x) hi hs
  have htm : ∀ q : Cs d, tm L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep q) x =
      ∫ u, ∫ v, kq L f s₁ z nb T uM (rep q) x (u, v) ∂(lam.restrict 𝓖) ∂(ν.restrict 𝓤) := fun q => rfl
  simp_rw [htm]
  refine ⟨h1, ?_⟩
  rw [← h2]
  refine integral_congr_ae (ae_of_all _ fun u => integral_congr_ae (ae_of_all _ fun β => ?_))
  simp only [SD.eis, GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term, kq, phz, rep]
  rw [tsum_mul_right]
  rfl

theorem ctSplit_of_parts : IndepDom → CptDom → AbsConv → FirstEq → SecLaw → CTSplit := by
  intro hI hC hA hF hS F E _ _ _ _ _ σ d R L s₁ f hf he
  obtain ⟨tA, hA'⟩ := hA F E σ d L s₁ f hf he
  obtain ⟨tF, hF'⟩ := hF F E σ d L s₁ f hf he
  obtain ⟨tS, hS'⟩ := hS F E σ d R L s₁ f hf he
  refine ⟨max tA (max tF tS), fun z hz nb lam 𝓖 hc nb' lam' 𝓖' hc' uM ν 𝓤 hU T T' hTT' => ?_⟩
  have hzA : tA < z.re := lt_of_le_of_lt (le_max_left _ _) hz
  have hzF : tF < z.re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hz
  have hzS : tS < z.re := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hz
  obtain ⟨𝓖₀, hc₀, hk₀⟩ := (hC F E σ d).1 nb lam 𝓖 hc
  obtain ⟨𝓤₀, hU₀, hkU⟩ := (hC F E σ d).2 L uM ν 𝓤 hU
  obtain ⟨𝓖'₀, hc'₀, hk'₀⟩ := (hC F E σ L.sd).1 nb' lam' 𝓖' hc'
  refine ⟨sec2 L f s₁ z nb lam 𝓖₀ T uM ν 𝓤₀, fun x => ?_, fun w τ y x hy =>
    hS' z hzS nb lam 𝓖₀ hc₀ hk₀ uM ν 𝓤₀ hU₀ hkU T T' hTT' nb' lam' 𝓖'₀ hc'₀ hk'₀ w τ y x hy⟩
  have e1 := (hI F E σ d L s₁ f hf z).1 nb lam 𝓖 𝓖₀ hc hc₀ uM ν 𝓤 𝓤₀ hU hU₀ T T' hTT' x
  have e2 := (hI F E σ d L s₁ f hf z).2 nb' lam' 𝓖' 𝓖'₀ hc' hc'₀ T' x
  have e3 := hF' z hzF nb lam 𝓖₀ hc₀ hk₀ nb' lam' 𝓖'₀ hc'₀ hk'₀ uM ν 𝓤₀ hU₀ hkU T T' hTT' x
  obtain ⟨hi, hs⟩ := hA' z hzA nb lam 𝓖₀ hc₀ hk₀ uM ν 𝓤₀ hU₀ hkU T x
  obtain ⟨hsum, e4⟩ := lhs_eq_tsum L f s₁ z nb lam 𝓖₀ T uM ν 𝓤₀ hU₀.2.2.2 hc₀.2.2.2 x hi hs
  change _ = first L f s₁ z nb' lam' 𝓖' T' x + _
  rw [e1, e2, ← e3, e4, ← hsum.tsum_subtype_add_tsum_subtype_compl {q : Cs d | LagrangianCondition L (rep q)}]
  rfl

end PositivityTheory.SiegelWeilFormula.Act

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MemStabiliserIffFrameLowerBlock
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E}

theorem mem_stabiliser_iff_frame_lower_block (hb : IsFrame2 σ Y b) (p : G2 σ Y) :
    p ∈ par2 σ Y ↔ (inFrame b p).toBlocks₂₁ = 0 := by
  obtain ⟨-, t₀, ht₀⟩ := hb
  rw [GlobalTheory.ThK.Dbl.mem_parabolic_GL2_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ((kunf.isPar_frame ht₀ p t).1 ht).1
  · intro h
    set M := inFrame b p with hM
    have hMi : M * inFrame b p⁻¹ = 1 := by
      rw [hM, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
    have hdet : IsUnit M.det := Matrix.isUnit_det_of_right_inverse hMi
    have hsplit : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
      rw [← h, Matrix.fromBlocks_toBlocks]
    have hdet2 : M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det := by
      rw [hsplit, Matrix.det_fromBlocks_zero₂₁]
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.fromBlocks]
    have hA : IsUnit M.toBlocks₁₁.det := isUnit_of_mul_isUnit_left (hdet2 ▸ hdet)
    set A := M.toBlocks₁₁
    set T0 := incM F t₀.1
    set T0i := incM F (t₀⁻¹).1
    have e1 : T0 * T0i = 1 := by
      simp only [T0, T0i, incM, ← Matrix.map_mul]
      rw [show t₀.1 * (t₀⁻¹).1 = 1 from t₀.mul_inv]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have e2 : T0i * T0 = 1 := by
      simp only [T0, T0i, incM, ← Matrix.map_mul]
      rw [show (t₀⁻¹).1 * t₀.1 = 1 from t₀.inv_mul]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
    have hAA' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
    let t : GL (Fin n) (AE F E) := ⟨T0 * A * T0i, T0 * A⁻¹ * T0i, by
        calc T0 * A * T0i * (T0 * A⁻¹ * T0i) = T0 * (A * (T0i * T0) * A⁻¹) * T0i := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [e2, Matrix.mul_one, hAA, Matrix.mul_one, e1], by
        calc T0 * A⁻¹ * T0i * (T0 * A * T0i) = T0 * (A⁻¹ * (T0i * T0) * A) * T0i := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [e2, Matrix.mul_one, hAA', Matrix.mul_one, e1]⟩
    exact ⟨t, (kunf.isPar_frame ht₀ p t).2 ⟨h, rfl⟩⟩

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ShiftCoordinatesColumn
section
noncomputable section

open Matrix PositivityTheory.SiegelWeilFormula.Act.C4.Bq

namespace PositivityTheory.SiegelWeilFormula.Act.C6.M

variable {R : Type} [CommRing R] (s : R →+* R) (e : R) {n : ℕ} (i₀ : Fin n)

def U (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) : Prop := Mᵀ * kunf.jw n e * M.map s = kunf.jw n e

variable {s e i₀}

theorem qms_inl (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (a : Fin n) (d : Fin n ⊕ Fin n) :
    (kunf.jw n e * M.map s) (Sum.inl a) d = s (M (Sum.inr a) d) := by
  simp [kunf.jw, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem qms_inr (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (a : Fin n) (d : Fin n ⊕ Fin n) :
    (kunf.jw n e * M.map s) (Sum.inr a) d = e * s (M (Sum.inl a) d) := by
  simp [kunf.jw, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.smul_apply]

theorem U_apply {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hU : U s e M) (c d : Fin n ⊕ Fin n) :
    ∑ r, M r c * (kunf.jw n e * M.map s) r d = kunf.jw n e c d := by
  have := congrFun (congrFun hU c) d
  rw [Matrix.mul_assoc, Matrix.mul_apply] at this
  simpa [Matrix.transpose_apply] using this

theorem shift_coordinates_column {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hN : NQ (Sum.inl i₀) (Sum.inr i₀) M)
    (W : Fin n ⊕ Fin n → R) : ∑ r, M r (Sum.inl i₀) * W r = W (Sum.inl i₀) := by
  have h : ∀ r, M r (Sum.inl i₀) = if r = Sum.inl i₀ then 1 else 0 := fun r => by
    rw [NQ.apply hN (Or.inl rfl), Matrix.one_apply]
  simp_rw [h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem col_c {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hN : NQ (Sum.inl i₀) (Sum.inr i₀) M)
    {c : Fin n ⊕ Fin n} (hcx : c ≠ Sum.inl i₀) (hcy : c ≠ Sum.inr i₀) (W : Fin n ⊕ Fin n → R) :
    ∑ r, M r c * W r = W c + M (Sum.inl i₀) c * W (Sum.inl i₀) := by
  have h : ∀ r, M r c = (if r = c then 1 else 0) + (if r = Sum.inl i₀ then M (Sum.inl i₀) c else 0) := by
    intro r
    by_cases hr : r = Sum.inl i₀
    · subst hr; rw [if_neg (Ne.symm hcx), if_pos rfl, zero_add]
    · rw [NQ.apply hN (Or.inr ⟨hcy, hr⟩), Matrix.one_apply]; simp [hr]
  rw [Finset.sum_congr rfl fun r _ => congrArg (· * W r) (h r)]
  simp_rw [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_split' {A : Type} [AddCommMonoid A] {m : ℕ} (em : Fin m → Fin n) (hem : Function.Injective em)
    (hrng : ∀ k, k ≠ i₀ ↔ k ∈ Set.range em) (f : Fin n → A) : ∑ a, f a = f i₀ + ∑ j, f (em j) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  congr 1
  rw [← Finset.sum_image (fun a _ b _ h => hem h)]
  congr 1
  ext k
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_image, true_and]
  exact hrng k

theorem columnBlock (hs : ∀ a, s (s a) = a) (he : e * e = 1) (hse : s e = e) {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    (hU : U s e M) (hN : NQ (Sum.inl i₀) (Sum.inr i₀) M) :
    M (Sum.inr i₀) (Sum.inr i₀) = 1 ∧ (∀ k, k ≠ i₀ → s (M (Sum.inr k) (Sum.inr i₀)) = -M (Sum.inl i₀) (Sum.inl k)) ∧
      ∀ k, k ≠ i₀ → s (M (Sum.inl k) (Sum.inr i₀)) = -(e * M (Sum.inl i₀) (Sum.inr k)) := by
  set W : Fin n ⊕ Fin n → R := fun r => (kunf.jw n e * M.map s) r (Sum.inr i₀) with hW
  have hyy : s (M (Sum.inr i₀) (Sum.inr i₀)) = 1 := by
    have h1 := U_apply hU (Sum.inl i₀) (Sum.inr i₀)
    rw [shift_coordinates_column hN W] at h1
    simp only [hW, qms_inl] at h1
    simpa [kunf.jw] using h1
  refine ⟨by rw [← hs (M _ _), hyy, map_one], fun k hk => ?_, fun k hk => ?_⟩
  · have h1 := U_apply hU (Sum.inl k) (Sum.inr i₀)
    rw [col_c hN (by simpa using hk) (by simp) W] at h1
    have h2 : s (M (Sum.inr k) (Sum.inr i₀)) + M (Sum.inl i₀) (Sum.inl k) = 0 := by
      simp only [hW, qms_inl, hyy, mul_one] at h1
      simpa [kunf.jw, Matrix.one_apply_ne hk] using h1
    exact eq_neg_of_add_eq_zero_left h2
  · have h1 := U_apply hU (Sum.inr k) (Sum.inr i₀)
    rw [col_c hN (by simp) (by simpa using hk) W] at h1
    have h2 : e * s (M (Sum.inl k) (Sum.inr i₀)) + M (Sum.inl i₀) (Sum.inr k) = 0 := by
      simp only [hW, qms_inl, qms_inr, hyy, mul_one] at h1
      simpa [kunf.jw] using h1
    have h3 := eq_neg_of_add_eq_zero_left h2
    calc s (M (Sum.inl k) (Sum.inr i₀)) = e * (e * s (M (Sum.inl k) (Sum.inr i₀))) := by rw [← mul_assoc, he, one_mul]
      _ = -(e * M (Sum.inl i₀) (Sum.inr k)) := by rw [h3, mul_neg]

theorem nq_unique (hs : ∀ a, s (s a) = a) (he : e * e = 1) (hse : s e = e)
    {M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hM : U s e M) (hN : U s e N)
    (hMq : NQ (Sum.inl i₀) (Sum.inr i₀) M) (hNq : NQ (Sum.inl i₀) (Sum.inr i₀) N)
    (hrow : ∀ c, M (Sum.inl i₀) c = N (Sum.inl i₀) c) : M = N := by
  obtain ⟨hM1, hM2, hM3⟩ := columnBlock hs he hse hM hMq
  obtain ⟨hN1, hN2, hN3⟩ := columnBlock hs he hse hN hNq
  have hinj : Function.Injective s := fun a b h => by rw [← hs a, h, hs b]
  ext r c
  by_cases hrx : r = Sum.inl i₀
  · subst hrx; exact hrow c
  by_cases hcy : c = Sum.inr i₀
  · subst hcy
    rcases r with k | k
    · have hk : k ≠ i₀ := fun h => hrx (by rw [h])
      exact hinj (by rw [hM3 k hk, hN3 k hk, hrow])
    · by_cases hk : k = i₀
      · subst hk; rw [hM1, hN1]
      · exact hinj (by rw [hM2 k hk, hN2 k hk, hrow])
  · rw [NQ.apply hMq (Or.inr ⟨hcy, hrx⟩), NQ.apply hNq (Or.inr ⟨hcy, hrx⟩)]

theorem even_im_hermitian_sub (hs : ∀ a, s (s a) = a) (he : e * e = 1) (hse : s e = e) {m : ℕ} (em : Fin m → Fin n)
    (hem : Function.Injective em) (hrng : ∀ k, k ≠ i₀ ↔ k ∈ Set.range em) {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    (hU : U s e M) (hN : NQ (Sum.inl i₀) (Sum.inr i₀) M) :
    s (M (Sum.inl i₀) (Sum.inr i₀) + ∑ j, M (Sum.inl i₀) (Sum.inr (em j)) * s (M (Sum.inl i₀) (Sum.inl (em j)))) =
      -(e * (M (Sum.inl i₀) (Sum.inr i₀) + ∑ j, M (Sum.inl i₀) (Sum.inr (em j)) * s (M (Sum.inl i₀) (Sum.inl (em j))))) := by
  obtain ⟨h1, h2, h3⟩ := columnBlock hs he hse hU hN
  have hem0 : ∀ j, em j ≠ i₀ := fun j => (hrng (em j)).2 ⟨j, rfl⟩
  have hl : ∀ j, M (Sum.inl (em j)) (Sum.inr i₀) = -(e * s (M (Sum.inl i₀) (Sum.inr (em j)))) := fun j => by
    rw [← hs (M (Sum.inl (em j)) (Sum.inr i₀)), h3 _ (hem0 j), map_neg, map_mul, hse]
  have hr : ∀ j, M (Sum.inr (em j)) (Sum.inr i₀) = -s (M (Sum.inl i₀) (Sum.inl (em j))) := fun j => by
    rw [← hs (M (Sum.inr (em j)) (Sum.inr i₀)), h2 _ (hem0 j), map_neg]
  have hyy : M (Sum.inr i₀) (Sum.inr i₀) = 1 := h1
  have h0 := U_apply hU (Sum.inr i₀) (Sum.inr i₀)
  rw [Fintype.sum_sum_type] at h0
  simp only [qms_inl, qms_inr] at h0
  rw [sum_split' em hem hrng (fun a => M (Sum.inl a) (Sum.inr i₀) * s (M (Sum.inr a) (Sum.inr i₀))),
    sum_split' em hem hrng (fun a => M (Sum.inr a) (Sum.inr i₀) * (e * s (M (Sum.inl a) (Sum.inr i₀))))] at h0
  simp only [hl, hr, hyy, map_one, map_neg, map_mul, hs, hse, kunf.jw, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] at h0
  set α := M (Sum.inl i₀) (Sum.inr i₀)
  set S1 := ∑ j, s (M (Sum.inl i₀) (Sum.inr (em j))) * M (Sum.inl i₀) (Sum.inl (em j))
  set S2 := ∑ j, M (Sum.inl i₀) (Sum.inr (em j)) * s (M (Sum.inl i₀) (Sum.inl (em j)))
  have hA : ∑ j, -(e * s (M (Sum.inl i₀) (Sum.inr (em j)))) * -M (Sum.inl i₀) (Sum.inl (em j)) = e * S1 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hB : ∑ j, -s (M (Sum.inl i₀) (Sum.inl (em j))) * (e * -(e * M (Sum.inl i₀) (Sum.inr (em j)))) = (e * e) * S2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hA, hB, he, one_mul] at h0
  have hS : s S2 = S1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [S2, S1, map_sum, map_mul, hs]
  rw [map_add (f := _), hS]
  linear_combination e * h0 - (s α + S1) * he

end PositivityTheory.SiegelWeilFormula.Act.C6.M

end
end

