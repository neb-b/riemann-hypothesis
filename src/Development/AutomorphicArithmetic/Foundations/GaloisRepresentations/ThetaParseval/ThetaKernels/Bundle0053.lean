module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.CongUnip
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0038
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0037
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.FrameOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0014
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0033
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0045

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActCut
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act
def IndepDom_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ s₁ f, IsSec d.K d.χ s₁ f → ∀ z : ℂ,
  (∀ nb lam 𝓖 𝓖₀, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖₀ →
    ∀ uM ν 𝓤 𝓤₀, L.UData uM ν 𝓤 → L.UData uM ν 𝓤₀ → ∀ T T', L.IsSub T T' → ∀ x,
      ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T (uM u * x) ∂ν =
        ∫ u in 𝓤₀, fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM u * x) ∂ν) ∧
  ∀ nb' lam' 𝓖' 𝓖'₀, CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖'₀ →
    ∀ T' x, _root_.PositivityTheory.SiegelWeilFormula.Act.first_k L f s₁ z nb' lam' 𝓖' T' x = _root_.PositivityTheory.SiegelWeilFormula.Act.first_k L f s₁ z nb' lam' 𝓖'₀ T' x
def CptDom_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  (∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 →
    ∃ 𝓖₀, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖₀ ∧ IsCompact (closure 𝓖₀)) ∧
  ∀ L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d, ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∃ 𝓤₀, L.UData uM ν 𝓤₀ ∧ IsCompact (closure 𝓤₀)
def AbsConv_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ (T : nF σ d.Y d.b) (x : d.G),
    (∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Integrable (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖))) ∧
    Summable fun q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d => ∫ p, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖))
def FirstEq_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → IsCompact (closure 𝓖') →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ T T', L.IsSub T T' → ∀ x,
    ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1) x = _root_.PositivityTheory.SiegelWeilFormula.Act.first_k L f s₁ z nb' lam' 𝓖' T' x
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} in
structure CLaw_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (w₁ : d.G) (cM : (Fin L.n → AE F E) × AF F → d.G)
    (κ : Measure ((Fin L.n → AE F E) × AF F)) : Prop where
  comm : ∀ w (τ : ℝ) (y : GR d.n) (g : G2 σ L.Y), IsDil (Pi.single L.i₀ 1) τ y → L.j g * R.ι w y = R.ι w y * L.j g
  wdil : ∀ w (τ : ℝ) (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y → ∃ p t, IsPar p t ∧
    (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = Real.exp (-(2 * τ)) ∧
    (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = 1 ∧ w₁ * R.ι w y = p * w₁
  cdil : ∀ w (τ : ℝ) (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y →
    ∃ sc : ((Fin L.n → AE F E) × AF F) ≃ᵐ ((Fin L.n → AE F E) × AF F), (∀ c, cM c * R.ι w y = R.ι w y * cM (sc c)) ∧
      κ.map sc = ENNReal.ofReal (Real.exp (2 * d.n * τ)) • κ
def SecUnf_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ →
  ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ T T', L.IsSub T T' →
  ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → IsCompact (closure 𝓖') →
  ∃ w₁ cM κ, _root_.PositivityTheory.SiegelWeilFormula.Act.CLaw_k R L w₁ cM κ ∧ ∃ K : ℂ, ∀ x,
    _root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 x = K * ∑' q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, ∫ β in 𝓖',
      (∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β) * x))) ∂κ) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β.1)))) ∂lam'
def SecLaw_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ →
  ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ T T', L.IsSub T T' →
  ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → IsCompact (closure 𝓖') →
  ∀ w (τ : ℝ) (y : GR d.n) x, IsDil (Pi.single L.i₀ 1) τ y →
    _root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 (R.ι w y * x) = Complex.exp (τ * (d.n - 2 * z)) * _root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 x
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} in
theorem phz_par_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {f : d.G → ℂ} {s₁ : ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {τ : ℝ} {p : d.G} {t : GL (Fin d.n) (AE F E)}
    (hp : IsPar p t) (ha : (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = Real.exp (-(2 * τ)))
    (hχ : (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = 1) (g : d.G) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (p * g) = Complex.exp (-(τ * (2 * z + d.n))) * _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z g := by
  have hH : ((d.Ht (p * g) : ℝ) : ℂ) = (Real.exp (-(2 * τ)) : ℂ) * ((d.Ht g : ℝ) : ℂ) := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht]
    rw [d.ok.hgt.mul hp, ha, Real.toNNReal_mul (Real.exp_pos _).le, NNReal.coe_mul, Real.coe_toNNReal _ (Real.exp_pos _).le,
      Complex.ofReal_mul]
  have he : ∀ w : ℂ, ((Real.exp (-(2 * τ)) : ℝ) : ℂ) ^ w = Complex.exp (-(2 * τ) * w) := by
    intro w
    rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp] <;> push_cast <;> simp [Real.pi_pos, Real.pi_pos.le]
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k
  rw [hH, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos _).le NNReal.zero_le_coe, hf.law p t g hp, hχ, ha, he, he,
    ← mul_assoc]
  have : Complex.exp (-(τ * (2 * z + d.n))) = Complex.exp (-(2 * τ) * (z - s₁)) * Complex.exp (-(2 * τ) * (s₁ + d.n / 2)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this]; ring
theorem secLaw_of_k : _root_.PositivityTheory.SiegelWeilFormula.Act.SecUnf_k → _root_.PositivityTheory.SiegelWeilFormula.Act.SecLaw_k := by
  intro hU F E _ _ _ _ _ σ d R L s₁ f hf he
  obtain ⟨t, ht⟩ := hU F E σ d R L s₁ f hf he
  refine ⟨t, fun z hz nb lam 𝓖 hc hcG uM ν 𝓤 hUd hcU T T' hTT' nb' lam' 𝓖' hc' hcG' w τ y x hy => ?_⟩
  obtain ⟨w₁, cM, κ, hL, K, hK⟩ := ht z hz nb lam 𝓖 hc hcG uM ν 𝓤 hUd hcU T T' hTT' nb' lam' 𝓖' hc' hcG'
  obtain ⟨p, tp, hp, ha, hχ, hw⟩ := hL.wdil w τ y hy
  obtain ⟨sc, hsc, hκ⟩ := hL.cdil w τ y hy
  have key : ∀ h : G2 σ L.Y, ∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j h * (R.ι w y * x)))) ∂κ =
      Complex.exp (τ * (d.n - 2 * z)) * ∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j h * x))) ∂κ := by
    intro h
    have h1 : ∀ c, w₁ * (cM c * (L.j h * (R.ι w y * x))) = p * (w₁ * (cM (sc c) * (L.j h * x))) := by
      intro c
      rw [← mul_assoc (L.j h), hL.comm w τ y h hy, mul_assoc, ← mul_assoc (cM c), hsc c, mul_assoc, ← mul_assoc w₁, hw,
        mul_assoc]
    simp_rw [h1, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_par_k hf z hp ha hχ]
    rw [integral_const_mul, ← integral_map_equiv sc (fun c => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j h * x)))), hκ,
      integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul, ← mul_assoc]
    congr 1
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hK, hK]
  simp_rw [key, mul_assoc (Complex.exp _), integral_const_mul]
  rw [tsum_mul_left]; ring
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} in
theorem lhs_eq_tsum_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b))
    (𝓖 : Set (nA σ d.Y d.b)) (T : nF σ d.Y d.b) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E))
    (𝓤 : Set (Fin L.n → AE F E)) (hν : ν 𝓤 = 1) (hlam : lam 𝓖 = 1) (x : d.G)
    (hi : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Integrable (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖)))
    (hs : Summable fun q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d => ∫ p, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖))) :
    Summable (fun q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d => _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) ∧
      ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T (uM u * x) ∂ν = ∑' q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x := by
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) := Quotient.countable
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by simp [hν])
  have : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by simp [hlam])
  obtain ⟨h1, h2⟩ := exch (fun q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d => _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) hi hs
  have htm : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x =
      ∫ u, ∫ v, _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x (u, v) ∂(lam.restrict 𝓖) ∂(ν.restrict 𝓤) := fun q => rfl
  simp_rw [htm]
  refine ⟨h1, ?_⟩
  rw [← h2]
  refine integral_congr_ae (ae_of_all _ fun u => integral_congr_ae (ae_of_all _ fun β => ?_))
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.eis, GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term, _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k, _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k]
  rw [tsum_mul_right]
  rfl
theorem ctSplit_of_parts_k : _root_.PositivityTheory.SiegelWeilFormula.Act.IndepDom_k → _root_.PositivityTheory.SiegelWeilFormula.Act.CptDom_k → _root_.PositivityTheory.SiegelWeilFormula.Act.AbsConv_k → _root_.PositivityTheory.SiegelWeilFormula.Act.FirstEq_k → _root_.PositivityTheory.SiegelWeilFormula.Act.SecLaw_k → _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k := by
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
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection L f s₁ z nb lam 𝓖₀ T uM ν 𝓤₀, fun x => ?_, fun w τ y x hy =>
    hS' z hzS nb lam 𝓖₀ hc₀ hk₀ uM ν 𝓤₀ hU₀ hkU T T' hTT' nb' lam' 𝓖'₀ hc'₀ hk'₀ w τ y x hy⟩
  have e1 := (hI F E σ d L s₁ f hf z).1 nb lam 𝓖 𝓖₀ hc hc₀ uM ν 𝓤 𝓤₀ hU hU₀ T T' hTT' x
  have e2 := (hI F E σ d L s₁ f hf z).2 nb' lam' 𝓖' 𝓖'₀ hc' hc'₀ T' x
  have e3 := hF' z hzF nb lam 𝓖₀ hc₀ hk₀ nb' lam' 𝓖'₀ hc'₀ hk'₀ uM ν 𝓤₀ hU₀ hkU T T' hTT' x
  obtain ⟨hi, hs⟩ := hA' z hzA nb lam 𝓖₀ hc₀ hk₀ uM ν 𝓤₀ hU₀ hkU T x
  obtain ⟨hsum, e4⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.lhs_eq_tsum_k L f s₁ z nb lam 𝓖₀ T uM ν 𝓤₀ hU₀.2.2.2 hc₀.2.2.2 x hi hs
  change _ = _root_.PositivityTheory.SiegelWeilFormula.Act.first_k L f s₁ z nb' lam' 𝓖' T' x + _
  rw [e1, e2, ← e3, e4, ← hsum.tsum_subtype_add_tsum_subtype_compl {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d | _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}]
  rfl
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAfcFcS
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp PositivityTheory.SiegelWeilFormula.kfour
namespace PositivityTheory.SiegelWeilFormula.Afc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem cong_unip_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (M : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (h0 : ∀ i, M L.i₀ i = 0 ∧ M i L.i₀ = 0) (u : Fin L.n → AE F E) :
    ((1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)).map (cA σ))ᵀ * M * (1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)) = M := by
  have h1 : M * (∑ j, Matrix.single L.i₀ (L.em j) (u j)) = 0 := by
    ext r s
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : L.i₀ = k
    · subst hk; simp [(h0 r).2]
    · simp [hk]
  have h2 : ((∑ j, Matrix.single L.i₀ (L.em j) (u j)).map (cA σ))ᵀ * M = 0 := by
    ext r s
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.zero_apply, Matrix.transpose_apply,
      Matrix.map_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : L.i₀ = k
    · subst hk; simp [(h0 s).1]
    · simp [hk]
  rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_add,
    Matrix.transpose_one, Matrix.add_mul, Matrix.one_mul, h2, add_zero, Matrix.mul_add, Matrix.mul_one, h1, add_zero]
theorem fc_U_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G}
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (T : nF σ d.Y d.b)
    (T' : nF σ L.Y L.b) (hs : L.IsSub T T') (φ : d.G → ℂ) (hφ : ∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g)
    (u : Fin L.n → AE F E) (hu : u ∈ L.ratV) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 φ T x := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have hb : IsFrame2 σ d.Y d.b := d.ok.frame
  have hψ : ∀ z : F, d.B.ψ (algebraMap F (AF F) z) = 1 := d.ok.good.std.2.1
  have hcc : ∀ z, cA σ (cA σ z) = z := _root_.PositivityTheory.SiegelWeilFormula.kfour.cA_cA' σ hσ
  obtain ⟨v, rfl⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Afc.mem_ratV_iff_k L u).1 hu
  obtain ⟨a', ha'⟩ := hU.1 (GlobalTheory.ThK.incV F v)
  set N0 : Matrix (Fin d.n) (Fin d.n) E := ∑ j, Matrix.single L.i₀ (L.em j) (v j) with hN0
  have hne : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
  have hN2 : N0 * N0 = 0 := by
    rw [hN0, Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun j' _ => ?_
    ext r s
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : L.i₀ = k
    · subst hk; simp [hne j]
    · simp [hk]
  let a : GL (Fin d.n) E := ⟨1 + N0, 1 - N0, by
      rw [mul_sub, mul_one, add_mul, one_mul, hN2, add_zero, add_sub_cancel_right], by
      rw [mul_add, mul_one, sub_mul, one_mul, hN2, sub_zero, sub_add_cancel]⟩
  obtain ⟨g, hg, hgf⟩ := levi_ex hσ hb a
  have hA : (1 + ∑ j, Matrix.single L.i₀ (L.em j) (GlobalTheory.ThK.incV F v j)) = incM F (1 + N0) := by
    ext r s
    simp [hN0, incM, Matrix.sum_apply, Matrix.single_apply, GlobalTheory.ThK.incV, Matrix.one_apply, apply_ite]
  rw [hA] at ha'
  have hgu : uM (GlobalTheory.ThK.incV F v) = g := by
    apply inFrame_injective d.b
    rw [ha', hgf]
    have r1 := (blk_rel hb _ ha').1
    have r2 := (blk_rel hb _ hgf).1
    have r1' := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 r1
    have e1 : a'.map (cA σ) = (incM F (((a⁻¹).1)ᵀ.map σ)).map (cA σ) := by
      calc a'.map (cA σ) = a'.map (cA σ) * ((incM F (a.1))ᵀ * (incM F (((a⁻¹).1)ᵀ.map σ)).map (cA σ)) := by
            rw [r2, Matrix.mul_one]
        _ = (a'.map (cA σ) * (incM F (a.1))ᵀ) * (incM F (((a⁻¹).1)ᵀ.map σ)).map (cA σ) := by rw [Matrix.mul_assoc]
        _ = _ := by rw [r1', Matrix.one_mul]
    have e2 : a' = incM F (((a⁻¹).1)ᵀ.map σ) := by
      have := congrArg (fun M => M.map (cA σ)) e1
      simpa [Matrix.map_map, Function.comp_def, hcc] using this
    rw [e2]
  have hgm : uM (GlobalTheory.ThK.incV F v) ∈ rat2 σ d.Y := hgu ▸ hg
  refine fc_levi hσ hb hψ hc _ hgm ha' T T ?_ φ hφ x
  rw [← hA]
  exact _root_.PositivityTheory.SiegelWeilFormula.Afc.cong_unip_k L T.1.1 hs.1 _
theorem fc_deg_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (hT : ¬ IsND T) :
    ∃ γ ∈ rat2 σ d.Y, ∃ T₀ T', L.IsSub T₀ T' ∧ ∀ φ : d.G → ℂ, Continuous φ →
      (∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g) → ∀ x,
        fc d.B.ψ d.b nb lam 𝓖 φ T x = fc d.B.ψ d.b nb lam 𝓖 φ T₀ (γ * x) := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have hb : IsFrame2 σ d.Y d.b := d.ok.frame
  have hψ : ∀ z : F, d.B.ψ (algebraMap F (AF F) z) = 1 := d.ok.good.std.2.1
  obtain ⟨ε, hε⟩ := hb.1
  obtain ⟨ε', hε'⟩ := L.ok.frame.1
  have hee := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  obtain ⟨T0, hT0⟩ := (mem_nF_iff T.1).1 T.2
  have hC : incM F T0 ∈ nCond σ d.n ε := hT0 ▸ (mem_nA_iff hσ hε T.1.1).1 T.1.2
  have hdet : T0.det = 0 := by
    have h1 : T.1.1.det = 0 := not_not.1 hT
    rw [hT0, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
    exact kfour.inclR_injective (F := F) (h1.trans (map_zero _).symm)
  obtain ⟨v, hv0, hTv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  obtain ⟨a', ha'⟩ := exists_gl_col v hv0 L.i₀
  obtain ⟨γ, hγ, hγf⟩ := levi_ex hσ hb a'⁻¹
  set M0 : Matrix (Fin d.n) (Fin d.n) E := (a'.1.map σ)ᵀ * T0 * a'.1 with hM0
  have hMc : incM F M0 = ((incM F a'.1).map (cA σ))ᵀ * incM F T0 * incM F a'.1 := by
    rw [incM_mapc, incM_tr, hM0, incM_mul', incM_mul']
  have hM0C : incM F M0 ∈ nCond σ d.n ε := hMc ▸ cong_nCond hσ _ _ hC
  have hM0A : incM F M0 ∈ nA σ d.Y d.b := (mem_nA_iff hσ hε _).2 hM0C
  let T₀ : nF σ d.Y d.b := ⟨⟨incM F M0, hM0A⟩, (mem_nF_iff _).2 ⟨M0, rfl⟩⟩
  have hsubC : (incM F M0).submatrix L.em L.em ∈ nCond σ L.n ε' := hee ▸ sub_nCond L.em _ hM0C
  let T' : nF σ L.Y L.b := ⟨⟨(incM F M0).submatrix L.em L.em, (mem_nA_iff hσ hε' _).2 hsubC⟩,
    (mem_nF_iff _).2 ⟨M0.submatrix L.em L.em, rfl⟩⟩
  have hcol : ∀ k, M0 k L.i₀ = 0 := fun k => by
    have e1 : M0 k L.i₀ = (((a'.1.map σ)ᵀ * T0) *ᵥ v) k := by
      simp only [hM0, Matrix.mul_apply, Matrix.mulVec, dotProduct, ha']
    rw [e1, ← Matrix.mulVec_mulVec, hTv, Matrix.mulVec_zero, Pi.zero_apply]
  have hrow : ∀ k, M0 L.i₀ k = 0 := fun k => by
    have e0 : ∀ l, ∑ p, σ (v p) * T0 p l = 0 := fun l => by
      have h1 := congrArg σ (congrFun hTv l)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at h1
      calc ∑ p, σ (v p) * T0 p l = ∑ p, σ (v p) * -(((ε : ℤ) : E) * σ (T0 l p)) :=
            Finset.sum_congr rfl fun p _ => by rw [nCond_rat T0 hC l p]
        _ = -(((ε : ℤ) : E) * ∑ p, σ (T0 l p) * σ (v p)) := by
            rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun p _ => by ring
        _ = 0 := by rw [h1, mul_zero, neg_zero]
    simp only [hM0, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, ha']
    simp only [e0, zero_mul, Finset.sum_const_zero]
  refine ⟨γ, hγ, T₀, T', ⟨fun i => ⟨?_, ?_⟩, rfl⟩, fun φ _ hφ x => ?_⟩
  · show inclR (F := F) (AF F) (M0 L.i₀ i) = 0
    rw [hrow, map_zero]
  · show inclR (F := F) (AF F) (M0 i L.i₀) = 0
    rw [hcol, map_zero]
  refine (fc_levi hσ hb hψ hc γ hγ hγf T₀ T ?_ φ hφ x).symm
  show ((incM F (a'⁻¹).1).map (cA σ))ᵀ * incM F M0 * incM F (a'⁻¹).1 = T.1.1
  rw [hT0, incM_mapc, incM_tr, ← incM_mul', ← incM_mul', hM0]
  congr 1
  have ha : a'.1 * (a'⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc ((a'⁻¹).1.map σ)ᵀ * ((a'.1.map σ)ᵀ * T0 * a'.1) * (a'⁻¹).1
      = ((a'.1 * (a'⁻¹).1).map σ)ᵀ * T0 * (a'.1 * (a'⁻¹).1) := by
        rw [mapσ_mul', Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = T0 := by rw [ha, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
theorem fcConj_of_k : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.FcConj_k := fun _ _F _E _ _ _ _ _ _σ _d L _nb _lam _𝓖 hc =>
  ⟨fun T hT => _root_.PositivityTheory.SiegelWeilFormula.Afc.fc_deg_k L hc T hT, fun _uM _ν _𝓤 hU T T' hs φ _ hφ u hu x => _root_.PositivityTheory.SiegelWeilFormula.Afc.fc_U_k L hc hU T T' hs φ hφ u hu x⟩
end PositivityTheory.SiegelWeilFormula.Afc
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldJ
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem jEx_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.JEx_k := by
  intro F E _ _ _ _ _ σ d n h Y b ε e1 e2
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (G2 σ Y) := Subgroup.instIsTopologicalGroupSubtypeMem _
  let j : G2 σ Y →* d.G := (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b).codRestrict _ (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_mem_k d h b ε e1 e2)
  have hfr : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => by
    rw [inFrame_eq]
    show incM F (d.b⁻¹).1 * (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1 * incM F d.b.1 = _
    rw [_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_val_k]
    simp only [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul, Matrix.mul_one]
  refine ⟨j, ?_, fun g => by rw [hfr]; exact blk_sub h _ _, fun g => by rw [hfr]; exact blk_out h _⟩
  have h1 : Continuous fun g : G2 σ Y => g.1.1 := Units.continuous_val.comp continuous_subtype_val
  have hv : Continuous fun g : G2 σ Y => (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g).1 := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_val_k, inFrame_eq]
    exact (continuous_const.matrix_mul ((((continuous_const.matrix_mul h1).matrix_mul continuous_const).matrix_fromBlocks
      continuous_const continuous_const continuous_const).matrix_submatrix _ _)).matrix_mul continuous_const
  have hc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h (Y := Y) b) := by
    refine Units.continuous_iff.2 ⟨hv, ?_⟩
    have e : (fun g : G2 σ Y => ((_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g)⁻¹ : GL _ _).1) = fun g : G2 σ Y => (_root_.PositivityTheory.SiegelWeilFormula.Ald.jHom_k d h b g⁻¹).1 :=
      funext fun g => by rw [map_inv]
    rw [e]
    exact hv.comp continuous_inv
  exact hc.subtype_mk _
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem kStd_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.KStd_k := by
  intro F E _ _ _ _ _ σ d n h Y b j hb hj
  have hX : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => eq_blk h _ _ (hj.2.1 g) (hj.2.2 g)
  intro k
  rw [Subgroup.mem_comap, d.ok.stdK (j k)]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, ← map_inv, hX]
  refine and_congr (forall_congr' fun w => ?_) (and_congr (int_blk h _) (int_blk h _))
  rw [blk_map _ _ _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _), blk_conjTranspose,
    Matrix.conjTranspose_one, blk_mul, Matrix.one_mul, blk_eq_one_iff]
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldYF
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
open PositivityTheory.SiegelWeilFormula.Ald.YFA
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem yFrame_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.YFrame_k := by
  intro F E _ _ _ _ _ σ d n hN hn
  have hc : ∀ z : E, σ (σ z) = z := sig_sig' d.ok.good.cm
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hεσ : σ (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast σ _
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · obtain ⟨ξ, hξ, hσξ⟩ := _root_.GlobalTheory.T.exists_trace_zero_element F E σ d.B d.ok.good
    have hξ' : -ξ ≠ 0 := neg_ne_zero.2 hξ
    let J : Matrix (Fin n) (Fin n) E := ξ • 1
    have hJ : ∀ i j, σ (J j i) = (-1) * J i j := fun i j => by
      by_cases h : i = j
      · subst h; simp [J, hσξ]
      · simp [J, Matrix.one_apply, h, Ne.symm h]
    let T : GL (Fin n) E := ⟨(-ξ)⁻¹ • 1, (-ξ) • 1,
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hξ', one_smul],
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ', one_smul]⟩
    have hm : T.1.map σ = ξ⁻¹ • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [T, map_inv₀, hσξ]
      · simp [T, Matrix.one_apply, h]
    have hT : J * T.1.map σ = 1 := by
      rw [hm, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ, one_smul]
    obtain ⟨b, hb, hd⟩ := frame_of hc (by norm_num) hJ T hT
    have hεv : ((ε : ℤ) : E) = -1 :=
      eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ
    refine ⟨spcOf F J, b, ε, Or.inl ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = -J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>
      · change b.1ᵀ * dbl J * b.1.map σ = _
        try simp only [jeps]
        rw [hεv]; exact hb
  · let J : Matrix (Fin n) (Fin n) E := 1
    have hJ : ∀ i j, σ (J j i) = 1 * J i j := fun i j => by
      by_cases h : i = j
      · subst h; simp [J]
      · simp [J, Matrix.one_apply, h, Ne.symm h]
    have hT : J * (1 : GL (Fin n) E).1.map σ = 1 := by
      simp [J, Matrix.map_one _ (map_zero σ) (map_one σ)]
    obtain ⟨b, hb, hd⟩ := frame_of hc (by norm_num) hJ 1 hT
    have hεv : ((ε : ℤ) : E) = 1 :=
      eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ
    refine ⟨spcOf F J, b, ε, Or.inr ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>
      · change b.1ᵀ * dbl J * b.1.map σ = _
        try simp only [jeps]
        rw [hεv]; exact hb
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRD
section
set_option synthInstance.maxHeartbeats 200000

section
namespace PositivityTheory.SiegelWeilFormula.Krd
theorem rdEx_k : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k := _root_.PositivityTheory.SiegelWeilFormula.Krd.rdEx_of_k _root_.PositivityTheory.SiegelWeilFormula.Krd.epsEx_k _root_.PositivityTheory.SiegelWeilFormula.Krd.frEx_k _root_.PositivityTheory.SiegelWeilFormula.Krd.iotaEx_k
end PositivityTheory.SiegelWeilFormula.Krd
end
end

