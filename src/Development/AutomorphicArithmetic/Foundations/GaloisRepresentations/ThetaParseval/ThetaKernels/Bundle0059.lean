module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.BddOfPer
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0045
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.GIinvA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0044
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0033
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0046

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingFour
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KSing
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem bdd_of_per_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {U : nA σ d.Y d.b × d.G → ℂ} (hU : Continuous U)
    (hper : ∀ β, ∀ l ∈ nF σ d.Y d.b, ∀ y, U (β + l, y) = U (β, y)) {C : Set d.G} (hC : IsCompact C) :
    ∃ M, ∀ β, ∀ y ∈ C, ‖U (β, y)‖ ≤ M := by
  obtain ⟨K, hK, hKβ⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSing.nCocompact_k d
  obtain ⟨M, hM⟩ := (hK.prod hC).exists_bound_of_continuousOn hU.continuousOn
  refine ⟨M, fun β y hy => ?_⟩
  obtain ⟨l, hl, hβl⟩ := hKβ β
  have e := hper (β - l) l hl y
  rw [sub_add_cancel] at e
  rw [e]
  exact hM _ ⟨hβl, hy⟩
set_option maxHeartbeats 800000 in
theorem fc_avg_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (hG : IsTopologicalGroup d.G)
    {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hCD : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (f : d.G → ℂ) (hf : Continuous f)
    (hinv : ∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g)
    (ψ₀ : (Fin d.n → Fin d.n → ℝ) → ℂ) (hψc : Continuous ψ₀) (hψs : HasCompactSupport ψ₀)
    (nr : (Fin d.n → Fin d.n → ℝ) → GR d.n) (hnr : ∀ x, mR (nr x) = nU (herm x))
    (β : (Fin d.n → Fin d.n → ℝ) → nA σ d.Y d.b) (hβc : Continuous β) (hβ : ∀ x, R.ι w (nr x) = nb (β x))
    (T : nF σ d.Y d.b) (z : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (fun y => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) T z =
      fc d.B.ψ d.b nb lam 𝓖 f T z * ∫ x, ψ₀ x * d.B.ψ (d.tt (T.1.1 * (β x).1)) := by
  have := hG
  set χ : nA σ d.Y d.b → ℂ := fun β₀ => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β₀.1))))
    with hχ
  set U : nA σ d.Y d.b × d.G → ℂ := fun p => f (nb p.1 * p.2) * χ p.1 with hUdef
  have hnbc := _root_.PositivityTheory.SiegelWeilFormula.KSing.continuous_nb_k d hCD.1
  have hnrc := cont_nr nr hnr
  have hιr : Continuous fun x => R.ι w (nr x) * z := ((R.cont w).comp hnrc).mul continuous_const
  have hUc : Continuous U :=
    (hf.comp ((hnbc.comp continuous_fst).mul continuous_snd)).mul ((_root_.PositivityTheory.SiegelWeilFormula.KSing.chi_cont_k d T).comp continuous_fst)
  have hUper : ∀ β₀, ∀ l ∈ nF σ d.Y d.b, ∀ y, U (β₀ + l, y) = U (β₀, y) := by
    intro β₀ l hl y
    simp only [hUdef, hχ]
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.chi_add_k d T β₀ l, _root_.PositivityTheory.SiegelWeilFormula.KSing.chi_per_k d T hl, mul_one, add_comm, _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hCD.1, mul_assoc, hinv _ (_root_.PositivityTheory.SiegelWeilFormula.KSing.nb_rat_k d hCD.1 hl)]
  obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSing.bdd_of_per_k d hUc hUper ((hψs.isCompact).image hιr)
  haveI : IsFiniteMeasure (lam.restrict 𝓖) :=
    ⟨by rw [Measure.restrict_apply_univ, hCD.2.2.2]; exact ENNReal.one_lt_top⟩
  have e1 : ∀ β₀ x, f (R.ι w (nr x) * (nb β₀ * z)) * ψ₀ x * χ β₀ = U (β₀, R.ι w (nr x) * z) * ψ₀ x := by
    intro β₀ x
    simp only [hUdef]
    rw [hβ x, ← mul_assoc, ← _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hCD.1, add_comm, _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hCD.1,
      show nb β₀ * nb (β x) * z = nb β₀ * (nb (β x) * z) from mul_assoc _ _ _]
    ring
  have eL : fc d.B.ψ d.b nb lam 𝓖 (fun y => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) T z =
      ∫ β₀, ∫ x, U (β₀, R.ι w (nr x) * z) * ψ₀ x ∂volume ∂(lam.restrict 𝓖) := by
    unfold fc
    congr 1
    funext β₀
    rw [← integral_mul_const]
    congr 1
    funext x
    exact e1 β₀ x
  have hcont : Continuous (Function.uncurry fun (β₀ : nA σ d.Y d.b) (x : Fin d.n → Fin d.n → ℝ) =>
      U (β₀, R.ι w (nr x) * z) * ψ₀ x) :=
    (hUc.comp (continuous_fst.prodMk (hιr.comp continuous_snd))).mul (hψc.comp continuous_snd)
  have hint : Integrable (Function.uncurry fun (β₀ : nA σ d.Y d.b) (x : Fin d.n → Fin d.n → ℝ) =>
      U (β₀, R.ι w (nr x) * z) * ψ₀ x) ((lam.restrict 𝓖).prod volume) := by
    refine Integrable.mono' ((integrable_const M).mul_prod (hψc.norm.integrable_of_hasCompactSupport hψs.norm))
      (_root_.PositivityTheory.SiegelWeilFormula.KSing.aesm_of_continuous_k d hCD hcont) (Eventually.of_forall fun p => ?_)
    show ‖U (p.1, R.ι w (nr p.2) * z) * ψ₀ p.2‖ ≤ M * ‖ψ₀ p.2‖
    rw [norm_mul]
    by_cases hx : p.2 ∈ tsupport ψ₀
    · exact mul_le_mul_of_nonneg_right (hM p.1 _ ⟨p.2, hx, rfl⟩) (norm_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [eL, integral_integral_swap hint]
  have e2 : ∀ x, ∫ β₀, U (β₀, R.ι w (nr x) * z) * ψ₀ x ∂(lam.restrict 𝓖) =
      fc d.B.ψ d.b nb lam 𝓖 f T z * (ψ₀ x * d.B.ψ (d.tt (T.1.1 * (β x).1))) := by
    intro x
    rw [integral_mul_const]
    have : ∫ β₀, U (β₀, R.ι w (nr x) * z) ∂(lam.restrict 𝓖) = fc d.B.ψ d.b nb lam 𝓖 f T (nb (β x) * z) := by
      rw [hβ x]
      rfl
    rw [this, _root_.PositivityTheory.SiegelWeilFormula.KSing.fc_shift_k d hCD f hinv T (β x) z]
    ring
  simp_rw [e2]
  rw [integral_const_mul]
end PositivityTheory.SiegelWeilFormula.KSing
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitGIinvA
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.KSplit
namespace PositivityTheory.SiegelWeilFormula.KSplitA
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem A_sym_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ ε : ℤˣ, ∀ i j, σ (d.A.J j i) = ((ε : ℤ) : E) * d.A.J i j := by
  rcases d.ok.sign with ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨1, fun i j => by rw [h.herm]; simp⟩
  · exact ⟨-1, fun i j => by rw [h.skew]; simp⟩
theorem A_det_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.A.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have key : (d.A.J.map (d.B.emb w).1).det ≠ 0 := by
    rcases d.ok.sign with ⟨h, -⟩ | ⟨h, -⟩
    · exact det_ne_of_hasSig (h.sig w)
    · have := det_ne_of_hasSig (h.sig w)
      rw [Matrix.det_smul] at this
      exact right_ne_zero_of_mul this
  intro h0
  apply key
  rw [show d.A.J.map (d.B.emb w).1 = ((d.B.emb w).1 : E →+* ℂ).mapMatrix d.A.J from rfl, ← RingHom.map_det, h0, map_zero]
theorem mu_right_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.μ.IsMulRightInvariant := by
  obtain ⟨ε, hε⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplitA.A_sym_k d
  exact (PositivityTheory.ThKF.unimodularity_holds F E σ d.cm d.m d.A.J ε hε (_root_.PositivityTheory.SiegelWeilFormula.KSplitA.A_det_k d)).2.2 d.μ d.ok.haar
theorem cw_mul'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) {p q r : Type} [Fintype q] (A : Matrix p q (AE F E))
    (B : Matrix q r (AE F E)) : d.cw w (A * B) = d.cw w A * d.cw w B :=
  Matrix.map_mul (f := piInf (d.B.emb w))
theorem cw_sub_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) {p q : Type} (A B : Matrix p q (AE F E)) :
    d.cw w (A - B) = d.cw w A - d.cw w B := by
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
theorem exists_embU_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (u : Matrix (Fin d.m) (Fin d.m) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin d.m) ℂ) : ∃ g : UA σ d.A.J, ∀ X : Mx F E d.m d.n,
      R.loc w (mat g⁻¹ * X) = (u * Matrix.of (R.loc w X) : Matrix (Fin d.m) (Fin d.n) ℂ) ∧
        (∀ w', w' ≠ w → d.cw w' (mat g⁻¹ * X - X) = 0) ∧ finOne F • (mat g⁻¹ * X - X) = 0 := by
  set fr : Matrix (Fin d.m) (Fin d.m) ℂ := (R.fr w).1 with hfr_def
  set fri : Matrix (Fin d.m) (Fin d.m) ℂ := ((R.fr w)⁻¹).1 with hfri_def
  have hb : fr * fri = 1 := by rw [hfr_def, hfri_def, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hb' : fri * fr = 1 := by rw [hfr_def, hfri_def, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have huu : u * uᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff).1 hu
  have huu' : uᴴ * u = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff').1 hu
  set h : Matrix (Fin d.m) (Fin d.m) ℂ := u.map star with hh_def
  have hhs : h.map star = u := by ext i j; simp [hh_def]
  have hht : hᵀ = uᴴ := by ext i j; simp [hh_def, Matrix.conjTranspose_apply]
  have h1 : h * uᵀ = 1 := by
    have : (u * uᴴ)ᵀ = h * uᵀ := by
      rw [Matrix.transpose_mul]; congr 1
    rw [← this, huu, Matrix.transpose_one]
  have h2 : uᵀ * h = 1 := by
    have : (uᴴ * u)ᵀ = uᵀ * h := by
      rw [Matrix.transpose_mul]; congr 1
    rw [← this, huu', Matrix.transpose_one]
  set Z := fr * h * fri with hZ_def
  set Z' := fr * uᵀ * fri with hZ'_def
  have hZZ : Z * Z' = 1 := by
    rw [hZ_def, hZ'_def, show fr * h * fri * (fr * uᵀ * fri) = fr * h * (fri * fr) * uᵀ * fri by
      simp only [Matrix.mul_assoc], hb', Matrix.mul_one, Matrix.mul_assoc fr h uᵀ, h1, Matrix.mul_one, hb]
  have hZZ' : Z' * Z = 1 := by
    rw [hZ_def, hZ'_def, show fr * uᵀ * fri * (fr * h * fri) = fr * uᵀ * (fri * fr) * h * fri by
      simp only [Matrix.mul_assoc], hb', Matrix.mul_one, Matrix.mul_assoc fr uᵀ h, h2, Matrix.mul_one, hb]
  have hζ0 : R.ζ ≠ 0 := by
    rcases R.hζ with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
    · exact one_ne_zero
    · exact Complex.I_ne_zero
  set D : Matrix (Fin d.m) (Fin d.m) ℂ := d.A.J.map (d.B.emb w).1 with hD_def
  set Q : Matrix (Fin d.m) (Fin d.m) ℂ := frᵀ * D * fr.map star with hQ_def
  have hQ : R.ζ • Q = ((R.sg w : ℤ) : ℂ) • 1 := R.hfr w
  have hhQ : hᵀ * Q * h.map star = Q := by
    apply smul_right_injective _ hζ0
    show R.ζ • (hᵀ * Q * h.map star) = R.ζ • Q
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hQ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hhs, hht, huu']
  have hmem : (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z)ᵀ * incM F d.A.J * (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z).map (cA σ) = incM F d.A.J := by
    refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
      unfold Krd.fam
      split_ifs with hw
      · subst hw
        exact Krd.conj_unit fr fri h D Q hb rfl hhQ
      · rw [Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]
    · have e1 : (finOne F • (1 : Matrix (Fin d.m) (Fin d.m) (AE F E))).map (cA σ) = finOne F • 1 := by
        rw [Krd.map_cA_smul, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [Krd.fin_mul, Krd.fin_mul, ← Matrix.transpose_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, ← Krd.map_cA_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, e1,
        Matrix.transpose_smul, Matrix.transpose_one, ← Krd.fin_mul, ← Krd.fin_mul, Matrix.mul_one, Matrix.one_mul]
  let k : UA σ d.A.J := ⟨⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z', by rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_mul_k, hZZ, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_one_k],
    by rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_mul_k, hZZ', _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_one_k]⟩, hmem⟩
  refine ⟨k⁻¹, fun X => ⟨?_, fun w' hw' => ?_, ?_⟩⟩
  · rw [inv_inv]
    show (fri * d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * X)).map star = u * (fri * d.cw w X).map star
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSplitA.cw_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    simp only [Krd.fam, if_true]
    rw [hZ_def, show fri * (fr * h * fri * d.cw w X) = (fri * fr) * h * (fri * d.cw w X) by
      simp only [Matrix.mul_assoc], hb', Matrix.one_mul, mapStar_mul', hhs]
  · rw [inv_inv]
    show d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * X - X) = 0
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSplitA.cw_sub_k, _root_.PositivityTheory.SiegelWeilFormula.KSplitA.cw_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    simp only [Krd.fam, if_neg hw', Matrix.one_mul, sub_self]
  · rw [inv_inv]
    show finOne F • (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * X - X) = 0
    rw [smul_sub, ← Matrix.smul_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, Matrix.smul_mul, Matrix.one_mul, sub_self]
end PositivityTheory.SiegelWeilFormula.KSplitA
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfCore
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kunf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E}
theorem unfoldCore_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hb : IsFrame2 σ Y b) {nb : nA σ Y b → G2 σ Y}
    {lam : Measure (nA σ Y b)} {𝓖 : Set (nA σ Y b)} (hc : CoefData (σ := σ) (Y := Y) b nb lam 𝓖)
    (φ : G2 σ Y → ℂ) (hφ : Continuous φ) (hrat : ∀ p ∈ par2 σ Y, p ∈ rat2 σ Y → ∀ y, φ (p * y) = φ y)
    (hone : ∀ p t, IsPar p t → Matrix.GeneralLinearGroup.det t = 1 → ∀ y, φ (p * y) = φ y)
    (hmaj : ∀ C : Set (G2 σ Y), IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ Y) (rat2 σ Y) φ g q‖ ≤ u q)
    {ε : ℤˣ} {w : G2 σ Y} (hw : inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0) (x : G2 σ Y) :
    Integrable (fun β => φ (w * nb β * x)) lam ∧ ∀ T : nF σ Y b, IsND T →
      fc B.ψ b nb lam 𝓖 (GlobalTheory.Eis.cosetSum (par2 σ Y) (rat2 σ Y) φ) T x =
        ∫ β, φ (w * nb β * x) * B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β.1).trace)) ∂lam := by
  classical
  obtain ⟨hnb, hHaar, h𝓖, -⟩ := hc
  have := hHaar
  have : Countable (rat2 σ Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ Y
  have : Countable (GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y)) := Quotient.countable
  obtain ⟨ε₀, hε₀⟩ := hb.1
  have hw_rat : w ∈ rat2 σ Y := by
    refine rat_of_inFrame (b := b) (M := Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ?_
    rw [hw]
    ext (i | i) (j | j) <;> simp [incM, Matrix.one_apply] <;> split_ifs <;> simp
  have hLI : GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ Y ⊓ rat2 σ Y) φ := fun γ hγ g => hrat γ hγ.1 hγ.2 g
  let nbR : nF σ Y b → rat2 σ Y := fun ν => ⟨nb ν.1, nb_rat hnb ν.2⟩
  have nbR_zero : nbR 0 = 1 := Subtype.ext (nb_zero hnb)
  have nbR_add : ∀ ν ν', nbR (ν + ν') = nbR ν * nbR ν' := fun ν ν' => Subtype.ext (nb_add hnb ν.1 ν'.1)
  let act : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) → nF σ Y b → GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) :=
    fun q ν => GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q
  have hact0 : ∀ q, act q 0 = q := fun q => by
    show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR 0) q = q
    rw [nbR_zero, GlobalTheory.AutomorphicL2Unitary.rmul_one]
  have hact : ∀ q ν ν', act (act q ν) ν' = act q (ν + ν') := fun q ν ν' => by
    show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν') (GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q) = GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR (ν + ν')) q
    rw [nbR_add, GlobalTheory.AutomorphicL2Unitary.rmul_mul]
  let A : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) → nA σ Y b → ℂ := fun q β =>
    GlobalTheory.Eis.term (par2 σ Y) (rat2 σ Y) φ (nb β * x) q
  have hA : ∀ q, Continuous (A q) := fun q =>
    hφ.comp (continuous_const.mul ((continuous_nb hnb).mul continuous_const))
  have hAmk : ∀ (γ : rat2 σ Y) β, A (GlobalTheory.AutomorphicL2Unitary.mk _ γ) β = φ (γ.1 * (nb β * x)) := fun γ β =>
    GlobalTheory.Eis.term_mk hLI (nb β * x) γ
  have hAact : ∀ q ν β, A (act q ν) β = A q (β + (ν : nA σ Y b)) := fun q ν β => by
    have e : act q ν = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * nbR ν) := by
      show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q = _
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [e, hAmk]
    show φ ((q.out : rat2 σ Y).1 * nb ν.1 * (nb β * x)) = φ ((q.out : rat2 σ Y).1 * (nb (β + ν.1) * x))
    rw [nb_add hnb, nb_comm hnb β]
    simp only [mul_assoc]
  obtain ⟨C, hC, hcov⟩ := _root_.PositivityTheory.SiegelWeilFormula.kunf.exists_cover_k B hB hb
  obtain ⟨u, hu, hAu'⟩ := hmaj ((fun β => nb β * x) '' C) (hC.image ((continuous_nb hnb).mul continuous_const))
  have hAu : ∀ q, ∀ β ∈ C, ‖A q β‖ ≤ u q := fun q β hβ => hAu' _ ⟨β, hβ, rfl⟩ q
  let q₀ : GlobalTheory.Eis.Cosets (par2 σ Y) (rat2 σ Y) := GlobalTheory.AutomorphicL2Unitary.mk _ ⟨w, hw_rat⟩
  have hq₀ : ∀ ν, act q₀ ν = GlobalTheory.AutomorphicL2Unitary.mk _ (⟨w, hw_rat⟩ * nbR ν) := fun ν => rfl
  have hinj : Function.Injective (act q₀) := fun ν ν' h => by
    rw [hq₀, hq₀] at h
    obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h
    have hP : (w * nb ν'.1) * (w * nb ν.1)⁻¹ ∈ par2 σ Y := by
      have e : (w * nb ν'.1) = (γ : rat2 σ Y).1 * (w * nb ν.1) := (congrArg Subtype.val hγ).symm
      rw [e, mul_inv_cancel_right]
      exact Subgroup.mem_subgroupOf.1 γ.2
    exact (Subtype.ext (big_inj hb hw hnb hP)).symm
  have hAq₀ : ∀ β, A q₀ β = φ (w * nb β * x) := fun β => by
    rw [hAmk, mul_assoc]
  have hI := abs_integrable lam (nF σ Y b) 𝓖 h𝓖 act hact0 hact A hA hAact C hC hcov u hu hAu q₀ hinj
  refine ⟨hI.congr (Filter.Eventually.of_forall hAq₀), fun T hT => ?_⟩
  let χ₀ : nA σ Y b → ℂ := fun β => B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β.1).trace))
  have htr : Continuous fun M : Matrix (Fin n) (Fin n) (AE F E) => Algebra.trace (AF F) (AE F E) M.trace :=
    (IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))).comp continuous_id.matrix_trace
  have hχc : Continuous χ₀ :=
    hB.std.1.comp ((htr.comp (continuous_const.matrix_mul continuous_subtype_val)).neg)
  have hχadd : ∀ β β', χ₀ (β + β') = χ₀ β * χ₀ β' := fun β β' => by
    simp only [χ₀, AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add]
    exact AddChar.map_add_eq_mul _ _ _
  have hχΛ : ∀ ν : nF σ Y b, χ₀ (ν : nA σ Y b) = 1 := fun ν => by
    simp only [χ₀, AddChar.map_neg_eq_inv, psi_rat hB.std T ν, inv_one]
  have hsmall : ∀ q, (∀ ν, act q₀ ν ≠ q) →
      ∃ β₀, χ₀ β₀ ≠ 1 ∧ ∀ ν β, A (act q ν) (β + β₀) = A (act q ν) β := fun q hq => by
    rcases _root_.PositivityTheory.SiegelWeilFormula.kunf.cells_k B hB hb hw hnb T hT (q.out : rat2 σ Y).1 (q.out : rat2 σ Y).2 with
      ⟨p, hpP, hpΓ, ν, hνF, hγ⟩ | ⟨β₀, hψ, t, hpar, hdet⟩
    · exfalso
      refine hq ⟨ν, hνF⟩ ?_
      rw [hq₀, ← Quotient.out_eq q]
      refine GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨⟨p, hpΓ⟩, Subgroup.mem_subgroupOf.2 hpP⟩, Subtype.ext ?_⟩
      exact hγ.symm
    · refine ⟨β₀, hψ, fun ν β => ?_⟩
      rw [hAact, hAact]
      show φ ((q.out : rat2 σ Y).1 * (nb (β + β₀ + ν.1) * x)) = φ ((q.out : rat2 σ Y).1 * (nb (β + ν.1) * x))
      set γ := (q.out : rat2 σ Y).1
      have e : γ * (nb (β + β₀ + ν.1) * x) = (γ * nb β₀ * γ⁻¹) * (γ * (nb (β + ν.1) * x)) := by
        rw [show β + β₀ + ν.1 = β₀ + (β + ν.1) by abel, nb_add hnb]
        group
      rw [e, hone _ t hpar hdet]
  obtain ⟨-, -, heq⟩ := abs_unfold lam (nF σ Y b) 𝓖 h𝓖 act hact0 hact A hA hAact χ₀ hχc hχadd hχΛ C hC hcov u hu hAu
    q₀ hinj hsmall
  show ∫ β in 𝓖, GlobalTheory.Eis.cosetSum (par2 σ Y) (rat2 σ Y) φ (nb β * x) * χ₀ β ∂lam = ∫ β, φ (w * nb β * x) * χ₀ β ∂lam
  have e2 : ∫ β, φ (w * nb β * x) * χ₀ β ∂lam = ∫ β, A q₀ β * χ₀ β ∂lam :=
    integral_congr_ae (Filter.Eventually.of_forall fun β => by simp only [hAq₀])
  rw [e2]
  exact heq
end PositivityTheory.SiegelWeilFormula.kunf
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDictAsm
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem asm_gramR_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) (Y : Fin d.n → Fin d.m → AF F ⊗[F] E) :
    HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) Y =
      (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) η) • (d.gram (toMx Y) (toMx Y))ᵀ := by
  ext c a
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.gramR, HeckeCharacterZeroLocus.SiegelWeilU.hR, HeckeCharacterZeroLocus.SiegelWeilU.hform, HeckeCharacterZeroLocus.SiegelWeilU.JR, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k,
    Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.mul_apply, toMx,
    Matrix.of_apply, incM, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [asm_incl, asm_cA]
  ring
theorem asm_phase_cell_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hr : _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g) (β : nA σ d.Y d.b)
    (Y : Fin d.n → Fin d.m → AF F ⊗[F] E) :
    -(⅟(2 : AF F) * d.tt (β.1 * d.gram (toMx Y) (toMx Y))) =
      PositivityTheory.PfSWUS.Loc.trPair (AF F) ((hOf β).1) (HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) Y) := by
  rw [PositivityTheory.PfSWUS.Loc.trPair, _root_.PositivityTheory.SiegelWeilFormula.KWhit.asm_gramR_k, hr.hof β, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, asm_half, Matrix.neg_mul, asm_scalar_mul,
    Matrix.smul_mul, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, map_neg, mul_neg, neg_neg]
  congr 1
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring
theorem asm_phase_whit_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hr : _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g) (β : nA σ d.Y d.b) :
    -d.tt (T.1.1 * β.1) =
      -PositivityTheory.PfSWUS.Loc.trPair (AF F) ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) ((hOf β).1) := by
  rw [neg_inj, PositivityTheory.PfSWUS.Loc.trPair, hr.hof β, hr.rat, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, asm_scalar_mul, Matrix.mul_neg, Matrix.mul_smul,
    Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, map_neg]
  have h2 : ∑ a, ∑ c, ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F))) a c * ((hOf β).1 : Mx F E d.n d.n) c a =
      algebraMap (AF F) (AE F E) (-2) * (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) η *
        (incM F T₀ * ((hOf β).1 : Mx F E d.n d.n)ᵀ).trace) := by
    simp only [Td, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_neg,
      map_ofNat, Matrix.trace, Matrix.diag, Matrix.mul_apply, incM, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [asm_incl]
    ring
  rw [h2, ← Algebra.smul_def (-2 : AF F) _, LinearMap.map_smul, smul_eq_mul, ← mul_assoc]
  have h5 : algebraMap F (AF F) (1 / 2) * (-2 : AF F) = -1 := by
    rw [show (-2 : AF F) = algebraMap F (AF F) (-2) by rw [map_neg, map_ofNat], ← map_mul]
    norm_num
  rw [h5]
  ring
theorem asm_c_ne_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (t : GL (Fin d.n) (AE F E)) :
    (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
  have hpos : 0 < (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := by
    have h : absE F E (Matrix.GeneralLinearGroup.det t) * absE F E (Matrix.GeneralLinearGroup.det t)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have h0 : absE F E (Matrix.GeneralLinearGroup.det t) ≠ 0 := left_ne_zero_of_mul_eq_one h
    exact_mod_cast pos_iff_ne_zero.2 h0
  exact mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hpos _).ne')
theorem dictAsmX_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.DictAsmX_k := by
  intro hCell hRel hH hM hTh hT hA F E _ _ _ _ _ σ d R Φ hΦ P gf hpg x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨t, u, hxtu⟩ := hx
  obtain ⟨η, T₀, hOf, θ, fr, g, l, εs, Φg, Φf, Φv, μ, ν, hr, hΦg, hani, hεs, hcm, hherm, hTT, hdet, hchr, hpl, hfr,
    hpure, hprod, hsdW, hsdH⟩ := hRel hT hA F E σ d R Φ hΦ P gf hpg x t u hxtu T hTnd
  obtain ⟨lv, L₁, L₂, C, hC, hlv, hco, hstd, hht⟩ := hH F E σ d R x t u T η T₀ hOf θ fr g hr nb lam 𝓖 hcd ε w hw
  obtain ⟨hMβ, hMZ⟩ := hM F E σ d R x t u T η T₀ hOf θ fr g hr
  obtain ⟨hembβ, hpresβ⟩ := hMβ nb lam 𝓖 hcd ν hsdH
  obtain ⟨νc, hνc⟩ := (hA F E σ d).1
  obtain ⟨hembZ, hpresZ⟩ := hMZ μ νc hsdW hνc
  obtain ⟨μH, 𝓕, hμH, h𝓕, horb⟩ := hTh F E σ d η hr.ne hr.herm
  set c : ℂ := (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.asm_c_ne_k d t
  have hTx : ∀ Y, d.T (d.om x Φ) (toMx Y) = c * Φg Y := by
    intro Y
    rw [hΦg Y]
    exact (hT.2.1 F E σ d Φ hΦ.1).2.1 x t u hxtu (toMx Y)
  have hint : ∀ z : ℂ, ∀ β : nA σ d.Y d.b,
      flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) =
        c * (C : ℂ) ^ (z - s0 d.m d.n) * Gen.whI (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) d.B.ψ μ Φg (Gen.nuA θ g lv L₁ L₂)
          ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z (hOf β) := by
    intro z β
    obtain ⟨hνpos, ha⟩ := hht β
    have hcell := hCell hT F E σ d νc hνc ε w hw Φ hΦ.1 (nb β) x β.1 (hcd.1 β)
    have hZ : ∫ Z, d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * d.gram Z Z))) * d.T (d.om x Φ) Z ∂νc =
        c * PositivityTheory.PfSWUS.Loc.jtR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) d.B.ψ μ Φg (hOf β) := by
      rw [← hpresZ.integral_comp hembZ]
      simp only [PositivityTheory.PfSWUS.Loc.jtR, hTx, _root_.PositivityTheory.SiegelWeilFormula.KWhit.asm_phase_cell_k hr β]
      rw [← integral_const_mul]
      congr 1
      funext Y
      ring
    have hs : s0 d.m d.n = ((d.m : ℂ) - d.n) / 2 := rfl
    simp only [flat]
    rw [hcell, hZ, ha, _root_.PositivityTheory.SiegelWeilFormula.KWhit.asm_phase_whit_k hr β, asm_cpow_split hC hνpos]
    simp only [Gen.whI, hs]
    ring
  refine ⟨2, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η, Td η T₀, d.bs, d.B.ψ, θ, l, εs, fr, g, lv, L₁, L₂, Φg, Φf, Φv, μ, ν, c, C,
    ⟨hcm, hherm, hTT, hdet, hchr, hpl, hfr, hlv, hco, hstd, hpure, hprod, hsdW, hsdH⟩, hani, hεs, hC,
    ⟨0, fun z _ => ⟨fun hI => ?_, ?_⟩⟩, μH, 𝓕, hμH, h𝓕, ?_⟩
  · have hk : c * (C : ℂ) ^ (z - s0 d.m d.n) ≠ 0 :=
      mul_ne_zero hc0 (Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 hC.ne')))
    have h1 : Integrable (fun β => flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) *
        d.B.ψ (-d.tt (T.1.1 * β.1))) lam :=
      hI.mul_bdd (_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_psi_meas_k d T.1.1).aestronglyMeasurable
        (Eventually.of_forall fun β => (GlobalTheory.StdCharFromIsStd.norm_psi d.ok.good.std _).le)
    have h2 := h1.const_mul (c * (C : ℂ) ^ (z - s0 d.m d.n))⁻¹
    have hcomp : Integrable (fun β => Gen.whI (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) d.B.ψ μ Φg (Gen.nuA θ g lv L₁ L₂)
        ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z (hOf β)) lam := by
      refine h2.congr (Eventually.of_forall fun β => ?_)
      simp only [hint z β]
      exact inv_mul_cancel_left₀ hk _
    exact (hpresβ.integrable_comp_emb hembβ).1 hcomp
  · simp_rw [hint z]
    rw [integral_const_mul, hpresβ.integral_comp hembβ]
  · rw [horb T T₀ hr.rat (d.om x Φ) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d x hΦ.1)]
    have : (fun Y => d.T (d.om x Φ) (toMx Y)) = fun Y => c * Φg Y := funext hTx
    rw [this, asm_meanC_smul]
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

