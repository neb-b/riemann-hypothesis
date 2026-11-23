module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.JnArcFin
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.LrhoPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0035
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.HgtMulRight
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0013
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourLB
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem lamBd_k : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k := by
  intro F E _ _ _ _ _ σ d L hL
  obtain ⟨nb, lam, 𝓖, T, x, ⟨hnb, hlam, hfd, hvol⟩, -, rfl⟩ := hL
  have hB := d.ok.good
  have hσ : ∀ a, σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k hB
  have hb := d.ok.frame
  obtain ⟨iLC, iSC, iT2, iBo⟩ := nA_top hσ hb
  have hcont := nb_continuous hσ hb hnb
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF hB.std
  obtain ⟨K, hK, hKc⟩ := nF_cocompact hσ hb
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
    with hχ
  have hχc : Continuous χ := continuous_chr hψ.1 T.1.1
  have hχn : ∀ β, ‖χ β‖ = 1 := fun β => hψ.2.1 _
  have hfin : lam 𝓖 < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hcm : Continuous fun β : nA σ d.Y d.b => nb β * x := hcont.mul continuous_const
  have hper : ∀ f : d.G → ℂ, (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → ∀ β, ∃ k ∈ K,
      f (nb β * x) = f (nb k * x) := by
    intro f hf β
    obtain ⟨γ, hγ, hk⟩ := hKc β
    refine ⟨γ + β, hk, ?_⟩
    rw [nb_add hnb, mul_assoc, hf _ (nb_rat hnb γ hγ)]
  have hbd : ∀ (f : d.G → ℂ) (M : ℝ), (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      (∀ y ∈ (fun β => nb β * x) '' K, ‖f y‖ ≤ M) → ∀ β, ‖f (nb β * x) * χ β‖ ≤ M := by
    intro f M hf hM β
    obtain ⟨k, hk, e⟩ := hper f hf β
    rw [norm_mul, hχn β, mul_one, e]
    exact hM _ ⟨k, hk, rfl⟩
  have hint : ∀ f : d.G → ℂ, Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      IntegrableOn (fun β => f (nb β * x) * χ β) 𝓖 lam := by
    intro f hfc hf
    obtain ⟨M, hM⟩ := (hK.image hcm).exists_bound_of_continuousOn hfc.continuousOn
    refine Measure.integrableOn_of_bounded (M := M) hfin.ne ?_ ?_
    · exact ((hfc.comp hcm).mul hχc).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun β => hbd f M hf hM β
  refine ⟨fun a f f' hfc hf'c hf hf' => ?_, ⟨(fun β => nb β * x) '' K, hK.image hcm, fun f M hfc hf hM => ?_⟩⟩
  · simp only [fc]
    have e : (fun β : nA σ d.Y d.b => (a • f + f') (nb β * x) *
        d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))) =
        fun β => a * (f (nb β * x) * χ β) + f' (nb β * x) * χ β := by
      funext β; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hχ]; ring
    rw [e, integral_add ((hint f hfc hf).const_mul a) (hint f' hf'c hf'), integral_const_mul]
  · show ‖∫ β in 𝓖, f (nb β * x) * χ β ∂lam‖ ≤ M
    have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun β _ => hbd f M hf hM β)
    have hr : lam.real 𝓖 = 1 := by simp [Measure.real, hvol]
    rwa [hr, mul_one] at h1
end PositivityTheory.SiegelWeilFormula.kfour
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
abbrev Yf_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := Fin d.m × Fin d.n × Fin 2 → Af F
abbrev Iw_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := InfinitePlace F × Fin d.m × Fin d.n × Bool
abbrev Vw_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := EuclideanSpace ℝ (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d)
def fin_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d := fun k => (d.crd X k).2
def arc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d :=
  (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).symm fun i => if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im
def gau_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : ℂ := ∏ w, fP (1 : PX d.m d.n) (R.loc w X)
def vac_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ) (X : Mx F E d.m d.n) : ℂ := _root_.PositivityTheory.SiegelWeilFormula.KFP.gau_k R X * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)
theorem vac_mem_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) : _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g ∈ R.fock :=
  Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
theorem exists_lift_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) :
    ∃ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g :=
  (hT.1 F E σ d).2.1 _ ((hF F E σ d R).1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.vac_mem_k R hg))
def zOf_k (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ) : InfinitePlace F → Fin d.m → Fin d.n → ℂ :=
  fun w a j => ⟨u (w, a, j, true), u (w, a, j, false)⟩
theorem arc_eq_iff_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) :
    _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X = u ↔ ∀ w, R.loc w X = _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ u) w := by
  constructor
  · rintro rfl w
    funext a j
    apply Complex.ext
    · simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k]
  · intro h
    apply (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).injective
    funext i
    obtain ⟨w, a, j, b⟩ := i
    have hw := congrFun (congrFun (h w) a) j
    cases b
    · simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k, ContinuousLinearEquiv.apply_symm_apply, Bool.false_eq_true, ite_false]
      rw [hw]
      rfl
    · simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k, ContinuousLinearEquiv.apply_symm_apply, ite_true]
      rw [hw]
      rfl
theorem exists_jn_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (y : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) : ∃! X : Mx F E d.m d.n, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X = u ∧ _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X = y := by
  have crd_cmb (c : Fin d.m × Fin d.n × Fin 2 → AF F) : d.crd (d.cmb c) = c := by
    funext k
    obtain ⟨i, j, l⟩ := k
    simp only [SD_k.crd, SD_k.cmb]
    simpa only [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      using congrFun ((Algebra.TensorProduct.basis (AF F) d.bs).repr_sum_self fun k => c (i, j, k)) l
  have cmb_crd (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
    ext i j
    simp only [SD_k.crd, SD_k.cmb]
    simpa only [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      using (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)
  have archEquiv :
      ∃ L : (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ),
        ∀ (c : Fin d.m × Fin d.n × Fin 2 → AF F) (w : InfinitePlace F),
          L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) w = R.loc w (d.cmb c) := by
    have hcm : IsCMExt F E σ := d.ok.good.cm
    have : IsTotallyReal F := hcm.1
    have : IsTotallyComplex E := hcm.2.1
    have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
    have detIm_ne (w : InfinitePlace F) :
        ((d.B.emb w).1 (d.bs 0)).im * ((d.B.emb w).1 (d.bs 1)).re -
        ((d.B.emb w).1 (d.bs 0)).re * ((d.B.emb w).1 (d.bs 1)).im ≠ 0 := by
      let τ : E →+* ℂ := (d.B.emb w).1
      have hreal : ∀ f : F, (τ (algebraMap F E f)).im = 0 := by
        intro f
        have e1 : τ (algebraMap F E f) = w.embedding f := RingHom.congr_fun (d.B.emb w).2 f
        have e3 : ComplexEmbedding.conjugate w.embedding = w.embedding :=
          ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp (hr w))
        have e4 := RingHom.congr_fun e3 f
        rw [ComplexEmbedding.conjugate_coe_eq] at e4
        rw [e1]
        exact Complex.conj_eq_iff_im.mp e4
      have hexp : ∀ e : E, τ e = τ (algebraMap F E (d.bs.repr e 0)) * τ (d.bs 0) +
          τ (algebraMap F E (d.bs.repr e 1)) * τ (d.bs 1) := by
        intro e
        conv_lhs => rw [← d.bs.sum_repr e]
        simp [Fin.sum_univ_two, Algebra.smul_def, map_add (f := _), map_mul]
      obtain ⟨e, he⟩ : ∃ e : E, (τ e).im ≠ 0 := by
        by_contra hne
        push Not at hne
        have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
        rw [InfinitePlace.isComplex_mk_iff] at hc
        apply hc
        rw [ComplexEmbedding.isReal_iff]
        refine RingHom.ext fun x => ?_
        rw [ComplexEmbedding.conjugate_coe_eq]
        exact Complex.conj_eq_iff_im.mpr (hne x)
      intro hD
      apply he
      have h1 := hexp 1
      have h2 := hexp e
      set p := τ (algebraMap F E (d.bs.repr 1 0))
      set q := τ (algebraMap F E (d.bs.repr 1 1))
      set p' := τ (algebraMap F E (d.bs.repr e 0))
      set q' := τ (algebraMap F E (d.bs.repr e 1))
      have ip : p.im = 0 := hreal _
      have iq : q.im = 0 := hreal _
      have ip' : p'.im = 0 := hreal _
      have iq' : q'.im = 0 := hreal _
      rw [map_one] at h1
      have h1re := congrArg Complex.re h1
      have h1im := congrArg Complex.im h1
      have h2im := congrArg Complex.im h2
      simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, ip, iq,
        ip', iq', zero_mul, sub_zero, add_zero] at h1re h1im h2im
      linear_combination -(p'.re * (τ (d.bs 0)).re + q'.re * (τ (d.bs 1)).re) * h1im - (p.re * q'.re - q.re * p'.re) * hD +
        (p'.re * (τ (d.bs 0)).im + q'.re * (τ (d.bs 1)).im) * h1re + h2im
    let coordinateMap :
        (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) :=
        { toFun r w a j := star (∑ i, ((R.fr w)⁻¹).1 a i *
            ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l))
          map_add' r s := by
            funext w a j
            simp only [Pi.add_apply, Prod.fst_add, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, mul_add, star_add]
          map_smul' c r := by
            funext w a j
            simp only [Pi.smul_apply, RingHom.id_apply, Complex.real_smul, Prod.smul_fst, smul_eq_mul, Complex.ofReal_mul]
            conv_rhs => rw [show (c : ℂ) = star (c : ℂ) from (Complex.conj_ofReal c).symm, ← star_mul']
            congr 1
            simp only [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring }
    have hinj : Function.Injective coordinateMap := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro r hr0
      have hz : ∀ w i j, ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l) = 0 := by
        intro w
        let Z : Matrix (Fin d.m) (Fin d.n) ℂ := fun i j => ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l)
        have h1 : ((R.fr w)⁻¹).1 * Z = 0 := by
          ext a j
          have h := congrFun (congrFun (congrFun hr0 w) a) j
          have h' : star (∑ i, ((R.fr w)⁻¹).1 a i * Z i j) = 0 := h
          rw [star_eq_zero] at h'
          rw [Matrix.mul_apply]
          exact h'
        have h2 : Z = 0 := by
          have e : Z = (R.fr w).1 * (((R.fr w)⁻¹).1 * Z) := by
            rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
          rw [e, h1, Matrix.mul_zero]
        intro i j
        exact congrFun (congrFun h2 i) j
      funext k
      obtain ⟨i, j, l⟩ := k
      refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
      · have h := hz v.1 i j
        rw [Fin.sum_univ_two] at h
        have hi := _root_.PositivityTheory.SiegelWeilFormula.KFock.real_indep (detIm_ne v.1) h
        have ev : (⟨v.1, hr v.1⟩ : {w : InfinitePlace F // w.IsReal}) = v := Subtype.ext rfl
        rw [ev] at hi
        fin_cases l
        · exact hi.1
        · exact hi.2
      · exact absurd v.2 (InfinitePlace.not_isComplex_iff_isReal.mpr (hr v.1))
    have hdim : Module.finrank ℝ (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) =
        Module.finrank ℝ (InfinitePlace F → Fin d.m → Fin d.n → ℂ) := by
      simp only [Module.finrank_pi_fintype, mixedEmbedding.finrank, Complex.finrank_real_complex, Finset.sum_const,
        Finset.card_univ, smul_eq_mul, Fintype.card_prod, Fintype.card_fin]
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, ← InfinitePlace.card_add_two_mul_card_eq_rank,
        IsTotallyReal.nrComplexPlaces_eq_zero]
      ring
    have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
    refine ⟨(LinearEquiv.ofBijective coordinateMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun c w => ?_⟩
    funext a j
    show star (∑ i, ((R.fr w)⁻¹).1 a i * ∑ l : Fin 2,
        ((((InfiniteAdeleRing.ringEquiv_mixedSpace F (c (i, j, l)).1).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l))) =
      star ((((R.fr w)⁻¹).1 * d.cw w (d.cmb c)) a j)
    rw [Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    show _ = piInf (d.B.emb w) (∑ l, c (i, j, l) ⊗ₜ[F] d.bs l)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    rfl
  obtain ⟨L, hL⟩ := archEquiv
  set Z := _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ u) with hZ
  let cI := L.symm Z
  let c : Fin d.m × Fin d.n × Fin 2 → AF F := fun k =>
    (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (cI k)) (y k) : AF F)
  have hc1 : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) = cI := by
    funext k
    exact RingEquiv.apply_symm_apply _ _
  refine ⟨d.cmb c, ⟨?_, ?_⟩, ?_⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_eq_iff_k]
    intro w
    rw [← hL c w, hc1]
    show L (L.symm Z) w = Z w
    rw [ContinuousLinearEquiv.apply_symm_apply]
  · funext k
    show (d.crd (d.cmb c) k).2 = y k
    rw [crd_cmb]
  · rintro X ⟨hX1, hX2⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_eq_iff_k] at hX1
    have e1 : L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1) = Z := by
      funext w
      rw [hL, cmb_crd]
      exact hX1 w
    have e2 : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1) = cI := by
      have h := congrArg L.symm e1
      rwa [ContinuousLinearEquiv.symm_apply_apply] at h
    have e3 : d.crd X = c := by
      funext k
      refine Prod.ext ?_ ?_
      · apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
        rw [congrFun e2 k]
        exact (congrFun hc1 k).symm
      · exact congrFun hX2 k
    rw [← e3, cmb_crd]
def jn_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (y : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) : Mx F E d.m d.n := (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R u y).exists.choose
theorem arc_jn_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (y : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) : _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) = u := (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R u y).exists.choose_spec.1
theorem fin_jn_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (y : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) : _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) = y := (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R u y).exists.choose_spec.2
theorem jn_arc_fin_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) : _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) = X :=
  ((_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)).unique (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)).exists.choose_spec ⟨rfl, rfl⟩)
def hg_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) (f : Mx F E d.m d.n → ℂ) (g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) : ℂ :=
  ∫ y, f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) * star (g y) ∂νf
def B_k (ν : Measure (Mx F E d.m d.n)) (Φ Ψ : d.Fn) : ℂ := ∫ X, d.T Φ X * star (d.T Ψ X) ∂ν
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLrhoPf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem rho_smul'_k (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (c : ℂ) (φ : d.Fn) :
    d.dd.rho d.B.ψ w (c • φ) = c • d.dd.rho d.B.ψ w φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring
theorem T_smul'_k (c : ℂ) (φ : d.Fn) (X : Mx F E d.m d.n) : d.T (c • φ) X = c * d.T φ X := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.KFP.rho_smul'_k, map_smul, smul_eq_mul]
theorem T_rho_sum'_k (hH : _root_.PositivityTheory.SiegelWeilFormula.THeis_k) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (Z Z' X : Mx F E d.m d.n) :
    d.T (d.dd.rho d.B.ψ (Z * (incM F d.b.1.toCols₂)ᵀ + Z' * (incM F d.b.1.toCols₁)ᵀ) Φ) X =
      d.B.ψ (-(⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d (Z * (incM F d.b.1.toCols₂)ᵀ) (Z' * (incM F d.b.1.toCols₁)ᵀ))) *
        (d.B.ψ (d.tt (d.gram Z' (X + Z))) * d.T Φ (X + Z)) := by
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hrho : ∀ w, ∀ φ ∈ d.sch, d.dd.rho d.B.ψ w φ ∈ d.sch := fun w φ hφ =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F d.B.ψ hψ d.κ _ φ hφ
  set a := Z * (incM F d.b.1.toCols₂)ᵀ
  set b := Z' * (incM F d.b.1.toCols₁)ᵀ
  have h1 := Tpar.rho_rho (dd := d.dd) (ψ := d.B.ψ) a b Φ
  have h2 : d.dd.rho d.B.ψ (a + b) Φ =
      d.B.ψ (-(⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d a b)) • d.dd.rho d.B.ψ a (d.dd.rho d.B.ψ b Φ) := by
    have h3 := congrArg (fun x : d.Fn => d.B.ψ (-(⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d a b)) • x) h1
    change d.B.ψ (-(⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d a b)) • d.dd.rho d.B.ψ a (d.dd.rho d.B.ψ b Φ) = d.B.ψ (-(⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d a b)) • (d.B.ψ (⅟(2 : AF F) * _root_.PositivityTheory.SiegelWeilFormula.KFP.spf_k d a b) • d.dd.rho d.B.ψ (a + b) Φ) at h3
    rw [smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul] at h3
    exact h3.symm
  rw [h2, _root_.PositivityTheory.SiegelWeilFormula.KFP.T_smul'_k, (hH F E σ d _ (hrho b Φ hΦ) Z X).1, (hH F E σ d Φ hΦ Z' (X + Z)).2]
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadMajor
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.SiegelWeilFormula.Khead
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem majorant_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hS : d.Strong) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) :
    ∃ t : ℝ, ∀ z : ℂ, t < z.re → ∀ C : Set d.G, IsCompact C →
      ∃ u : GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y) → ℝ, Summable u ∧
        ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ d.Y) (rat2 σ d.Y) (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) g q‖ ≤ u q := by
  obtain ⟨r', s', hY⟩ := hS
  have hKc : IsCompact (d.K : Set d.G) := _root_.GlobalTheory.T.isCompact_standard_maximal_compact F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.b d.K d.a
    d.ok.frame d.ok.stdK d.ok.hgt
  obtain ⟨hac, hpos⟩ := _root_.GlobalTheory.T.height_function_continuous_pos F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.b d.K d.a d.ok.frame d.ok.stdK d.ok.hgt
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.flat_section_growth_bound d.K d.a hKc d.ok.hgt hpos d.χ s₁ f hf
  obtain ⟨σ₀, hσ⟩ := _root_.GlobalTheory.T.eisenstein_series_convergence_bound F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.b d.K d.a d.ok.frame d.ok.stdK d.ok.hgt
  refine ⟨σ₀ - (d.n : ℝ) / 2, fun z hz C hC => ?_⟩
  set σ' : ℝ := z.re + (d.n : ℝ) / 2 with hσ'
  have h1 : σ₀ < σ' := by linarith
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup d.G := Subgroup.instIsTopologicalGroupSubtypeMem _
  have hKC : IsCompact ((d.K : Set d.G) * C) := hKc.mul hC
  obtain ⟨M, hM⟩ := hKC.exists_bound_of_continuousOn hac.continuousOn
  obtain ⟨M', hM'⟩ := hKC.exists_bound_of_continuousOn (hac.inv₀ fun y => (hpos y).ne').continuousOn
  have hr : ∀ x, ∀ c ∈ C, d.a (x * c) ^ σ' ≤ (|M| ^ σ' + (|M'|⁻¹) ^ σ') * d.a x ^ σ' := by
    intro x c hc
    obtain ⟨k, hk, e⟩ := hgt_mul_right d.ok.hgt x c
    have hkc : k * c ∈ (d.K : Set d.G) * C := Set.mul_mem_mul hk hc
    have r0 := hpos (k * c)
    have rM : d.a (k * c) ≤ |M| := (Real.le_norm_self _).trans ((hM _ hkc).trans (le_abs_self M))
    have hm := hM' _ hkc
    rw [Pi.inv_apply, norm_inv, Real.norm_of_nonneg r0.le] at hm
    have hM'pos : 0 < |M'| := lt_of_lt_of_le (inv_pos.2 r0) (hm.trans (le_abs_self _))
    have rm : |M'|⁻¹ ≤ d.a (k * c) := (inv_le_comm₀ hM'pos r0).2 (hm.trans (le_abs_self _))
    have hb : d.a (k * c) ^ σ' ≤ |M| ^ σ' + (|M'|⁻¹) ^ σ' := by
      rcases le_total 0 σ' with hs | hs
      · exact (Real.rpow_le_rpow r0.le rM hs).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg (inv_nonneg.2 (abs_nonneg _)) _))
      · exact (Real.rpow_le_rpow_of_nonpos (inv_pos.2 hM'pos) rm hs).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _))
    rw [e, Real.mul_rpow (hpos x).le r0.le, mul_comm]
    exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (hpos x).le _)
  obtain ⟨_, _, hsum⟩ := hσ σ' h1
  refine ⟨fun q => |C0| * (|M| ^ σ' + (|M'|⁻¹) ^ σ') * d.a ((Quotient.out q).1 * 1) ^ σ', (hsum 1).1.mul_left _,
    fun g hg q => ?_⟩
  have hΦ : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) = flat d.a f s₁ z := funext fun y => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, flat]
    rw [Real.coe_toNNReal _ (hpos y).le]
  rw [hΦ]
  show ‖flat d.a f s₁ z ((Quotient.out q).1 * g)‖ ≤ _
  simp only [mul_one]
  calc _ ≤ C0 * d.a ((Quotient.out q).1 * g) ^ σ' := hC0 z _
    _ ≤ |C0| * d.a ((Quotient.out q).1 * g) ^ σ' := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (hpos _).le _)
    _ ≤ |C0| * ((|M| ^ σ' + (|M'|⁻¹) ^ σ') * d.a (Quotient.out q).1 ^ σ') :=
        mul_le_mul_of_nonneg_left (hr _ g hg) (abs_nonneg _)
    _ = _ := by ring
end PositivityTheory.SiegelWeilFormula.Khead
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopCore
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
abbrev SD_k.LF (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := (Fin d.m → Fin d.n → ℂ) → ℂ
abbrev SD_k.MF (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := Mx F E d.m d.n → ℂ
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.StepOK (x : d.G) (A : d.LF → d.LF) (B : d.MF → d.MF) : Prop :=
  (∀ f, IsSw f → IsSw (A f)) ∧ ∀ Ψ, d.IsAwayW w Ψ → d.IsAwayW w (B Ψ) ∧
    ∀ f, IsSw f → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om x Φ) = R.tens w (A f) (B Ψ)
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.Good (y : GR d.n) (g f : d.LF) : Prop :=
  ∀ Ψ, d.IsAwayW w Ψ → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om (R.ι w y) Φ) = R.tens w g Ψ
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.OkY (y : GR d.n) : Prop := ∀ f, IsSw f → ∃ g, IsSw g ∧ R.Good w y g f
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.Lc (y : GR d.n) (f : d.LF) : d.LF := if h : ∃ g, IsSw g ∧ R.Good w y g f then h.choose else 0
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.isLocOp_of_ok (h : ∀ y, R.OkY w y) : R.IsLocOp w (R.Lc w) := by
  intro y f hf
  have hx := h y f hf
  have e : R.Lc w y f = hx.choose := by simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.Lc, dif_pos hx]
  rw [e]
  exact ⟨hx.choose_spec.1, fun Ψ hΨ Φ hΦ hT => hx.choose_spec.2 Ψ hΨ Φ hΦ hT⟩
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.ok_of_step {y : GR d.n} {A : d.LF → d.LF} (h : R.StepOK w (R.ι w y) A id) : R.OkY w y := by
  intro f hf
  exact ⟨A f, h.1 f hf, fun Ψ hΨ Φ hΦ hT => (h.2 Ψ hΨ).2 f hf Φ hΦ hT⟩
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.step_comp (hsch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch) {x x' : d.G} {A A' : d.LF → d.LF}
    {B B' : d.MF → d.MF} (h : R.StepOK w x A B) (h' : R.StepOK w x' A' B') :
    R.StepOK w (x * x') (A ∘ A') (B ∘ B') := by
  refine ⟨fun f hf => h.1 _ (h'.1 f hf), fun Ψ hΨ => ⟨(h.2 _ (h'.2 Ψ hΨ).1).1, fun f hf Φ hΦ hT => ?_⟩⟩
  have e1 := (h'.2 Ψ hΨ).2 f hf Φ hΦ hT
  have e2 := (h.2 (B' Ψ) (h'.2 Ψ hΨ).1).2 (A' f) (h'.1 f hf) (d.om x' Φ) (hsch x' Φ hΦ) e1
  rw [map_mul, Module.End.mul_apply]
  exact e2
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.ok_mul (hsch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch) {y y' : GR d.n} (h : R.OkY w y)
    (h' : R.OkY w y') : R.OkY w (y * y') := by
  intro f hf
  obtain ⟨g', hg', hG'⟩ := h' f hf
  obtain ⟨g, hg, hG⟩ := h g' hg'
  refine ⟨g, hg, fun Ψ hΨ Φ hΦ hT => ?_⟩
  rw [map_mul, map_mul, Module.End.mul_apply]
  exact hG Ψ hΨ _ (hsch _ Φ hΦ) (hG' Ψ hΨ Φ hΦ hT)
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

