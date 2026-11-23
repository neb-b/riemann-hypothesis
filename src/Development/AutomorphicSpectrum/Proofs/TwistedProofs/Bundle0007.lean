module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.CMAdele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_moved {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ β : E, σ β ≠ β := by
  by_contra hne
  push Not at hne
  have := h.2.1
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have := h.2.2.2 τ y
  rw [hne y] at this
  simpa using this.symm

theorem im_ne_zero {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {β : E} (hβ : σ β ≠ β) (τ : E →+* ℂ) : (τ β).im ≠ 0 := by
  intro h0
  apply hβ
  apply τ.injective
  rw [h.2.2.2 τ β]
  exact Complex.conj_eq_iff_im.2 h0

theorem exists_basis {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {β : E} (hβ : σ β ≠ β) :
    ∃ B : Module.Basis (Fin 2) F E, B 0 = 1 ∧ B 1 = β := by
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
  have hli : LinearIndependent F ![(1 : E), β] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hβ
      have e : β = algebraMap F E (-(s / t)) := by
        have ht' : algebraMap F E t ≠ 0 := by simpa using ht
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        rw [map_neg, map_div₀]
        field_simp
        linear_combination hst
      rw [e, AlgHom.commutes]
    subst ht
    simpa using hst
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [h.2.2.1]), ?_, ?_⟩ <;> simp

theorem eq_add_tmul (B : Module.Basis (Fin 2) F E) (x : AF F ⊗[F] E) :
    x = (Algebra.TensorProduct.basis (AF F) B).repr x 0 ⊗ₜ[F] B 0 +
      (Algebra.TensorProduct.basis (AF F) B).repr x 1 ⊗ₜ[F] B 1 := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF F) B).sum_repr x]
  simp [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

theorem piInf_tmul {w : InfinitePlace F} (τ : GlobalTheory.AdelicU.EmbOver E w) (a : AF F) (y : E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ (a ⊗ₜ[F] y) =
      InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 y := rfl

theorem im_extension (hF : IsTotallyReal F) (w : InfinitePlace F) (z : w.Completion) :
    (InfinitePlace.Completion.extensionEmbedding w z).im = 0 := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) z]
  exact Complex.ofReal_im _

theorem eq_zero_of_piInf : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) x → (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w) x = 0) → x = 0 := by
  intro F E _ _ _ _ _ σ h emb x hx hinf
  obtain ⟨β, hβ⟩ := exists_moved h
  obtain ⟨B, hB0, hB1⟩ := exists_basis h hβ
  have hdec := eq_add_tmul B x
  set C := Algebra.TensorProduct.basis (AF F) B with hC
  have hu : pairA F 0 1 • x = 0 := hx _ (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  have hfin : ∀ i, (C.repr x i).2 = 0 := fun i => by
    have h1 : C.repr (pairA F 0 1 • x) i = 0 := by rw [hu]; simp
    rw [map_smul] at h1
    have h2 : pairA F 0 1 * C.repr x i = 0 := h1
    have h3 := congrArg (sndA F) h2
    rw [map_mul, map_zero] at h3
    exact (one_mul _).symm.trans h3
  have hre : ∀ w i, (C.repr x i).1 w = 0 := fun w => by
    have e := hinf w
    rw [hdec, map_add (f := _), piInf_tmul, piInf_tmul, hB0, hB1, map_one, mul_one] at e
    have hi := congrArg Complex.im e
    have him := im_ne_zero h hβ (emb w).1
    set p := InfinitePlace.Completion.extensionEmbedding w ((C.repr x 0).1 w) with hp
    set q := InfinitePlace.Completion.extensionEmbedding w ((C.repr x 1).1 w) with hq
    have hpi : p.im = 0 := im_extension h.1 w _
    have hqi : q.im = 0 := im_extension h.1 w _
    simp only [Complex.add_im, Complex.mul_im, Complex.zero_im, hpi, hqi, zero_mul, add_zero, zero_add] at hi
    have hq0 : q.re = 0 := (mul_eq_zero.1 hi).resolve_right him
    have hq1 : q = 0 := Complex.ext hq0 hqi
    rw [hq1, zero_mul, add_zero] at e
    have inj := (InfinitePlace.Completion.extensionEmbedding w).injective
    intro i
    fin_cases i
    · show (C.repr x 0).1 w = 0
      exact inj (e.trans (map_zero _).symm)
    · show (C.repr x 1).1 w = 0
      exact inj (hq1.trans (map_zero _).symm)
  have hz : C.repr x = 0 := by
    ext i
    show C.repr x i = 0
    exact Prod.ext (funext fun w => hre w i) (hfin i)
  simpa using hz

end GlobalTheory.CompanionTheory.CMAdele

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExistsAdelePiInf
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.CompanionTheory.RealPlaceAdele

open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ofInf (c : ∀ w : InfinitePlace F, w.Completion) : AF F := ((c : Ainf F), (0 : Af F))

theorem mul_ofInf (u : AF F) (hu : evI F u = 0) (c : ∀ w : InfinitePlace F, w.Completion) : u * ofInf c = 0 := by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    rw [mul_zero]

theorem exists_adele_piInf : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w)
    (z : InfinitePlace F → ℂ), ∃ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) x ∧
      ∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w) x = z w := by
  intro F E _ _ _ _ _ σ h emb z
  have hF := h.1
  have hE := h.2.1
  have hconj := h.2.2.2
  obtain ⟨β, hβ⟩ : ∃ β : E, σ β ≠ β := by
    by_contra hcon
    push Not at hcon
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_))
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := hconj φ x
    rw [hcon x] at this
    exact this.symm
  have him : ∀ w, ((emb w).1 β).im ≠ 0 := fun w hw => hβ ((emb w).1.injective (by
    rw [hconj]
    exact Complex.conj_eq_iff_im.2 hw))
  let e : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ := fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  have he : ∀ w a, InfinitePlace.Completion.extensionEmbedding w a = ((e w a : ℝ) : ℂ) := fun w a =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) a).symm
  let s : InfinitePlace F → ℝ := fun w => (z w).im / ((emb w).1 β).im
  let r : InfinitePlace F → ℝ := fun w => (z w).re - s w * ((emb w).1 β).re
  refine ⟨ofInf (fun w => (e w).symm (r w)) ⊗ₜ[F] 1 + ofInf (fun w => (e w).symm (s w)) ⊗ₜ[F] β, ?_, fun w => ?_⟩
  · intro u hu
    rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_ofInf u hu,
      mul_ofInf u hu, TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  · have hc : ∀ (c : ∀ w : InfinitePlace F, w.Completion) (y : E),
        piInf (emb w) (ofInf c ⊗ₜ[F] y) = ((e w (c w) : ℝ) : ℂ) * (emb w).1 y := fun c y => by
      rw [← he]
      rfl
    rw [map_add (f := _), hc, hc]
    simp only [(e w).apply_symm_apply, map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, r]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, s]
      have := him w
      field_simp
      ring

end GlobalTheory.CompanionTheory.RealPlaceAdele

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExtensionEmbeddingEvInfRealAd
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.CompanionTheory.RealAdeleComponent

open scoped TensorProduct
open GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem extensionEmbedding_evInf_realAd {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w (evInf F w (realAd F t)) = (t : ℂ) := by
  have h := (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply
    (algebraMap ℝ (mixedEmbedding.mixedSpace F) t)
  have e : evInf F w (realAd F t) = ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
    (algebraMap ℝ (mixedEmbedding.mixedSpace F) t)) w := rfl
  rw [e]
  generalize (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
    (algebraMap ℝ (mixedEmbedding.mixedSpace F) t) = y at h
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h
  by_cases hw : w.IsReal
  · have h1 := congrFun (congrArg Prod.fst h) ⟨w, hw⟩
    have h2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (y w) = t := h1
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, h2]
  · have h1 := congrFun (congrArg Prod.snd h) ⟨w, InfinitePlace.not_isReal_iff_isComplex.1 hw⟩
    exact h1

theorem piInf_realAd_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {w : InfinitePlace F} (τ : GlobalTheory.AdelicU.EmbOver E w) (t : ℝ) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F t • x) = (t : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  | tmul a e =>
    have h : ∀ b : AF F, piInf τ (b ⊗ₜ[F] e) =
        InfinitePlace.Completion.extensionEmbedding w (evInf F w b) * τ.1 e := fun b => rfl
    rw [TensorProduct.smul_tmul', smul_eq_mul, h, h, map_mul, map_mul, extensionEmbedding_evInf_realAd, mul_assoc]

end GlobalTheory.CompanionTheory.RealAdeleComponent

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmithNormalFormExists
section
noncomputable section

open Matrix Formalism.UG GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertSmith

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem exists_zpow_val {ϖ y : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (hy : y ≠ 0) :
    ∃ d : ℤ, Valued.v y = Valued.v (ϖ ^ d) := by
  refine ⟨Formalism.UG.ordL y, ?_⟩
  rw [GlobalTheory.Hk3.Smith.v_eq_ord hy, map_zpow₀, hϖ]
  change _ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ Formalism.UG.ordL y
  rw [← WithZero.coe_zpow, ← ofAdd_zsmul]
  congr 2
  simp

theorem isInt_diagonal {n : ℕ} {s : Fin n → L} (hs : ∀ i, Valued.v (s i) = 1) : IsInt (Matrix.diagonal s) := by
  intro i j
  rw [GlobalTheory.Hk3.Smith.mem_intL, Matrix.diagonal_apply]
  split_ifs with h
  · exact (hs i).le
  · simp

theorem smith : Smith := by
  intro L _ _ ϖ n hϖ g hg
  obtain ⟨P, Q, ⟨hPi, P', hP'i, hPP'⟩, ⟨hQi, Q', hQ'i, hQQ'⟩, hD⟩ := GlobalTheory.Hk3.Smith.exists_diag n n g
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  have hdetP : P.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hPP'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hdetQ : Q.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hQQ'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hDdiag : P * g * Q = Matrix.diagonal (fun i => (P * g * Q) i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hD i j (fun h => hij (Fin.ext h))
  have hne : ∀ i, (P * g * Q) i i ≠ 0 := by
    have hdet : (P * g * Q).det ≠ 0 := by
      rw [Matrix.det_mul, Matrix.det_mul]
      exact mul_ne_zero (mul_ne_zero hdetP hg) hdetQ
    rw [hDdiag, Matrix.det_diagonal] at hdet
    exact fun i => Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)
  have hvϖ : Valued.v ϖ ≠ 0 := by
    rw [hϖ]
    exact WithZero.coe_ne_zero
  have hϖ0 : ϖ ≠ 0 := fun h => hvϖ (by rw [h, map_zero])
  choose d hd using fun i => exists_zpow_val hϖ (hne i)
  have hpow0 : ∀ i, ϖ ^ d i ≠ 0 := fun i => zpow_ne_zero _ hϖ0
  obtain ⟨u, hu⟩ : ∃ u : Fin n → L, ∀ i, u i = (P * g * Q) i i / ϖ ^ d i := ⟨_, fun i => rfl⟩
  have hvu : ∀ i, Valued.v (u i) = 1 := by
    intro i
    rw [hu i, map_div₀, hd i, div_self]
    exact fun h => hpow0 i (by
      by_contra h'
      exact h' ((Valuation.zero_iff _).mp h))
  have hvu' : ∀ i, Valued.v ((u i)⁻¹) = 1 := fun i => by rw [map_inv₀, hvu i, inv_one]
  have hu0 : ∀ i, u i ≠ 0 := fun i h => by
    have h1 := hvu i
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  have hDfac : P * g * Q = Matrix.diagonal (fun i => ϖ ^ d i) * Matrix.diagonal u := by
    rw [Matrix.diagonal_mul_diagonal]
    conv_lhs => rw [hDdiag]
    congr 1
    funext i
    rw [hu i]
    field_simp
  have hinv : (fun i => u i * (u i)⁻¹) = fun _ => (1 : L) := funext fun i => mul_inv_cancel₀ (hu0 i)
  refine ⟨d, P', P, Matrix.diagonal u * Q', Q * Matrix.diagonal (fun i => (u i)⁻¹), hP'i, hPi,
    GlobalTheory.Hk3.Smith.mul_int (isInt_diagonal hvu) hQ'i, GlobalTheory.Hk3.Smith.mul_int hQi (isInt_diagonal hvu'),
    hPP', ?_, ?_⟩
  · calc Matrix.diagonal u * Q' * (Q * Matrix.diagonal fun i => (u i)⁻¹)
        = Matrix.diagonal u * (Q' * Q) * Matrix.diagonal (fun i => (u i)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [mul_eq_one_comm.mp hQQ', Matrix.mul_one, Matrix.diagonal_mul_diagonal, hinv,
            Matrix.diagonal_one]
  · calc g = P' * (P * g * Q) * Q' := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP'P, Matrix.one_mul, Matrix.mul_assoc, hQQ',
            Matrix.mul_one]
      _ = _ := by
          rw [hDfac]
          simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.InertSmith

end
end

