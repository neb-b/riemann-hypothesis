module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0033
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.DetLast
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ExistsLth
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0026
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0034
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.PiInfInclR

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitTheta
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem th_JR_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) :
    HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) = inclR (F := F) (E := E) (AF F) η • (incM F d.A.J)ᵀ := by
  ext i j
  simp [HeckeCharacterZeroLocus.SiegelWeilU.JR, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, incM, th_inclR_eq, Matrix.transpose_apply, map_mul]
theorem th_mem_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (g : GL (Fin d.m) (AE F E)) :
    g ∈ UG (cA σ) (incM F d.A.J) ↔ g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := by
  have hc : IsUnit (inclR (F := F) (E := E) (AF F) η) := (Ne.isUnit hη).map _
  have hm : (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) =
      (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ) := by
    ext i j; exact th_sigR_eq _
  show (g : Matrix (Fin d.m) (Fin d.m) (AE F E))ᵀ * incM F d.A.J * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ) =
      incM F d.A.J ↔ HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) (g : Matrix (Fin d.m) (Fin d.m) (AE F E)) *
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)) = HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η)
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_JR_k, HeckeCharacterZeroLocus.SiegelWeilU.cT, hm]
  set L := (g : Matrix (Fin d.m) (Fin d.m) (AE F E))ᵀ * incM F d.A.J * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ)
  have hL : ((g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ))ᵀ *
      (inclR (F := F) (E := E) (AF F) η • (incM F d.A.J)ᵀ) * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)) =
      inclR (F := F) (E := E) (AF F) η • Lᵀ := by
    simp only [L, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [hL]
  constructor
  · intro h; rw [h]
  · intro h
    have h2 := congrArg (fun M => (hc.unit⁻¹ : (AE F E)ˣ) • M) h
    simp only [Units.smul_def, smul_smul] at h2
    have h3 : ((hc.unit⁻¹ : (AE F E)ˣ) : AE F E) * inclR (F := F) (E := E) (AF F) η = 1 := by
      exact hc.val_inv_mul
    rw [h3, one_smul, one_smul] at h2
    have := congrArg Matrix.transpose h2
    simpa using this
def thE_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : UA σ d.A.J ≃* HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) :=
  MulEquiv.subgroupCongr (Subgroup.ext (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_mem_iff_k d hη))
theorem thE_cont_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη) :=
  continuous_subtype_val.subtype_mk _
theorem thE_symm_cont_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).symm :=
  continuous_subtype_val.subtype_mk _
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilLdexbVal
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Ldexb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem jpar_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} {j : G2 σ Y →* d.G}
    (hJ : _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j) {p : G2 σ Y} (hp : ParF b p) :
    ParF d.b (j p) ∧ (inFrame d.b (j p)).toBlocks₁₁.det = (inFrame b p).toBlocks₁₁.det := by
  obtain ⟨-, h2, h3⟩ := hJ
  set X := inFrame d.b (j p) with hX
  have hsub : ∀ x y, X (Sum.map (Ald.em0 h) (Ald.em0 h) x) (Sum.map (Ald.em0 h) (Ald.em0 h) y) = inFrame b p x y :=
    fun x y => by rw [← h2 p]; rfl
  have hl : ∀ v, X (Sum.inl (Ald.i0 h)) v = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inl (Ald.i0 h)) v :=
    fun v => (h3 p _ (by simp) v).1
  have hl' : ∀ v, X v (Sum.inl (Ald.i0 h)) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) v (Sum.inl (Ald.i0 h)) :=
    fun v => (h3 p _ (by simp) v).2
  have hr : ∀ v, X (Sum.inr (Ald.i0 h)) v = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr (Ald.i0 h)) v :=
    fun v => (h3 p _ (by simp) v).1
  constructor
  · show X.toBlocks₂₁ = 0
    ext a c
    show X (Sum.inr a) (Sum.inl c) = 0
    by_cases ha : a = Ald.i0 h
    · subst ha; rw [hr]; simp [Matrix.one_apply]
    by_cases hc : c = Ald.i0 h
    · subst hc; rw [hl']; simp [Matrix.one_apply]
    obtain ⟨a', rfl⟩ := (Ald.ne_last_iff_mem_range h a).1 ha
    obtain ⟨c', rfl⟩ := (Ald.ne_last_iff_mem_range h c).1 hc
    have e := hsub (Sum.inr a') (Sum.inl c')
    simp only [Sum.map_inr, Sum.map_inl] at e
    rw [e]
    exact congrFun (congrFun hp a') c'
  · rw [det_last h X.toBlocks₁₁ (fun c => by
      show X (Sum.inl (Ald.i0 h)) (Sum.inl c) = _
      rw [hl]; by_cases hc : c = Ald.i0 h
      · subst hc; simp
      · simp [Matrix.one_apply, hc, Ne.symm hc])]
    congr 1
    ext a c
    have e := hsub (Sum.inl a) (Sum.inl c)
    simp only [Sum.map_inl] at e
    exact e
theorem val_pull_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} {j : G2 σ Y →* d.G}
    (hJ : _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j) (hb : IsFrame2 σ Y b) :
    ∀ (p : G2 σ Y) (t : GL (Fin n) (AE F E)), IsPar p t → ∀ k ∈ d.K.comap j,
      (d.a ∘ j) (p * k) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := by
  intro p t hpt k hk
  obtain ⟨hpf, hdet⟩ := par_to hb hpt
  obtain ⟨hbig, hdet2⟩ := _root_.PositivityTheory.SiegelWeilFormula.Ldexb.jpar_k h hJ hpf
  obtain ⟨t', ht', hdt'⟩ := par_of d.ok.frame hbig
  show d.a (j (p * k)) = _
  rw [map_mul, d.ok.hgt.val (j p) t' ht' (j k) hk]
  congr 2
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  rw [hdt', hdet2, hdet]
end PositivityTheory.SiegelWeilFormula.Ldexb
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilMeasdictSign
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.MeasD
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem eta_sign_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) {ε : ℤˣ}
    (hb : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    σ η = -(((ε : ℤ) : E)) * η := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · have he := frame_sign hσ d.ok.hn d.Y.J (-1) (fun i j => by rw [hY, neg_one_mul]) d.b ε hb
    obtain ⟨i, j, hij⟩ := exists_ne_zero_of_map d.A.J (d.B.emb w).1 1
      (by rw [one_smul]; exact ne_zero_of_sig d.ok.hm _ (hA.sig w))
    have h := herm i j
    rw [map_mul, hA.herm] at h
    rw [he, neg_neg, one_mul]
    exact mul_right_cancel₀ hij h
  · have he := frame_sign hσ d.ok.hn d.Y.J 1 (fun i j => by rw [hY, one_mul]) d.b ε hb
    obtain ⟨i, j, hij⟩ := exists_ne_zero_of_map d.A.J (d.B.emb w).1 Complex.I (ne_zero_of_sig d.ok.hm _ (hA.sig w))
    have h := herm i j
    rw [map_mul, hA.skew] at h
    rw [he, neg_one_mul]
    apply mul_right_cancel₀ hij
    linear_combination -h
end PositivityTheory.SiegelWeilFormula.MeasD
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilMeasdictToMx
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.MeasD
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem meas_toMx_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (𝓕 : Set (Fin d.n → Fin d.m → AF F ⊗[F] E))
    (hμ : μ.IsAddHaarMeasure) (hF : IsAddFundamentalDomain (MeasP.ratTupA F E d.n d.m) 𝓕 μ) (h1 : μ 𝓕 = 1) :
    MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) ∧ (μ.map toMx).IsAddHaarMeasure ∧
      IsAddFundamentalDomain d.ratM (toMx '' 𝓕) (μ.map toMx) ∧ μ.map toMx (toMx '' 𝓕) = 1 := by
  have hemb : MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) := (colM d.m d.n).measurableEmbedding
  refine ⟨hemb, ?_, ?_, ?_⟩
  · exact (colE (F := F) (E := E) d.m d.n).toAddEquiv.isAddHaarMeasure_map μ (colE d.m d.n).continuous
      (colE d.m d.n).symm.continuous
  · rw [_root_.PositivityTheory.SiegelWeilFormula.kfour.ratM_eq_k]
    refine hF.image_of_equiv (colM d.m d.n).toEquiv ?_ (ratEq d.m d.n) ?_
    · exact ((colM d.m d.n).measurePreserving_symm μ).quasiMeasurePreserving
    · intro g x
      rfl
  · rw [hemb.map_apply, Set.preimage_image_eq _ hemb.injective, h1]
end PositivityTheory.SiegelWeilFormula.MeasD
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoMean
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem cpt_k (hS : GlobalTheory.Published.SiegelSetUnitary) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Cpt σ d.A.J := by
  have h := _root_.GlobalTheory.ThK.Dbl.cptAll_of_k PositivityTheory.ThKEst.grpTop_of _root_.PositivityTheory.ThKEst.epsOf_of_k (PositivityTheory.ThKEst.siegelAll_of hS)
    PositivityTheory.ThKEst.finVolU PositivityTheory.ThKF.unimodularity_holds
  rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
  · exact h F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inl hA) d.ok.aniso
  · exact h F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inr hA) d.ok.aniso
theorem exists_lth_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ l ∈ (adeleClass F).adm d.κ, ∀ Φ ∈ d.sch, l Φ = thetaSum F Φ :=
  _root_.GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F d.κ
theorem cont_S_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) : Continuous fun g : UA σ d.A.J => thetaSum F (d.S g Ψ) := by
  obtain ⟨l, hl, hlθ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.exists_lth_k d
  exact (d.ok.dbl.lin.cont l hl Ψ hΨ).congr fun g => hlθ _ (d.ok.dbl.lin.pres g Ψ hΨ)
theorem inv_S_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    ∀ γ ∈ ratU σ d.A.J, ∀ g, thetaSum F (d.S (γ * g) Ψ) = thetaSum F (d.S g Ψ) := fun γ hγ g => by
  rw [map_mul, Module.End.mul_apply, _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaSum_S_rat_k hP hT d hγ (d.ok.dbl.lin.pres g Ψ hΨ)]
theorem bdd_S_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    ∃ C : ℝ, ∀ g, ‖thetaSum F (d.S g Ψ)‖ ≤ C :=
  (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d).bdd (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cont_S_k d hΨ) (_root_.PositivityTheory.SiegelWeilFormula.Tauto.inv_S_k hP hT d hΨ)
theorem intOn_S_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    IntegrableOn (fun g => thetaSum F (d.S g Ψ)) d.D d.μ := by
  obtain ⟨C, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.bdd_S_k hS hP hT d hΨ
  exact Measure.integrableOn_of_bounded (M := C) ((_root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d).fin d.μ d.D d.ok.haar d.ok.dom).ne
    (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cont_S_k d hΨ).aestronglyMeasurable (Eventually.of_forall hC)
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoOrth
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open PositivityTheory.SiegelWeilFormula.kfour PositivityTheory.SiegelWeilFormula.Place
theorem frame_sign_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ ε : ℤˣ, FrameEq σ d.Y d.b ε ∧
    ∀ i j, d.A.J j i = -(((ε : ℤ) : E)) * σ (d.A.J i j) := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  refine ⟨ε, hε, ?_⟩
  have key : ∀ e : E, e * e = 1 → (∀ i j, σ (d.Y.J j i) = e * d.Y.J i j) → ((ε : ℤ) : E) = e := by
    intro e he hY
    have hY' : ∀ i j, d.Y.J j i = e * σ (d.Y.J i j) := fun i j => by
      rw [hY j i, ← mul_assoc, he, one_mul]
    have hD : (dbl d.Y.J)ᵀ = e • (dbl d.Y.J).map σ := by
      ext (i | i) (j | j)
      · simp [dbl, hY' i j]
      · simp [dbl]
      · simp [dbl]
      · simp [dbl, hY' i j]
    have hM : (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ)ᵀ = e • (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ).map σ := by
      have e1 : (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ).map σ = (d.b.1.map σ)ᵀ * (dbl d.Y.J).map σ * d.b.1 := by
        have h1 : ∀ {p q r : Type} [Fintype q] (P : Matrix p q E) (Q : Matrix q r E), (P * Q).map σ = P.map σ * Q.map σ :=
          fun P Q => Matrix.map_mul (f := σ.toRingHom)
        have h2 : (d.b.1.map σ).map σ = d.b.1 := by
          rw [Matrix.map_map]
          exact Matrix.ext fun i j => hσ _
        rw [h1, h1, h2, Matrix.transpose_map]
      rw [e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hD, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_assoc]
    rw [hε] at hM
    have hn : 0 < d.n := d.ok.hn
    have := congrFun (congrFun hM (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
    simpa [Matrix.fromBlocks] using this
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · have e := key (-1) (by ring) fun i j => by rw [hY i j]; ring
    intro i j
    rw [e, neg_neg, one_mul]
    exact (hA.herm j i).symm
  · have e := key 1 (by ring) fun i j => by rw [hY i j, one_mul]
    intro i j
    rw [e, hA.skew j i]
    ring
theorem gram_cond_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) (hε : ∀ i j, d.A.J j i = -(((ε : ℤ) : E)) * σ (d.A.J i j))
    (X : Matrix (Fin d.m) (Fin d.n) (AE F E)) : d.gram X X ∈ nCond σ d.n ε := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have hJ : (incM F d.A.J)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F d.A.J).map (cA σ)) := by
    ext i j
    simp only [Matrix.transpose_apply, incM, Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
      cA_inclR']
    rw [hε i j, map_mul, map_neg, inclR_int, neg_mul]
  show (Xᵀ * incM F d.A.J * X.map (cA σ))ᵀ = -((((ε : ℤ) : AE F E)) • (Xᵀ * incM F d.A.J * X.map (cA σ)).map (cA σ))
  have h1 : ∀ {p q r : Type} [Fintype q] (P : Matrix p q (AE F E)) (Q : Matrix q r (AE F E)),
      (P * Q).map (cA σ) = P.map (cA σ) * Q.map (cA σ) := fun P Q => Matrix.map_mul (f := (cA σ).toRingHom)
  have h2 : (X.map (cA σ)).map (cA σ) = X := by
    rw [Matrix.map_map]
    exact Matrix.ext fun i j => cA_cA' σ hσ _
  rw [h1, h1, h2, Matrix.transpose_map, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hJ,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
theorem gram_incM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = incM F (Xᵀ * d.A.J * X.map σ) := by
  show (incM F X)ᵀ * incM F d.A.J * (incM F X).map (cA σ) = _
  rw [incM_mul'', incM_mul'', incM_map]
  rfl
theorem gram_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Matrix (Fin d.m) (Fin d.n) E) (T : nF σ d.Y d.b) :
    ⅟(2 : AF F) • d.gram (incM F X) (incM F X) + T.1.1 ∈ nA σ d.Y d.b ∧
      ∃ S₀ : Matrix (Fin d.n) (Fin d.n) E, ⅟(2 : AF F) • d.gram (incM F X) (incM F X) + T.1.1 = incM F S₀ := by
  obtain ⟨ε, hb, hε⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.frame_sign_k d
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨T₀, hT₀⟩ := (mem_nF_iff T.1).1 T.2
  refine ⟨(mem_nA_iff hσ hb _).2 (add_mem (smul_cond ε _ (_root_.PositivityTheory.SiegelWeilFormula.Tauto.gram_cond_k d ε hε _)) ((mem_nA_iff hσ hb _).1 T.1.2)),
    (2⁻¹ : E) • (Xᵀ * d.A.J * X.map σ) + T₀, ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.Tauto.gram_incM_k, hT₀]
  ext i j
  simp only [incM, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_add (f := _), map_mul]
  rw [Algebra.smul_def, ← half_eq]
theorem exists_twist_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) (S₀ : Matrix (Fin d.n) (Fin d.n) E) (hS : incM F S₀ ∈ nCond σ d.n ε)
    (h0 : S₀ ≠ 0) : ∃ β₀ ∈ nCond σ d.n ε, d.B.ψ (-(d.tt (incM F S₀ * β₀))) ≠ 1 := by
  have hcm := d.cm
  have hS' : (incM F S₀)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F S₀).map (cA σ)) := hS
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, S₀ i j ≠ 0 := by
    by_contra h
    exact h0 (Matrix.ext fun i j => by_contra fun hne => h ⟨i, j, hne⟩)
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ := d.B.emb
  set Sw : Matrix (Fin d.n) (Fin d.n) ℂ := (incM F S₀).map (piInf (τ w)) with hSw
  have hSwT : ∀ i j, Sw j i = -(((ε : ℤ) : ℂ)) * star (Sw i j) := fun i j => by
    have := congrArg (fun M => (M.map (piInf (τ w))) i j) hS'
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg,
      map_mul, map_intCast, piInf_cA hcm] at this
    simpa [hSw] using this
  set q : ℂ := piInf (τ w) ((incM F S₀ * incM F S₀).trace) with hq
  have hqe : q = -(((ε : ℤ) : ℂ)) * ∑ i, ∑ j, ((Complex.normSq (Sw i j) : ℝ) : ℂ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hq, Matrix.trace, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.diag_apply, Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    change Sw i j * Sw j i = _
    rw [hSwT i j, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  have hN : 0 < ∑ i, ∑ j, Complex.normSq (Sw i j) := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (Sw i j))
      (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i₀))
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j => Complex.normSq (Sw i₀ j))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ j₀))
    refine Complex.normSq_pos.2 ?_
    simp only [hSw, Matrix.map_apply, incM, piInf_inclR']
    exact (map_ne_zero _).2 hij
  have hε1 : (((ε : ℤ) : ℝ)) ≠ 0 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hqre : q.re = -(((ε : ℤ) : ℝ)) * ∑ i, ∑ j, Complex.normSq (Sw i j) := by
    rw [hqe]
    simp [Complex.mul_re, ← Complex.ofReal_sum]
  have hqre0 : q.re ≠ 0 := by
    rw [hqre]
    exact mul_ne_zero (neg_ne_zero.2 hε1) hN.ne'
  set r : ℝ := -1 / (4 * q.re) with hr
  obtain ⟨s, -, hs1, hs2, -, hs4⟩ := exists_sec hcm τ
  set x : InfinitePlace F → ℂ := fun u => if u = w then (r : ℂ) else 0 with hx
  set c : AE F E := s x with hc
  have hcc : cA σ c = c := by
    refine ad_ext hcm τ (fun u => ?_) ?_
    · rw [piInf_cA hcm, hc, hs1]
      by_cases hu : u = w <;> simp [hx, hu]
    · rw [← map_smul, hc, hs2, map_zero]
  refine ⟨c • incM F S₀, ?_, ?_⟩
  · show (c • incM F S₀)ᵀ = -((((ε : ℤ) : AE F E)) • (c • incM F S₀).map (cA σ))
    have e : (c • incM F S₀).map (cA σ) = c • (incM F S₀).map (cA σ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hcc]
    rw [Matrix.transpose_smul, hS', e, smul_neg, smul_comm]
  · set z : AE F E := -(c * (incM F S₀ * incM F S₀).trace) with hz
    have e1 : -(d.tt (incM F S₀ * (c • incM F S₀))) = Algebra.trace (AF F) (AE F E) z := by
      rw [hz, map_neg, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hf : finOne F • z = 0 := by
      rw [hz, smul_neg, ← smul_mul_assoc, hc, hs2, zero_mul, neg_zero]
    have hw : ∀ u, u ≠ w → piInf (τ u) z = 0 := fun u hu => by
      rw [hz, map_neg, map_mul, hc, hs1]
      simp [hx, hu]
    rw [e1, psi_trace_at d.std hcm τ w z hf hw]
    have hzw : (piInf (τ w) z).re = 1 / 4 := by
      rw [hz, map_neg, map_mul, hc, hs1, ← hq]
      simp only [hx, if_pos rfl, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [hr]
      field_simp
    rw [hzw]
    intro h
    have h2 : Complex.exp (-(2 * Real.pi * Complex.I) * (((2 * (1 / 4 : ℝ)) : ℝ) : ℂ)) = -1 := by
      rw [show (2 * (1 / 4 : ℝ)) = 1 / 2 by norm_num]
      rw [show -(2 * Real.pi * Complex.I) * (((1 / 2 : ℝ)) : ℂ) = -(Real.pi * Complex.I) by push_cast; ring]
      rw [Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    rw [h2] at h
    norm_num at h
theorem orth_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (S : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (hS : S ∈ nA σ d.Y d.b) (hr : ∃ S₀ : Matrix (Fin d.n) (Fin d.n) E, S = incM F S₀) :
    ∫ β in 𝓖, d.B.ψ (-(d.tt (S * β.1))) ∂lam = if S = 0 then 1 else 0 := by
  classical
  obtain ⟨ε, hb, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.frame_sign_k d
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨-, hH, hfd, h1⟩ := hc
  haveI := hH
  haveI : BorelSpace (nA σ d.Y d.b) := (nA_top hσ d.ok.frame).2.2.2
  obtain ⟨S₀, rfl⟩ := hr
  split_ifs with h0
  · have hone : ∀ β : nA σ d.Y d.b, d.B.ψ (-(d.tt (incM F S₀ * β.1))) = 1 := fun β => by
      rw [h0, Matrix.zero_mul, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_zero, map_zero, neg_zero, AddChar.map_zero_eq_one]
    simp_rw [hone]
    rw [setIntegral_const]
    simp [Measure.real, h1]
  · have hS0 : S₀ ≠ 0 := fun h => h0 (by rw [h]; ext i j; simp [incM])
    obtain ⟨β₀, hβ₀, hne⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.exists_twist_k d ε S₀ ((mem_nA_iff hσ hb _).1 hS) hS0
    let h : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(d.tt (incM F S₀ * β.1)))
    have hadd : ∀ β β' : nA σ d.Y d.b, h (β + β') = h β * h β' := fun β β' => by
      simp only [h, AddSubgroup.coe_add, Matrix.mul_add, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_add, map_add (f := _), neg_add,
        AddChar.map_add_eq_mul]
    have hper : ∀ g ∈ nF σ d.Y d.b, ∀ y, h (g + y) = h y := fun g hg y => by
      obtain ⟨T₀, hT₀⟩ := (mem_nF_iff g).1 hg
      rw [hadd]
      have hg1 : h g = 1 := by
        simp only [h, hT₀, ← incM_mul'', _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, trace_incM, trace_inclR, ← map_neg]
        exact d.std.2.1 _
      rw [hg1, one_mul]
    exact GlobalTheory.ThetaParsevalInner.setIntegral_eq_zero_of_twist lam (nF σ d.Y d.b) hfd hper
      (c := ⟨β₀, (mem_nA_iff hσ hb _).2 hβ₀⟩) (fun y => hadd _ y) hne
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

