module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.RelReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.BasisReprMap
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR.PureA

section Repr

variable {k : Type} [Field k] {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra k R] [Algebra k S]
  [Algebra k B]

theorem basis_repr_map' {J : Type} (b : Module.Basis J k B) (ρ : R →ₐ[k] S) (x : R ⊗[k] B) (i : J) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map ρ (AlgHom.id k B) x) i =
      ρ ((Algebra.TensorProduct.basis R b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [hx, hy]

end Repr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def phiV (v : HeightOneSpectrum (𝓞 F)) : HeckeCharacterZeroLocus.SiegelWeilU.AF F →ₐ[F] HeckeCharacterZeroLocus.SiegelWeilU.Fv F v :=
  (HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)

def mapV (v : HeightOneSpectrum (𝓞 F)) :
    HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E →ₐ[F] HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E :=
  Algebra.TensorProduct.map (phiV v) (AlgHom.id F E)

theorem mapV_eq (v : HeightOneSpectrum (𝓞 F)) (x : HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) :
    mapV v x = Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def IntV (bs : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (z : HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) : Prop :=
  ∀ k, (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs).repr z k ∈ v.adicCompletionIntegers F

theorem ev_int_adele (a : HeckeCharacterZeroLocus.SiegelWeilU.AF F) :
    ∀ᶠ v in cofinite, phiV v a ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F := by
  filter_upwards [a.2.2] with v hv
  exact hv

theorem ev_int_F (f : F) :
    ∀ᶠ v in cofinite, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) f ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F := by
  filter_upwards [ev_int_adele (algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.AF F) f)] with v hv
  rwa [AlgHom.commutes] at hv

theorem intV_sum (bs : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι)
    (z : ι → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) (h : ∀ i ∈ s, IntV bs v (z i)) : IntV bs v (∑ i ∈ s, z i) := by
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  exact sum_mem fun i hi => h i hi k

theorem ev_mul_int (bs : Module.Basis (Fin 2) F E) (c : HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) :
    ∀ᶠ v in cofinite, ∀ z, IntV bs v z → IntV bs v (mapV v c * z) := by
  set bA := Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) bs
  have h1 : ∀ᶠ v in cofinite, ∀ k, phiV v (bA.repr c k) ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => ev_int_adele _
  have h2 : ∀ᶠ v in cofinite, ∀ k j l, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) (bs.repr (bs k * bs j) l) ∈
      (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun l => ev_int_F _
  filter_upwards [h1, h2] with v hv1 hv2
  intro z hz l
  set bV := Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs
  have hc : mapV v c = ∑ k, phiV v (bA.repr c k) • bV k := by
    conv_lhs => rw [← bV.sum_repr (mapV v c)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mapV, basis_repr_map']
  have hzz : z = ∑ j, bV.repr z j • bV j := (bV.sum_repr z).symm
  have hprod : bV.repr (mapV v c * z) l =
      ∑ k, ∑ j, (phiV v (bA.repr c k) * bV.repr z j) * algebraMap F _ (bs.repr (bs k * bs j) l) := by
    rw [hc]
    conv_lhs => rw [hzz]
    rw [Finset.sum_mul_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [smul_mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, bV, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply, one_smul]
  rw [hprod]
  exact sum_mem fun k _ => sum_mem fun j _ => mul_mem (mul_mem (hv1 k) (hz j)) (hv2 k j l)

def IntM (bs : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) : Prop := ∀ i j, IntV bs v (M i j)

theorem ev_matmul_int (bs : Module.Basis (Fin 2) F E) {q : ℕ} (A : Matrix (Fin q) (Fin q) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    ∀ᶠ v in cofinite, ∀ (p : ℕ) (M : Matrix (Fin p) (Fin q) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)),
      IntM bs v M → IntM bs v (M * A.map (mapV v)) := by
  have h : ∀ᶠ v in cofinite, ∀ i j, ∀ z, IntV bs v z → IntV bs v (mapV v (A i j) * z) :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_mul_int bs (A i j)
  filter_upwards [h] with v hv
  intro p M hM i j
  simp only [Matrix.mul_apply, Matrix.map_apply]
  refine intV_sum bs v _ _ fun l _ => ?_
  rw [mul_comm]
  exact hv l j _ (hM i l)

end PositivityTheory.SiegelWeilFormula.ThetaDictR.PureA

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Frames
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sig_invol (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [hcm.2.2.2, hcm.2.2.2, star_star]


omit [NumberField F] [NumberField E] in
theorem conj_form {ι κ : Type} [Fintype ι] [Fintype κ] (hσ : ∀ x, σ (σ x) = x) (M : Matrix κ κ E) (b : Matrix κ ι E)
    (s : E) (hM : ∀ k l, σ (M l k) = s * M k l) (i j : ι) :
    σ ((bᵀ * M * b.map σ) j i) = s * (bᵀ * M * b.map σ) i j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hM, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

omit [NumberField F] [NumberField E] in
theorem dbl_conj {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (hJ : ∀ i j, σ (J j i) = s * J i j)
    (k l : Fin n ⊕ Fin n) : σ (GlobalTheory.WeilM.dbl J l k) = s * GlobalTheory.WeilM.dbl J k l := by
  rcases k with k | k <;> rcases l with l | l <;> simp [GlobalTheory.WeilM.dbl, hJ]

theorem eps_of_form {d : SD σ} (R : RD d) (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (s : E)
    (hY : ∀ i j, σ (d.Y.J j i) = s * d.Y.J i j) : s * ((R.ε : ℤ) : E) = 1 := by
  have hσ := sig_invol hcm
  set i0 : Fin d.n := ⟨0, d.ok.hn⟩
  have key := conj_form hσ (GlobalTheory.WeilM.dbl d.Y.J) d.b.1 s (dbl_conj d.Y.J s hY) (Sum.inr i0) (Sum.inl i0)
  rw [R.hε] at key
  simpa using key.symm

theorem zeta_of_eps {d : SD σ} (R : RD d) :
    (((R.ε : ℤ) : E) = -1 → R.ζ = 1) ∧ (((R.ε : ℤ) : E) = 1 → R.ζ = Complex.I) := by
  have h2 : (1 : E) ≠ -1 := by
    intro h
    have : (2 : E) = 0 := by linear_combination h
    exact two_ne_zero this
  constructor
  · intro h
    rcases R.hζ with ⟨_, hz⟩ | ⟨he, _⟩
    · exact hz
    · rw [he] at h; exact absurd (by simpa using h) h2
  · intro h
    rcases R.hζ with ⟨he, _⟩ | ⟨_, hz⟩
    · rw [he] at h; exact absurd (by simpa using h.symm) h2
    · exact hz

theorem exists_J_ne (d : SD σ) : ∃ i j, d.A.J i j ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hJ : d.A.J = 0 := Matrix.ext hcon
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hm := d.ok.hm
  have fin : ∀ (A : Matrix (Fin d.m) (Fin d.r ⊕ Fin d.s) ℂ),
      d.r + d.s = d.m → Aᵀ * (0 : Matrix (Fin d.m) (Fin d.m) ℂ) * A.map star = Matrix.fromBlocks 1 0 0 (-1) → False := by
    intro A hrs hA
    rw [Matrix.mul_zero, Matrix.zero_mul] at hA
    rcases Nat.eq_zero_or_pos d.r with hr | hr
    · have hs : 0 < d.s := by omega
      have := congrFun (congrFun hA (Sum.inr ⟨0, hs⟩)) (Sum.inr ⟨0, hs⟩)
      simp at this
    · have := congrFun (congrFun hA (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)
      simp at this
  rcases d.ok.sign with ⟨hA, _⟩ | ⟨hA, _⟩
  · obtain ⟨hrs, A, hA'⟩ := hA.sig (InfinitePlace.mk (φ.comp (algebraMap F E)))
    rw [hJ] at hA'
    exact fin A hrs (by simpa using hA')
  · obtain ⟨hrs, A, hA'⟩ := hA.sig (InfinitePlace.mk (φ.comp (algebraMap F E)))
    rw [hJ] at hA'
    exact fin A hrs (by simpa using hA')

theorem not_herm_skew (d : SD σ) (hA : d.A.IsHerm σ d.B d.r d.s) (hA' : d.A.IsSkew σ d.B d.r d.s) : False := by
  obtain ⟨i, j, hij⟩ := exists_J_ne d
  have h1 := hA.herm i j
  have h2 := hA'.skew i j
  rw [h1] at h2
  have : (2 : E) * d.A.J i j = 0 := by linear_combination h2
  rcases mul_eq_zero.1 this with h | h
  · exact two_ne_zero h
  · exact hij h

theorem zeta_of_sign' {d : SD σ} (R : RD d) :
    (d.A.IsHerm σ d.B d.r d.s → R.ζ = 1) ∧ (d.A.IsSkew σ d.B d.r d.s → R.ζ = Complex.I) := by
  have hcm := d.ok.good.cm
  constructor
  · intro hA
    rcases d.ok.sign with ⟨_, hY⟩ | ⟨hA', _⟩
    · refine (zeta_of_eps R).1 ?_
      have := eps_of_form R hcm (-1) (fun i j => by rw [hY]; ring)
      linear_combination -this
    · exact (not_herm_skew d hA hA').elim
  · intro hA
    rcases d.ok.sign with ⟨hA', _⟩ | ⟨_, hY⟩
    · exact (not_herm_skew d hA' hA).elim
    · refine (zeta_of_eps R).2 ?_
      have := eps_of_form R hcm 1 (fun i j => by rw [hY]; ring)
      linear_combination this

theorem eta_zeta' {d : SD σ} (R : RD d) {η : E} (hη : η ≠ 0) (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    (σ η = η ∧ R.ζ = 1) ∨ (σ η = -η ∧ R.ζ = Complex.I) := by
  obtain ⟨i, j, hij⟩ := exists_J_ne d
  rcases d.ok.sign with ⟨hA, _⟩ | ⟨hA, _⟩
  · left
    refine ⟨?_, (zeta_of_sign' R).1 hA⟩
    have h := herm i j
    rw [map_mul, hA.herm] at h
    exact mul_right_cancel₀ hij h
  · right
    refine ⟨?_, (zeta_of_sign' R).2 hA⟩
    have h := herm i j
    rw [map_mul, hA.skew] at h
    have : (σ η + η) * d.A.J i j = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h' | h'
    · linear_combination h'
    · exact (hij h').elim

end PositivityTheory.SiegelWeilFormula.ThetaDictR

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Places
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def archimedeanEmbeddingTensor (B : Base F E) (w : InfinitePlace F) : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ :=
  (infEmb (B.emb w)).comp (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)).toRingHom

theorem thW_eq (B : Base F E) (w : InfinitePlace F) (z : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E) :
    thW B w z = starRingEnd ℂ (archimedeanEmbeddingTensor B w z) := rfl

theorem archimedean_embedding_tmul (B : Base F E) (w : InfinitePlace F) (a : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (x : E) :
    archimedeanEmbeddingTensor B w (a ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding w (a w) * (B.emb w).1 x := rfl

theorem thW_th' (B : Base F E) (w : InfinitePlace F) (y : AE F E) :
    thW B w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (B.emb w) y) := by
  have h : Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = compInf F E w y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  show starRingEnd ℂ (infEmb (B.emb w) (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y))) = _
  rw [h]
  rfl

theorem archimedean_embedding_family (B : Base F E) :
    Formalism.IndefR.DatumF.IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) (archimedeanEmbeddingTensor B) := by
  intro w
  refine ⟨fun x => ?_, ?_⟩
  · rw [archimedean_embedding_tmul]
    show InfinitePlace.Completion.extensionEmbedding w 1 * (B.emb w).1 x = (B.emb w).1 x
    rw [map_one, one_mul]
  · have : (fun a : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F => archimedeanEmbeddingTensor B w (a ⊗ₜ[F] (1 : E))) =
        fun a => InfinitePlace.Completion.extensionEmbedding w (a w) := by
      funext a; rw [archimedean_embedding_tmul, map_one, mul_one]
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

theorem thW_infEmb (B : Base F E) (w : InfinitePlace F) :
    Formalism.MainNotions.StandardLattice.IsInfEmb (ComplexEmbedding.conjugate (B.emb w).1) (thW B w) := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [thW_eq, (archimedean_embedding_family B w).1 x]
    rfl
  · exact Complex.continuous_conj.comp (archimedean_embedding_family B w).2

theorem isCMFam_conj (B : Base F E) (h : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) :
    GlobalTheory.Mem.Vol.IsCMFam (fun w : InfinitePlace F => ComplexEmbedding.conjugate (B.emb w).1) := by
  have hT := GlobalTheory.BotLValue.isCMType_embOver h B.emb
  have cc : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := fun φ => star_star φ
  beta_reduce at hT
  constructor
  · intro i j e
    simp only [InfinitePlace.mk_conjugate_eq] at e
    obtain ⟨k, -, hk⟩ := hT (B.emb i).1
    have hi := hk i (Or.inl rfl)
    have hj : j = k := by
      refine hk j ?_
      rcases InfinitePlace.mk_eq_iff.1 e with e' | e'
      · exact Or.inl e'
      · right
        show (B.emb i).1 = ComplexEmbedding.conjugate (B.emb j).1
        rw [← e', cc]
    rw [hi, hj]
  · intro φ
    obtain ⟨k, hk, -⟩ := hT φ.embedding
    beta_reduce at hk
    refine ⟨k, ?_⟩
    simp only [InfinitePlace.mk_conjugate_eq]
    rcases hk with e | e
    · rw [← e, InfinitePlace.mk_embedding]
    · rw [show (B.emb k).1 = ComplexEmbedding.conjugate φ.embedding by
          rw [e, cc],
        InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

theorem isPlaces_thW' (B : Base F E) (hB : B.IsGood σ) : Gen.IsPlaces σ B.ψ (thW B) (fun _ => -1) := by
  have : IsTotallyReal F := hB.cm.1
  refine ⟨fun w => GlobalTheory.Mem.VolExists.infEmb_continuous (thW_infEmb B w),
    GlobalTheory.Mem.VolExists.infEmb_bijective hB.cm (isCMFam_conj B hB.cm) (fun w => thW_infEmb B w),
    fun w z => GlobalTheory.Mem.VolExists.infEmb_sigR hB.cm (thW_infEmb B w) z, fun _ => by norm_num, fun x => ?_⟩
  have hs := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).2.2 (archimedeanEmbeddingTensor B) (archimedean_embedding_family B) x
  have hs' : B.ψ ((x, 0) : AF F) = _ := hs
  change B.ψ ((x, 0) : AF F) = _
  rw [hs']
  congr 1
  have hr : ∀ w, starRingEnd ℂ (archimedeanEmbeddingTensor B w (x ⊗ₜ[F] (1 : E))) = archimedeanEmbeddingTensor B w (x ⊗ₜ[F] (1 : E)) := fun w => by
    rw [archimedean_embedding_tmul, map_one, mul_one, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w),
      Complex.conj_ofReal]
  simp only [thW_eq, hr]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

end PositivityTheory.SiegelWeilFormula.ThetaDictR

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.ProjInf
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR.PureB

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem map_star_mul {p q r : Type} [Fintype q] (A : Matrix p q ℂ) (B : Matrix q r ℂ) :
    (A * B).map star = A.map star * B.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem crd_eq {d : SD σ} (R : RD d) (u : GL (Fin d.n) (AE F E)) (η : E)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ))
    (th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y))
    (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star)
    (g : InfinitePlace F → GL (Fin d.n) ℂ)
    (gc : ∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1)
    (w : InfinitePlace F) (X : Fin d.n → Fin d.m → AF F ⊗[F] E) :
    Gen.crd (θ w) (fr w) (g w) (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) = R.loc w (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) := by
  set c : ℂ := ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hcdef
  have hm : Nonempty (Fin d.m) := ⟨⟨0, d.ok.hm⟩⟩
  have hc : c ≠ 0 := by
    intro h0
    have h1 := frc w
    rw [← hcdef, h0, zero_smul] at h1
    have h2 : ((fr w)⁻¹).1 * (fr w).1 = 1 := Units.inv_mul (fr w)
    rw [h1, Matrix.mul_zero] at h2
    exact zero_ne_one h2
  have hfr : ((fr w)⁻¹).1 = c⁻¹ • (((R.fr w)⁻¹).1).map star := by
    refine Units.inv_eq_of_mul_eq_one_left ?_
    rw [frc w, ← hcdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, ← map_star_mul,
      Units.inv_mul]
    exact Matrix.map_one _ (star_zero _) (star_one _)
  have hN : ((d.cw w u.1)ᵀ).map star * ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star = 1 := by
    rw [← map_star_mul, ← Matrix.transpose_mul]
    have : d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1 * d.cw w u.1 = 1 := by
      unfold SD.cw
      rw [← Matrix.map_mul (f := piInf (d.B.emb w)), Units.inv_mul]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [this, Matrix.transpose_one]
    exact Matrix.map_one _ (star_zero _) (star_one _)
  have hg : (g w).1 = c • ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star := by
    calc (g w).1 = (g w).1 * (((d.cw w u.1)ᵀ).map star * ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star) := by
          rw [hN, Matrix.mul_one]
      _ = c • ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star := by
          rw [← Matrix.mul_assoc, gc w, ← hcdef, Matrix.smul_mul, Matrix.one_mul]
  have hX : Matrix.of (fun a j => θ w (HeckeCharacterZeroLocus.SiegelWeilU.projInf X j a)) = (d.cw w (toMx X)).map star := by
    ext a j
    simp only [Matrix.of_apply, HeckeCharacterZeroLocus.SiegelWeilU.projInf, th, SD.cw, Matrix.map_apply, toMx]
  have hZ : d.cw w (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) =
      d.cw w (toMx X) * (d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ := by
    unfold SD.cw
    rw [Matrix.map_mul (f := piInf (d.B.emb w)), Matrix.transpose_map]
  unfold Gen.crd RD.loc
  rw [hfr, hX, hg, hZ, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc, one_smul,
    map_star_mul, map_star_mul, Matrix.mul_assoc]

end PositivityTheory.SiegelWeilFormula.ThetaDictR.PureB

end
end

