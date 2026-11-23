module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRestrictedProductTupleMeasureMapLeftRightActio
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeamExLinCpt
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem seamEx_lin_cpt {K E : Type} [Field K] [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ) {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] E) (x : Fin n → K) :
    lin (fun k => j (Pi.single k 1)) (cpt σ x) = j x := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lin, cpt, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ]

theorem seamEx_coords {K V E ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup E] [Module ℂ E]
    (σ : K →+* ℂ) {n : ℕ} (j : V →ₛₗ[σ] E) (b : Module.Basis ι K V) (e : (Fin n → K) ≃ₗ[K] V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range (fun i => j (b i))) = ⊤) :
    ∃ c : E ≃ₗ[ℂ] (Fin n → ℂ), ∀ x, c.symm (cpt σ x) = j (e x) := by
  let g : (Fin n → K) →ₛₗ[σ] E := j.comp e.toLinearMap
  let f : (Fin n → ℂ) →ₗ[ℂ] E := lin (fun k => g (Pi.single k 1))
  have hf : ∀ x, f (cpt σ x) = j (e x) := fun x => seamEx_lin_cpt σ g x
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨cpt σ (e.symm (b i)), by rw [hf]; simp⟩
  haveI : Module.Finite K V := Module.Finite.equiv e
  haveI : Finite ι := Module.Finite.finite_basis b
  haveI : Fintype ι := Fintype.ofFinite ι
  let B : Module.Basis ι ℂ E := Module.Basis.mk hb.1 hb.2.ge
  haveI : Module.Finite ℂ E := Module.Finite.of_basis B
  have hr : Module.finrank ℂ (Fin n → ℂ) = Module.finrank ℂ E := by
    rw [Module.finrank_eq_card_basis B, ← Module.finrank_eq_card_basis b, ← e.finrank_eq]
    simp
  have hinj : Function.Injective f := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).2 hsurj
  exact ⟨(LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm, hf⟩

theorem seam_nonempty (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs)
    (s : Bool) (R : Read D X fc s) (cr : Crd A fc) : Nonempty (Seam R cr) := by
  choose cφ hφ using fun u => seamEx_coords D.what₂.embLL (D.jN u) (D.div.Nu u).b (R.eNu u) (D.jN_basis u)
  obtain ⟨c, hc⟩ := seamEx_coords D.what₂.embLL D.jEE D.div.RR.b R.eRR D.jEE_basis
  refine ⟨{ cφ := cφ
            cF := lin (fun k => R.jV (Pi.single k 1))
            eR :=
              { toFun := fun F => X.iC cr true Bs.μ0 (cjv s (c F))
                map_add' := fun F G => ?_
                map_smul' := fun a F => ?_ }
            cφ_eq := hφ
            cF_eq := fun y => seamEx_lin_cpt _ _ y
            eR_eq := fun y => ?_ }⟩
  · rw [← map_add (f := _)]
    congr 1
    funext i
    simp [cjv]
  · rw [← map_smul]
    congr 1
    funext i
    simp [cjv]
  · show X.iC cr true Bs.μ0 (cjv s (c _)) = _
    rw [← hc, LinearEquiv.apply_symm_apply]
    congr 1
    funext i
    simp [cjv, cpt, R.twist]

end GlobalTheory.Mem.SJ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdHermitianFibreProductChangeOfBasis
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.BasisX

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (e : E) :
    sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem hform_eq {A : Type} [CommRing A] (τ : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) : Formalism.UG.hform τ J x y = (τ ∘ x) ⬝ᵥ J.mulVec y := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] (τ : A →+* A) {M : ℕ} (J P : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) :
    Formalism.UG.hform τ J (P.mulVec x) (P.mulVec y) = Formalism.UG.hform τ (Formalism.UG.cT τ P * J * P) x y := by
  rw [hform_eq, hform_eq]
  have h : (τ ∘ P.mulVec x) = (P.map τ).mulVec (τ ∘ x) := by
    funext i
    exact RingHom.map_mulVec τ P x i
  rw [h, Formalism.UG.cT, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (τ ∘ x), Matrix.vecMul_transpose]

theorem qR_mulVec (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J P : Matrix (Fin M) (Fin M) E) (z : Fin M → R ⊗[F] E) :
    qR R σ J ((P.map (inclR R)).mulVec z) = qR R σ (Formalism.UG.cT (σ : E →+* E) P * J * P) z := by
  have h : JR R (Formalism.UG.cT (σ : E →+* E) P * J * P) =
      Formalism.UG.cT (sigR R σ) (P.map (inclR R)) * JR R J * P.map (inclR R) := by
    unfold JR
    rw [Matrix.map_mul, Matrix.map_mul]
    have hc : (Formalism.UG.cT (σ : E →+* E) P).map (inclR (F := F) R) =
        Formalism.UG.cT (sigR R σ) (P.map (inclR R)) := by
      ext i j
      exact (sigR_inclR R σ _).symm
    rw [hc]
  unfold qR hR
  rw [hform_mulVec, h]

end Alg

section Proj

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem prInf_inclR (e : E) : prInf (inclR (AF F) e) = inclR (Ainf F) e := by
  simp [prInf, inclR]

theorem prV_inclR (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV v (inclR (AF F) e) = inclR (Fv F v) e := by
  simp [prV, inclR]

end Proj

theorem fibAt_basis (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (hR : Nice R) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E)
    (lam : Measure (R ⊗[F] E)) (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hl : lam.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (h : FibAt R σ (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J *
      (P : Matrix (Fin M) (Fin M) E)) (tupMeas lam 1 M) ν β m) :
    FibAt R σ J (tupMeas lam 1 M) ν β
      (modu (R ⊗[F] E) (inclR R (P : Matrix (Fin M) (Fin M) E).det) •
        m.map (lrAct ((P : Matrix (Fin M) (Fin M) E).map (inclR R)) 1)) := by
  have hdet : ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R)).det =
      inclR R (P : Matrix (Fin M) (Fin M) E).det := (RingHom.map_det _ _).symm
  have hu : IsUnit ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R)).det := by
    rw [hdet]
    exact ((Matrix.isUnits_det_units P)).map _
  have := _root_.GlobalTheory.GaugeEx.fibAt_similitude F E σ R hR M _ J lam ν β 1 m _ hl hν hu isUnit_one
    (fun z => by rw [one_mul, qR_mulVec]) h
  rw [one_mul, (modu_basic R).2.2.1, inv_one, mul_one, hdet] at this
  exact this

theorem isStdX_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E) (β : F) (ν' : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) → IsStdX s σ J' β ν' → IsStdX s σ J β (ν'.map (lrAct ((P : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) 1)) := by
  intro F E _ _ _ _ _ σ hσ d b s M J J' P β ν' hJ ⟨mi, mv, hi, hv, hp⟩
  subst hJ
  obtain ⟨hni, hnv⟩ := nice_ainf_fv F
  have hdet : (P : Matrix (Fin M) (Fin M) E).det ≠ 0 := (Matrix.isUnits_det_units P).ne_zero
  obtain ⟨hfin, hone⟩ := _root_.GlobalTheory.GaugeEx.prod_modu_inclR F E σ hσ _ hdet
  refine ⟨_, _, fibAt_basis F E σ (Ainf F) hni M J P _ _ _ _ s.haar_lamI s.haar_nuI hi,
    fun v => fibAt_basis F E σ (Fv F v) (hnv v) M J P _ _ _ _ (s.haar_lamV v) (s.haar_nuV v) (hv v), ?_⟩
  have h1 := _root_.GlobalTheory.GaugeEx.ProdTransport.isProd_map_lrAct F E d b 1 M ν' mi mv
    (Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) P) 1 hp
  have hg : (Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) P).val =
      (P : Matrix (Fin M) (Fin M) E).map (inclR (AF F)) := rfl
  have hI : ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (AF F))).map prInf =
      (P : Matrix (Fin M) (Fin M) E).map (inclR (Ainf F)) := by
    ext i j
    exact prInf_inclR _
  have hV : ∀ v, ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (AF F))).map (prV v) =
      (P : Matrix (Fin M) (Fin M) E).map (inclR (Fv F v)) := by
    intro v
    ext i j
    exact prV_inclR v _
  have h1I : (1 : Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)).map prInf = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have h1V : ∀ v, (1 : Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)).map (prV v) = 1 := fun v =>
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [hg, Units.val_one, hI, hV, h1I, h1V] at h1
  have h2 := GlobalTheory.T.restrictedProduct_measure_smul_factors_eq_smul F E d b 1 M _ _ _
    (modu (Ainf F ⊗[F] E) (inclR (Ainf F) (P : Matrix (Fin M) (Fin M) E).det)) _ h1 hfin
  rw [hone, one_smul] at h2
  exact h2

end GlobalTheory.GaugeEx.BasisX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMapReferenceTupleGoodPartOntoRows
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem kOf_apply_self_on {K : Type} [Field K] (σ : K →+* ℂ) (a : K) : kOf σ (σ a) = a := by
  unfold kOf
  have h : ∃ b : K, σ b = σ a := ⟨a, rfl⟩
  rw [dite_eq_left h]
  exact σ.injective h.choose_spec

theorem relMat_self_on {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] E)
    (hf : Function.Injective f) : relMat f f = 1 := by
  ext i k
  have h : ∃ y, f y = f (Pi.single k 1) := ⟨_, rfl⟩
  have : solve f (f (Pi.single k 1)) = Pi.single k 1 := by
    unfold solve
    rw [dite_eq_left h]
    exact hf h.choose_spec
  simp only [relMat, Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply]

theorem kMat_one_on {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} : kMat σ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i k
  simp only [kMat, Matrix.map_apply, Matrix.one_apply]
  split_ifs
  · simpa using kOf_apply_self_on σ 1
  · simpa using kOf_apply_self_on σ 0

theorem thetaMap_referenceTuple_goodPart_onto_rows : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.IotaRd cr → R.ReadingFormsSpanGoodSubspace → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D Bs A X fc s R cr eV hF hI hV
  have h1 : X.rowMat cr true Bs.μ0 = 1 := by
    unfold CxData.rowMat CxData.rowMatC
    rw [relMat_self_on _ hF.h2.1, kMat_one_on]
  rw [eq_top_iff, ← D.jEE_basis.2, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨x, hx⟩ := R.eRR.surjective (D.div.RR.b i)
  obtain ⟨y, hy⟩ := hF.wf.Pq_surj Bs.μ0 x
  refine ⟨R.jV y, ?_, ?_⟩
  · have : R.jV y ∈ Submodule.span ℂ (Set.range R.jV) := Submodule.subset_span ⟨y, rfl⟩
    rw [hV] at this
    exact this
  · have := hI y
    rw [h1, Matrix.one_mulVec] at this
    exact this.trans (congrArg D.jEE ((congrArg R.eRR hy).trans hx))

end GlobalTheory.Mem.SJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WittTheoremAdelicOneVector
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.AdelicWitt

theorem qR_ratTup {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (b : Module.Basis (Fin 2) F E) (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F)
    (h : hE σ J (x 0) (x 0) = algebraMap F E β) :
    qR R σ J (ratTup (F := F) R x 0) = algebraMap F R β := by
  have h1 : hR R σ J (ratTup (F := F) R x 0) (ratTup (F := F) R x 0) =
      inclR (F := F) R (hE σ J (x 0) (x 0)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hR, hE, Formalism.UG.hform, map_sum, map_mul, ratTup, JR, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 2
  have h2 : inclR (F := F) R (algebraMap F E β) = algebraMap R (R ⊗[F] E) (algebraMap F R β) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes β
  rw [qR, h1, h, h2, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b),
    Fintype.card_fin, ← map_nsmul, ← map_mul]
  congr 1
  rw [nsmul_eq_mul]; push_cast; field_simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem prInf_sigR (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) :
    prInf (sigR (AF F) σ z) = sigR (Ainf F) σ (prInf z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add a c ha hc => simp only [map_add (f := _), ha, hc]

omit [NumberField E] in
theorem prV_sigR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    prV v (sigR (AF F) σ z) = sigR (Fv F v) σ (prV v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add a c ha hc => simp only [map_add (f := _), ha, hc]

omit [NumberField E] in
theorem prInf_inclR (e : E) : prInf (inclR (F := F) (AF F) e) = inclR (F := F) (Ainf F) e := by
  simp [prInf, inclR]

omit [NumberField E] in
theorem prV_inclR (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV v (inclR (F := F) (AF F) e) = inclR (F := F) (Fv F v) e := by
  simp [prV, inclR]

theorem ext_comp {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ} (X Y : Fin n → Fin M → AF F ⊗[F] E)
    (hi : ∀ a i, prInf (X a i) = prInf (Y a i))
    (hv : ∀ (v : HeightOneSpectrum (𝓞 F)) a i, prV v (X a i) = prV v (Y a i)) : X = Y := by
  apply (GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M).1.injective
  refine Prod.ext ?_ ?_
  · funext a i; exact hi a i
  · funext v a i; exact hv v a i

theorem mat_ext {d : ℕ} (b : Module.Basis (Fin d) F E) {M : ℕ}
    (X Y : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))
    (hi : X.map prInf = Y.map prInf)
    (hv : ∀ v : HeightOneSpectrum (𝓞 F), X.map (prV v) = Y.map (prV v)) : X = Y :=
  ext_comp b X Y (fun a i => congrFun (congrFun hi a) i) (fun v a i => congrFun (congrFun (hv v) a) i)

theorem exists_mat {d : ℕ} (b : Module.Basis (Fin d) F E) {M : ℕ}
    (Xi : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E))
    (Xv : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E))
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, Xv v i j ∈ intV b v) :
    ∃ X : Matrix (Fin M) (Fin M) (AF F ⊗[F] E), X.map prInf = Xi ∧ ∀ v, X.map (prV v) = Xv v := by
  have := ((Set.ext_iff.1 (GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b M M).2.1) (Xi, Xv)).2 h
  obtain ⟨X, hX⟩ := this
  exact ⟨X, congrArg Prod.fst hX, fun v => congrFun (congrArg Prod.snd hX) v⟩

theorem map_unit {A B : Type} [CommRing A] [CommRing B] {M : ℕ} (φ : A →+* B) (s : A →+* A)
    (t : B →+* B) (h : ∀ z, φ (s z) = t (φ z)) (X J : Matrix (Fin M) (Fin M) A) :
    (Formalism.UG.cT s X * J * X).map φ = Formalism.UG.cT t (X.map φ) * J.map φ * X.map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  exact h _

theorem exists_HA {d : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (gi : HA (Ainf F) σ J)
    (gv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j,
      (HA.mat (Fv F v) σ J (gv v)).val i j ∈ intV b v ∧
        (HA.mat (Fv F v) σ J (gv v)⁻¹).val i j ∈ intV b v) :
    ∃ g : HA (AF F) σ J, (HA.mat (AF F) σ J g).val.map prInf = (HA.mat (Ainf F) σ J gi).val ∧
      ∀ v, (HA.mat (AF F) σ J g).val.map (prV v) = (HA.mat (Fv F v) σ J (gv v)).val := by
  obtain ⟨X, hXi, hXv⟩ := exists_mat b (HA.mat (Ainf F) σ J gi).val
    (fun v => (HA.mat (Fv F v) σ J (gv v)).val) (h.mono fun v hv i j => (hv i j).1)
  obtain ⟨Y, hYi, hYv⟩ := exists_mat b (HA.mat (Ainf F) σ J gi).inv
    (fun v => (HA.mat (Fv F v) σ J (gv v)).inv) (h.mono fun v hv i j => (hv i j).2)
  have hXY : X * Y = 1 := by
    refine mat_ext b _ _ ?_ fun v => ?_
    · rw [Matrix.map_mul, hXi, hYi, Units.val_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Matrix.map_mul, hXv, hYv, Units.val_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hYX : Y * X = 1 := by
    refine mat_ext b _ _ ?_ fun v => ?_
    · rw [Matrix.map_mul, hXi, hYi, Units.inv_val, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Matrix.map_mul, hXv, hYv, Units.inv_val, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJi : (JR (F := F) (AF F) J).map prInf = JR (F := F) (Ainf F) J := by
    ext i j; exact prInf_inclR _
  have hJv : ∀ v, (JR (F := F) (AF F) J).map (prV v) = JR (F := F) (Fv F v) J := by
    intro v; ext i j; exact prV_inclR v _
  have hU : Formalism.UG.cT (sigR (AF F) σ) X * JR (F := F) (AF F) J * X = JR (F := F) (AF F) J := by
    refine mat_ext b _ _ ?_ fun v => ?_
    · rw [map_unit _ _ _ (prInf_sigR σ), hXi, hJi]
      exact (show HR (Ainf F) σ J from gi).2
    · rw [map_unit _ _ _ (prV_sigR σ v), hXv, hJv]
      exact (show HR (Fv F v) σ J from gv v).2
  exact ⟨(show HR (AF F) σ J from ⟨⟨X, Y, hXY, hYX⟩, hU⟩), hXi, hXv⟩

theorem witt_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ y : (Fin 1 → Fin M → AF F ⊗[F] E), qR (AF F) σ J (y 0) = algebraMap F (AF F) β → ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y := by
  intro F E _ _ _ _ _ σ hCM M J x β hJ hβ hx y hy
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hCM.2.2.1
  obtain ⟨hyi, hyv⟩ := ((_root_.GlobalTheory.GaugeEx.q_and_unitary_local_components F E σ M J).1 (y 0) β).1 hy
  have hu : IsUnit β := hβ.isUnit
  obtain ⟨gi, hgi⟩ := _root_.GlobalTheory.GaugeWittLoc.exists_smul_eq F E σ hCM (Ainf F) (_root_.GlobalTheory.GaugeEx.nice_ainf_fv F).1 M J hJ
    (algebraMap F _ β) (ratTup (F := F) (Ainf F) x) (projInf y) (hu.map _)
    (qR_ratTup b _ σ J x β hx) hyi
  have hlat : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, projV v (projFin y) ∈ latV b v := by
    have h := (GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E 2 b 1 M).2.1 ▸ Set.mem_range_self (f := fun X : (Fin 1 → Fin M → AF F ⊗[F] E) =>
      (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) y
    exact h
  have hae := GlobalTheory.T.integral_witt_theorem_almost_all_places F E σ hCM 2 b M J x β hJ hβ hx
  let P : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J → Prop := fun v g => ∀ i j,
      (HA.mat (Fv F v) σ J g).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J g⁻¹).val i j ∈ intV b v
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g : HA (Fv F v) σ J,
      g • ratTup (F := F) (Fv F v) x = projV v (projFin y) ∧
      ((∃ g' : HA (Fv F v) σ J, g' • ratTup (F := F) (Fv F v) x = projV v (projFin y) ∧ P v g') →
        P v g) := by
    intro v
    by_cases h : ∃ g' : HA (Fv F v) σ J,
        g' • ratTup (F := F) (Fv F v) x = projV v (projFin y) ∧ P v g'
    · obtain ⟨g, h1, h2⟩ := h
      exact ⟨g, h1, fun _ => h2⟩
    · obtain ⟨g, hg⟩ := _root_.GlobalTheory.GaugeWittLoc.exists_smul_eq F E σ hCM (Fv F v) ((_root_.GlobalTheory.GaugeEx.nice_ainf_fv F).2 v) M J hJ
        (algebraMap F _ β) (ratTup (F := F) (Fv F v) x) (projV v (projFin y)) (hu.map _)
        (qR_ratTup b _ σ J x β hx) (hyv v)
      exact ⟨g, hg, fun h' => absurd h' h⟩
  choose gv hgv hP using hloc
  obtain ⟨g, hi, hv⟩ := exists_HA b σ J gi gv (by
    filter_upwards [hlat, hae] with v h1 h2
    exact hP v (h2 _ h1 (hyv v)))
  refine ⟨g, ext_comp b _ _ (fun a i => ?_) (fun v a i => ?_)⟩
  · have h1 := congrFun (congrFun hgi a) i
    rw [projInf_apply] at h1
    rw [← h1]
    show prInf ((HA.mat (AF F) σ J g).val.mulVec (ratTup (F := F) (AF F) x a) i) =
      (HA.mat (Ainf F) σ J gi).val.mulVec (ratTup (F := F) (Ainf F) x a) i
    rw [RingHom.map_mulVec, hi]
    exact congrArg (fun w => (HA.mat (Ainf F) σ J gi).val.mulVec w i)
      (funext fun k => prInf_inclR (x a k))
  · have h1 := congrFun (congrFun (hgv v) a) i
    rw [projV_apply] at h1
    rw [← h1]
    show prV v ((HA.mat (AF F) σ J g).val.mulVec (ratTup (F := F) (AF F) x a) i) =
      (HA.mat (Fv F v) σ J (gv v)).val.mulVec (ratTup (F := F) (Fv F v) x a) i
    rw [RingHom.map_mulVec, hv]
    exact congrArg (fun w => (HA.mat (Fv F v) σ J (gv v)).val.mulVec w i)
      (funext fun k => prV_inclR v (x a k))

end GlobalTheory.AdelicWitt
end

