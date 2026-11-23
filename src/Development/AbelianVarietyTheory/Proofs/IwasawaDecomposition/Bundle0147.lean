module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0138
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0139

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNiceLocalFieldProductRingInfiniteAdelesComplet
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem exists_local_sqrt_nontrivial (K : Type) [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) :
    ∃ U : Set K, IsOpen U ∧ (1 : K) ∈ U ∧ ∃ s : K → K, ContinuousOn s U ∧ s 1 = 1 ∧
      ∀ u ∈ U, s u * s u = u := by
  have hd : HasStrictDerivAt (fun x : K => x * x) 2 1 := by
    have := (hasStrictDerivAt_id (1 : K)).mul (hasStrictDerivAt_id (1 : K))
    have h11 : (1 : K) * id 1 + id 1 * 1 = 2 := by simp; norm_num
    rw [h11] at this
    exact this
  have hF := hd.hasStrictFDerivAt_equiv h2
  let e := hF.toOpenPartialHomeomorph
  have he : ∀ x, e x = x * x := fun x => rfl
  have h1 : (1 : K) ∈ e.source := hF.mem_toOpenPartialHomeomorph_source
  have h1' : e 1 = 1 := by rw [he, mul_one]
  refine ⟨e.target, e.open_target, h1' ▸ e.map_source h1, e.symm, e.continuousOn_symm, ?_, ?_⟩
  · have := e.left_inv h1
    rwa [h1'] at this
  · intro u hu
    rw [← he]; exact e.right_inv hu

theorem exists_local_sqrt (K : Type) [NormedField K] [CompleteSpace K] (h2 : (2 : K) ≠ 0) :
    ∃ U : Set K, IsOpen U ∧ (1 : K) ∈ U ∧ ∃ s : K → K, ContinuousOn s U ∧ s 1 = 1 ∧
      ∀ u ∈ U, s u * s u = u := by
  by_cases h : ∃ x : K, 1 < ‖x‖
  · let : NontriviallyNormedField K := { (inferInstance : NormedField K) with non_trivial := h }
    exact exists_local_sqrt_nontrivial K h2
  · push Not at h
    refine ⟨Metric.ball 1 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, fun _ => 1,
      continuousOn_const, rfl, fun u hu => ?_⟩
    rw [mem_ball_iff_norm] at hu
    by_contra hne
    have h0 : u - 1 ≠ 0 := fun h0 => hne (by rw [sub_eq_zero.1 h0, mul_one])
    have h3 := h (u - 1)⁻¹
    rw [norm_inv, inv_le_one₀ (norm_pos_iff.2 h0)] at h3
    exact absurd hu (not_lt.2 h3)

theorem nice_field (K : Type) [NormedField K] [CompleteSpace K] (h2 : (2 : K) ≠ 0) : Nice K :=
  ⟨inferInstance, inferInstance, inferInstance, exists_local_sqrt K h2⟩

theorem nice_pi {ι : Type} [Fintype ι] (K : ι → Type) [∀ i, NormedField (K i)]
    [∀ i, CompleteSpace (K i)] (h2 : ∀ i, (2 : K i) ≠ 0) : Nice (∀ i, K i) := by
  refine ⟨inferInstance, inferInstance, ⟨Units.isOpenEmbedding_val⟩, ?_⟩
  choose U hU h1 s hs hs1 hss using fun i => exists_local_sqrt (K i) (h2 i)
  refine ⟨Set.univ.pi U, isOpen_set_pi Set.finite_univ fun i _ => hU i, fun i _ => h1 i,
    fun x i => s i (x i), ?_, funext fun i => hs1 i, fun u hu => funext fun i => hss i _ (hu i trivial)⟩
  exact continuousOn_pi.2 fun i => (hs i).comp (continuous_apply i).continuousOn
    fun x hx => hx i trivial

theorem nice_ainf_fv : ∀ (F : Type) [Field F] [NumberField F],
    Nice (Ainf F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Nice (Fv F v) := by
  intro F _ _
  refine ⟨nice_pi (fun w : InfinitePlace F => w.Completion) fun w => ?_, fun v => nice_field _ ?_⟩
  · have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
    exact two_ne_zero
  · have : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
    exact two_ne_zero

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsAll
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2


set_option maxHeartbeats 1600000 in
theorem laws_all : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (Q : PerIn I) (hQ : Q.Ok) (Pl : Rows.Places K), J.Laws emb σ hc ∧ FmLaws J Q emb σ hc Pl hI hQ := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc hF hI hJ Q hQ Pl
  have hd := _root_.GlobalTheory.Mem.Col2.DiaRep.diamond_rep I J emb σ hc hF hI hJ
  have hfam : ∀ i, ((I.S i).fam emb (lamT hc i)).Ok := fun i => _root_.GlobalTheory.Mem.Col2.fam_ok (I.S i) emb σ (lamT hc i) hF (hI.step i)
  have hfamP : (Q.S'.fam emb Q.sgT).Ok := _root_.GlobalTheory.Mem.Col2.fam_ok Q.S' emb σ Q.sgT hF hQ.step
  refine ⟨⟨hd.1, hd.2, GlobalTheory.T.complexForms_finiteDimensional (I.S 0) emb σ (lamT hc 0) hF (hI.step 0), GlobalTheory.T.levelPrimeDiamond_preserves_complexForms I J emb σ hc hF hI hJ⟩, ?_⟩
  exact
    { fam := hfam
      famP := hfamP
      lev := fun i => _root_.GlobalTheory.Mem.Col2.TDat.laws_of_ok (J.A i) J.T (hI.step i) (hJ.lev i)
      good := fun i => GlobalTheory.T.weight_law_good_of_field_embedding (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      basis := fun i => _root_.GlobalTheory.Mem.Col2.lawBasis_all (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      norm := fun i => letI := I.clFin hI i; _root_.GlobalTheory.Mem.Col2.GStep.lawNorm (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      goodP := GlobalTheory.T.weight_law_good_of_field_embedding Q.S' emb σ Q.sgT hF hQ.step _
      basisP := _root_.GlobalTheory.Mem.Col2.lawBasis_all Q.S' emb σ Q.sgT hF hQ.step _
      normP := letI := Q.clFin hQ; _root_.GlobalTheory.Mem.Col2.GStep.lawNorm Q.S' emb σ Q.sgT hF hQ.step _
      dia_lat := _root_.GlobalTheory.Mem.Col2.DiaLat.dia_lat I J emb σ hc hF hI hJ _
      B_span := fun i w P => _root_.GlobalTheory.Mem.BSpan.span_locW_BLat I J emb σ hc hF hI hJ Pl i _ w P }

end GlobalTheory.Mem.Col2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowZeroMulRightIff
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Datum
open scoped Matrix

namespace GlobalTheory.TwistDatumRight

section
variable {κ : Type} [CommRing κ] {b r : ℕ}

theorem topL_mul_right (y : Matrix (Fin b) (Fin r) κ) (h : Matrix (Fin r) (Fin r) κ) :
    topL r (y * h) = topL r y * h := by
  ext i j
  by_cases hi : i.val < b
  · simp [topL, hi, Matrix.mul_apply]
  · simp [topL, hi, Matrix.mul_apply]

theorem lowZero_mul_right {y : Matrix (Fin b) (Fin r) κ} (hy : LowZero r y) (h : Matrix (Fin r) (Fin r) κ) :
    LowZero r (y * h) := by
  intro i j hi _
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun k _ => by rw [hy i k hi k.2, zero_mul]

theorem lowZero_mul_right_iff (y : Matrix (Fin b) (Fin r) κ) (h : GL (Fin r) κ) :
    LowZero r (y * h.1) ↔ LowZero r y := by
  refine ⟨fun H => ?_, fun H => lowZero_mul_right H _⟩
  have := lowZero_mul_right H (h⁻¹).1
  rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this

theorem det_topL_mul_right (y : Matrix (Fin b) (Fin r) κ) (h : GL (Fin r) κ) :
    (topL r (y * h.1)).det = ((Matrix.GeneralLinearGroup.det h : κˣ) : κ) * (topL r y).det := by
  rw [topL_mul_right, Matrix.det_mul, mul_comm, Matrix.GeneralLinearGroup.val_det_apply]

end

theorem omegaQ_mul_right : ∀ (D : D7) (b r : ℕ) (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (h : ∀ PP : Pl D.host.E, GL (Fin r) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin r) (kP PP)), (∀ PP ∈ Q, y' PP = y PP * (h PP).1) → omegaQ Q r ξ (-1) y' = ((∏ PP ∈ Q, ξ PP (Matrix.GeneralLinearGroup.det (h PP)) : ℂˣ) : ℂ)⁻¹ * omegaQ Q r ξ (-1) y := by
  intro D b r Q ξ h y y' hy
  have hiff : (∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det) ↔
      (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) := by
    refine forall₂_congr fun PP hP => ?_
    rw [hy PP hP, lowZero_mul_right_iff, det_topL_mul_right, Units.isUnit_units_mul]
  unfold omegaQ
  by_cases c : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
  · rw [dite_eq_left c, dite_eq_left (hiff.2 c), ← Finset.prod_attach Q, Units.coe_prod, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have e : ((hiff.2 c) PP.1 PP.2).2.unit =
        Matrix.GeneralLinearGroup.det (h PP.1) * (c PP.1 PP.2).2.unit := by
      apply Units.ext
      rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hy PP.1 PP.2, det_topL_mul_right]
    rw [e, map_mul, Units.val_mul, zpow_neg_one, zpow_neg_one, mul_inv]
  · rw [dite_eq_right c, dite_eq_right (fun h' => c (hiff.1 h')), mul_zero]

end GlobalTheory.TwistDatumRight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponents
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeGlue

theorem polishSpace_addCommGroup (G : Type) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] :
    PolishSpace G := by
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace G := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace G
  haveI : (uniformity G).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  infer_instance

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem repr_map (φ : R →ₐ[F] R') (z : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem tens_ext {z z' : R ⊗[F] E} (h : ∀ k, (Algebra.TensorProduct.basis R b).repr z k =
    (Algebra.TensorProduct.basis R b).repr z' k) : z = z' :=
  (Algebra.TensorProduct.basis R b).ext_elem h

theorem exists_repr (c : Fin d → R) :
    ∃ z : R ⊗[F] E, ∀ k, (Algebra.TensorProduct.basis R b).repr z k = c k :=
  ⟨(Algebra.TensorProduct.basis R b).equivFun.symm c, fun k => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]⟩

include b in
theorem continuous_map [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace R']
    [IsTopologicalRing R'] (φ : R →ₐ[F] R') (hφ : Continuous φ) :
    Continuous (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have h1 : Continuous (Algebra.TensorProduct.basis R b).equivFun :=
    IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
  have h2 : Continuous (Algebra.TensorProduct.basis R' b).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R' b).equivFun.symm.toLinearMap
  have h3 : Continuous fun z : R ⊗[F] E => fun k => φ ((Algebra.TensorProduct.basis R b).equivFun z k) :=
    continuous_pi fun k => hφ.comp ((continuous_apply k).comp h1)
  refine (h2.comp h3).congr fun z => ?_
  simp only [Function.comp_apply]
  rw [LinearEquiv.symm_apply_eq]
  funext k
  simp only [Module.Basis.equivFun_apply, repr_map]

end Coord

section Adele

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) {n M : ℕ}

theorem repr_projInf (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).1 :=
  repr_map b (fstA F) _ k

theorem repr_projV (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n)
    (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k =
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2 v :=
  (repr_map b (evalV F v) _ k).trans (congrArg (evalV F v) (repr_map b (sndA F) _ k))

theorem continuous_fstA : Continuous (fstA F) := continuous_fst

theorem continuous_sndA : Continuous (sndA F) := continuous_snd

theorem continuous_evalV (v : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F v) :=
  RestrictedProduct.continuous_eval v

theorem adele_ext {x y : AF F} (h1 : x.1 = y.1) (h2 : ∀ v, x.2 v = y.2 v) : x = y :=
  Prod.ext h1 (RestrictedProduct.ext _ _ h2)

theorem exists_adele (x : Ainf F) (y : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (hy : ∀ᶠ v in Filter.cofinite, y v ∈ v.adicCompletionIntegers F) :
    ∃ z : AF F, z.1 = x ∧ ∀ v, z.2 v = y v :=
  ⟨pairA F x ⟨y, hy⟩, rfl, fun _ => rfl⟩

include b in
theorem continuous_projInf : Continuous (projInf (F := F) (E := E) (M := M) (n := n)) :=
  continuous_pi fun a => continuous_pi fun i =>
    (continuous_map b (fstA F) continuous_fstA).comp
      ((continuous_apply i).comp (continuous_apply a))

include b in
theorem continuous_projV (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun X : (Fin n → Fin M → AF F ⊗[F] E) => projV v (projFin X) :=
  continuous_pi fun a => continuous_pi fun i =>
    (continuous_map b (evalV F v) (continuous_evalV v)).comp
      ((continuous_map b (sndA F) continuous_sndA).comp
        ((continuous_apply i).comp (continuous_apply a)))

include b in
theorem injective_glue : Function.Injective (fun X : (Fin n → Fin M → AF F ⊗[F] E) =>
    (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) := by
  intro X X' h
  have h1 : projInf X = projInf X' := congrArg Prod.fst h
  have h2 : ∀ v, projV v (projFin X) = projV v (projFin X') := congrFun (congrArg Prod.snd h)
  funext a i
  refine tens_ext b fun k => adele_ext ?_ fun v => ?_
  · rw [← repr_projInf, ← repr_projInf, h1]
  · rw [← repr_projV, ← repr_projV, h2]

theorem range_glue : Set.range (fun X : (Fin n → Fin M → AF F ⊗[F] E) =>
    (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) =
    {Y | ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Y.2 v ∈ latV b v} := by
  ext Y
  constructor
  · rintro ⟨X, rfl⟩
    have : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ a i k,
        ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2 v ∈ v.adicCompletionIntegers F :=
      Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k =>
        ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2.2
    filter_upwards [this] with v hv a i k
    rw [repr_projV]
    exact hv a i k
  · intro hY
    choose c hc1 hc2 using fun (a : Fin n) (i : Fin M) (k : Fin d) =>
      exists_adele ((Algebra.TensorProduct.basis (Ainf F) b).repr (Y.1 a i) k)
        (fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (Y.2 v a i) k)
        (Filter.Eventually.mono hY fun v hv => hv a i k)
    choose X hX using fun a i => exists_repr b (c a i)
    have h1 : projInf X = Y.1 := by
      funext a i
      refine tens_ext b fun k => ?_
      rw [repr_projInf, hX, hc1]
    have h2 : ∀ v, projV v (projFin X) = Y.2 v := fun v => by
      funext a i
      refine tens_ext b fun k => ?_
      rw [repr_projV, hX, hc2]
    exact ⟨X, Prod.ext h1 (funext h2)⟩

end Adele

theorem adelicTuple_measurableEmbedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), MeasurableEmbedding (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) ∧ Set.range (fun X : (Fin n → Fin M → AF F ⊗[F] E) => (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) = {Y | ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Y.2 v ∈ latV b v} ∧ Continuous (projInf (F := F) (E := E) (M := M) (n := n)) ∧ ∀ v : HeightOneSpectrum (𝓞 F), Continuous fun X : (Fin n → Fin M → AF F ⊗[F] E) => projV v (projFin X) := by
  intro F E _ _ _ _ _ d b n M
  refine ⟨?_, range_glue b, continuous_projInf b, continuous_projV b⟩
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  haveI : PolishSpace (Fin n → Fin M → AF F ⊗[F] E) := polishSpace_addCommGroup _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (Fv F v ⊗[F] E) := fun v =>
    inferInstance
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v =>
    inferInstance
  haveI : BorelSpace (∀ v : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F v ⊗[F] E) :=
    Pi.borelSpace
  haveI : BorelSpace (Fin n → Fin M → Ainf F ⊗[F] E) := inferInstance
  exact ((continuous_projInf b).prodMk (continuous_pi (continuous_projV b))).measurableEmbedding
    (injective_glue b)

end GlobalTheory.GaugeGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableSetOrbitExistsMeasurableSection
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.OrbitSection

theorem exists_section_real {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (C : Set ℝ) [CompactSpace C] (c₀ : C) (f : C → X) (hf : Continuous f) :
    ∃ τ : X → C, Measurable τ ∧ ∀ y ∈ Set.range f, f (τ y) = y := by
  have h : ∀ y : X, ∃ c : C, (y ∈ Set.range f → f c = y ∧ ∀ c', f c' = y → (c : ℝ) ≤ c') ∧
      (y ∉ Set.range f → c = c₀) := by
    intro y
    by_cases hy : y ∈ Set.range f
    · have hc : IsCompact (f ⁻¹' {y}) := (isClosed_singleton.preimage hf).isCompact
      obtain ⟨c, hc1, hc2⟩ := hc.exists_isMinOn (f := fun c : C => (c : ℝ)) hy
        continuous_subtype_val.continuousOn
      exact ⟨c, fun _ => ⟨hc1, fun c' h' => hc2 h'⟩, fun h => absurd hy h⟩
    · exact ⟨c₀, fun h => absurd h hy, fun _ => rfl⟩
  choose τ h1 h2 using h
  refine ⟨τ, ?_, fun y hy => (h1 y hy).1⟩
  have hm : Measurable fun y => (τ y : ℝ) := by
    refine measurable_of_Iic fun a => ?_
    have he : (fun y => (τ y : ℝ)) ⁻¹' Set.Iic a =
        f '' {c : C | (c : ℝ) ≤ a} ∪ ((Set.range f)ᶜ ∩ {_y | (c₀ : ℝ) ≤ a}) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff, Set.mem_setOf_eq]
      by_cases hy : y ∈ Set.range f
      · constructor
        · intro h
          exact Or.inl ⟨τ y, h, (h1 y hy).1⟩
        · rintro (⟨c, hc, hcy⟩ | h)
          · exact ((h1 y hy).2 c hcy).trans hc
          · exact absurd hy h.1
      · rw [h2 y hy]
        constructor
        · intro h
          exact Or.inr ⟨hy, h⟩
        · rintro (⟨c, -, hcy⟩ | h)
          · exact absurd ⟨c, hcy⟩ hy
          · exact h.2
    rw [he]
    refine MeasurableSet.union ?_ (MeasurableSet.inter ?_ (MeasurableSet.const _))
    · exact ((isClosed_le continuous_subtype_val continuous_const).isCompact.image
        hf).isClosed.measurableSet
    · exact (isCompact_range hf).isClosed.measurableSet.compl
  exact hm.subtype_mk (h := fun y => (τ y).2)

theorem exists_section_compact {K X : Type} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (f : K → X) (hf : Continuous f) :
    ∃ τ : X → K, Measurable τ ∧ ∀ y ∈ Set.range f, f (τ y) = y := by
  letI := TopologicalSpace.metrizableSpaceMetric K
  obtain ⟨p, hp, hps⟩ := exists_nat_bool_continuous_surjective_of_compact K
  have : CompactSpace cantorSet := isCompact_iff_compactSpace.1 isCompact_cantorSet
  let q : cantorSet → K := p ∘ cantorSetHomeomorphNatToBool
  have hq : Continuous q := hp.comp cantorSetHomeomorphNatToBool.continuous
  have hqs : Function.Surjective q := hps.comp cantorSetHomeomorphNatToBool.surjective
  obtain ⟨τ, h1, h2⟩ := exists_section_real cantorSet ⟨0, zero_mem_cantorSet⟩ (f ∘ q)
    (hf.comp hq)
  refine ⟨q ∘ τ, hq.measurable.comp h1, fun y hy => h2 y ?_⟩
  rwa [hqs.range_comp]

theorem measurableSet_orbit_and_exists_section : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X] (x₀ : X), MeasurableSet {y : X | ∃ g : G, g • x₀ = y} ∧ ∃ s : X → G, Measurable s ∧ ∀ y, (∃ g : G, g • x₀ = y) → s y • x₀ = y := by
  intro G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x₀
  classical
  have hπ : Continuous fun g : G => g • x₀ := by fun_prop
  let K : ℕ → Set G := fun n => insert 1 (compactCovering G n)
  have hK : ∀ n, IsCompact (K n) := fun n => (isCompact_compactCovering G n).insert 1
  have hKU : ∀ g : G, ∃ n, g ∈ K n := fun g => by
    obtain ⟨n, hn⟩ := exists_mem_compactCovering g
    exact ⟨n, Or.inr hn⟩
  let A : ℕ → Set X := fun n => (fun g : G => g • x₀) '' K n
  have hA : ∀ n, MeasurableSet (A n) := fun n => ((hK n).image hπ).isClosed.measurableSet
  have hO : MeasurableSet {y : X | ∃ g : G, g • x₀ = y} := by
    have : {y : X | ∃ g : G, g • x₀ = y} = ⋃ n, A n := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨g, hg⟩
        obtain ⟨n, hn⟩ := hKU g
        exact ⟨n, g, hn, hg⟩
      · rintro ⟨n, g, -, hg⟩
        exact ⟨g, hg⟩
    rw [this]
    exact MeasurableSet.iUnion hA
  have hs : ∀ n, ∃ s : X → G, Measurable s ∧ ∀ y ∈ A n, s y • x₀ = y := by
    intro n
    have : CompactSpace (K n) := isCompact_iff_compactSpace.1 (hK n)
    have : Nonempty (K n) := ⟨⟨1, Or.inl rfl⟩⟩
    obtain ⟨τ, h1, h2⟩ := exists_section_compact (fun g : K n => (g : G) • x₀)
      (hπ.comp continuous_subtype_val)
    refine ⟨fun y => τ y, measurable_subtype_coe.comp h1, ?_⟩
    rintro y ⟨g, hg, hgy⟩
    exact h2 y ⟨⟨g, hg⟩, hgy⟩
  choose s hs1 hs2 using hs
  have hex : ∀ y : X, ∃ n, (y ∈ A n ∨ ¬ ∃ g : G, g • x₀ = y) := by
    intro y
    by_cases hy : ∃ g : G, g • x₀ = y
    · obtain ⟨g, hg⟩ := hy
      obtain ⟨n, hn⟩ := hKU g
      exact ⟨n, Or.inl ⟨g, hn, hg⟩⟩
    · exact ⟨0, Or.inr hy⟩
  refine ⟨hO, fun y => s (Nat.find (hex y)) y, ?_, fun y hy => ?_⟩
  · exact Measurable.find (p := fun n y => y ∈ A n ∨ ¬ ∃ g : G, g • x₀ = y) hs1 (fun n => (hA n).union hO.compl) hex
  · exact hs2 _ y ((Nat.find_spec (hex y)).resolve_right (not_not.2 hy))

end GlobalTheory.OrbitSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjConjLevelLeIntegralGLAtTypePrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projConjLevel_le_integralGL_at_typePrime : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∈ Pr.vGs → ∀ h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P), prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.prCat_le_GLint | exact GlobalTheory.Mem.Col2.IdxEx.prCat_le_GLint | (intros; apply GlobalTheory.Mem.Col2.IdxEx.prCat_le_GLint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityMemRayClassFieldOfMultipleStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootsOfUnity_mem_rayClassField_of_multiple : ∀ (K M L : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L] [IsGalois K L] (𝔮 : Ideal (𝓞 K)) (p : ℕ), p ≠ 0 → 𝔮 ≤ Ideal.span {(p : 𝓞 K)} → IsRayField K M 𝔮 → Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧ IsFrob L v σ} = ⊤ → (∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} → Ideal.absNorm I ≡ 1 [MOD p]) → ∀ ζ : L, ζ ^ p = 1 → ζ ∈ Set.range (algebraMap M L) := by
  first | exact @GlobalTheory.Mem.RayZeta.root_mem_rayField | exact GlobalTheory.Mem.RayZeta.root_mem_rayField | (intros; apply GlobalTheory.Mem.RayZeta.root_mem_rayField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnLevelAtTwistPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowType_mul_on_level_at_twistPrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ g ∈ Jat (Pr := Pr) (R := R) sharp j P, ∀ g' ∈ Jat (Pr := Pr) (R := R) sharp j P, lamRow Ch mu sharp j P (g * g').toLinearMap = lamRow Ch mu sharp j P g.toLinearMap * lamRow Ch mu sharp j P g'.toLinearMap := by
  first | exact @GlobalTheory.TwistRowMul.lamRow_mul | exact GlobalTheory.TwistRowMul.lamRow_mul | (intros; apply GlobalTheory.TwistRowMul.lamRow_mul <;> assumption)
end

