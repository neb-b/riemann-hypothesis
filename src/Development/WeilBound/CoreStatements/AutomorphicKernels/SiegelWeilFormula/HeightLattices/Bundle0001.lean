module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.IsModuleTopologyTens
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.FinAlg
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.VolImageMulVec

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.EvLatLatO
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.KWhit.Ht

namespace PositivityTheory.SiegelWeilFormula.HeightDict

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem latM_coe (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (M : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E)) :
    (latM v M : Set (Fin n → v.adicCompletion F ⊗[F] E)) = (fun y => M *ᵥ y) '' (lat E v n : Set _) := by
  ext x; simp [latM]

theorem latM_isCO (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (M : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E))
    (hM : IsUnit M.det) : Gen.IsCO (latM v M) := by
  haveI := isModuleTopology_tens (E := E) v
  haveI : IsTopologicalRing (v.adicCompletion F ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  obtain ⟨ho, hc⟩ := lat_isCO (E := E) v n
  set φ := GlobalTheory.ModuLR.mulVecCE M hM
  have hs : (latM v M : Set (Fin n → v.adicCompletion F ⊗[F] E)) = φ '' (lat E v n : Set _) := by
    rw [latM_coe]; rfl
  show IsOpen _ ∧ IsCompact _
  rw [hs]
  exact ⟨φ.toHomeomorph.isOpenMap _ ho, hc.image φ.continuous⟩

theorem latM_eq_lat (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (M M' : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E))
    (hMM : M * M' = 1) (hM : ∀ i j, M i j ∈ OE E v) (hM' : ∀ i j, M' i j ∈ OE E v) :
    (latM v M : Set (Fin n → v.adicCompletion F ⊗[F] E)) = lat E v n := by
  ext y
  rw [latM_coe]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_lat] at hz ⊢
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact AddSubgroup.sum_mem _ fun j _ => OE_mul v (hM i j) (hz j)
  · intro hy
    refine ⟨M' *ᵥ y, ?_, by show M *ᵥ (M' *ᵥ y) = y; rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]⟩
    rw [SetLike.mem_coe, mem_lat] at hy ⊢
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact AddSubgroup.sum_mem _ fun j _ => OE_mul v (hM' i j) (hy j)

theorem ev_alg (c : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    algebraMap F (v.adicCompletion F) c ∈ v.adicCompletionIntegers F := by
  exact (algebraMap F (FiniteAdeleRing (𝓞 F) F) c).2

theorem ev_inclR (e : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    inclR (F := F) (v.adicCompletion F) e ∈ OE E v := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
  have hyi : IsIntegral ℤ (y • e) := hy e (Finset.mem_singleton_self e)
  have hyF : (y : F) ≠ 0 := Int.cast_ne_zero.2 hy0
  filter_upwards [ev_alg (F := F) ((y : F)⁻¹)] with v hv
  refine AddSubgroup.subset_closure ⟨algebraMap F (v.adicCompletion F) ((y : F)⁻¹), hv, ⟨y • e, (mem_integralClosure_iff ℤ E).2 hyi⟩, ?_⟩
  show (1 : v.adicCompletion F) ⊗ₜ[F] e = algebraMap F (v.adicCompletion F) ((y : F)⁻¹) ⊗ₜ[F] (y • e)
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul F, smul_smul,
    inv_mul_cancel₀ hyF, one_smul]

theorem ev_OE (x : AF F ⊗[F] E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, compFin F E v x ∈ OE E v := by
  induction x using TensorProduct.induction_on with
  | zero => exact Filter.Eventually.of_forall fun v => by rw [map_zero]; exact zero_mem _
  | tmul a e =>
    filter_upwards [ev_inclR (F := F) e, (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F a).2] with v he ha
    have h : compFin F E v (a ⊗ₜ[F] e) =
        (evFin F v a ⊗ₜ[F] (1 : E)) * inclR (F := F) (v.adicCompletion F) e := by
      show evFin F v a ⊗ₜ[F] e = (evFin F v a ⊗ₜ[F] (1 : E)) * ((1 : v.adicCompletion F) ⊗ₜ[F] e)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h]
    exact OE_mul v (AddSubgroup.subset_closure ⟨evFin F v a, ha, 1, by simp⟩) he
  | add x y hx hy =>
    filter_upwards [hx, hy] with v h1 h2
    rw [map_add (f := _)]
    exact add_mem h1 h2

theorem ev_OE_latO {k : ℕ} (bs : Module.Basis (Fin k) F E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    ∀ z : v.adicCompletion F ⊗[F] E, z ∈ OE E v ↔
      ∀ j, (Algebra.TensorProduct.basis (v.adicCompletion F) bs).repr z j ∈ v.adicCompletionIntegers F := by
  set ω := RingOfIntegers.basis E
  have hC1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ j,
      inclR (F := F) (v.adicCompletion F) (bs j) ∈ OE E v :=
    Filter.eventually_all.2 fun j => ev_inclR (bs j)
  have hC2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ i j,
      algebraMap F (v.adicCompletion F) (bs.repr ((ω i : 𝓞 E) : E) j) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_alg _
  filter_upwards [hC1, hC2] with v h1 h2
  intro z
  set B := Algebra.TensorProduct.basis (v.adicCompletion F) bs
  constructor
  · intro hz j
    have hz' : z ∈ (OE E v : Set (v.adicCompletion F ⊗[F] E)) := hz
    rw [OE_eq_image] at hz'
    obtain ⟨c, hc, rfl⟩ := hz'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    change (Finsupp.applyAddHom j) (∑ i, B.repr (c i ⊗ₜ[F] ((RingOfIntegers.basis E) i : E))) ∈ _
    rw [map_sum]
    refine sum_mem fun i _ => ?_
    change B.repr (c i ⊗ₜ[F] ((RingOfIntegers.basis E) i : E)) j ∈ _
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    exact mul_mem (hc i trivial) (h2 i j)
  · intro hz
    rw [← B.sum_repr z]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    rw [Algebra.TensorProduct.basis_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    exact OE_mul v (AddSubgroup.subset_closure ⟨B.repr z j, hz j, 1, by simp⟩) (h1 j)

theorem ev_lat_latO {k : ℕ} (bs : Module.Basis (Fin k) F E) (n : ℕ) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    (lat E v n : Set (Fin n → v.adicCompletion F ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO bs v := by
  filter_upwards [ev_OE_latO bs] with v hv
  ext y
  simp only [SetLike.mem_coe, mem_lat, PositivityTheory.PfSWUS.Loc.latO, Set.mem_setOf_eq, hv]

theorem fin_std (d : SD σ) (n : ℕ) (t u : GL (Fin n) (AE F E)) (η : E) (hη : η ≠ 0) :
    (∀ v : HeightOneSpectrum (𝓞 F),
      Gen.IsCO (latM v ((t.1.map (GlobalTheory.AdelicU.compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ))) ∧
      Gen.IsCO (latM v (((inclR (F := F) (v.adicCompletion F) η) • u.1.map (GlobalTheory.AdelicU.compFin F E v)).map
        (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)))) ∧
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ((latM v ((t.1.map (GlobalTheory.AdelicU.compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)) :
        Set (Fin n → v.adicCompletion F ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v) ∧
      ((latM v (((inclR (F := F) (v.adicCompletion F) η) • u.1.map (GlobalTheory.AdelicU.compFin F E v)).map
        (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)) : Set (Fin n → v.adicCompletion F ⊗[F] E)) =
          PositivityTheory.PfSWUS.Loc.latO d.bs v) := by
  classical
  have hinv1 : ∀ v : HeightOneSpectrum (𝓞 F),
      (t.1.map (compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) *
        ((t⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1 := by
    intro v
    have h := congrArg (fun M => (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ).mapMatrix
      ((compFin F E v).mapMatrix M)) (Units.mul_inv t)
    simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
  have hinv2 : ∀ v : HeightOneSpectrum (𝓞 F),
      ((inclR (F := F) (v.adicCompletion F) η) • u.1.map (compFin F E v)).map
          (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) *
        ((inclR (F := F) (v.adicCompletion F) η⁻¹) • (u⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v)).map
          (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1 := by
    intro v
    have hu : u.1.map (compFin F E v) * (u⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v) = 1 := by
      have h := congrArg (fun M => (compFin F E v).mapMatrix M) (Units.mul_inv u)
      simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
    have hc : inclR (F := F) (v.adicCompletion F) η * inclR (F := F) (v.adicCompletion F) η⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hη, map_one]
    have h2 : (inclR (F := F) (v.adicCompletion F) η • u.1.map (compFin F E v)) *
        (inclR (F := F) (v.adicCompletion F) η⁻¹ • (u⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v)) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, hu, smul_smul, hc, one_smul]
    have h := congrArg (fun M => (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ).mapMatrix M) h2
    simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
  refine ⟨fun v => ⟨latM_isCO v _ (Matrix.isUnit_det_of_right_inverse (hinv1 v)),
    latM_isCO v _ (Matrix.isUnit_det_of_right_inverse (hinv2 v))⟩, ?_⟩
  have ent : ∀ M : Matrix (Fin n) (Fin n) (AE F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∀ i j, compFin F E v (M i j) ∈ OE E v := fun M =>
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_OE (M i j)
  filter_upwards [ent t.1, ent (t⁻¹ : GL (Fin n) (AE F E)).1, ent u.1, ent (u⁻¹ : GL (Fin n) (AE F E)).1,
    ev_inclR (F := F) η, ev_inclR (F := F) η⁻¹, ev_lat_latO d.bs n] with v ht ht' hu hu' he he' hl
  refine ⟨?_, ?_⟩
  · rw [latM_eq_lat v _ _ (hinv1 v) (fun i j => OE_sig v (ht i j)) (fun i j => OE_sig v (ht' i j)), hl]
  · rw [latM_eq_lat v _ _ (hinv2 v) (fun i j => OE_sig v (OE_mul v he (hu i j)))
      (fun i j => OE_sig v (OE_mul v he' (hu' i j))), hl]

end PositivityTheory.SiegelWeilFormula.HeightDict
end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.FinIndex
section
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.HeightDict

open PositivityTheory.SiegelWeilFormula.KWhit.Ht

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem lat_vol (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    [lam.IsAddHaarMeasure] : lam (lat E v n : Set (Fin n → v.adicCompletion F ⊗[F] E)) ≠ 0 ∧
      lam (lat E v n : Set (Fin n → v.adicCompletion F ⊗[F] E)) ≠ ⊤ := by
  obtain ⟨ho, hc⟩ := lat_isCO (E := E) v n
  exact ⟨ho.measure_ne_zero lam ⟨0, zero_mem _⟩, hc.measure_lt_top.ne⟩

theorem vol_sig (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) [lam.IsAddHaarMeasure]
    (S : Set (Fin n → v.adicCompletion F ⊗[F] E)) :
    lam ((fun y i => HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ (y i)) '' S) = lam S := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (v.adicCompletion F ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : T2Space (v.adicCompletion F ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  let b := Algebra.TensorProduct.basis (v.adicCompletion F) (Module.finBasis F E)
  let coord : (v.adicCompletion F ⊗[F] E) ≃ₜ+ (Fin (Module.finrank F E) → v.adicCompletion F) :=
    { b.equivFun.toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  haveI : LocallyCompactSpace (v.adicCompletion F ⊗[F] E) :=
    coord.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (v.adicCompletion F ⊗[F] E) :=
    coord.toHomeomorph.isEmbedding.secondCountableTopology
  have : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) := ⟨rfl⟩
  set sg := HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ with hsg
  let Lsg : (v.adicCompletion F ⊗[F] E) →ₗ[v.adicCompletion F] (v.adicCompletion F ⊗[F] E) :=
    (Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion F) (v.adicCompletion F)) σ).toLinearMap
  have hL : ∀ z, Lsg z = sg z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Lsg, hsg, HeckeCharacterZeroLocus.SiegelWeilU.sigR]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hc : Continuous sg := by
    have := IsModuleTopology.continuous_of_linearMap Lsg
    exact (funext hL : ⇑Lsg = ⇑sg) ▸ this
  have hcv : Continuous fun y : Fin n → v.adicCompletion F ⊗[F] E => fun i => sg (y i) :=
    continuous_pi fun i => hc.comp (continuous_apply i)
  let φ : (Fin n → v.adicCompletion F ⊗[F] E) ≃ₜ+ (Fin n → v.adicCompletion F ⊗[F] E) :=
    { toFun := fun y i => sg (y i)
      invFun := fun y i => sg (y i)
      left_inv := fun y => funext fun i => sgv_sgv hcm v (y i)
      right_inv := fun y => funext fun i => sgv_sgv hcm v (y i)
      map_add' := fun y y' => funext fun i => map_add sg _ _
      continuous_toFun := hcv
      continuous_invFun := hcv }
  have hsymm : φ.symm = φ := rfl
  have hχ : addEquivAddHaarChar φ = 1 := by
    have h1 := addEquivAddHaarChar_symm (φ := φ)
    rw [hsymm] at h1
    have hpos := addEquivAddHaarChar_pos φ
    have h2 : addEquivAddHaarChar φ * addEquivAddHaarChar φ = 1 := by
      conv_lhs => arg 1; rw [h1]
      exact inv_mul_cancel₀ hpos.ne'
    have h3 : ((addEquivAddHaarChar φ : ℝ≥0) : ℝ) * (addEquivAddHaarChar φ : ℝ) = 1 := by exact_mod_cast h2
    rcases mul_self_eq_one_iff.1 h3 with h | h
    · exact_mod_cast h
    · linarith [NNReal.coe_nonneg (addEquivAddHaarChar φ)]
  have : lam.Regular := by
    obtain ⟨ho, hc⟩ := lat_isCO (E := E) v n
    exact Measure.regular_of_isAddLeftInvariant hc ⟨0, mem_interior_iff_mem_nhds.mpr (ho.mem_nhds (zero_mem _))⟩ hc.measure_lt_top.ne
  have h1 := addEquivAddHaarChar_smul_map lam φ
  have himg : (fun y i => sg (y i)) '' S = φ.toHomeomorph.toMeasurableEquiv '' S := rfl
  calc lam ((fun y i => sg (y i)) '' S) = (addEquivAddHaarChar φ • lam.map φ) ((fun y i => sg (y i)) '' S) := by
        rw [h1]
    _ = _ := by
      rw [Measure.smul_apply, himg, hχ, one_smul]
      have : Measure.map φ lam = Measure.map φ.toHomeomorph.toMeasurableEquiv lam := rfl
      rw [this, MeasurableEquiv.map_apply, MeasurableEquiv.preimage_image]

theorem norm_sig (v : HeightOneSpectrum (𝓞 F)) (z : v.adicCompletion F ⊗[F] E) :
    Algebra.norm (v.adicCompletion F) (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ z) =
      Algebra.norm (v.adicCompletion F) z :=
  GlobalTheory.Doubling.norm_sigR σ z

theorem fin_index (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (t u D β h : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E)) (η e : v.adicCompletion F ⊗[F] E)
    (k k' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (v.adicCompletion F ⊗[F] E))
    (ht : IsUnit t.det) (hD : IsUnit D.det) (htu : tᵀ * u.map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1)
    (hη : IsUnit η) (he : IsUnit e) (he1 : ‖Algebra.norm (v.adicCompletion F) e‖ = 1) (hβ : β = -(η • hᵀ))
    (hh : ∀ a b, HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ (h b a) = h a b) (hkk : k * k' = 1)
    (hk : ∀ i j, k i j ∈ OE E v) (hk' : ∀ i j, k' i j ∈ OE E v)
    (h1 : e • t = D * k.toBlocks₂₁) (h2 : e • (β * u) = D * k.toBlocks₂₂)
    (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) [lam.IsAddHaarMeasure] :
    ‖Algebra.norm (v.adicCompletion F) D.det‖ = ‖Algebra.norm (v.adicCompletion F) t.det‖ *
      Gen.nu2 lam (latM v (t.map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)))
        (latM v ((η • u).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ))) h := by
  set sg := HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ with hsg
  set O : Set (Fin n → v.adicCompletion F ⊗[F] E) := ((lat E v n : AddSubgroup _) : Set (Fin n → v.adicCompletion F ⊗[F] E)) with hO
  set sv : (Fin n → v.adicCompletion F ⊗[F] E) → (Fin n → v.adicCompletion F ⊗[F] E) := fun y i => sg (y i) with hsv
  have hsvO : ∀ y ∈ O, sv y ∈ O := fun y hy => (mem_lat v _).2 fun i => OE_sig v ((mem_lat v y).1 hy i)
  have hsvsv : ∀ y, sv (sv y) = y := fun y => funext fun i => sgv_sgv hcm v (y i)
  have hsvM : ∀ (M : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E)) y, sv (M *ᵥ y) = M.map sg *ᵥ sv y :=
    fun M y => funext fun i => RingHom.map_mulVec sg M y i
  have hsvadd : ∀ y y', sv (y + y') = sv y + sv y' := fun y y' => funext fun i => map_add sg _ _
  have hsvneg : ∀ y, sv (-y) = -sv y := fun y => funext fun i => map_neg sg _
  have hsvsmul : ∀ (c : v.adicCompletion F ⊗[F] E) y, sv (c • y) = sg c • sv y := fun c y => funext fun i => map_mul sg _ _
  have hkO : ∀ (M : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E)), (∀ i j, M i j ∈ OE E v) → ∀ y ∈ O, M *ᵥ y ∈ O :=
    fun M hM y hy => (mem_lat v _).2 fun i => by
      simp only [Matrix.mulVec, dotProduct]
      exact sum_mem fun j _ => OE_mul v (hM i j) ((mem_lat v y).1 hy j)
  have hk21 : ∀ i j, k.toBlocks₂₁ i j ∈ OE E v := fun i j => hk _ _
  have hk22 : ∀ i j, k.toBlocks₂₂ i j ∈ OE E v := fun i j => hk _ _

  have hβs : β.map sg = -(sg η • h) := by
    ext a b
    simp [hβ, Matrix.transpose_apply, hh]
  have hD1 : ∀ y, D *ᵥ (k.toBlocks₂₁ *ᵥ y) = e • (t *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, ← h1, Matrix.smul_mulVec]
  have hD2 : ∀ y, D *ᵥ (k.toBlocks₂₂ *ᵥ y) = e • (β *ᵥ (u *ᵥ y)) := fun y => by
    rw [Matrix.mulVec_mulVec, ← h2, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have hηu : (η • u).map sg = sg η • u.map sg := by
    ext a b; simp

  set X : Set (Fin n → v.adicCompletion F ⊗[F] E) :=
    {x | ∃ y ∈ latM v (t.map sg), ∃ y' ∈ latM v ((η • u).map sg), x = y + h *ᵥ y'} with hX
  have hset : (fun x => (sg e • (1 : Matrix (Fin n) (Fin n) _)) *ᵥ x) '' X = sv '' ((fun y => D *ᵥ y) '' O) := by
    ext w
    constructor
    · rintro ⟨x, ⟨y, hy, y', hy', rfl⟩, rfl⟩
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hy'
      refine ⟨D *ᵥ (k.toBlocks₂₁ *ᵥ sv a + k.toBlocks₂₂ *ᵥ (-sv b)), ⟨_, add_mem (hkO _ hk21 _ (hsvO _ ha))
        (hkO _ hk22 _ (neg_mem (hsvO _ hb))), rfl⟩, ?_⟩
      simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply]
      rw [Matrix.mulVec_add, hD1, hD2, hsvadd, hsvsmul, hsvsmul, hsvM, hsvM, hsvM, hsvsv, hβs, hsvneg, hsvsv,
        Matrix.smul_mulVec, Matrix.one_mulVec, hηu]
      simp only [Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg, Matrix.smul_mulVec, Matrix.mulVec_smul,
        smul_add, smul_neg]
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨y₁, y₂, hy₁, hy₂, hyz⟩ := bottom_onto (OEsub E v) k k' hkk hk hk' z ((mem_lat v z).1 hz)
      refine ⟨t.map sg *ᵥ sv y₁ + h *ᵥ ((η • u).map sg *ᵥ (-sv y₂)),
        ⟨_, ⟨sv y₁, hsvO _ ((mem_lat v _).2 hy₁), rfl⟩, _, ⟨-sv y₂, neg_mem (hsvO _ ((mem_lat v _).2 hy₂)), rfl⟩, rfl⟩, ?_⟩
      dsimp only
      rw [← hyz, Matrix.mulVec_add D, hD1, hD2, hsvadd, hsvsmul, hsvsmul, hsvM, hsvM, hsvM, hβs, hηu]
      simp only [Matrix.mulVec_add, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, Matrix.mulVec_neg,
        Matrix.mulVec_smul, smul_add, smul_neg, neg_neg, Matrix.mulVec_mulVec, Matrix.mul_smul, Matrix.smul_mul]
      rw [Matrix.one_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.neg_mulVec, smul_neg,
        smul_comm (sg η) (sg e)]
      simp only [Matrix.smul_mulVec]
  have hsc : IsUnit ((sg e • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E))).det) := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact (he.map sg).pow _
  have hnsc : ‖Algebra.norm (v.adicCompletion F) ((sg e • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E))).det)‖₊
      = 1 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, map_pow, norm_sig, nnnorm_pow]
    have : ‖Algebra.norm (v.adicCompletion F) e‖₊ = 1 := by ext; simpa using he1
    rw [this, one_pow]
  have hvX : lam X = ((‖Algebra.norm (v.adicCompletion F) D.det‖₊ : ℝ≥0) : ℝ≥0∞) * lam O := by
    have e1 := vol_image_mulVec' v lam (sg e • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E))) hsc X
    rw [hset, vol_sig hcm v lam, vol_image_mulVec' v lam D hD O, hnsc, ENNReal.coe_one, one_mul] at e1
    exact e1.symm
  have hdet : (t.map sg).det = sg t.det := (RingHom.map_det sg t).symm
  have htu' : IsUnit (t.map sg).det := by rw [hdet]; exact ht.map sg
  have hvL1 : lam (latM v (t.map sg) : Set (Fin n → v.adicCompletion F ⊗[F] E)) =
      ((‖Algebra.norm (v.adicCompletion F) t.det‖₊ : ℝ≥0) : ℝ≥0∞) * lam O := by
    have e2 := vol_image_mulVec' v lam (t.map sg) htu' O
    rw [hdet, norm_sig] at e2
    rw [← e2]
    rfl
  obtain ⟨hO0, hOT⟩ := lat_vol (E := E) v lam
  have hnt : (‖Algebra.norm (v.adicCompletion F) t.det‖₊ : ℝ≥0∞) ≠ 0 := by
    have : Algebra.norm (v.adicCompletion F) t.det ≠ 0 := (ht.map (Algebra.norm (v.adicCompletion F))).ne_zero
    simpa using this
  show _ = _ * (lam X / lam (latM v (t.map sg) : Set (Fin n → v.adicCompletion F ⊗[F] E))).toReal
  rw [hvX, hvL1, ENNReal.mul_div_mul_right _ _ hO0 hOT, ENNReal.toReal_div, ENNReal.coe_toReal, ENNReal.coe_toReal,
    coe_nnnorm, coe_nnnorm]
  have : ‖Algebra.norm (v.adicCompletion F) t.det‖ ≠ 0 := by simpa using hnt
  field_simp

end PositivityTheory.SiegelWeilFormula.HeightDict
end
end

