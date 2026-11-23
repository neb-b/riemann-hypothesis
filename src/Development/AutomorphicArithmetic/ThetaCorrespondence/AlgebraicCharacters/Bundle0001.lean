module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.EmbOrbit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import GroundTheory.GlobalFields.NormResidueSymbol.Bundle0002
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.ArtNorm
section
open UpperTheory.Lit.CharWD GlobalTheory.Published
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
  UpperTheory.V.W GroundTheory.Global GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal

section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]

private theorem val_of_norm
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := by
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, normV] using hf
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hx : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  rw [WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf',
    Nat.cast_pow, ← zpow_natCast, ← zpow_mul] at h
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h2 := zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h
  rw [← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]
  refine congrArg _ (Multiplicative.toAdd.injective ?_)
  rw [toAdd_pow, WithZero.toAdd_unzero_eq_log, WithZero.toAdd_unzero_eq_log, h2, nsmul_eq_mul]

variable [Algebra K L]

private theorem norm_loc (w : HeightOneSpectrum (𝓞 L)) (x : (w.adicCompletion L)ˣ) :
    ∃ y : ((below K w).adicCompletion K)ˣ, GroundTheory.Global.ideleNorm K L (localIdele L w x) = localIdele K (below K w) y ∧
      Valued.v (y : (below K w).adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, h, val_of_norm _ w _ x hm' _ (GlobalTheory.ArtinTransport.normV_eq_pow rfl)⟩

omit [Algebra K L] in
private theorem art_diag {Ω : Type} [Field Ω] [Algebra K Ω] {art : Ideles K →* Gab K Ω} (ha : IsGlobalArtin art) (k : Kˣ) :
    art (diagUnits K k) = 1 := by
  have hk : diagUnits K k ∈ art.ker := by
    rw [ha.ker]
    exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
  exact hk

private theorem glob_norm {Ω : Type} [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω]
    [IsAlgClosure L Ω] {art : Ideles K →* Gab K Ω} {art' : Ideles L →* Gab L Ω} (ha : IsGlobalArtin art)
    (ha' : IsGlobalArtin art') (x : Ideles L) (τ : G L Ω) (σ : G K Ω) (hσ : ∀ z, σ z = τ z) (hx : art' x = toAb L Ω τ) :
    art (GroundTheory.Global.ideleNorm K L x) = toAb K Ω σ := by
  classical
  have hφ : ∀ x, RingEquiv.refl Ω (algebraMap K Ω x) = algebraMap L Ω (algebraMap K L x) :=
    fun x => IsScalarTower.algebraMap_apply K L Ω x
  obtain ⟨ρ, hρc, hρ⟩ := GlobalTheory.HeckeGal.exists_abHom_of_ringEquiv K Ω L Ω (RingEquiv.refl Ω) (algebraMap K L) hφ
  rw [← hρ τ σ hσ, ← hx, eq_comm, ← mul_inv_eq_one]
  refine GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup K Ω _ fun U hU => ?_
  let χ : Gab K Ω →* Gab K Ω ⧸ U := QuotientGroup.mk' U
  haveI : DiscreteTopology (Gab K Ω ⧸ U) := QuotientGroup.discreteTopology hU
  have hχ : Continuous χ := QuotientGroup.continuous_mk
  let Nm : Ideles L →* Ideles K := GroundTheory.Global.ideleNorm K L
  have hN : Continuous Nm := GroundTheory.Global.continuous_ideleNorm
  let ψ : Ideles L →* Gab K Ω ⧸ U := χ.comp (ρ.comp art') * (χ.comp (art.comp Nm))⁻¹
  have hψ : ∀ y, ψ y = χ (ρ (art' y)) * (χ (art (Nm y)))⁻¹ := fun _ => rfl
  have ho : IsOpen ((χ.comp art).ker : Set (Ideles K)) :=
    (isOpen_discrete {1}).preimage (hχ.comp ha.quot.continuous)
  obtain ⟨S, -, -, hS, -⟩ := GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr K _ ho ∅
  have hT : {w : HeightOneSpectrum (𝓞 L) | ¬ below K w ∉ S}.Finite :=
    Filter.eventually_cofinite.1 ((tendsto_below (K := K) (L := L)).eventually S.eventually_cofinite_notMem)
  have h1 : ψ = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_away ψ
      ((hχ.comp (hρc.comp ha'.quot.continuous)).mul (hχ.comp (ha.quot.continuous.comp hN)).inv) (fun k => ?_) hT.toFinset
      fun w hw => ?_
    · have e : Nm (diagUnits L k) = diagUnits K _ := GroundTheory.Global.ideleNorm_diagonal (K := K) k
      rw [hψ, e, art_diag ha, art_diag ha']
      simp
    · have hv : below K w ∉ S := by simpa using hw
      have hu : ∀ x, IsUnitAt (below K w) x → χ (art (localIdele K (below K w) x)) = 1 := hS _ hv
      refine GlobalTheory.FrobDense.eq_one_of_unif (ψ.comp (localIdele L w)) fun y hy => ?_
      have h2 := unif_spec (below K w)
      have h3 := (GlobalTheory.ArtinTransport.chi_artin_transport K Ω L Ω _ hφ art art' ha ha' ρ hρ _ χ (below K w) w rfl hu).2
        y _ hy h2
      obtain ⟨z, hz, hv⟩ := norm_loc (K := K) w y
      have h4 := hu (z * ((atFin _ (unif (below K w))) ^ w.asIdeal.inertiaDeg (𝓞 K))⁻¹) (by
        unfold IsUnitAt IsUnifAt at *
        rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, hy, h2]
        exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero))
      simp only [map_mul, map_inv, map_pow, mul_inv_eq_one] at h4
      rw [MonoidHom.comp_apply, hψ, h3, show Nm (localIdele L w y) = _ from hz, h4, mul_inv_cancel]
  have h5 := DFunLike.congr_fun h1 x
  rw [hψ, ← map_inv, ← map_mul] at h5
  exact (QuotientGroup.eq_one_iff _).1 h5

open Classical in
private theorem emb_norm {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 L)) (res : Emb l w → Emb l (below K w))
    (hres : ∀ τ' x, (res τ').1 x = τ'.1 (algebraMap _ _ x)) (τ : Emb l (below K w)) (y : w.adicCompletion L) :
    τ.1 (Algebra.norm ((below K w).adicCompletion K) y) = ∏ᶠ (τ' : Emb l w) (_ : res τ' = τ), τ'.1 y := by
  letI := τ.1.toAlgebra
  haveI : ContinuousSMul ((below K w).adicCompletion K) (Qbar l) := continuousSMul_of_algebraMap _ _ τ.2
  haveI : ContinuousSMul ((below K w).adicCompletion K) (w.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ (continuous_completionMap _ _)
  haveI : FiniteDimensional ((below K w).adicCompletion K) (w.adicCompletion L) := inferInstance
  haveI : CharZero ((below K w).adicCompletion K) := algebraRat.charZero _
  have h := Algebra.norm_eq_prod_embeddings ((below K w).adicCompletion K) (Qbar l) y
  refine h.trans ?_
  rw [← finprod_eq_prod_of_fintype, ← finprod_subtype_eq_finprod_cond (f := fun τ' : Emb l w => τ'.1 y) (fun τ' => res τ' = τ)]
  have hc : ∀ σ : w.adicCompletion L →ₐ[(below K w).adicCompletion K] Qbar l, Continuous σ := fun σ => by
    letI : NontriviallyNormedField ((below K w).adicCompletion K) := Valued.toNontriviallyNormedField _ _
    have := LinearMap.continuous_of_finiteDimensional σ.toLinearMap
    exact this
  let e : (w.adicCompletion L →ₐ[(below K w).adicCompletion K] Qbar l) ≃ {τ' : Emb l w // res τ' = τ} :=
    { toFun := fun σ => ⟨⟨σ, hc σ⟩,
        Subtype.ext (RingHom.ext fun x => (hres _ x).trans (σ.commutes x))⟩
      invFun := fun τ' => ⟨τ'.1.1, fun x => (hres _ x).symm.trans (by rw [τ'.2]; rfl)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← finprod_comp_equiv e]
  rfl

end

theorem UpperTheory.Lit.CharWD.artNorm :
    GlobalArtinReciprocity → ArtNorm := by
  intro hG F F' Ω _ _ _ _ _ _ _ _ _ _ _ l _ A w w' h h' _
  obtain rfl : below F w' = w := HeightOneSpectrum.ext (GlobalTheory.WeilRestrict.comap_eq_of_isPlaceOver h h')
  refine ⟨fun τ' => ⟨τ'.1.comp (algebraMap _ _), τ'.2.comp (continuous_completionMap _ _)⟩,
    GroundTheory.LocalField.normUnits _ _, fun τ' x => ?_, fun τ y => emb_norm w' _ (fun _ _ => rfl) τ y,
    fun a a' ha ha' σ σ' hσ => ?_⟩
  · show τ'.1 (algebraMap _ _ (algebraMap F ((below F w').adicCompletion F) x)) = _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F F' (w'.adicCompletion F')]
  · obtain ⟨art, hart⟩ := hG F Ω
    obtain ⟨art', hart'⟩ := hG F' Ω
    refine GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' F Ω art hart _ ?_
    refine (ha.glob art hart σ).trans ((glob_norm hart hart' _ _ _ hσ (ha'.glob art' hart' σ')).symm.trans ?_)
    exact congrArg art (GroundTheory.Global.ideleNorm_finiteEmbedding (K := F) w' (a' σ'))
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.ChCoef
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne
open GlobalTheory.Pst GlobalTheory.TripleGal Module TensorProduct Polynomial Formalism.MainNotions.N
open UpperTheory.Lit.CharWD GlobalTheory.Published
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

private theorem letter_lift {L U D M : Type} [Field L] [Field U] [AddCommGroup D] [Module L D] (m : U →+* End L D)
    (F : Type) [Field F] [Algebra L F] (τ : U →+* F) [AddCommGroup M] [Module F M] (g : D →+ M)
    (h1 : ∀ (a : L) x, g (a • x) = algebraMap L F a • g x) (h2 : ∀ c x, g (m c x) = τ c • g x) :
    ∃ Φ : Letter m F τ →ₗ[F] M, ∀ x, Φ (letterMk m F τ x) = g x := by
  letI : Module L M := Module.compHom _ (algebraMap L F)
  haveI : IsScalarTower L F M := ⟨fun a c y => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let g' : D →ₗ[L] M := { g with map_smul' := h1 }
  have e : ∀ (a : F) x, LinearMap.liftBaseChange F g' (a ⊗ₜ x) = a • g x := fun a x =>
    LinearMap.liftBaseChange_tmul _ _ _ _
  refine ⟨(letterKer m F τ).liftQ (LinearMap.liftBaseChange F g') (iSup_le fun c => ?_), fun x =>
    (e 1 x).trans (one_smul _ _)⟩
  rintro _ ⟨y, rfl⟩
  rw [LinearMap.mem_ker]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [LinearMap.sub_apply, LinearMap.baseChange_tmul, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul, e, e, h2, smul_comm, sub_self]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

private theorem line_smul {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (hd : finrank ℂ W = 1)
    (f : End ℂ W) (c : ℂ) (hc : c ∈ f.charpoly.roots) (v : W) : f v = c • v := by
  rw [mem_roots (LinearMap.charpoly_monic _).ne_zero, ← End.hasEigenvalue_iff_isRoot_charpoly] at hc
  obtain ⟨u, hu⟩ := hc.exists_hasEigenvector
  obtain ⟨d, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℂ) u hu.2).mp hd v
  rw [map_smul, hu.apply_eq_smul, smul_comm]

section

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L₁ L₂ : FinExt l}
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module ↥L₁.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥L₁.1 V₁]
  [AddCommGroup V₂] [Module ↥L₂.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥L₂.1 V₂]

open EnlargeCoeff in
private theorem dQ_inv {ρ₁ : Representation ↥L₁.1 ↥(GK K) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK K) V₂}
    {f : V₁ →ₗ[ℚ_[l]] V₂} {f' : V₂ →ₗ[ℚ_[l]] V₁} (hf : ∀ g v, f (ρ₁ g v) = ρ₂ g (f v))
    (hf' : ∀ g v, f' (ρ₂ g v) = ρ₁ g (f' v)) (e : ∀ v, f (f' v) = v) (y : ↥(Dpst P ρ₂)) :
    dQ P hf (dQ P hf' y) = y := by
  apply Subtype.ext
  rw [coe_dQ, coe_dQ]
  induction (y : V₂ ⊗[ℚ_[l]] Bst P) using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rw [tensQ_tmul, tensQ_tmul, e]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]


open EnlargeCoeff in
private theorem dQ_bij {ρ₁ : Representation ↥L₁.1 ↥(GK K) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK K) V₂}
    (f : V₁ ≃ₗ[ℚ_[l]] V₂) (hf : ∀ g v, f.toLinearMap (ρ₁ g v) = ρ₂ g (f.toLinearMap v)) :
    Function.Bijective (dQ P hf) := by
  have hf' : ∀ g v, f.symm.toLinearMap (ρ₂ g v) = ρ₁ g (f.symm.toLinearMap v) := fun g v =>
    f.injective ((f.apply_symm_apply _).trans ((congrArg (ρ₂ g) (f.apply_symm_apply v).symm).trans (hf g _).symm))
  exact Function.bijective_iff_has_inverse.2
    ⟨dQ P hf', dQ_inv P hf' hf f.symm_apply_apply, dQ_inv P hf hf' f.apply_symm_apply⟩

open EnlargeCoeff in
private theorem isPst_equiv {ρ₁ : Representation ↥L₁.1 ↥(GK K) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK K) V₂}
    (f : V₁ ≃ₗ[ℚ_[l]] V₂) (hf : ∀ g v, f.toLinearMap (ρ₁ g v) = ρ₂ g (f.toLinearMap v)) (hV : IsPst P ρ₁) :
    IsPst P ρ₂ := by
  let T : DpstUr P ρ₁ →ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ₂ :=
    { toFun := dQ P hf
      map_add' := (dQ P hf).map_add
      map_smul' := dQ_mulD P hf }
  unfold IsPst at hV ⊢
  rw [← (LinearEquiv.ofBijective T (dQ_bij P f hf)).rank_eq, hV, f.rank_eq]

end

section

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces B)

private theorem exists_semi {K L₁ L₂ : FinExt l}
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module ↥L₁.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥L₁.1 V₁]
    [AddCommGroup V₂] [Module ↥L₂.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥L₂.1 V₂]
    {ρ₁ : Representation ↥L₁.1 ↥(GK K) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK K) V₂} (g : GQ l)
    (S : ↥(Dpst P ρ₁) →+ ↥(Dpst P ρ₂))
    (h1 : ∀ a : ↥L₁.1, ∃ a' : ↥L₂.1, (a' : Om l) = g a ∧ ∀ x, S (a • x) = a' • S x)
    (h2 : ∀ c : ↥(MaximalUnramifiedExtension l), ∃ c' : ↥(MaximalUnramifiedExtension l), (c' : Om l) = g c ∧ ∀ x, S (mulD P ρ₁ c x) = mulD P ρ₂ c' (S x)) :
    ∃ Φ : WDSpace P ι ρ₁ → WDSpace P ι ρ₂, (∀ (z : Om l) y, Φ (ι z • y) = ι (g z) • Φ y) ∧
      ∀ x, Φ (wdMk P ι ρ₁ x) = wdMk P ι ρ₂ (S x) := by
  let θ : ℂ →+* ℂ := ι.toRingHom.comp ((g : Om l →+* Om l).comp ι.symm.toRingHom)
  have hθ : ∀ z, θ (ι z) = ι (g z) := fun z => congrArg (fun t => ι (g t)) (ι.symm_apply_apply z)
  letI := algC ι L₁
  obtain ⟨Φ, hΦ⟩ := @letter_lift _ _ _ (WDSpace P ι ρ₂) _ _ _ _ (mulD P ρ₁) ℂ _ _ (urC ι) _ (Module.compHom _ θ)
    ((AddMonoidHom.mk' (wdMk P ι ρ₂) (wdMk_add P ι ρ₂)).comp S)
    (fun a x => by
      obtain ⟨a', e1, e2⟩ := h1 a
      show wdMk P ι ρ₂ (S (a • x)) = θ (ι a) • wdMk P ι ρ₂ (S x)
      rw [e2]
      change wdMk P ι ρ₂ ((Dpst P ρ₂).module.toSMul.smul a' (S x)) = _
      rw [wdMk_smul, hθ, e1])
    (fun c x => by
      obtain ⟨c', e1, e2⟩ := h2 c
      show wdMk P ι ρ₂ (S (mulD P ρ₁ c x)) = θ (ι c) • wdMk P ι ρ₂ (S x)
      rw [e2, wdMk_mul, hθ, e1])
  refine ⟨fun y => Φ y, fun z y => ?_, hΦ⟩
  rw [← hθ]
  exact @LinearMap.map_smul _ _ _ _ _ _ _ (Module.compHom _ θ) Φ _ _


open EnlargeCoeff in
private theorem eig_conj {L₁ L₂ : FinExt l}
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module ↥L₁.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥L₁.1 V₁]
    [AddCommGroup V₂] [Module ↥L₂.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥L₂.1 V₂]
    [FiniteDimensional ↥L₁.1 V₁] [FiniteDimensional ↥L₂.1 V₂]
    {ρ₁ : Representation ↥L₁.1 ↥(GK B.Kw) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK B.Kw) V₂} (g : GQ l)
    (d₁ : finrank ↥L₁.1 V₁ = 1) (d₂ : finrank ↥L₂.1 V₂ = 1)
    (s : ↥L₁.1 →+* ↥L₂.1) (hs : ∀ a, (s a : Om l) = g a)
    (f : V₁ ≃ₗ[ℚ_[l]] V₂) (hf : ∀ g v, f.toLinearMap (ρ₁ g v) = ρ₂ g (f.toLinearMap v))
    (hfs : ∀ (a : ↥L₁.1) v, f.toLinearMap (a • v) = s a • f.toLinearMap v) (hV₁ : IsPst P ρ₁)
    (σ : Weil h) (z : Om l) (hz : ι z ∈ (wdPst P ι B h hj ρ₁).eig σ) : ι (g z) ∈ (wdPst P ι B h hj ρ₂).eig σ := by
  have hV₂ := isPst_equiv P f hf hV₁
  haveI := hV₁.finite
  haveI := hV₂.finite
  obtain ⟨T, t1, t2, t3, -⟩ := BridgeParam.exists_isTwist P ρ₂ g
  obtain ⟨Φ, hΦ1, hΦ2⟩ := exists_semi P ι g ((T : End ↥L₂.1 ↥(Dpst P ρ₂)).toAddMonoidHom.comp (dQ P hf))
    (fun a => ⟨s a, hs a, fun x => by
      have e : dQ P hf (a • x) = s a • dQ P hf x := Subtype.ext (tensQ_smul P s hfs a x.1)
      exact (congrArg (T : End ↥L₂.1 ↥(Dpst P ρ₂)) e).trans (map_smul _ _ _)⟩)
    (fun c => ⟨⟨g c, (BridgeInd.mem_Kur_iff g _).1 c.2⟩, rfl, fun x =>
      (congrArg (T : End ↥L₂.1 ↥(Dpst P ρ₂)) (dQ_mulD P hf c x)).trans (LinearMap.congr_fun (t1 c _ rfl) _)⟩)
  have e₁ : finrank ℂ (WDSpace P ι ρ₁) = 1 := (LetterDim.finrank_wdSpace l P ι _ L₁ _ _ hV₁).trans d₁
  have e₂ : finrank ℂ (WDSpace P ι ρ₂) = 1 := (LetterDim.finrank_wdSpace l P ι _ L₂ _ _ hV₂).trans d₂
  obtain ⟨y, hy⟩ : ∃ y, wdMk P ι ρ₂ y ≠ 0 := by
    by_contra hc
    have h0 : (⊤ : Submodule ℂ (WDSpace P ι ρ₂)) = ⊥ := by
      rw [← span_wdMk, Submodule.span_eq_bot]
      rintro _ ⟨y, rfl⟩
      exact not_not.1 fun hn => hc ⟨y, hn⟩
    rw [← finrank_top, h0, finrank_bot] at e₂
    exact zero_ne_one e₂
  obtain ⟨y, rfl⟩ := ((End.isUnit_iff _).1 T.isUnit).2 y
  obtain ⟨x, rfl⟩ := (dQ_bij P f hf).2 y
  have hc : Commute (T : End ↥L₂.1 ↥(Dpst P ρ₂)) (weilD B h P ρ₂ σ) :=
    (t2 _).mul_right (Commute.units_zpow_right (u := phiU P ρ₂) t3 _)
  have k1 := line_smul e₁ (wdRho P ι B h hj ρ₁ σ) (ι z)
    (by rw [← DpstMap.charPol_wdPst P ι B h hj ρ₁ hV₁]; exact hz) (wdMk P ι ρ₁ x)
  have k2 := congrArg Φ k1
  rw [hΦ1, wdRho_mk, hΦ2, hΦ2] at k2
  have k3 : wdRho P ι B h hj ρ₂ σ (wdMk P ι ρ₂ ((T : End ↥L₂.1 ↥(Dpst P ρ₂)) (dQ P hf x))) =
      ι (g z) • wdMk P ι ρ₂ ((T : End ↥L₂.1 ↥(Dpst P ρ₂)) (dQ P hf x)) := by
    refine Eq.trans (congrArg (wdMk P ι ρ₂) ?_) k2
    exact ((congrArg (T : End ↥L₂.1 ↥(Dpst P ρ₂)) (dQ_weilD P B h hf σ x)).trans (LinearMap.congr_fun hc.eq _)).symm
  show ι (g z) ∈ ((wdPst P ι B h hj ρ₂).charPol σ).roots
  rw [DpstMap.charPol_wdPst P ι B h hj ρ₂ hV₂, mem_roots (LinearMap.charpoly_monic _).ne_zero,
    ← End.hasEigenvalue_iff_isRoot_charpoly]
  exact End.hasEigenvalue_of_hasEigenvector ⟨End.mem_eigenspace_iff.mpr k3, hy⟩

private theorem wdAt_eq_of {a : ℕ} (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (L : FinExt l)
    (r₂ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (hm : mapRep (algebraMap ↥L.1 (Om l)) r₂ = r)
    (hV : IsPst P (B.repE L r₂)) : IsPstAt P B r ∧ wdAt P ι B h hj r = wdPst P ι B h hj (B.repE L r₂) := by
  have k : L.1 ≤ (supExt L B.LL).1 := le_sup_left
  have hr : IsPstAt P B r := ⟨supExt L B.LL, mapRep (IntermediateField.inclusion k).toRingHom r₂,
    ⟨le_sup_right, by rw [← hm]; ext g i j; rfl⟩, GlobalTheory.PstExt.isPst_enlarge P B k r₂ hV⟩
  obtain ⟨L₁, r₁, m₁, V₁, e₁⟩ := wdAt_of_isPstAt ι B h hj hr
  have k₁ : L₁.1 ≤ (supExt L₁ L).1 := le_sup_left
  have k₂ : L.1 ≤ (supExt L₁ L).1 := le_sup_right
  have e : mapRep (IntermediateField.inclusion k₁).toRingHom r₁ =
      mapRep (IntermediateField.inclusion k₂).toRingHom r₂ := by
    ext g i j
    exact congrArg (fun f : ↥(Dec (F := E) A) →* GL (Fin a) (Om l) => (f g : Matrix (Fin a) (Fin a) (Om l)) i j)
      (m₁.2.trans hm.symm)
  refine ⟨hr, ?_⟩
  rw [e₁, BridgeParam.wdPst_enlarge P ι B h hj k₁ r₁ V₁, BridgeParam.wdPst_enlarge P ι B h hj k₂ r₂ hV, e]

end

theorem UpperTheory.Lit.CharWD.chCoef :
    ChCoef := by
  intro F Ω _ _ _ _ _ l _ A w ι h O _ _ _ Bw hj s κ ξ _ ⟨hp, hs, e⟩
  obtain ⟨L, r, hm, hV, e₁⟩ := wdAt_of_isPstAt ι Bw h hj hp
  let t : ↥L.1 ≃ₐ[ℚ_[l]] ↥(mapExt s L).1 := L.1.equivMap (s : Om l →ₐ[ℚ_[l]] Om l)
  let f : (Fin 1 → ↥L.1) ≃ₗ[ℚ_[l]] (Fin 1 → ↥(mapExt s L).1) := LinearEquiv.piCongrRight fun _ => t.toLinearEquiv
  let r₂ := mapRep (t : ↥L.1 →+* ↥(mapExt s L).1) r
  have hf : ∀ g v, f.toLinearMap (Bw.repE L r g v) = Bw.repE (mapExt s L) r₂ g (f.toLinearMap v) := fun g v =>
    funext fun i => RingHom.map_mulVec (t : ↥L.1 →+* ↥(mapExt s L).1)
      (r (Bw.e.symm g) : Matrix (Fin 1) (Fin 1) ↥L.1) v i
  have hm₂ : mapRep (algebraMap ↥(mapExt s L).1 (Om l)) r₂ = rk1 ((Units.map (s : Qbar l →* Qbar l)).comp κ) := by
    ext g i j
    have := congrArg (fun f : ↥(Dec (F := F) A) →* GL (Fin 1) (Om l) => s ((f g : Matrix (Fin 1) (Fin 1) (Om l)) i j))
      hm.2
    refine Eq.trans this ?_
    fin_cases i; fin_cases j
    simp [rk1]
  obtain ⟨hp₂, e₂⟩ := wdAt_eq_of _ ι Bw h hj _ _ r₂ hm₂ (isPst_equiv _ f hf hV)
  refine ⟨hp₂, hs.of_le fun σ hσ => ?_,
    ParamAboveModel.eq_lpOfChar h _ (GlobalTheory.Pst.Test.lpDim_wdAt _ ι Bw h hj _) _ _ fun σ => ?_⟩
  · have h1 : ξ σ = 1 := Units.ext (ι.injective ((congrArg Units.val hσ).trans (map_one ι).symm))
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_one, map_one]
  · rw [e₂]
    refine eig_conj _ ι Bw h hj s (by simp) (by simp) (t : ↥L.1 →+* ↥(mapExt s L).1) (fun _ => rfl) f hf
      (fun a v => funext fun i => map_mul t a (v i)) hV σ (ξ σ) ?_
    rw [← e₁, e, GlobalTheory.LocLanglands.eig_lpOfChar]
    exact Multiset.mem_singleton.2 rfl
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.EmbOrbitAlt
section
open UpperTheory.Lit.CharWD GlobalTheory.Published

section SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.W

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] {w : Plc F}

private theorem eo_lt (j : Emb l w) (x : 𝓞 F) (hx : x ∈ w.asIdeal) : ‖j.1 (algebraMap F _ (x : F))‖ < 1 := by
  have h1 : ‖algebraMap F (w.adicCompletion F) (x : F)‖ < 1 := by
    have := (NumberField.FinitePlace.norm_lt_one_iff_mem (K := F) (v := w) x).2 hx
    exact this
  have h2 := tendsto_pow_atTop_nhds_zero_of_norm_lt_one h1
  have h3 := ((j.2.tendsto 0).comp h2)
  rw [map_zero] at h3
  have h4 : Filter.Tendsto (fun n : ℕ => ‖j.1 (algebraMap F _ (x : F))‖ ^ n) Filter.atTop (nhds 0) := by
    have := h3.norm
    simpa [Function.comp_def, map_pow, norm_pow] using this
  have := tendsto_pow_atTop_nhds_zero_iff.1 h4
  simpa [abs_of_nonneg (norm_nonneg _)] using this

private theorem eo_over (j : Emb l w) : w.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := by
  have hmax : (w.asIdeal.under ℤ).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal w.asIdeal
  have hle : w.asIdeal.under ℤ ≤ Ideal.span {(l : ℤ)} := by
    intro n hn
    rw [Ideal.mem_span_singleton]
    have hmem : (algebraMap ℤ (𝓞 F) n) ∈ w.asIdeal := hn
    have h := eo_lt j _ hmem
    have e : j.1 (algebraMap F _ ((algebraMap ℤ (𝓞 F) n : 𝓞 F) : F)) = ((n : ℚ_[l]) : PadicAlgCl l) := by
      simp
    rw [e, PadicAlgCl.norm_extends] at h
    rw [← PadicInt.norm_int_lt_one_iff_dvd]
    simpa [PadicInt.norm_def] using h
  have hne : Ideal.span {(l : ℤ)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun hu => (Fact.out : l.Prime).ne_one (by simpa using Int.isUnit_iff_natAbs_eq.1 hu)
  exact ⟨(hmax.eq_of_le hne hle).symm⟩

private theorem eo_comp (j : Emb l w) (φ : ℚ_[l] →+* w.adicCompletion F) (hφ : Continuous φ) (x : ℚ_[l]) :
    j.1 (φ x) = algebraMap ℚ_[l] (Qbar l) x := by
  have h1 : Continuous fun y : ℚ_[l] => j.1 (φ y) := j.2.comp hφ
  have h2 : Continuous (algebraMap ℚ_[l] (Qbar l)) := continuous_algebraMap ℚ_[l] (Qbar l)
  have key : (fun y => j.1 (φ y)) = algebraMap ℚ_[l] (Qbar l) := by
    refine (Padic.denseRange_ratCast l).equalizer h1 h2 ?_
    funext q
    simp
  exact congrFun key x

private theorem eo_abs {k K Ω : Type} [Field k] [Field K] [Field Ω] [CharZero K] [Algebra k K] [Algebra k Ω]
    [IsAlgClosure k Ω] (τ₀ : K →ₐ[k] Ω) :
    (∀ τ : K →ₐ[k] Ω, ∃ s : Ω ≃ₐ[k] Ω, ∀ x, τ x = s (τ₀ x)) ∧
    ∀ y : Ω, (∀ s : Ω ≃ₐ[k] Ω, (∀ x, τ₀ x = s (τ₀ x)) → y = s y) → ∃ u, y = τ₀ u := by
  haveI : CharZero k := (algebraMap k K).charZero
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
  haveI : Normal k Ω := inferInstance
  haveI : IsGalois k Ω := inferInstance
  constructor
  · intro τ
    letI : Algebra K Ω := τ₀.toRingHom.toAlgebra
    haveI : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq (fun r => (τ₀.commutes r).symm)
    let g := τ.liftNormal Ω
    refine ⟨AlgEquiv.ofBijective g (Algebra.IsAlgebraic.algHom_bijective g), fun x => ?_⟩
    have := τ.liftNormal_commutes Ω x
    exact this.symm
  · intro y hy
    have hmem : y ∈ IntermediateField.fixedField τ₀.fieldRange.fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro f hf
      rw [IntermediateField.mem_fixingSubgroup_iff] at hf
      exact (hy f (fun x => (hf _ ⟨x, rfl⟩).symm)).symm
    rw [InfiniteGalois.fixedField_fixingSubgroup, AlgHom.mem_fieldRange] at hmem
    obtain ⟨u, hu⟩ := hmem
    exact ⟨u, hu.symm⟩

end SlopeTestRemainingChoices

theorem UpperTheory.Lit.CharWD.embOrbit :
    EmbOrbit := by
  intro F _ _ l _ w c hc hne
  obtain ⟨τ₀⟩ := hne
  haveI := eo_over τ₀
  obtain ⟨f, φ, -, hφc, -, -, -⟩ := KStar.Ram.existsUnique_padic_hom w l
  letI : Algebra ℚ_[l] (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w) := φ.toAlgebra
  have toAlg : ∀ τ : UpperTheory.V.W.Emb l w,
      ∃ t : IsDedekindDomain.HeightOneSpectrum.adicCompletion F w →ₐ[ℚ_[l]] Formalism.ConjugateSelfDual.Qbar l,
        ∀ x, t x = τ.1 x :=
    fun τ => ⟨AlgHom.mk τ.1 (fun r => eo_comp τ φ hφc r), fun _ => rfl⟩
  haveI : CharZero (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w) :=
    charZero_of_injective_algebraMap
      (algebraMap F (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w)).injective
  obtain ⟨t₀, ht₀⟩ := toAlg τ₀
  obtain ⟨hext, hfix⟩ := eo_abs t₀
  obtain ⟨u, hu⟩ := hfix (c τ₀) (fun s hs => hc s τ₀ τ₀ (fun x => by
    have h := hs x
    rwa [ht₀] at h))
  refine ⟨u, fun τ => ?_⟩
  obtain ⟨t, ht⟩ := toAlg τ
  obtain ⟨s, hs⟩ := hext t
  have h := hc s τ₀ τ (fun x => by
    have h' := hs x
    rwa [ht, ht₀] at h')
  rw [h, hu, ← hs u, ht]
end

