module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaValuesCoefficientExists
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift.BaseDatum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def along {K X Z : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Z] [Module ℂ Z] {s s' : K →+* ℂ} (h : s = s')
    (f : X →ₛₗ[s] Z) : X →ₛₗ[s'] Z where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := by rw [← h]; exact f.map_smulₛₗ a x

theorem ext_val {G Γ W K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (hact : ∀ γ, ∃ T : M → M, ∀ v, c₀ (T v) = ρ γ (c₀ v))
    (hχ : ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ)) (f : S.Cl → S.V) (h : G) : ∃ v, P.ext f h = c₀ v := by
  obtain ⟨T, hT⟩ := hact (P.decG h)
  obtain ⟨y, hy⟩ := hχ (P.decK h)
  refine ⟨y • T (e (f (P.decC h))), ?_⟩
  rw [map_smulₛₗ, hT, hy, ← he]
  rfl

theorem pair_val {G Γ W K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (pr : M → M → K) (hp : ∀ x x', pr (e x) (e x') = S.pair x x') (v w : M) :
    inner ℂ (c₀ v) (c₀ w) = σ₀ (pr v w) := by
  have h := P.coef_pair (e.symm v) (e.symm w)
  rw [he, he, ← hp] at h
  simpa only [LinearEquiv.apply_symm_apply] using h

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

include R in
theorem realisation_embedding_eq_baseEmbedding : D.what₂.embLL = sg0 D A := (sgAt_mk _ R.hv0).symm

theorem isEtaConj_base (hL : R.toLevCh.Is A.μ0) (hV : EtaVals R) : IsEtaConj (sg0 D A) R.eta R.eta :=
  ⟨hL.eta.1, GlobalTheory.EtaConjExist.unram_of_chrEq hL.eta R.C.isEta.unr, fun P e he x hx =>
    (hV P e he x hx).imp fun y hy => ⟨hy, (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) y).symm.trans hy⟩⟩


theorem places_base (hL : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2 fun PP hPP =>
    (hL.Q_ram A.μ0 PP).2 (Or.inl hPP) (by rw [hL.xi_base]; exact fun _ _ => rfl)

theorem mu_base (hL : R.toLevCh.Is A.μ0) (j : ℕ) : R.toLevCh.mu A.μ0 j = R.mu0 j := by
  have hxi : R.xi A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0))
  exact (congrArg (R.mu0 j * ·) hxi).trans (mul_one _)

theorem omegaQ_empty {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  rw [dite_eq_left (by simp)]
  simp

theorem isThPVecOf_empty {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS sT ΛS ΛT βS βT}
    {Pg Q : Finset (Pl D.host.E)} (hQ : Q = ∅) {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    {f₀ f : WO S T → ℂ} (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) :
    IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg ∅ ξ' f₀ f := by
  subst hQ
  unfold IsThPVecOf at h ⊢
  simp only [omegaQ_empty] at h ⊢
  exact h

include R in
theorem deltaConj_base : deltaConj i (sg0 D A) = RealDat.Delta i := by
  have hl : lab (sg0 D A) = id := by
    rw [← realisation_embedding_eq_baseEmbedding R]; exact funext GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.lab_base
  unfold deltaConj
  rw [hl]
  rfl


end GlobalTheory.GalLift.BaseDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateNearGenericPoint
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

namespace GlobalTheory.GenericEtale

theorem trdeg_eq (k K A B : Type) [CommRing k] [IsDomain k] [Field K] [Algebra k K]
    [IsFractionRing k K] [CommRing A] [Algebra k A] [FaithfulSMul k A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Algebra.IsAlgebraic A B] [Algebra K B] [Algebra k B]
    [IsScalarTower k K B] [IsScalarTower k A B] : Algebra.trdeg K B = Algebra.trdeg k A := by
  have : Nontrivial A := (algebraMap A B).domain_nontrivial
  have : Algebra.IsAlgebraic k K := IsLocalization.isAlgebraic K (nonZeroDivisors k)
  have h₁ := trdeg_add_eq k K (A := B)
  have h₂ := trdeg_add_eq k A (A := B)
  rw [trdeg_eq_zero, zero_add] at h₁
  rw [trdeg_eq_zero (R := A), add_zero] at h₂
  rw [h₁, h₂]

theorem formallySmooth_fractionField (k A L : Type) [CommRing k] [IsDomain k] [CharZero k]
    [CommRing A] [IsDomain A] [Algebra k A] [FaithfulSMul k A] [Algebra.FiniteType k A] [Field L]
    [Algebra A L] [IsFractionRing A L] [Algebra k L] [IsScalarTower k A L] :
    Algebra.FormallySmooth k L ∧ Module.rank L Ω[L⁄k] = Algebra.trdeg k A := by
  let K := FractionRing k
  have hinj : Function.Injective (algebraMap k L) := by
    rw [IsScalarTower.algebraMap_eq k A L]
    exact (IsFractionRing.injective A L).comp (FaithfulSMul.algebraMap_injective k A)
  let : Algebra K L := (IsFractionRing.lift (K := K) hinj).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap (K := K) hinj a).symm
  have : Algebra.EssFiniteType A L := .of_isLocalization L (nonZeroDivisors A)
  have : Algebra.EssFiniteType k L := .comp k A L
  have : Algebra.EssFiniteType K L := .of_comp k K L
  have : Algebra.FormallySmooth K L := Algebra.FormallySmooth.of_perfectField
  have : Algebra.FormallyEtale k K := .of_isLocalization (nonZeroDivisors k)
  have : Algebra.IsAlgebraic A L := IsLocalization.isAlgebraic L (nonZeroDivisors A)
  refine ⟨.comp k K L, ?_⟩
  have hb : Function.Bijective (KaehlerDifferential.map k K L L) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, KaehlerDifferential.map_surjective k K L⟩
    obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map k K L x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  rw [(LinearEquiv.ofBijective _ hb).rank_eq, rank_kaehler_eq_trdeg, trdeg_eq k K A L]

theorem exists_away (k A : Type) [CommRing k] [IsDomain k] [CharZero k] [IsNoetherianRing k]
    [CommRing A] [IsDomain A] [Algebra k A] [FaithfulSMul k A] [Algebra.FiniteType k A] {D : ℕ}
    (hd : Algebra.trdeg k A = D) :
    ∃ f : A, f ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension D k (Localization.Away f) := by
  have : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let L := Localization.AtPrime (⊥ : Ideal A)
  have : IsFractionRing A L :=
    (congrArg (fun M : Submonoid A => IsLocalization M L) (Ideal.primeCompl_bot (α := A))).mp
      inferInstance
  have hL : IsField L :=
    (FractionRing.algEquiv A L).symm.toMulEquiv.isField (Field.toIsField (FractionRing A))
  let : Field L := hL.toField
  obtain ⟨h₁, h₂⟩ := formallySmooth_fractionField k A L
  have : Algebra.IsSmoothAt k (⊥ : Ideal A) := h₁
  obtain ⟨f, hf, h⟩ := exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt k (⊥ : Ideal A)
    (d := D) (Module.finrank_eq_of_rank_eq (h₂.trans hd))
  exact ⟨f, hf, h⟩

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem trdeg_chart (h : IsArithVar p D) {A : Type} [CommRing A] [Algebra k A]
    (i : Sp A ⟶ X) [IsOpenImmersion i] (hi : i ≫ p = spMap (algebraMap k A)) [Nontrivial A] :
    Algebra.trdeg k A = D := by
  have := h.isDomain
  let K := FractionRing k
  obtain ⟨_, _, _⟩ := RegGenSmooth.chart_props h i hi
  obtain ⟨_, hd⟩ := RegGenSmooth.ringKrullDim_chart h
    (IsPullback.of_hasPullback p (spMap (algebraMap k K))) i hi
  have := IsLocalization.tensorRight (S := A) K (nonZeroDivisors k)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have : FaithfulSMul A (K ⊗[k] A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic A (K ⊗[k] A) :=
    IsLocalization.isAlgebraic _ (Algebra.algebraMapSubmonoid A (nonZeroDivisors k))
  obtain ⟨d, hd₁, hd₂⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq K (K ⊗[k] A)
  have e : d = D := by exact_mod_cast hd₁.symm.trans hd
  rw [← trdeg_eq k K A (K ⊗[k] A), hd₂, e]

theorem exists_etale_coords [IsIntegral X] (h : IsArithVar p D) :
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  have := h.isDomain
  have := h.charZero_base
  have := h.isNoetherianRing
  obtain ⟨A, _, _, i, _, a, -, hi⟩ := exists_affine_chart_over p (genericPoint X)
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩
  obtain ⟨_, _, _⟩ := RegGenSmooth.chart_props h i hi
  obtain ⟨f, hf, hs⟩ := exists_away k A (trdeg_chart h i hi)
  let B := Localization.Away f
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsOpenImmersion (spMap (algebraMap A B)) := IsOpenImmersion.of_isLocalization f
  let j : Sp B ⟶ X := spMap (algebraMap A B) ≫ i
  have hj : j ≫ p = spMap (algebraMap k B) := by
    rw [Category.assoc, hi, IsScalarTower.algebraMap_eq k A B, ← Spec.map_comp]
    rfl
  have h₁ : SmoothOfRelativeDimension D (j ≫ p) := by
    rw [hj]
    refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension D)).mpr ?_
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).mpr hs)
  have h₂ : SmoothOfRelativeDimension D (j.opensRange.ι ≫ p) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc]
    have : SmoothOfRelativeDimension (0 + D) (j.isoOpensRange.inv ≫ j ≫ p) := inferInstance
    rwa [zero_add] at this
  refine ModelCharts.exists_etale_coords_of_opens p D j.opensRange ?_
  exact ⟨genericPoint _, genericPoint_eq_of_isOpenImmersion j⟩

end GlobalTheory.GenericEtale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyNotMemChartBallSaturation
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SaturationClosed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


omit [NumberField E] [IsCMField E] in
def adjEnt {Ψ : Finset (E →+* ℂ)} (k w : Frame Ψ r) (τ : Ψ) (a c : Fin r) : ℂ :=
  (Matrix.adjugate (mat k τ) * mat w τ) a c

omit [NumberField E] [IsCMField E] in
theorem lact_lact {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact a (lact b x) = lact (a * b) x := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
    Matrix (Fin r) (Fin r) ℂ) = (((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]; rfl


omit [NumberField E] [IsCMField E] in
theorem adjEnt_rmul {Ψ : Finset (E →+* ℂ)} (k b : Frame Ψ r) (hb : b ∈ Bor Ψ r) (τ : Ψ) (a c : Fin r)
    (hca : c < a) : adjEnt k (rmul k b) τ a c = 0 := by
  have h1 : mat (rmul k b) τ = mat k τ * mat b τ := rfl
  rw [adjEnt, h1, ← Matrix.mul_assoc, Matrix.adjugate_mul]
  simp [Matrix.smul_mul, mat, (hb τ).2 a c hca]


omit [NumberField E] [IsCMField E] in
theorem exists_of_adjEnt {Ψ : Finset (E →+* ℂ)} (k w : Frame Ψ r) (hk : ∀ τ, (mat k τ).det ≠ 0)
    (hw : ∀ τ, (mat w τ).det ≠ 0) (h0 : ∀ τ a c, c < a → adjEnt k w τ a c = 0) :
    ∃ b ∈ Bor Ψ r, w = rmul k b := by
  refine ⟨fun τ => ((mat k τ)⁻¹ * mat w τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩, ?_⟩
  · show ((mat k τ)⁻¹ * mat w τ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero (hk τ)) (hw τ)
  · show ((mat k τ)⁻¹ * mat w τ) a c = 0
    rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply]
    have := h0 τ a c hca
    rw [adjEnt] at this
    rw [this, smul_zero]
  · funext τ
    show mat w τ = mat k τ * ((mat k τ)⁻¹ * mat w τ)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 (hk τ))]

omit [NumberField E] [IsCMField E] in
theorem continuous_mat {α : Type} [TopologicalSpace α] {Ψ : Finset (E →+* ℂ)} {f : α → Frame Ψ r}
    (hf : Continuous f) (τ : Ψ) : Continuous fun p => mat (f p) τ :=
  (continuous_apply τ).comp hf

omit [NumberField E] [IsCMField E] in
theorem continuous_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) :
    Continuous (lact (Ψ := Ψ) γ) := by
  refine continuous_pi fun τ => ?_
  exact continuous_const.matrix_mul (continuous_mat continuous_id τ)

omit [NumberField E] [IsCMField E] in
theorem continuous_adjEnt {α : Type} [TopologicalSpace α] {Ψ : Finset (E →+* ℂ)} {f g : α → Frame Ψ r}
    (hf : Continuous f) (hg : Continuous g) (τ : Ψ) (a c : Fin r) :
    Continuous fun p => adjEnt (f p) (g p) τ a c :=
  (((continuous_mat hf τ).matrix_adjugate).matrix_mul (continuous_mat hg τ)).matrix_elem a c

theorem eventually_not_mem_saturation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (x : Frame X.Ψ r) (ρ : ℝ), (∀ z : V (nd X), ‖z‖ ≤ ρ → z ∈ OmF X x) →
    ∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) →
    ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y' = lact γ (rmul (cpt X x z) b) := by
  intro E _ _ _ r X x ρ hΩ y hy hny
  have hcpt : Continuous (cpt X x) := (GlobalTheory.InterpCompare.differentiable_chart X x).continuous
  have hK : IsCompact (Metric.closedBall (0 : V (nd X)) ρ) := isCompact_closedBall 0 ρ
  have key : ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ, ∀ᶠ p : Frame X.Ψ r × V (nd X) in 𝓝 (y, z),
      ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, p.1 ≠ lact γ (rmul (cpt X x p.2) b) := by
    intro z hz
    have hz' : ‖z‖ ≤ ρ := by simpa using hz
    have hk : cpt X x z ∈ X.dom := hΩ z hz'
    obtain ⟨U, hU, U', hU', hfin⟩ := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X y hy _ hk
    have h1 : ∀ᶠ p : Frame X.Ψ r × V (nd X) in 𝓝 (y, z), p.1 ∈ U ∧ cpt X x p.2 ∈ U' := by
      refine Filter.Eventually.and (continuous_fst.continuousAt.preimage_mem_nhds hU) ?_
      exact (hcpt.comp continuous_snd).continuousAt.preimage_mem_nhds hU'
    have h2 : ∀ᶠ p : Frame X.Ψ r × V (nd X) in 𝓝 (y, z),
        ∀ δ ∈ {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r, lact γ u = rmul u' b},
          ∃ τ : X.Ψ, ∃ a c : Fin r, c < a ∧ adjEnt (cpt X x p.2) (lact δ p.1) τ a c ≠ 0 := by
      refine (Filter.eventually_all_finite hfin).2 fun δ hδ => ?_
      have hopen : IsOpen {p : Frame X.Ψ r × V (nd X) |
          ∃ τ : X.Ψ, ∃ a c : Fin r, c < a ∧ adjEnt (cpt X x p.2) (lact δ p.1) τ a c ≠ 0} := by
        simp only [Set.setOf_exists]
        refine isOpen_iUnion fun τ => isOpen_iUnion fun a => isOpen_iUnion fun c => ?_
        by_cases hca : c < a
        · simp only [hca, true_and]
          exact isOpen_ne_fun (continuous_adjEnt (hcpt.comp continuous_snd)
            ((continuous_lact δ).comp continuous_fst) τ a c) continuous_const
        · simp [hca]
      refine hopen.mem_nhds ?_
      by_contra hcon
      simp only [Set.mem_setOf_eq, not_exists, not_and, not_not] at hcon
      have hdk : ∀ τ, (mat (cpt X x z) τ).det ≠ 0 := fun τ => (hk τ).1
      have hdw : ∀ τ, (mat (lact δ y) τ).det ≠ 0 := by
        intro τ h0
        have e : y = lact δ⁻¹ (lact δ y) := by rw [lact_lact, inv_mul_cancel, lact_one]
        have : (mat y τ).det = 0 := by
          rw [e]
          show (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat (lact δ y) τ).det = 0
          rw [Matrix.det_mul, h0, mul_zero]
        exact (hy τ).1 this
      obtain ⟨b, hb, hwb⟩ := exists_of_adjEnt _ _ hdk hdw hcon
      refine hny ⟨δ⁻¹, X.Γ.inv_mem hδ.1, b, hb, z, hz', ?_⟩
      rw [← hwb, lact_lact, inv_mul_cancel, lact_one]
    filter_upwards [h1, h2] with p hp1 hp2
    intro γ hγ b hb he
    have hδ : γ⁻¹ ∈ {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r, lact γ u = rmul u' b} := by
      refine ⟨X.Γ.inv_mem hγ, p.1, hp1.1, cpt X x p.2, hp1.2, b, hb, ?_⟩
      rw [he, lact_lact, inv_mul_cancel, lact_one]
    obtain ⟨τ, a, c, hca, hne⟩ := hp2 _ hδ
    apply hne
    rw [he, lact_lact, inv_mul_cancel, lact_one]
    exact adjEnt_rmul _ _ hb τ a c hca
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun y' z => ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, y' ≠ lact γ (rmul (cpt X x z) b)) key] with y' hy'
  rintro ⟨γ, hγ, b, hb, z, hz, he⟩
  exact hy' z (by simpa using hz) γ hγ b hb he

end GlobalTheory.SaturationClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineGaloisCoverDualNumberEpiStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_galois_cover_dual_number_epi : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ Y), ∃ (R'' : Type) (_ : CommRing R'') (g₁ : R' →+* R'') (x'' : Sp R'' ⟶ X) (d₁ : DualNumber R' →+* DualNumber R''), x'' ≫ π = spMap g₁ ≫ x ∧ d₁.comp (algebraMap R' (DualNumber R')) = (algebraMap R'' (DualNumber R'')).comp g₁ ∧ (TrivSqZeroExt.fstHom R'' R'' R'').toRingHom.comp d₁ = g₁.comp (TrivSqZeroExt.fstHom R' R' R').toRingHom ∧ (∀ r : R', d₁.comp (epsScaleR r) = (epsScaleR (g₁ r)).comp d₁) ∧ Epi (spMap d₁) := by
  first | (exact @GlobalTheory.DualCover.exists_dualCover) | (exact GlobalTheory.DualCover.exists_dualCover) | (intros; apply GlobalTheory.DualCover.exists_dualCover  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjGLOfCharpolyEqOfSeparable
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SepConj

theorem conj_of_charpoly_eq_of_separable : ∀ (K : Type) [Field K] (n : ℕ) (a b : GL (Fin n) K),
    a.val.charpoly = b.val.charpoly → a.val.charpoly.Separable → ∃ h : GL (Fin n) K, b = h⁻¹ * a * h := by
  intro K _ n a b he hs
  exact GlobalTheory.BCT.ClsFin.conj_of_charpoly a b hs he

end GlobalTheory.SepConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentEndomorphismQuotientGroupSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_endomorphism_quotient_group_scheme : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (H : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ f : A ⟶ A, IsMonHom f → (∀ h ∈ H, h ≫ f ∈ H) → ∃ f' : A' ⟶ A', IsMonHom f' ∧ ψ ≫ f' = f ≫ ψ := by
  first | exact @GlobalTheory.UPel.HT.Hecke.exists_desc_endo | exact GlobalTheory.UPel.HT.Hecke.exists_desc_endo | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_desc_endo; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSubextensionCls
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.LBDescent

theorem exists_finite_subextension_cls (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (B X : Scheme.{0}) (pB : B ⟶ Sp K) [QuasiCompact pB]
    [QuasiSeparated pB] (p : X ⟶ Sp Ω) (φ : X ⟶ B)
    (hX : IsPullback φ p pB (spMap (algebraMap K Ω))) (L : LB X) (hL : L.IsLB) :
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧
      ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp F) (φ₁ : X₁ ⟶ B),
        IsPullback φ₁ p₁ pB (spMap (algebraMap K F)) →
        ∀ j : X ⟶ X₁, j ≫ φ₁ = φ → j ≫ p₁ = p ≫ spMap (algebraMap F Ω) →
          ∃ x : CechPic.Pic X₁, CechPic.pull j x = CechPic.cls L hL := by
  obtain ⟨R, M, ρ, ⟨T, hT⟩, hM, h1, h2, hI⟩ := exists_fg_lb pB p φ hX L hL
  let F : IntermediateField K Ω := IntermediateField.adjoin K (T : Set Ω)
  have hle : R ≤ F.toSubalgebra := by
    rw [← hT]
    exact IntermediateField.algebra_adjoin_le_adjoin K _
  refine ⟨F, IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral), ?_⟩
  intro X₁ p₁ φ₁ hX₁ j hj1 hj2
  let ι : R →+* F := (Subalgebra.inclusion hle).toRingHom
  have e1 : spMap ι ≫ spMap (algebraMap K R) = spMap (algebraMap K F) := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  have e2 : spMap (algebraMap F Ω) ≫ spMap ι = spMap R.val.toRingHom := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  let q : X₁ ⟶ Limits.pullback pB (spMap (algebraMap K R)) :=
    Limits.pullback.lift φ₁ (p₁ ≫ spMap ι) (by rw [Category.assoc, e1, hX₁.w])
  have hq : j ≫ q = ρ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, hj1, h1]
    · rw [Category.assoc, Limits.pullback.lift_snd, ← Category.assoc, hj2, Category.assoc, e2, h2]
  refine ⟨CechPic.pull q (CechPic.cls M hM), ?_⟩
  rw [← CechPic.pull_comp, hq, ← CechPic.cls_pull hM ρ (pull_isLB hM ρ), eq_comm, CechPic.cls_eq_iff]
  exact hI

end GlobalTheory.LBDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasNonzeroSecPowOfAmpleSubAmpleStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hasNonzeroSec_pow_of_ample_sub_ample' : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsAmpleLB B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  first | exact @GlobalTheory.exists_hasNonzeroSec_pow_of_ample_sub_ample | exact GlobalTheory.exists_hasNonzeroSec_pow_of_ample_sub_ample | (intros; apply GlobalTheory.exists_hasNonzeroSec_pow_of_ample_sub_ample <;> assumption)
end

