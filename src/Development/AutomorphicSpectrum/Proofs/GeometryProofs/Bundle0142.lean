module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHolds
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0094
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0123
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0025
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0004
public import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
public import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0115
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncModelEmbeddedLogResolution
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinCoordsArithVar
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0042
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0048
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0140
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CiGrDeg
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationCharts
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TorusUniformizationContinuous

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticProvisionHolds
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem prov_an : Prov.An :=
  ⟨GlobalTheory.CompanionTheory.Ar.Giv.tailBound_holds, _root_.GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds, _root_.GlobalTheory.CompanionTheory.Ar.Giv.SignedConv.convergenceSigned, _root_.GlobalTheory.CompanionTheory.Ar.Giv.convergenceRate_holds, _root_.GlobalTheory.CompanionTheory.Ar.Giv.unifInt_holds,
    _root_.GlobalTheory.CompanionTheory.Ar.Giv.pullbackStatement, _root_.GlobalTheory.CompanionTheory.Ar.Giv.regGlobalStatement_holds⟩

end GlobalTheory.CompanionTheory.Ar.Link
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockExtensionArithVar
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.Good

theorem coord_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  unfold mCoordIdeal
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem join_blocks {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {M : ℕ} (y₂ : (Σ _ : Unit, Fin M) → Ω) (hy : IsRelevant (mCoordIdeal y))
    (h₂ : ∃ i, y₂ ⟨(), i⟩ ≠ 0) : ∀ k, ∃ i, joinVec y y₂ ⟨k, i⟩ ≠ 0 := by
  rintro (k | u)
  · obtain ⟨i, hi⟩ := hy k
    exact ⟨i, coord_ne_zero y ⟨k, i⟩ hi⟩
  · obtain ⟨i, hi⟩ := h₂
    exact ⟨i, hi⟩

theorem exists_good_model : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomog β b → β ∉ mCoordIdeal y → ∃ (K' : Type) (_ : Fintype K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (y' : (Σ k, ι' k) → Ω) (J : Ideal (MRing ι')) (R : AnLogRes (mCoordIdeal y') J e) (Amp : HermLine ι'), IsBlockMap κ v ∧ y' ∘ v = y ∧ blockFnField y' = blockFnField y ∧ IsArithVar (mCoordIdeal y') (e + 1) ∧ IsEmbedded R.A (mCoordIdeal y') R.U R.lift ∧ IsSmoothHerm Amp ∧ IsPotential R.A (potOf R Amp) ∧ IsPosPot R.A (potOf R Amp) ∧ ∀ z ∈ mcPts (mCoordIdeal y'), evC z (rename v β) = 0 → z ∈ mcPts J := by
  intro hRes K _ ι _ Ω _ _ y e β b hV hβ hβP
  obtain ⟨M, y₂, J, ⟨i₀, hi₀⟩, hfield, hJh, hJ, hsnc, hz⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.SncRes.exists_snc_model hRes K ι Ω y e β b hV hβ hβP
  have hj := (_root_.GlobalTheory.CompanionTheory.Ar.Cmp.join_block_maps).1 K ι Unit (fun _ => Fin M) Ω y y₂
  have hb₁ := hj.1
  have hcomp : joinVec y y₂ ∘ joinInl ι (fun _ : Unit => Fin M) = y := hj.2.2.1
  have hblocks := join_blocks y y₂ hV.2.1.2.2 ⟨i₀, hi₀⟩
  have harith : IsArithVar (mCoordIdeal (joinVec y y₂)) (e + 1) := by
    refine GlobalTheory.T.isArithVar_of_block_algebraic K ι (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M) Sum.inl
      (joinInl ι fun _ : Unit => Fin M) Ω (joinVec y y₂) (e + 1) hb₁ hblocks ?_ ?_
    · rw [hcomp]; exact hV
    · rw [hcomp, hfield]
      intro t ht
      exact isAlgebraic_algebraMap (⟨t, ht⟩ : blockFnField y)
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.isEmbedded_of_isSncModel (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M) Ω (joinVec y y₂) e J
    harith hJh hJ hsnc
  obtain ⟨Amp, h₁, h₂, h₃⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.exists_smooth_hermLine_posPot_of_isEmbedded (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M)
    (mCoordIdeal (joinVec y y₂)) J e R hR
  exact ⟨K ⊕ Unit, inferInstance, joinIdx ι fun _ : Unit => Fin M, inferInstance, Sum.inl,
    joinInl ι fun _ : Unit => Fin M, joinVec y y₂, J, R, Amp, hb₁, hcomp, hfield, harith, hR, h₁, h₂, h₃, hz⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.Good
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderBaseChangeGeneric
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.BaseChangeOrder

theorem exists_smul_mem_of_separates {R R' T : Type} [CommRing R] [CommRing R'] [IsDomain R'] [Finite T]
    (φ : R →+* R') (A : Subalgebra R (T → R))
    (hsep : ∀ s t : T, s ≠ t → ∃ a ∈ A, φ (a s) ≠ φ (a t)) :
    ∃ d : R, φ d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A := by
  classical
  cases nonempty_fintype T
  have h1 : ∀ t s : T, s ≠ t → ∃ b ∈ A, b s = 0 ∧ φ (b t) ≠ 0 := by
    intro t s hst
    obtain ⟨a, ha, hne⟩ := hsep s t hst
    refine ⟨a - algebraMap R _ (a s), A.sub_mem ha (A.algebraMap_mem _), by simp, ?_⟩
    simpa [sub_eq_zero, map_sub] using hne.symm
  have h2 : ∀ t, ∃ c ∈ A, (∀ s, s ≠ t → c s = 0) ∧ φ (c t) ≠ 0 := by
    intro t
    choose! b hbA hb0 hb1 using h1 t
    refine ⟨∏ s ∈ Finset.univ.erase t, b s,
      Subalgebra.prod_mem _ fun s hs => hbA s (Finset.ne_of_mem_erase hs), ?_, ?_⟩
    · intro s hs
      rw [Finset.prod_apply]
      exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩) (hb0 s hs)
    · rw [Finset.prod_apply, map_prod]
      exact Finset.prod_ne_zero_iff.2 fun s hs => hb1 s (Finset.ne_of_mem_erase hs)
  choose c hcA hc0 hc1 using h2
  refine ⟨∏ t, c t t, by rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun t _ => hc1 t, fun f => ?_⟩
  have key : (∏ t, c t t) • f = ∑ t, (f t * ∏ u ∈ Finset.univ.erase t, c u u) • c t := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rw [Finset.sum_eq_single x]
    · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
      ring
    · intro t _ ht
      rw [hc0 t x ht.symm, mul_zero]
    · simp
  rw [key]
  exact Subalgebra.sum_mem _ fun t _ => Subalgebra.smul_mem _ (hcA t) _

variable {R : Type} [CommRing R] {T : Type} [CommGroup T]

theorem translate_mem {A : Subalgebra R (T → R)} (hA : IsHopfOrder A) (t : T) {f : T → R} (hf : f ∈ A) :
    (fun h => f (t * h)) ∈ A := by
  have key : ∀ g ∈ prodSpan A, (fun h => g (t, h)) ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      exact A.smul_mem hb (a t)
    | zero => exact A.zero_mem
    | add x y _ _ hx hy => exact A.add_mem hx hy
    | smul r x _ hx => exact A.smul_mem hx r
  exact key _ (hA.comul f hf)

def transl {A : Subalgebra R (T → R)} (hA : IsHopfOrder A) (s : T) : A →+* A where
  toFun f := ⟨fun h => (f : T → R) (s * h), translate_mem hA s f.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R'] [Algebra R R']

theorem pt_comp_emb {Γ : QFGroup R T} {Γ' : QFGroup R' T} {F : Γ'.G.left ⟶ Γ.G.left}
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F) {A : Subalgebra R (T → R)}
    {j : Γ.G.left ⟶ Spec (CommRingCat.of A)} (hj : Γ.IsEmb A j) (t : T) :
    (Γ'.pt t).left ≫ F ≫ j = Spec.map (CommRingCat.ofHom
      ((algebraMap R' (FractionRing R')).comp ((algebraMap R R').comp
        ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom)))) := by
  obtain ⟨B, _, i, k, k', σ, hinj, h1, h2, -, h4, h5⟩ := hbc.pts
  have hρ := Spec.map_preimage (σ t ≫ j)
  set ρ := Spec.preimage (σ t ≫ j) with hρdef
  have e1 : ρ ≫ CommRingCat.ofHom k = CommRingCat.ofHom
      ((algebraMap R (FractionRing R)).comp ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, ← Category.assoc, h4, hj.pt]
  have e2 : ∀ a : A, ρ.hom a = i ((a : T → R) t) := by
    intro a
    apply hinj
    have := congrArg (fun g => g.hom a) e1
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    rw [this, ← RingHom.comp_apply k i, h1]
    rfl
  rw [← Category.assoc, ← h5 t, Category.assoc, ← hρ, ← Spec.map_comp]
  congr 1
  ext a
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  rw [e2, ← RingHom.comp_apply k' i, h2]
  rfl

theorem separates {Γ : QFGroup R T} {Γ' : QFGroup R' T} {F : Γ'.G.left ⟶ Γ.G.left}
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F) {A : Subalgebra R (T → R)}
    {j : Γ.G.left ⟶ Spec (CommRingCat.of A)} (hj : Γ.IsEmb A j) [Mono j] (s t : T) (hst : s ≠ t) :
    ∃ a ∈ A, algebraMap R R' (a s) ≠ algebraMap R R' (a t) := by
  by_contra hcon
  push_neg at hcon
  apply hst
  have e : (Γ'.pt s).left ≫ F ≫ j = (Γ'.pt t).left ≫ F ≫ j := by
    rw [pt_comp_emb hbc hj, pt_comp_emb hbc hj]
    congr 2
    ext a
    simp only [RingHom.comp_apply]
    exact congrArg _ (hcon a.1 a.2)
  have e' : (Γ'.pt s).left ≫ F = (Γ'.pt t).left ≫ F := by
    rw [← cancel_mono j]
    simpa only [Category.assoc] using e
  have e'' : (Γ'.pt s).left = (Γ'.pt t).left := by
    apply hbc.cart.hom_ext e'
    rw [Over.w, Over.w]
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R'))) := inferInstance
  exact Γ'.pt_inj s t x x (by rw [e''])

end GlobalTheory.CompanionTheory.Ar.BT.BaseChangeOrder

namespace GlobalTheory.CompanionTheory.Ar.BT.BaseChangeOrder

variable {R : Type} [CommRing R] {T : Type} [CommGroup T]
variable [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R'] [Algebra R R']

theorem isPullback_spec {A : Subalgebra R (T → R)} {A' : Subalgebra R' (T → R')}
    (e : R' ⊗[R] A ≃ₐ[R'] A') :
    IsPullback (Spec.map (CommRingCat.ofHom (e.toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight.toRingHom : A →+* R' ⊗[R] A))))
      (Spec.map (CommRingCat.ofHom (algebraMap R' A')))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  have P := CommRingCat.isPushout_tensorProduct R R' A
  have P' : IsPushout (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R' A'))
      (CommRingCat.ofHom (e.toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight.toRingHom : A →+* R' ⊗[R] A))) := by
    refine P.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · ext x t
      have h : e (x ⊗ₜ[R] 1) = algebraMap R' A' x := by
        rw [← e.commutes]
        rfl
      simpa using congrFun (congrArg (fun y : A' => (y : T → R')) h) t
    · ext x
      simp
  exact isPullback_SpecMap_of_isPushout _ _ _ _ P'.flip

theorem exists_emb {Γ : QFGroup R T} {Γ' : QFGroup R' T} {F : Γ'.G.left ⟶ Γ.G.left}
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F) {A : Subalgebra R (T → R)} {A' : Subalgebra R' (T → R')}
    (hA : IsHopfOrder A) (hA' : IsHopfOrder A') (e : R' ⊗[R] A ≃ₐ[R'] A')
    (he : ∀ (a : A) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t))
    {j : Γ.G.left ⟶ Spec (CommRingCat.of A)} (hj : Γ.IsEmb A j) (hopen : IsOpenImmersion j)
    (hcov : Γ.TranslatesCover A j ⊤) :
    ∃ j' : Γ'.G.left ⟶ Spec (CommRingCat.of A'), Γ'.IsEmb A' j' ∧ IsOpenImmersion j' ∧
      Γ'.TranslatesCover A' j' ⊤ := by
  have hsq := isPullback_spec e
  set ψ : A →+* A' := e.toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight.toRingHom : A →+* R' ⊗[R] A) with hψ
  have hψt : ∀ (a : A) (t : T), (ψ a : T → R') t = algebraMap R R' ((a : T → R) t) := fun a t => he a t
  have hw : (F ≫ j) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [Category.assoc, hj.isOver, hbc.cart.w]
  let j' : Γ'.G.left ⟶ Spec (CommRingCat.of A') := hsq.lift (F ≫ j) Γ'.G.hom hw
  have hj1 : j' ≫ Spec.map (CommRingCat.ofHom ψ) = F ≫ j := hsq.lift_fst _ _ _
  have hj2 : j' ≫ Spec.map (CommRingCat.ofHom (algebraMap R' A')) = Γ'.G.hom := hsq.lift_snd _ _ _
  have hl : IsPullback F j' j (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_bot ?_ hj1.symm hsq
    rw [hj2, hj.isOver]
    exact hbc.cart
  have hj'open : IsOpenImmersion j' := MorphismProperty.of_isPullback hl hopen
  have hemb : Γ'.IsEmb A' j' := by
    refine ⟨hj2, fun t => ?_⟩
    apply hsq.hom_ext
    · rw [Category.assoc, hj1, pt_comp_emb hbc hj, ← Spec.map_comp]
      congr 1
      ext a
      simp [hψt]
    · rw [Category.assoc, hj2, ← Spec.map_comp, Over.w]
      congr 1
  refine ⟨j', hemb, hj'open, fun P => ?_⟩
  obtain ⟨t, g₀, -, hg₀⟩ := hcov (PrimeSpectrum.comap ψ P)
  have hcomm : ∀ a : A, transl hA' t⁻¹ (ψ a) = ψ (transl hA t⁻¹ a) := by
    intro a
    ext h
    rw [hψt]
    change (ψ a : T → R') (t⁻¹ * h) = algebraMap R R' ((a : T → R) (t⁻¹ * h))
    exact hψt a (t⁻¹ * h)
  let P' : PrimeSpectrum A' := PrimeSpectrum.comap (transl hA' t⁻¹) P
  have hP' : j g₀ = Spec.map (CommRingCat.ofHom ψ) P' := by
    apply PrimeSpectrum.ext
    ext a
    have h1 := hg₀ (transl hA t⁻¹ a) a (fun h => by
      change (a : T → R) h = (a : T → R) (t⁻¹ * (t * h))
      rw [inv_mul_cancel_left])
    change a ∈ (j g₀).asIdeal ↔ transl hA' t⁻¹ (ψ a) ∈ P.asIdeal
    rw [← h1, hcomm]
    rfl
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := j) (g := Spec.map (CommRingCat.ofHom ψ)) g₀ P' hP'
  have hg' : j' (hl.isoPullback.inv z) = P' := by
    rw [← Scheme.Hom.comp_apply, hl.isoPullback_inv_snd, hz]
  refine ⟨t, hl.isoPullback.inv z, trivial, fun f f' hf => ?_⟩
  rw [hg']
  change _ ↔ transl hA' t⁻¹ f' ∈ P.asIdeal
  have : transl hA' t⁻¹ f' = f := by
    ext h
    change (f' : T → R') (t⁻¹ * h) = (f : T → R') h
    rw [hf, mul_inv_cancel_left]
  rw [this]

end GlobalTheory.CompanionTheory.Ar.BT.BaseChangeOrder

theorem GlobalTheory.CompanionTheory.Ar.BT.btOrder_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → (∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤) ∧ Γ'.btOrder ⊤ = extOrder (algebraMap R R') (Γ.btOrder ⊤) := by
  intro R _ _ _ _ T _ _ Γ R' _ _ _ Γ' F hbc
  have hH := _root_.PositivityTheory.UnitarySelfGeneration.bt_hopf R T Γ
  obtain ⟨j, hj, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.exists_unique_emb_btOrder_top R T Γ
  obtain ⟨hopen, hcov⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.isOpenImmersion_emb_and_translatesCover R T Γ j hj
  have hd : ∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ :=
    BaseChangeOrder.exists_smul_mem_of_separates _ _ (BaseChangeOrder.separates hbc hj)
  refine ⟨hd, ?_⟩
  obtain ⟨hH', e, he⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change R T R' (Γ.btOrder ⊤) hH hd
  obtain ⟨j', hj', hopen', hcov'⟩ := BaseChangeOrder.exists_emb hbc hH hH' e he hj hopen hcov
  exact _root_.GlobalTheory.CompanionTheory.Ar.BT.btOrder_eq_of_open_cover R' T Γ' _ hH' j' hj' hopen' hcov'
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedGroupSmoothRelDim
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.CompanionTheory.Ggeo

theorem exists_smoothOfRelativeDimension_of_geometricallyConnected :
    ∀ (X : Scheme.{0}) [ConnectedSpace X] (G : Over X) [GrpObj G], Smooth G.hom →
      GeometricallyConnected G.hom → ∃ g : ℕ, SmoothOfRelativeDimension g G.hom := by
  intro X _ G _ hs hc
  haveI : Smooth G.hom := hs
  obtain ⟨d, W, hxW, hW⟩ : ∃ (d : G.left → ℕ) (W : G.left → G.left.Opens), (∀ x, x ∈ W x) ∧
      ∀ x, SmoothOfRelativeDimension (d x) ((W x).ι ≫ G.hom) := by
    choose d W hxW hW using fun x => ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom x
    exact ⟨d, W, hxW, hW⟩
  have hres : ∀ (x : G.left) (V : G.left.Opens), V ≤ W x →
      SmoothOfRelativeDimension (d x) (V.ι ≫ G.hom) := by
    intro x V hV
    have h := HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension (d x))
      (G.left.homOfLE hV) ((W x).ι ≫ G.hom) (hW x)
    rwa [← Category.assoc, Scheme.homOfLE_ι] at h
  have hd : IsLocallyConstant d := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨W x, (W x).isOpen, hxW x, fun y hy => ?_⟩
    have h1 := hres x (W x ⊓ W y) inf_le_left
    have h2 := hres y (W x ⊓ W y) inf_le_right
    exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h2 h1 ⟨y, hy, hxW y⟩
  let e : X ⟶ G.left := (η[G]).left
  have hcomp : e ≫ G.hom = 𝟙 X := Over.w (η[G])
  have he : ∀ s : X, G.hom (e s) = s := by
    intro s
    have h := congrArg (fun g : X ⟶ X => g s) hcomp
    simpa using h
  have hfib : ∀ s : X, _root_.IsPreconnected (G.hom ⁻¹' {s}) := by
    intro s
    rw [← Scheme.Hom.range_fiberι]
    exact isPreconnected_range (Scheme.Hom.continuous _)
  obtain ⟨s₀⟩ : Nonempty X := inferInstance
  have hconst : ∀ x, d x = d (e s₀) := by
    intro x
    have h1 : d x = d (e (G.hom x)) :=
      hd.apply_eq_of_isPreconnected (hfib (G.hom x)) rfl (he (G.hom x))
    have h2 : d (e (G.hom x)) = d (e s₀) :=
      (hd.comp_continuous (Scheme.Hom.continuous e)).apply_eq_of_isPreconnected
        isPreconnected_univ trivial trivial
    exact h1.trans h2
  refine ⟨d (e s₀), ?_⟩
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (d (e s₀))) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (d (e s₀))) W
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩)
    (fun x => by rw [← hconst x]; exact hW x)

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieLatticeDegree
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.GrDeg

theorem grLine_deg_eq_sub : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] [FiniteDimensional K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (S : Set (Cpt ξ)) (L L' : Lat ξ V) (r r' : ℕ) (b₀ : Fin r → V) (U' : Submodule Ω V), IsCptGen ξ → Smooth G.hom → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → LinearIndependent Ω b₀ → L.IsFlagVBOn S b₀ → L'.IsVBOn S r' U' → IsCompl (Submodule.span Ω (Set.range b₀)) U' → (∀ q ∈ S, M.lat q = L q ⊔ L' q) → ∃ W : ℕ → Submodule K Vz, W 0 = ⊥ ∧ W r = Submodule.span K {v | ∃ e ∈ L ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} ∧ ∀ s : Fin r, Y.IsDeg (L.gr b₀ s) (subDeg C (Y.lieLat Mz) (W (s + 1)) - subDeg C (Y.lieLat Mz) (W s)) :=
  PositivityTheory.HtPt.Ci.gr_deg

end GlobalTheory.CompanionTheory.Ar.GrDeg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentFiniteCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts

theorem exists_halfPolydisc_cover : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∃ (n nc : ℕ) (w : Fin nc → (Fin n → ℂ) → (Σ k, J k) → ℂ) (a : Fin nc → ℕ), (∀ i, a i ≤ n) ∧ (∀ i, AnalyticOnNhd ℂ (w i) (ball 0 1)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, w i t ∈ mcPts (mCoordIdeal y)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, (∀ j : Fin n, (j : ℕ) < a i → t j ≠ 0) → ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w i t) → 𝔐.Interior z) ∧ ∀ x ∈ mcPts (mCoordIdeal y), ∃ (i : Fin nc) (t : Fin n → ℂ) (b : K → ℂ), ‖t‖ ≤ 1 / 2 ∧ (∀ k, b k ≠ 0) ∧ x = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul b (w i t) :=
  PositivityTheory.Xgn.quotient_uniformization_charts

end GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFinitePullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem gramAt_continuous_anTop : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Fin r → (Xc →+ ℤ)) (H : (Sp ℂ ⟶ Z') → Matrix (Fin r) (Fin r) ℂ),
    (∀ (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
      ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G), (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) →
        H zc = RootHt.gramAt h (zc ≫ ρ) v) →
    @Continuous _ _ (anTop Z') _ H :=
  @PositivityTheory.Xgn.torus_uniformization_continuous

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

