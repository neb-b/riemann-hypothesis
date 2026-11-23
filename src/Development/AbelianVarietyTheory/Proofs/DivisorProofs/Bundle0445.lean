module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodSemilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentVanishingFiniteAlgebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsZmodOfFlatResolution
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedQis

theorem quasiIso_of_cone_acyclic {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K L : CochainComplex 𝒜 ℤ} (u : K ⟶ L) (h : (CochainComplex.mappingCone u).Acyclic) : QuasiIso u := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h
  have hu : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map u) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished u)).2 h
  rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hu

theorem flatS_cone {R : Type} [CommRing R] (F : Shv R) (hF : FlatS F) (T : Cx R) (hT : ∀ t, FlatS (T.X t))
    (ε : sgl F ⟶ T) (n : ℤ) : FlatS ((mappingCone ε).X n) := by
  obtain ⟨hiso, hzero⟩ := _root_.GlobalTheory.EtC.flatS_iso_and_zero R
  refine hiso (HomologicalComplex.homotopyCofiber.XIsoBiprod ε n (n + 1) rfl).symm
    (GlobalTheory.T.isLocallyFlatEtaleSheaf_biprod _ _ _ ?_ (hT n))
  by_cases h : n + 1 = 0
  · exact hiso (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 F (n + 1) h).symm hF
  · exact hzero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)

theorem quasiIso_extCx_of_flat : ∀ (Q q : ℕ) [NeZero Q] (h : q ∣ Q) (F : Shv (ZMod Q)) (T : Cx (ZMod Q))
    [T.IsStrictlyGE 0], FlatS F → (∀ t, FlatS (T.X t)) → ∀ ε : sgl F ⟶ T, QuasiIso ε →
    QuasiIso ((GlobalTheory.EtC.ScalarExt.extCx (ZMod.castHom h (ZMod q))).map ε) := by
  intro Q q _ h F T _ hF hT ε hε
  have hK : (mappingCone ε).Acyclic := GlobalTheory.mappingCone_acyclic_of_quasiIso _
  haveI : (mappingCone ε).IsStrictlyGE (-1) := CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1)
  have hE := _root_.GlobalTheory.EtC.flatExtAcyc.main Q q h (mappingCone ε) (-1) (flatS_cone F hF T hT ε) hK
  have hC : (mappingCone (((extSh (ZMod.castHom h (ZMod q))).mapHomologicalComplex _).map ε)).Acyclic := fun n =>
    (hE n).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso ε (extSh (ZMod.castHom h (ZMod q))))
  exact quasiIso_of_cone_acyclic _ hC

end GlobalTheory.EtC.RedQis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartBoundedCoefficients
section
open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankChart

open ValuativeRel

def coeffOnChart {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] (τ : R → D)
    (Y : Matrix (R ⊕ T) D k) : Matrix T R k :=
  (Y.submatrix Sum.inl τ).det⁻¹ • (Y.toRows₂.submatrix id τ * (Y.submatrix Sum.inl τ).adjugate)

theorem coeffOnChart_stack {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T]
    [Fintype D] [DecidableEq D] (τ : R → D)
    (Y₁ : Matrix R D k) (C : Matrix T R k) (h : (Y₁.submatrix id τ).det ≠ 0) :
    coeffOnChart τ (stack Y₁ C) = C := by
  have e1 : (stack Y₁ C).submatrix Sum.inl τ = Y₁.submatrix id τ := by
    rw [submatrix_inl_eq, toRows₁_stack]
  have e2 : (stack Y₁ C).toRows₂.submatrix id τ = C * Y₁.submatrix id τ := by
    ext i j; simp [stack, Matrix.mul_apply]
  rw [coeffOnChart, e1, e2, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    inv_mul_cancel₀ h, one_smul]

theorem coeffOnChart_continuousOn {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    [ContinuousInv₀ k] {R T D : Type} [Fintype R] [DecidableEq R] (τ : R → D) :
    ContinuousOn (coeffOnChart (T := T) (k := k) τ) {Y | (Y.submatrix Sum.inl τ).det ≠ 0} := by
  have hA : Continuous fun Y : Matrix (R ⊕ T) D k => Y.submatrix Sum.inl τ :=
    continuous_id.matrix_submatrix _ _
  have hB : Continuous fun Y : Matrix (R ⊕ T) D k => Y.toRows₂.submatrix id τ :=
    (continuous_id.matrix_submatrix Sum.inr id).matrix_submatrix _ _
  exact ContinuousOn.smul (f := fun Y : Matrix (R ⊕ T) D k => (Y.submatrix Sum.inl τ).det⁻¹)
    (hA.matrix_det.continuousOn.inv₀ fun Y hY => hY) (hB.matrix_mul hA.matrix_adjugate).continuousOn

theorem bounded_coeff_of_SB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D) :
    ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) →
      ∃ a : kˣ, ∀ (Y₁ : Matrix R D k) (C : Matrix T R k), f (GlobalTheory.RankChart.stack Y₁ C) ≠ 0 →
        C ∈ GlobalTheory.LocMod.Inhab.box T R a := by
  intro f hf hdet
  have hcl : IsClosed (Function.support f) := by
    have := (hf.1.isOpen_fiber 0).isClosed_compl
    simpa [Function.support, Set.compl_setOf] using this
  have hK : IsCompact (Function.support f) := by
    have h2 : HasCompactSupport f := hf.2
    rw [HasCompactSupport, tsupport, hcl.closure_eq] at h2
    exact h2
  have hcont : ContinuousOn (coeffOnChart (T := T) (k := k) τ) (Function.support f) :=
    (coeffOnChart_continuousOn τ).mono fun Y hY => hdet Y hY
  obtain ⟨a, ha⟩ := GlobalTheory.BoxCharComb.exists_box_superset (hK.image_of_continuousOn hcont)
  refine ⟨a, fun Y₁ C hY => ?_⟩
  have hd := hdet _ hY
  rw [submatrix_inl_eq, toRows₁_stack] at hd
  have := ha _ ⟨_, hY, coeffOnChart_stack τ Y₁ C hd⟩
  exact this

end GlobalTheory.RankChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecFunctionsEqOfRestrictionsOnPairsStatement
section
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_functions_eq_of_restrictions_on_pairs : ∀ {X : Scheme.{0}} (B B' : Type) [CommRing B] [CommRing B'] (x : Sp B ⟶ X) (ψ : Sp B' ⟶ Sp B) (a b : B'), (∀ (V' : (Sp B').affineOpens) (p : Pair x), V'.1 ≤ ψ ⁻¹ᵁ p.1.1.1 → (secMap (𝟙 (Sp B')) V'.1).hom a = (secMap (𝟙 (Sp B')) V'.1).hom b) → a = b := by
  first | exact @GlobalTheory.CechDR.AffLoc.eq_of_secMap_eq_on_pairs | exact GlobalTheory.CechDR.AffLoc.eq_of_secMap_eq_on_pairs | (intros; apply GlobalTheory.CechDR.AffLoc.eq_of_secMap_eq_on_pairs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryWeilRepresentationIsSmoothStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitUnitaryWeilRepresentation_isSmooth : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → GlobalTheory.SplitWeil.IsSmoothRep ω := by
  first | exact @GlobalTheory.KSp.isKW_isSmoothRep | exact GlobalTheory.KSp.isKW_isSmoothRep | (intros; apply GlobalTheory.KSp.isKW_isSmoothRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarCoeffEisensteinSeriesReversePoly
section
noncomputable section

open Polynomial CategoryTheory

namespace GlobalTheory.SerConj

open Formalism.IrreducibleCountingLemmas.TYPES

section Tensor

variable {ι : Type} {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

def semiMap (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v) :
    PiTensorProduct ℂ V →+ PiTensorProduct ℂ W :=
  PiTensorProduct.liftAddHom (fun p => σ p.1 • PiTensorProduct.tprod ℂ fun i => j i (p.2 i))
    (fun r f i hf => by
      rw [MultilinearMap.map_coord_zero _ i (by simp [hf]), smul_zero])
    (fun f => by simp)
    (fun r f i m₁ m₂ => by
      have e : ∀ m : V i, (fun k => j k (Function.update f i m k)) =
          Function.update (fun k => j k (f k)) i (j i m) := fun m =>
        funext fun k => Function.apply_update (fun k => j k) f i m k
      simp only [e, map_add (f := _), MultilinearMap.map_update_add, smul_add])
    (fun r r' f => by simp [add_smul])
    (fun r f i r' => by
      have e : ∀ m : V i, (fun k => j k (Function.update f i m k)) =
          Function.update (fun k => j k (f k)) i (j i m) := fun m =>
        funext fun k => Function.apply_update (fun k => j k) f i m k
      simp only [e, hj, MultilinearMap.map_update_smul, RingHom.id_apply, Function.update_eq_self,
        map_mul, smul_smul, mul_comm])

theorem semiMap_tprod (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v)
    (a : ℂ) (f : ∀ i, V i) :
    semiMap σ j hj (a • PiTensorProduct.tprod ℂ f) = σ a • PiTensorProduct.tprod ℂ fun i => j i (f i) := by
  rw [← PiTensorProduct.tprodCoeff_eq_smul_tprod]
  rfl

theorem semiMap_smul (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v)
    (a : ℂ) (x : PiTensorProduct ℂ V) : semiMap σ j hj (a • x) = σ a • semiMap σ j hj x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f => rw [smul_smul, semiMap_tprod, semiMap_tprod, smul_smul, map_mul]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem semiMap_map (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v)
    (A : ∀ i, V i →ₗ[ℂ] V i) (B : ∀ i, W i →ₗ[ℂ] W i) (h : ∀ i v, j i (A i v) = B i (j i v))
    (x : PiTensorProduct ℂ V) :
    semiMap σ j hj (PiTensorProduct.map A x) = PiTensorProduct.map B (semiMap σ j hj x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.map_tprod, semiMap_tprod, semiMap_tprod, map_smul, PiTensorProduct.map_tprod]
    simp only [h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem symm_smul {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (σ : ℂ ≃+* ℂ)
    (j : A ≃+ B) (hj : ∀ (a : ℂ) v, j (a • v) = σ a • j v) (a : ℂ) (w : B) :
    j.symm (a • w) = σ.symm a • j.symm w := by
  apply j.injective
  rw [hj]; simp

theorem semiMap_injective (σ : ℂ ≃+* ℂ) (j : ∀ i, V i ≃+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v) :
    Function.Injective (semiMap σ.toRingHom (fun i => (j i).toAddMonoidHom) hj) := by
  refine Function.LeftInverse.injective
    (g := semiMap σ.symm.toRingHom (fun i => (j i).symm.toAddMonoidHom) fun i => symm_smul σ (j i) (hj i)) fun x => ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine (congrArg _ (semiMap_tprod _ _ _ r f)).trans ((semiMap_tprod _ _ _ _ _).trans ?_)
    simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end Tensor

section Conj

variable {Γ : Type} [Group Γ]

def bcEquiv (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) : τ ≃+ bc σ τ :=
  (Module.finBasis ℂ τ).equivFun.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => σ.toAddEquiv)

theorem bcEquiv_smul (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (a : ℂ) (v : τ) :
    bcEquiv σ τ (a • v) = σ a • bcEquiv σ τ v := by
  refine funext fun i => ?_
  change σ ((Module.finBasis ℂ τ).repr (a • v) i) = σ a * σ ((Module.finBasis ℂ τ).repr v i)
  simp

theorem bcEquiv_ρ (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (γ : Γ) (v : τ) :
    bcEquiv σ τ (τ.ρ γ v) = (bc σ τ).ρ γ (bcEquiv σ τ v) := by
  refine funext fun i => ?_
  change σ ((Module.finBasis ℂ τ).repr (τ.ρ γ v) i) =
    (((LinearMap.toMatrix (Module.finBasis ℂ τ) (Module.finBasis ℂ τ) (τ.ρ γ)).map σ).mulVec
      fun k => σ ((Module.finBasis ℂ τ).repr v k)) i
  rw [← LinearMap.toMatrix_mulVec_repr (Module.finBasis ℂ τ) (Module.finBasis ℂ τ)]
  simp [Matrix.mulVec, dotProduct]

theorem character_bc (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (γ : Γ) : (bc σ τ).character γ = σ (τ.character γ) :=
  trace_bcRepr σ τ.ρ γ

theorem simple_bc [Fintype Γ] (σ : ℂ ≃+* ℂ) {τ : FDRep ℂ Γ} (h : Simple τ) : Simple (bc σ τ) := by
  rw [FDRep.simple_iff_char_is_norm_one] at h ⊢
  simp only [character_bc]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_natCast σ, ← h, map_sum]
  simp only [map_mul]

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isCuspidal_bc (σ : ℂ ≃+* ℂ) {τ : FDRep ℂ (GL ι K)} (h : IsCuspidal K τ) : IsCuspidal K (bc σ τ) := by
  intro s b hb hs w hw
  obtain ⟨v, rfl⟩ := (bcEquiv σ τ).surjective w
  rw [h s b hb hs v fun u hu => (bcEquiv σ τ).injective ((bcEquiv_ρ σ τ u v).trans (hw u hu)), map_zero]

theorem isConstituent_bc (σ : ℂ ≃+* ℂ) {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    {τ : FDRep ℂ (GL ι K)} (h : IsConstituent τ (hcRep K b lam)) :
    IsConstituent (bc σ τ) (hcRep K b fun c => bc σ (lam c)) := by
  obtain ⟨φ, hφ, hne⟩ := h
  let J := semiMap σ.toRingHom (fun c => (bcEquiv σ (lam c)).toAddMonoidHom) fun c => bcEquiv_smul σ (lam c)
  have hJ : Function.Injective J := semiMap_injective σ _ _
  let ψ : bc σ τ →ₗ[ℂ] hcSpace K b fun c => bc σ (lam c) :=
    { toFun := fun w => ⟨fun x => J ((φ ((bcEquiv σ τ).symm w)).1 x), fun p x => by
        refine (congrArg J ((φ ((bcEquiv σ τ).symm w)).2 p x)).trans ?_
        exact semiMap_map _ _ _ _ _ (fun c v => bcEquiv_ρ σ (lam c) _ v) _⟩
      map_add' := fun w w' => by
        ext x
        simp
      map_smul' := fun a w => by
        ext x
        change J ((φ ((bcEquiv σ τ).symm (a • w))).1 x) = a • J ((φ ((bcEquiv σ τ).symm w)).1 x)
        rw [symm_smul σ _ (bcEquiv_smul σ τ), map_smul]
        refine (semiMap_smul _ _ _ _ _).trans ?_
        simp [J] }
  refine ⟨ψ, fun γ => ?_, fun h0 => hne ?_⟩
  · refine LinearMap.ext fun w => Subtype.ext (funext fun x => ?_)
    obtain ⟨v, rfl⟩ := (bcEquiv σ τ).surjective w
    change J ((φ ((bcEquiv σ τ).symm ((bc σ τ).ρ γ (bcEquiv σ τ v)))).1 x) =
      J ((φ ((bcEquiv σ τ).symm (bcEquiv σ τ v))).1 (x * γ))
    rw [← bcEquiv_ρ, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    have := LinearMap.congr_fun (hφ γ) v
    rw [LinearMap.comp_apply] at this
    rw [this]
    rfl
  · refine LinearMap.ext fun v => Subtype.ext (funext fun x => hJ ?_)
    have := congrFun (congrArg Subtype.val (LinearMap.congr_fun h0 (bcEquiv σ τ v))) x
    change J ((φ ((bcEquiv σ τ).symm (bcEquiv σ τ v))).1 x) = 0 at this
    rw [AddEquiv.symm_apply_apply] at this
    rw [this]
    exact (map_zero J).symm

end Conj

section Label

variable {K : Type} [Field K]

theorem normRev_prod {α : Type} (s : Finset α) (P : α → K[X]) :
    C ((∏ c ∈ s, P c).coeff 0)⁻¹ * (∏ c ∈ s, P c).reverse = ∏ c ∈ s, C ((P c).coeff 0)⁻¹ * (P c).reverse := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reverse]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih, mul_coeff_zero, mul_inv, C_mul, reverse_mul_of_domain]
    ring

theorem normRev_normRev {f : K[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    C ((C (f.coeff 0)⁻¹ * f.reverse).coeff 0)⁻¹ * (C (f.coeff 0)⁻¹ * f.reverse).reverse = f := by
  have h1 : (C (f.coeff 0)⁻¹ * f.reverse).coeff 0 ≠ 0 := by
    rw [coeff_C_mul, coeff_zero_reverse, hm.leadingCoeff, mul_one]
    exact inv_ne_zero h0
  refine GlobalTheory.DualLabel.eq_of_rootsBar_eq (GlobalTheory.DualLabel.monic_normRev h1) hm ?_
  rw [GlobalTheory.DualLabel.rootsBar_normRev (GlobalTheory.DualLabel.monic_normRev h0) h1, GlobalTheory.DualLabel.rootsBar_normRev hm h0,
    Multiset.map_map]
  simp

variable [Fintype K] [DecidableEq K] {Cv : LabelConv K}

theorem hasLabelO_conj (O : LabelMap K Cv) (hO : LabelMapEquivariant O) {ι : Type} [Fintype ι] [DecidableEq ι]
    {τ : FDRep ℂ (GL ι K)} {f : K[X]} (h : HasLabelO O τ f) :
    HasLabelO O (bc (starRingAut : ℂ ≃+* ℂ) τ) (C (f.coeff 0)⁻¹ * f.reverse) := by
  obtain ⟨s, b, lam, hb, hl, hc, rfl⟩ := h
  refine ⟨s, b, fun c => bc starRingAut (lam c), hb, fun c => ⟨simple_bc _ (hl c).1, isCuspidal_bc _ (hl c).2⟩,
    isConstituent_bc _ b lam hc, ?_⟩
  rw [normRev_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  have hd : 1 ≤ Fintype.card {i // b i = c} := by
    obtain ⟨i, hi⟩ := hb c
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  refine (GlobalTheory.DualLabel.lab_dual O hO _ _ _ hd (Formalism.L2.PT.simple_transp _ (hl c).1)
    (Formalism.L2.PT.isCuspidal_transp _ (hl c).2) (Formalism.L2.PT.simple_transp _ (simple_bc _ (hl c).1))
    (Formalism.L2.PT.isCuspidal_transp _ (isCuspidal_bc _ (hl c).2)) fun γ => ?_).symm
  change (transp _ (bc starRingAut (lam c))).character γ = (transp _ (lam c)).character γ⁻¹
  rw [Formalism.L2.PT.character_transp, Formalism.L2.PT.character_transp, character_bc, map_inv]
  exact PI.SerBridgeGLW.conjugate_character_formula _ _ _

end Label

theorem star_coeff_eSerO : ∀ {g : ℕ} [Fact g.Prime] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)}
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O →
    ∀ (r : ℕ) (f : Polynomial (ZMod g)), f.Monic → f.coeff 0 ≠ 0 → ∀ x,
      star ((Formalism.L2.NT.eSerO O r f).coeff x) =
        (Formalism.L2.NT.eSerO O r (Polynomial.C (f.coeff 0)⁻¹ * f.reverse)).coeff x := by
  intro g _ Cv O hO r f hm h0 x
  classical
  let S : MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) ≃+ MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) :=
    MonoidAlgebra.mapAddEquiv _ (starRingAut : ℂ ≃+* ℂ).toAddEquiv
  have hS : ∀ z y, (S z).coeff y = star (z.coeff y) := fun z y => MonoidAlgebra.coeff_mapAddEquiv _ _ _
  have hSS : ∀ z, S (S z) = z := fun z => by
    ext y
    rw [hS, hS, star_star]
  have hz : ∀ τ : FDRep ℂ (GL (Fin r) (ZMod g)), zIdem (bc starRingAut τ) = S (zIdem τ) := fun τ => by
    ext y
    rw [hS]
    exact (galoisConjCentralIdempotent _ starRingAut τ y).symm
  rw [← hS]
  congr 2
  unfold Formalism.L2.NT.eSerO
  rw [S.map_finsum]
  refine finsum_eq_of_bijective S S.bijective fun z => ?_
  have hiff : (∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f) ↔
      ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = S z ∧
        HasLabelO O τ (C (f.coeff 0)⁻¹ * f.reverse) := by
    constructor
    · rintro ⟨τ, h1, h2, h3⟩
      exact ⟨_, simple_bc _ h1, by rw [hz, h2], hasLabelO_conj O hO h3⟩
    · rintro ⟨τ, h1, h2, h3⟩
      have h4 := hasLabelO_conj O hO h3
      rw [normRev_normRev hm h0] at h4
      exact ⟨_, simple_bc _ h1, by rw [hz, h2, hSS], h4⟩
  rw [finsum_eq_if, finsum_eq_if, ← hiff]
  split_ifs
  · rfl
  · exact map_zero S

end GlobalTheory.SerConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonHypercohomologyOfLocallyExactOnSuppoStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support : ∀ (R : Type) [CommRing R] (E : Spc) (C : Cx R) [C.IsKInjective], (∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) a = Sec.res g b) → ∀ n, Subsingleton (CohomologyClass ((chains R).obj E) C n) := by
  first | (exact @GlobalTheory.EtC.subsingleton_of_locExact_supp) | (exact GlobalTheory.EtC.subsingleton_of_locExact_supp) | (intros; apply GlobalTheory.EtC.subsingleton_of_locExact_supp  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentVanishingFiniteAlgebraStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_laurent_vanishing_finite_algebra : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 2 ≤ s → s < n → Subsingleton (Ht q (sp (LaurentPolynomial T)) s i) := by
  first | (exact @GlobalTheory.EtC.laurent_vanishing_finite) | (exact GlobalTheory.EtC.laurent_vanishing_finite) | (intros; apply GlobalTheory.EtC.laurent_vanishing_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistIsFreeRankOneOnGeneratorSection
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.TwistedGenericPoint

theorem loc_point {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), Etale j ∧ j v = u ∧ P V j := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  obtain ⟨hsurj, hprop⟩ := (Scheme.ofArrows_mem_precoverage_iff _).1 𝒰.mem₀
  obtain ⟨k, v, hv⟩ := hsurj u
  exact ⟨𝒰.X k, 𝒰.f k, v, hprop k, hv, hP _ _ (h𝒰 _ (𝒰.f k) (Presieve.ofArrows.mk k))⟩

theorem isEmpty_of_subsingleton (X : Scheme.{0}) [Subsingleton Γ(X, ⊤)] : IsEmpty X := by
  refine ⟨fun x => ?_⟩
  have := (X.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  exact not_subsingleton Γ(X, ⊤) inferInstance

theorem smul_residue {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (n : ℕ) (y : M) :
    n • y = (ULift.up (n : ZMod q) : ULift.{1} (ZMod q)) • y := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  rfl

end GlobalTheory.TwistedGenericPoint

namespace GlobalTheory


open GlobalTheory.TwistedGenericPoint in
theorem twGen_gen : ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)), Gen (tw q i) S (twGen i ζ) := by
  intro q i S ζ U s
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have : Subsingleton Γ(S, ⊤) := by
      obtain ⟨hu, _⟩ := ζ.2
      exact subsingleton_of_zero_eq_one (isUnit_zero_iff.1 (by simpa using hu))
    have hS := isEmpty_of_subsingleton S
    have hU : IsEmpty U := ⟨fun u => hS.elim (s u)⟩
    exact ⟨fun _ u => (hU.elim u), fun _ hne _ => (hU.elim hne.some)⟩
  · haveI : NeZero q := ⟨hq.ne'⟩
    obtain ⟨-, h2, h3, h4, -⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q i
    refine ⟨fun x u => ?_, fun c hne hc => ?_⟩
    · obtain ⟨V, j, v, hj, hjv, c, hc⟩ := loc_point (h2 U (ζ.map s.appTop.hom) x) u
      refine ⟨V, j, v, (c : ZMod q), hj, hjv, ?_⟩
      have e : Sec.pull (j ≫ s) (twGen i ζ) = twGen i ((ζ.map s.appTop.hom).map j.appTop.hom) :=
        h4 V S (j ≫ s) ζ
      rw [e]
      exact hc.trans (smul_residue c _)
    · haveI : Nonempty U := hne
      have e : Sec.pull s (twGen i ζ) = twGen i (ζ.map s.appTop.hom) := h4 U S s ζ
      rw [e] at hc
      have h0 : c.val • twGen i (ζ.map s.appTop.hom) = 0 := by
        rw [smul_residue (q := q), ZMod.natCast_zmod_val]
        exact hc
      have hd := h3 U _ c.val h0
      rw [← ZMod.natCast_zmod_val c]
      exact (ZMod.natCast_eq_zero_iff _ _).2 hd

end GlobalTheory
end

