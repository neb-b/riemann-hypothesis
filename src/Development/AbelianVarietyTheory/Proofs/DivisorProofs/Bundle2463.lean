module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.TendstoUnderCofinite
public import Formalism.ConjugateSelfDual.Statement
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.RealStructures.Imports
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.ImportsBis
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWittModelUnitaryActionStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_witt_model_unitary_action : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) (locMat t b g) (locMat t c h) (ι φ) := by
  first | exact @GlobalTheory.KSplit.om_linW_split | exact GlobalTheory.KSplit.om_linW_split | (intros; apply GlobalTheory.KSplit.om_linW_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingGraphGenericPointOfInjectiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localRing_graph_generic_point_of_injective : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  Function.Injective π → (∀ g : K, ∃ a b : R, (b : K) ≠ 0 ∧ g * b = a) →
  IsLocModel (algebraMap ℂ K) R → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → 1 ≤ k →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin k → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1)) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) = (q : L) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  first | exact @GlobalTheory.FieldPair.localRing_graph_of_injective | exact GlobalTheory.FieldPair.localRing_graph_of_injective | (intros; apply GlobalTheory.FieldPair.localRing_graph_of_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerWedgeFrameChangeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logKodairaSpencer_wedge_frameChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (w w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left)) (D D' : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), GlobalTheory.LogKSDiv.GenKS TF Z w D → GlobalTheory.LogKSDiv.GenKS TF Z w' D' → (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (w' τ) (A τ i) (w τ i)) → (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) → ∃ u : (X₀ TF.Y Z).functionField, (u = 1 ∨ u = -1) ∧ ∀ η : RatForms (s₀ TF.Y Z) Dw.dim, GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D η = u * ((∏ τ, d τ ^ (if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p) : (X₀ TF.Y Z).functionFieldˣ) : (X₀ TF.Y Z).functionField) * GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D' η := by
  first | exact @GlobalTheory.LogKSDiv.topPair_frameChange | exact GlobalTheory.LogKSDiv.topPair_frameChange | (intros; apply GlobalTheory.LogKSDiv.topPair_frameChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MK
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.HomMum

abbrev MK : Type := ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2))

variable {S : Scheme.{0}}

def mφ (H₁ H₂ : Over S) [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] (a b : H₁ ⟶ H₂) :
    MK → ((H₁ ⊗ H₁).left ⟶ H₁.left ⨿ H₂.left) :=
  Sum.elim (fun I => (lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b)).left ≫ (psum H₂ (x2 H₂) I.down).left ≫ coprod.inr)
    (fun I => (psum H₁ (x2 H₁) I.down).left ≫ coprod.inl)

def mε : MK → ℤ :=
  Sum.elim (fun I => (-1 : ℤ) ^ (2 - I.down.card)) (fun I => -((-1 : ℤ) ^ (2 - I.down.card)))

def IsNrm {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] {a b : H₁ ⟶ H₂}
    {L₁ : LB H₁.left} {L₂ : LB H₂.left} (u : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε)) : Prop :=
  u.IsGen ∧ ∀ (y : (𝟙_ (Over S)).left) (J), Good (join L₁ L₂) y J →
    val u (lift (1 : 𝟙_ (Over S) ⟶ H₁) (1 : 𝟙_ (Over S) ⟶ H₁)).left y J = 1

end GlobalTheory.HomMum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MumCmp

section Maps

variable {X Y X' : Scheme.{0}} (L : LB X) (L' : LB X') {J : Type} [Fintype J]

lemma mapsAtExp_le_b (pr : J → (X' ⟶ X)) (ε : J → ℤ) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr ε) L').U (jN, jL) ≤ LB.wchart L (fun i => p ≫ pr i) jN := by
  intro y hy
  refine Set.mem_iInter.2 fun i => ?_
  have h1 : p.base y ∈ LB.wchart L pr jN := hy.1
  exact Set.mem_iInter.1 h1 i

lemma mapsAtExp_le_a (pr : J → (X' ⟶ X)) (ε : J → ℤ) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr ε) L').U (jN, jL) ≤ LB.wchart L' (fun _ : PUnit => p) (fun _ => jL) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

def MapsAtExp (pr : J → (X' ⟶ X)) (ε : J → ℤ) (w : LB.Iso L' (LB.LinComb L pr ε)) (p : Y ⟶ X') (n : ℤ)
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n)))
    (b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun i => n * ε i))) : Prop :=
  ∀ (jN : J → L.ι) (jL : L'.ι),
    res (mapsAtExp_le_b L L' pr ε p jN jL) (b.s jN) =
      (pullU p _ (w.s (jN, jL))) ^ n * res (mapsAtExp_le_a L L' pr ε p jN jL) (a.s (fun _ => jL))

end Maps

variable {R : Type} [CommRing R] [IsDomain R]

def twφ (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A) : Fin 3 → (D₀.P.A.left ⟶ D.P.A.left) :=
  ![(padd D.P.A β (toUnit D₀.P.A ≫ b)).left, (toUnit D₀.P.A ≫ b).left, (toUnit D₀.P.A ≫ η[D.P.A]).left]

def twε : Fin 3 → ℤ := ![1, -1, 1]

def IsTwist (D₀ D : DegPre R) (g : GtPt D (𝟙_ (Over (Sp R)))) : Prop :=
  ∃ (β : D₀.P.A ≅ D.P.A) (xe : D₀.X ≃+ D.X), IsMonHom β.hom ∧ (∀ χ, D₀.c χ ≫ β.hom = D.c (xe χ)) ∧
    ∃ w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β.hom g.b) twε), w.IsGen ∧
      ∀ χ : D₀.X, ∃ t : LB.Gen (LB.LinComb D.P.L (fun i => D₀.xK χ ≫ twφ D₀ D β.hom g.b i) (fun i => -1 * twε i)),
        MapsAtExp D.P.L D₀.P.L (twφ D₀ D β.hom g.b) twε w (D₀.xK χ) (-1) (D₀.psi χ) t ∧
        LB.Gen.Corr D.P.L _ _ _ _ t
          (LB.mulGen D.P.L _ _ _ _ (D.psi (xe χ)) (LB.pullGen D.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left))

end GlobalTheory.MumCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDecompositionSubgroupIff
section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual
open scoped Pointwise

namespace GlobalTheory.QuadSplit

theorem mem_decompositionSubgroup_iff' {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : ValuationSubring Ω)
    (g : Ω ≃ₐ[K] Ω) : g ∈ A.decompositionSubgroup K ↔ ∀ x, g x ∈ A ↔ x ∈ A := by
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  constructor
  · intro h x
    rw [← ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (S := A) (x := x), h]
    rfl
  · intro h
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h]
    simp [AlgEquiv.smul_def]

end GlobalTheory.QuadSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfBaseChangeRatioSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_of_base_change_ratio_sections : ∀ {K L : Type} [Field K] [Field L] (ψ : K →+* L) {X : Scheme.{0}} (h : X ⟶ Sp K) (U : X.Opens) (f₁ f₂ : Γ(X, U)) (l : L), f₂ ≠ 0 → ((pullback.fst h (spMap ψ)).app U).hom f₁ = ((pullback.fst h (spMap ψ)).app U).hom f₂ * resTop _ (scal (pullback.snd h (spMap ψ)) l) → l ∈ Set.range ψ := by
  first | exact @GlobalTheory.ConstDescent.mem_range_of_pullback_eq | exact GlobalTheory.ConstDescent.mem_range_of_pullback_eq | (intros; apply GlobalTheory.ConstDescent.mem_range_of_pullback_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringClosureOfIsIntegralElemAffineOpenLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem resK_bijective {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {V W : S.Opens} (h : W ≤ V)
    (e : gp ⁻¹ᵁ V ≤ gp ⁻¹ᵁ W) : Function.Bijective (resK gp h) := by
  have e' : gp ⁻¹ᵁ W = gp ⁻¹ᵁ V := le_antisymm (gp.preimage_mono h) e
  have hh : homOfLE (gp.preimage_mono h) = eqToHom e' := Subsingleton.elim _ _
  show Function.Bijective ((Sp K).presheaf.map (homOfLE (gp.preimage_mono h)).op).hom
  rw [hh]
  exact ConcreteCategory.bijective_of_isIso ((Sp K).presheaf.map (eqToHom e').op)

theorem isIntegralElem_of_comp_injective {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (hg : Function.Injective g) {y : A}
    (h : (g.comp f).IsIntegralElem (g y)) : f.IsIntegralElem y := by
  obtain ⟨p, hp, hy⟩ := h
  refine ⟨p, hp, hg ?_⟩
  rw [Polynomial.hom_eval₂, hy, map_zero]

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem eq_bot_or_eq_top_of_sp (K : Type) [Field K] (O : (Sp K).Opens) : O = ⊥ ∨ O = ⊤ := by
  by_cases h : O = ⊥
  · exact Or.inl h
  · right
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty O).mp h
    refine top_unique fun z _ => ?_
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rwa [Subsingleton.elim z x]
end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_closure_of_isIntegralElem_affine_le : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) (V W : S.Opens) (hWV : W ≤ V),
    IsAffineOpen V → IsAffineOpen W → ∀ b : Γ(Sp K, gp ⁻¹ᵁ W), (gp.app W).hom.IsIntegralElem b →
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ V), (∀ y ∈ s, (gp.app V).hom.IsIntegralElem y) ∧
      b ∈ Subring.closure (Set.range (gp.app W).hom ∪ resK gp hWV '' (s : Set _)) := by
  intro S K _ gp V W hWV hV hW b hb
  classical
  let C : Finset Γ(Sp K, gp ⁻¹ᵁ V) → Subring Γ(Sp K, gp ⁻¹ᵁ W) := fun s =>
    Subring.closure (Set.range (gp.app W).hom ∪ resK gp hWV '' (s : Set _))
  have Cmono : ∀ s t : Finset Γ(Sp K, gp ⁻¹ᵁ V), s ⊆ t → C s ≤ C t := by
    intro s t hst
    refine Subring.closure_mono (Set.union_subset_union_right _ (Set.image_mono ?_))
    exact_mod_cast hst
  let J : Ideal Γ(S, W) :=
    { carrier := {c | ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ V), (∀ y ∈ s, (gp.app V).hom.IsIntegralElem y) ∧
        (gp.app W).hom c * b ∈ C s}
      zero_mem' := ⟨∅, by simp, by rw [map_zero, zero_mul]; exact zero_mem _⟩
      add_mem' := by
        rintro c d ⟨s, hs, hc⟩ ⟨t, ht, hd⟩
        refine ⟨s ∪ t, fun y hy => (Finset.mem_union.mp hy).elim (hs y) (ht y), ?_⟩
        rw [map_add (f := _), add_mul]
        exact add_mem (Cmono _ _ Finset.subset_union_left hc) (Cmono _ _ Finset.subset_union_right hd)
      smul_mem' := by
        rintro c d ⟨s, hs, hd⟩
        refine ⟨s, hs, ?_⟩
        rw [smul_eq_mul, map_mul, _root_.mul_assoc]
        exact mul_mem (Subring.subset_closure (Or.inl ⟨c, rfl⟩)) hd }
  let T : Set Γ(S, W) := {c | ∃ g : Γ(S, V), S.basicOpen g ≤ W ∧ (S.presheaf.map (homOfLE hWV).op).hom g = c}
  have hspan : Ideal.span T = ⊤ := by
    refine hW.self_le_iSup_basicOpen_iff.mp ?_
    intro x hx
    obtain ⟨g, hg, hxg⟩ := hV.exists_basicOpen_le (V := W) ⟨x, hx⟩ (hWV hx)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨⟨_, g, hg, rfl⟩, ?_⟩
    show x ∈ S.basicOpen ((S.presheaf.map (homOfLE hWV).op).hom g)
    rw [Scheme.basicOpen_res]
    exact ⟨hx, hxg⟩
  have hT : T ⊆ J.radical := by
    rintro _ ⟨g, hg, rfl⟩
    set D := S.basicOpen g with hD
    rcases eq_bot_or_eq_top_of_sp K (gp ⁻¹ᵁ D) with h0 | h1
    ·
      have hz : (gp.app V).hom g = 0 := by
        rw [← AlgebraicGeometry.basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
        exact h0
      refine ⟨1, ∅, by simp, ?_⟩
      rw [pow_one, ← resK_app, hz, map_zero, zero_mul]
      exact zero_mem _
    ·
      have hDW : D ≤ W := hg
      have hDV : D ≤ V := hDW.trans hWV
      have := hV.isLocalization_basicOpen g
      letI : Algebra Γ(S, D) Γ(Sp K, gp ⁻¹ᵁ D) := (gp.app D).hom.toAlgebra
      letI : Algebra Γ(S, V) Γ(Sp K, gp ⁻¹ᵁ D) := ((gp.app D).hom.comp (algebraMap Γ(S, V) Γ(S, D))).toAlgebra
      haveI : IsScalarTower Γ(S, V) Γ(S, D) Γ(Sp K, gp ⁻¹ᵁ D) := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have sq : (resK gp hDW).comp (gp.app W).hom =
          (gp.app D).hom.comp (S.presheaf.map (homOfLE hDW).op).hom := by
        ext a; exact resK_app gp hDW a
      have hb' : IsIntegral Γ(S, D) (resK gp hDW b) := by
        have := hb.map (resK gp hDW)
        rw [sq] at this
        exact RingHom.isIntegralElem.of_comp _ _ this
      obtain ⟨⟨_, N, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers g)
        (Rₘ := Γ(S, D)) _ hb'
      have top : ∀ U : S.Opens, gp ⁻¹ᵁ U ≤ gp ⁻¹ᵁ D := fun _ => h1 ▸ le_top
      obtain ⟨y, hy⟩ := (resK_bijective gp hDV (top V)).2 ((g ^ N) • resK gp hDW b)
      have alg : ∀ a : Γ(S, V), algebraMap Γ(S, V) Γ(Sp K, gp ⁻¹ᵁ D) a = resK gp hDV ((gp.app V).hom a) := by
        intro a; rw [resK_app]; rfl
      have hyi : (gp.app V).hom.IsIntegralElem y := by
        refine isIntegralElem_of_comp_injective _ (resK gp hDV) (resK_bijective gp hDV (top V)).1 ?_
        have e : (resK gp hDV).comp (gp.app V).hom = algebraMap Γ(S, V) Γ(Sp K, gp ⁻¹ᵁ D) := by
          ext a; exact (alg a).symm
        rw [e, hy]
        exact hm
      refine ⟨N, {y}, by simpa using hyi, ?_⟩
      have key : resK gp hWV y = (gp.app W).hom ((S.presheaf.map (homOfLE hWV).op).hom g ^ N) * b := by
        apply (resK_bijective gp hDW (top W)).1
        rw [resK_resK, hy, Algebra.smul_def, alg, map_mul]
        simp only [map_pow]
        rw [← resK_app gp hWV g, resK_resK]
      rw [← key]
      exact Subring.subset_closure (Or.inr ⟨y, by simp, rfl⟩)
  have hJ : J = ⊤ := Ideal.radical_eq_top.mp (top_unique (hspan ▸ Ideal.span_le.mpr hT))
  obtain ⟨s, hs, h⟩ : (1 : Γ(S, W)) ∈ J := hJ ▸ Submodule.mem_top
  refine ⟨s, hs, ?_⟩
  simpa using h

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitsK
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit

noncomputable section

namespace GlobalTheory.Mum.TensPol

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem exists_int (A : Over (Spec (CommRingCat.of R))) [IsSeparated A.hom] (L : LB A.left) (hL : L.IsLB) (z : (TK R).left) :
    ∃ J, Good L z J ∧
      ∀ p : Spec (CommRingCat.of R) ⟶ A.left, p ≫ A.hom = 𝟙 _ → p (closedPoint R) ∈ L.U (J (jK R ≫ p)) := by
  have : IsDominant (jK R) := DVR.isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ A.left => exists_chart hL (p (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL (Z := (TK R).left) z
    (K := {p : Spec (CommRingCat.of R) ⟶ A.left // p ≫ A.hom = 𝟙 _}) (fun p => jK R ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R)) A.hom
      (a.2.trans b.2.symm) (jK R) h))
    (fun p => (IsLocalRing.specializes_closedPoint (jK R z)).mem_open (p.1 ⁻¹ᵁ L.U (pick p.1)).isOpen (hpk p.1))
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

theorem val_mem {A : Over (Spec (CommRingCat.of R))} {L : LB A.left} (z : (TK R).left) {J : ((TK R).left ⟶ A.left) → L.ι}
    (hJ : ∀ p : Spec (CommRingCat.of R) ⟶ A.left, p ≫ A.hom = 𝟙 _ → p (closedPoint R) ∈ L.U (J (jK R ≫ p)))
    {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of R) ⟶ A.left)) (hφ : ∀ k, φ k ≫ A.hom = 𝟙 _) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) : val t (toUnit (TK R)).left z J ∈ unitsS z := by
  have := gm_mem z (𝟙 _) (LB.wchart L φ (fun k => J (jK R ≫ φ k))) (Set.mem_iInter.2 fun k => hJ (φ k) (hφ k))
    (t.s (fun k => J (jK R ≫ φ k)))
  rw [Category.comp_id] at this
  exact this

theorem mem_unitsK (z : (TK R).left) {x : (FractionRing R)ˣ} (h : Units.map (ev z).toMonoidHom x ∈ unitsS z) : x ∈ unitsK R := by
  obtain ⟨y, hy, e⟩ := h
  exact (Units.map_injective (ev_inj z) e) ▸ hy

theorem gm_unitOn (z : (TK R).left) (k : (FractionRing R)ˣ) :
    gm (𝟙 (TK R).left) z ⊤ (unitOn k) = Units.map (ev z).toMonoidHom k :=
  Units.ext ((gs_unit _ z ⊤ trivial _).symm.trans (ev_eq z k))

end GlobalTheory.Mum.TensPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimiserCellFunctionMinFinitelyManyCombinations
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem GlobalTheory.Poinc.finite_types : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ, r ≤ g → ∃ (ι : ℕ) (𝓛 : Finset (Finset ((Fin 8 → Fin r → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) → ∃ L ∈ 𝓛, ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ c)) ∧ ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ c) := by
  intro g φ hφ W hW N _ hN hε r hr
  classical
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut g φ hφ W hW N hN r hr
  have hP : ∀ μ' : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ),
      ((∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i) ∧ ∃ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ),
        (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
        (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b₀ (μ' c) ≤ qW W b₀ α)) →
      ∃ (ι : ℕ) (L : Finset ((Fin 8 → Fin r → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)),
        (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) →
        (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ' c) ≤ qW W b' α) →
        (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ' c)) ∧
          ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ' c) :=
    fun μ' ⟨h1, b₀, h2, h3, h4⟩ => _root_.GlobalTheory.Poinc.polFn_cell_eq_min_integral g φ hφ W hW N hN hε r hr μ' h1 b₀ h2 h3 h4
  choose! ιf Lf hιf hLf using hP
  set ι : ℕ := ∏ μ' ∈ S, max (ιf μ') 1 with hιdef
  refine ⟨ι, S.biUnion fun μ' => Finset.univ.image fun σ : Equiv.Perm (Fin 8 → Fin r → ZMod N) =>
    (Lf μ').image fun ν c => ((ι / ιf μ' : ℕ) : ℤ) * ν (σ c), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ => by omega)
  intro b hbs hbp μ hμ hmin
  obtain ⟨e, he⟩ := hS b hbs hbp
  obtain ⟨σ, hσ1, hσ2⟩ := _root_.GlobalTheory.relabel_minimisers W N r μ hμ e
  have hpd : ∀ x, x ≠ 0 → 0 < pull e.toLinearMap b x x := fun x hx => by
    simpa using hbp (e x) (by simpa using hx)
  have hPμ := And.intro hσ1 (⟨pull e.toLinearMap b, fun x y => hbs _ _, hpd, hσ2 b hmin⟩ :
    ∃ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
      (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) →
        qW W b₀ ((fun c u => e.symm (μ (σ c) u)) c) ≤ qW W b₀ α))
  have hmem := he _ hσ1 (hσ2 b hmin)
  have hι1 := hιf _ hPμ
  have hL := hLf _ hPμ
  set μ' : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ) := fun c u => e.symm (μ (σ c) u) with hμ'
  have hdvd : ιf μ' ∣ ι := by
    have := Finset.dvd_prod_of_mem (fun μ'' => max (ιf μ'') 1) hmem
    simpa [max_eq_left hι1] using this
  set k : ℕ := ι / ιf μ' with hk
  have hkι : (ι : ℝ) = k * ιf μ' := by exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  refine ⟨(Lf μ').image fun ν c => ((k : ℕ) : ℤ) * ν (σ.symm c),
    Finset.mem_biUnion.2 ⟨μ', hmem, Finset.mem_image.2 ⟨σ.symm, Finset.mem_univ _, rfl⟩⟩, ?_⟩
  intro b' hb's hb'p hb'min
  have key := hL (pull e.toLinearMap b') (fun x y => hb's _ _) (fun x => hb'p _) (hσ2 b' hb'min)
  have hφ' : φ.evalZ (pull e.toLinearMap b') = φ.evalZ b' := evalZ_pull φ e.surjective b'
  have hq : ∀ c, qW W (pull e.toLinearMap b') (μ' c) = qW W b' (μ (σ c)) := fun c => by
    simp [qW, μ']
  have hsum : ∀ ν : (Fin 8 → Fin r → ZMod N) → ℤ,
      ∑ c, ((((k : ℕ) : ℤ) * ν (σ.symm c) : ℤ) : ℝ) * qW W b' (μ c) =
        k * ∑ c, (ν c : ℝ) * qW W (pull e.toLinearMap b') (μ' c) := fun ν => by
    rw [Finset.mul_sum, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hq]; simp; ring
  have hlhs : (ι * N : ℝ) * φ.evalZ b' = k * ((ιf μ' * N : ℝ) * φ.evalZ (pull e.toLinearMap b')) := by
    rw [hφ', hkι]; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  refine ⟨fun ν' hν' => ?_, ?_⟩
  · obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hν'
    rw [hsum, hlhs]
    exact mul_le_mul_of_nonneg_left (key.1 ν hν) hk0
  · obtain ⟨ν, hν, heq⟩ := key.2
    exact ⟨_, Finset.mem_image_of_mem _ hν, by rw [hsum, hlhs, heq]⟩
end

