module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialZeroLocusCoordinates
public import Formalism.UnipotentAdelicQuotients.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0968
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0975
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchIff
section
noncomputable section

namespace GlobalTheory.ThK.PolynomialMatching

open scoped TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def PolMatchOn (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (T : Finset (Pl F)) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) : Prop :=
  ∃ (m m' : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ)
    (f' : Fin m' → SInf F _) (φ' : Fin m' → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    (∀ j, f' j ∈ G.M'.Pol B.ψ B.emb ∧ (∀ v, φ' j v ∈ SB _) ∧ ∀ v ∉ T, φ' j v = G.M'.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧ Φ' = ∑ j, pure (f' j) (φ' j) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v))

theorem polMatch_iff (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) :
    PolMatch B G X R Rf Φ Φ' ↔ ∃ T : Finset (Pl F), X.T ⊆ T ∧ PolMatchOn B G X R Rf T Φ Φ' := Iff.rfl

end GlobalTheory.ThK.PolynomialMatching
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialZeroLocusCoordinatesStatement
section
open GlobalTheory.LKTrip
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomialLocus_similitudeCentralizerTorus : ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D),
  ∃ (N : ℕ) (S : Set (MvPolynomial (Fin N × Fin N) ℚ)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S)
    (φ : ∀ (R : Type) [CommRing R] [Algebra ℚ R], HeckeCharacterZeroLocus.locusSubgroup S hS R →* (R ⊗[ℚ] D)ˣ × Rˣ),
    (∀ (R : Type) [CommRing R] [Algebra ℚ R], Function.Injective (φ R) ∧
      ∀ z : (R ⊗[ℚ] D)ˣ × Rˣ, GlobalTheory.TorCls.TC D σ β y R z ↔ z ∈ Set.range (φ R)) ∧
    (∀ (R R' : Type) [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
      (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) (g' : HeckeCharacterZeroLocus.locusSubgroup S hS R'),
      (g' : GL (Fin N) R') = Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom (g : GL (Fin N) R) →
      φ R' g' = (Units.map (Algebra.TensorProduct.map f (AlgHom.id ℚ D)).toRingHom.toMonoidHom (φ R g).1,
        Units.map f.toRingHom.toMonoidHom (φ R g).2)) ∧
    (∀ (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R],
      letI : TopologicalSpace (R ⊗[ℚ] D) := moduleTopology R (R ⊗[ℚ] D)
      Continuous (φ R)) := by
  first | (exact @GlobalTheory.TorLoc.exists_locus) | (exact GlobalTheory.TorLoc.exists_locus) | (intros; apply GlobalTheory.TorLoc.exists_locus  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelRowsEqTopStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.EEg3_eq_univ_of_weakCharacterisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (⨆ p, R.EEp3 p) = ⊤ → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) = ⊤ := by
  first | exact @GlobalTheory.PrincipalRows.principal_level_rows_eq_top | exact GlobalTheory.PrincipalRows.principal_level_rows_eq_top | (intros; apply GlobalTheory.PrincipalRows.principal_level_rows_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLiftFormsEqGoodFormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalFormsSubspace_eq_good_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ i, (⨆ p, R.Wp3 i p) = LinearMap.range (eH R.toRealDat i)) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmA → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → ∀ i, principalFormsSubspace A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) i = Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) := by
  first | exact @GlobalTheory.WgLift.principal_lift_forms_eq_good_forms | exact GlobalTheory.WgLift.principal_lift_forms_eq_good_forms | (intros; apply GlobalTheory.WgLift.principal_lift_forms_eq_good_forms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiPNeighborhoodInLevelSubgroup
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_p_neighborhood_in_level_subgroup : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r₂ : Gr G 1), letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C); ∃ O : Set ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, r₂⁻¹ * psiP G z * r₂ ∈ KHT p G.m G.n 1 G.Fw := by
  first | (exact @GlobalTheory.TorCls.OpenP.openp) | (exact GlobalTheory.TorCls.OpenP.openp) | (intros; apply GlobalTheory.TorCls.OpenP.openp  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticOperatorEigenvectorDiagonalBlockIdentit
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem qop_quadratic_on_eigenvector : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (α β x : ℂ) (y : ι → M), (∀ a b, qop F α β a b = 0) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ j, s j = false → ∑ b, F j b (y b) = 0) → ∀ a, (x ^ 2 - α * x - β) • y a = 0 := by
  intro ι M _ _ _ _ s F α β x y hq hs ht hf a
  have hall : ∀ c, ∑ b, F c b (y b) = x • y c := by
    intro c
    cases hc : s c
    · rw [hf c hc, hs c hc, smul_zero]
    · exact ht c hc
  cases ha : s a
  · rw [hs a ha, smul_zero]
  · have key : ∑ b, qop F α β a b (y b) = 0 := by simp [hq]
    have pt : ∀ b, qop F α β a b (y b)
        = ∑ c, F a c (F c b (y b)) - α • F a b (y b) - (if a = b then β • y b else 0) := by
      intro b
      simp only [qop, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]
      split_ifs <;> simp
    have expand : ∑ b, qop F α β a b (y b)
        = ∑ c, F a c (∑ b, F c b (y b)) - α • ∑ b, F a b (y b) - β • y a := by
      rw [Finset.sum_congr rfl (fun b _ => pt b), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_comm, Finset.sum_ite_eq, ← Finset.smul_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum]
    rw [expand, ht a ha] at key
    simp only [hall, map_smul] at key
    rw [← Finset.smul_sum, ht a ha] at key
    rw [sub_smul, sub_smul, pow_two, mul_smul, mul_smul]
    exact key

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorBaseLevelTwistedModel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.WType

theorem range_w0C_type : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → R.toRealDat.LUnif → ∀ i, LinearMap.range ((R.toCx3 F).w0C false i) = Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) ⊓ typeSubspace A3 (R.toCx3 F) i (R.gWx F i) F.P0 F.ψ0⁻¹ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hW hEx hU i
  obtain ⟨hC, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hI := (_root_.GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hC hX i).1
  have hs : ∀ a, cj (twAt D.what₂.embLL A3.A.v0) (A3.A.fam.v0.embedding a) = sg0 D A3.A a := fun a => by
    show cj _ (A3.A.v0.embedding a) = _
    rw [emb_eq D.what₂.embLL A3.A.v0 a, cj_cj]
  rw [_root_.GlobalTheory.LevelRange.range_w0C_eq R F hOk hW hU false i]
  ext x
  have hw := GlobalTheory.WatType.wat_iff_type R.toRealDat F.lv2 hOk.ok2 hC false i (Tw.out x)
  have hL : x ∈ Tw.sub (twAt D.what₂.embLL A3.A.v0) ((R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap (R.HW i (sg0 D A3.A)).e) ↔ (R.HW i (sg0 D A3.A)).e (Tw.out x) ∈ R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) := Iff.rfl
  have hR : Tw.out x ∈ LinearMap.range (eH R.toRealDat i) ↔ eH R.toRealDat i (Tw.out x) = Tw.out x := by
    refine ⟨?_, fun h => ⟨_, h⟩⟩
    rintro ⟨y, hy⟩
    rw [← hy, ← Module.End.mul_apply, hI]
  have hT : x ∈ typeSubspace A3 (R.toCx3 F) i (R.gWx F i) F.P0 F.ψ0⁻¹ ↔ ∀ p : (F.lv2.lvl false).P, R.gW i (sg0 D A3.A) (p : G) (Tw.out x) = sg0 D A3.A ((((F.lv2.lvl false).ψ⁻¹ p : D.what₂.LLˣ)) : D.what₂.LL) • Tw.out x := by
    unfold typeSubspace
    refine (Submodule.mem_iInf (R := ℂ) (M := (R.toCx3 F).W i) _).trans (forall_congr' fun p => ?_)
    show R.gW i (sg0 D A3.A) (p : G) (Tw.out x) - cj (twAt D.what₂.embLL A3.A.v0) (A3.A.fam.v0.embedding ((F.ψ0⁻¹ p : D.what₂.LLˣ) : D.what₂.LL)) • Tw.out x = 0 ↔ _
    rw [sub_eq_zero, hs]
    rfl
  constructor
  · intro h
    rw [hL, hw] at h
    exact ⟨hR.2 h.1, hT.2 h.2⟩
  · intro h
    rw [hL, hw]
    exact ⟨hR.1 h.1, hT.1 h.2⟩

end GlobalTheory.WType

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatMuPOfRowTest
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


open Formalism.IndefR.Rat Formalism.IndefR.Cx.CxData in
theorem ratMuP_of_rowTest : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), Formalism.IndefR.Rat.RowTest (R.toCx3 F) → R.PrincipalLevelBijective F → (R.toCx3 F).RATmu (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R F hT hH2
  obtain ⟨N, ψ, hψ, hr⟩ := hT
  obtain ⟨hinj0, hall⟩ := hH2
  intro t i k
  have hmem : (R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t (Pi.single k 1) ∈
      LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false A3.A.fam.μ0) := by
    rw [← (hall t).2]; exact LinearMap.mem_range_self _ _
  have key := coord_rat _ ψ hψ ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false A3.A.fam.μ0) hinj0
    (fun j l => by rw [CxData.iC, Formalism.IndefR.Rat.lin_single]; exact hr _ _ _)
    (solve ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false A3.A.fam.μ0)
      ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t (Pi.single k 1)))
    (fun j => by rw [solve_spec _ _ hmem, CxData.iC, Formalism.IndefR.Rat.lin_single]; exact hr _ _ _) i
  obtain ⟨a, ha⟩ := key
  exact ⟨a, ha⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationPrincipalLevelEqCoreLevelOpen
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolDict.PrincLev

def congGroup {D : D7} (V : HSp D) (N : ℕ) : Subgroup (GA D V) where
  carrier := {k | GlobalTheory.Member.FinCong V N k}
  one_mem' := GlobalTheory.Member.PrincLevel.finCong_one V N
  mul_mem' := fun ha hb => GlobalTheory.Member.PrincLevel.finCong_mul ha hb
  inv_mem' := fun ha => GlobalTheory.Member.PrincLevel.finCong_inv ha

theorem isOpen_congGroup {D : D7} (V : HSp D) {N : ℕ} (hN : 0 < N) : IsOpen (congGroup V N : Set (GA D V)) :=
  haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  Subgroup.isOpen_of_mem_nhds _ (GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN)

theorem mem_of_isLevelK {D : D7} {V W : HSp D} (hV : V = W) {N : ℕ} {Kf : Subgroup (GA D V)} (hK : IsLevelK V N Kf)
    (k : GA D W) (h1 : k ∈ congGroup W N) (h2 : k ∈ GfC W) : cast (congrArg (GA D) hV.symm) k ∈ Kf := by
  subst hV
  exact (hK k).2 ⟨h2, h1⟩

theorem mem_levG_triv_iff {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    k ∈ levG (Wc D i) (L.βW i) (L.datWp i L.triv) ↔ IsLevelLift (Wc D i) (L.βW i) (L.datWp i L.triv) 1 k :=
  ⟨fun h => ⟨h.1, h.2.1, Subgroup.mem_bot.1 h.2.2⟩, fun h => ⟨h.1, h.2.1, Subgroup.mem_bot.2 h.2.2⟩⟩

theorem levChi_triv_eq_one {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  have h : ∀ x, ext1 L.triv.H L.triv.chi x = 1 := fun x => by
    unfold ext1; split_ifs <;> rfl
  unfold levChi levFn
  simp [LevCh.datWp, datY]
  exact h _


set_option maxHeartbeats 1000000 in
theorem principal_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, (∀ g : GA D (Wc D i), g ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ↔ cast (congrArg (GA D) hV.symm) g ∈ T.Kf ((i : ℕ) + 1) (res T σ)) ∧ (∀ k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)), levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1) ∧ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ≤ GfC (Wc D i) ∧ ∃ U : Subgroup (GA D (Wc D i)), IsOpen (U : Set (GA D (Wc D i))) ∧ ∀ k ∈ U, k ∈ GfC (Wc D i) → k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL _ ht hpb i σ hσ hV
  have key : ∀ g : GA D (Wc D i), g ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv) ↔
      cast (congrArg (GA D) hV.symm) g ∈ T.Kf ((i : ℕ) + 1) (res T σ) := fun g =>
    (mem_levG_triv_iff R.toLevCh i g).trans (_root_.GlobalTheory.LiftLevel.isLift_one_iff_mem_level T R κ v₀ hL ht hpb i (res T σ) hσ hV g)
  have hg : 0 < D.host.g 0 * D.host.g 1 := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  refine ⟨key, fun k _ => levChi_triv_eq_one R.toLevCh i k, fun k hk => hk.1,
    congGroup (Wc D i) (D.host.g 0 * D.host.g 1), isOpen_congGroup _ hg, fun k h1 h2 => (key k).2 ?_⟩
  exact mem_of_isLevelK hV (ht.laws.levelK _ (inR i) _ hσ) k h1 h2

end GlobalTheory.HolDict.PrincLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFunctionsPthPowerTwist
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI


open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.DI.pow_mul_locRing_subset_regularAt {X : Scheme.{0}} [IsIntegral X] (p : ℕ)
    (G H : _root_.GlobalTheory.Cartier.CartierDiv X) (y : X) (h : (H - p • G).Eff) :
    {z : X.functionField | ∃ c ∈ {c : X.functionField | G.RegularAt y c},
      ∃ b ∈ _root_.GlobalTheory.LogDR.locRing y, z = c ^ p * b} ⊆
      {c | H.RegularAt y c} := by
  rintro z ⟨c, ⟨g, hg, hcg⟩, b, hb, rfl⟩
  obtain ⟨k, hk, hk1⟩ := h y
  have hH : H.IsEqn y (k * g ^ p) := by
    have := hk.add (hg.nsmul p)
    simpa using this
  refine ⟨k * g ^ p, hH, ?_⟩
  rw [← _root_.GlobalTheory.LogDR.mem_locRing] at hcg hk1 ⊢
  have hz : c ^ p * b * ((k * g ^ p : (X.functionField)ˣ) : X.functionField) =
      (c * g) ^ p * b * (1 * k) := by
    push_cast
    ring
  rw [hz]
  exact mul_mem (mul_mem (pow_mem hcg p) hb) hk1

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictChernPart
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess bas wd wdb)
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts GlobalTheory.FinChart
open scoped ENNReal

namespace GlobalTheory.ChernMA

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {B : LB Y} {φ : Weight p σ B} {A : FinHolAtlas D (CxPts p σ)}

variable [SecondCountableTopology (CxPts p σ)]

theorem restrict_chernPart (h : φ.IsCInf) (ε : ℤˣ) (c : AlgChart p σ D) :
    (φ.chernPart D ε).restrict c.finChart.source = ((volume.restrict c.finChart.target).withDensity
      fun z => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ (c.finChart.symm z))).map c.finChart.symm := by
  ext T hT
  have ht := c.finChart.open_target.measurableSet
  have hs : AEMeasurable c.finChart.symm (volume.restrict c.finChart.target) :=
    c.finChart.continuousOn_symm.aemeasurable ht
  have hp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin D → ℂ)) :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin D → ℂ)).symm
      (volume_preserving_ofLp_complex (Fin D))
  rw [Measure.restrict_apply hT, Weight.chernPart_apply h ε c
      (hT.inter c.finChart.open_source.measurableSet) inter_subset_right,
    Measure.map_apply_of_aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)) hT,
    withDensity_apply', Measure.restrict_restrict' ht, inter_comm, AlgChart.finChart_source,
    c.e.image_source_inter_eq', ← hp.setLIntegral_comp_preimage_emb
      (MeasurableEquiv.measurableEmbedding _), inter_comm]
  rfl

variable [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]


end GlobalTheory.ChernMA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActExtendsSemiAbelianDvr
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

open GlobalTheory.ExtUnique

theorem ringAct_extends_semiAbelian_dvr : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∃ act' : O → (G ⟶ G), ((∀ a, IsMonHom (act' a)) ∧ act' 1 = 𝟙 G ∧ (∀ a b, act' (a * b) = act' a ≫ act' b) ∧ (∀ a b, act' (a + b) = act' a * act' b)) ∧ ∀ a, (act a).left ≫ φ = φ ≫ (act' a).left := by
  intro W L _ _ _ _ _ _ G _ A _ φ hG hφ O _ act hh h1 hmul hadd
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing W L
  have hq : QuasiCompact (spMap (algebraMap W L)) := ‹_›
  have hd : IsSchemeTheoreticallyDominant (spMap (algebraMap W L)) := ‹_›
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G (spMap (algebraMap W L))) hφ
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hφ (isGrpPullback_pullback G (spMap (algebraMap W L)))
  have ext : ∀ x : O, ∃ F : G ⟶ G, (act x).left ≫ φ = φ ≫ F.left := by
    intro x
    have := hh x
    obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W L G G hG hG
      (a.hom ≫ act x ≫ b.hom) inferInstance
    refine ⟨F, ?_⟩
    have h₁ := pullback_map_left_fst (spMap (algebraMap W L)) F
    rw [hF, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ← ha', Category.assoc] at h₁
    have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
    exact (cancel_epi a.hom.left).1 h₁
  choose f hf using ext
  refine ⟨f, ⟨fun x => ?_, ?_, fun x y => ?_, fun x y => ?_⟩, hf⟩
  · have := hh x
    exact isMonHom_of_isGrpPullback hφ hφ (act x) (f x) (hf x)
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback hφ.1 ?_
    rw [← hf, h1, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback hφ.1 ?_
    rw [← hf, hmul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback hφ.1 ?_
    let φ₀ : Over.mk (A.hom ≫ spMap (algebraMap W L)) ⟶ G := Over.homMk φ hφ.1.w
    have h := hφ.2 A (act x) (act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm
    rw [← MonObj.comp_mul] at h
    rw [← hf, hadd, ← h]
    rfl

end GlobalTheory
end

