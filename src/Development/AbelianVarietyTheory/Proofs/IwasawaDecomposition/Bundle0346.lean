module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0012
public import ReciprocityTheory.GaloisValuations.Global
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrtLeHPartOfCarries
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem isSF_ssetF_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : R.WeakCharacterisation F) (hC : GlobalTheory.Hk3.Core R.toRealDat F.lv2) :
    GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat A3.A.μ0) := by
  intro v
  have hQ := (_root_.GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.lev).1
  have hS : R.Sb = R.Pg := hW.allPl
  unfold SsetF
  rw [hQ, hS]
  simp only [Finset.union_empty, Finset.mem_image]
  refine exists_congr fun PP => and_congr_right fun _ => ?_
  exact ⟨fun h => by rw [← h]; rfl, fun h => HeightOneSpectrum.ext h⟩


set_option maxHeartbeats 1000000 in
theorem prt_le_hPart_of_carries : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c p, HasEig R F Y π c → R.Carries p c → (Y.Ish.prt : D.what₂.FT → Submodule ℂ (AmbT (R.MY 0))) π ≤ (hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A3.A.ok A3.A.μ0) R.pl A3.A.q (RealDat.polE (A := A3.A) p.1.1)).map (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap := by
  intro _ _ _ hR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ π c p hE hc
  obtain ⟨hC, hSF, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have hS := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hR R.toRealDat
  have hμ : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hSF' : GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) := by
    rw [hμ]; exact isSF_ssetF_base R F hP.char hC
  have hinj := GlobalTheory.AdjPart.adjoint_injective_on_part R
    ⟨hH.prim.posScal.1, fun i t p => hH.prim.posScal.2 i t p _⟩ hH.prim.thmB
  have hlab := GlobalTheory.T.heckePolynomials_of_carried_eigensystem R F (GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hR D) hH.ok hP.char hH.aux.ex hS hinj p c hc
  have hpart := (_root_.GlobalTheory.HeckeSplitPart.parts_in_hPart R.toRealDat F.lv2 (s := 1) hH.ok.ok2 hC _ hSF' c (RealDat.polE (A := A3.A) p.1.1)).1
    fun P hP => (hlab P hP).1
  rw [Y.prtE π]
  refine Submodule.map_mono fun U hU => ?_
  obtain ⟨x, hx, rfl⟩ := _root_.GlobalTheory.TypePart.isotE_sub_eigenpart R.toRealDat F.lv2 (s := 1) hC hS _ hSF' Y.hF Y.PY Y.PW Y.stdPsi.1 Y.stdPsi.2
    _ _ c hE true U hU
  exact hpart x hx

end GlobalTheory.Mem.R3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrtWLeHPart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3


set_option maxHeartbeats 1000000 in
theorem prtW_le_hPart : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c p, HasEig R F Y π c → R.Carries p c → ∀ i : Fin D.R.m, (Y.IL.prtW : ∀ i : Fin D.R.m, D.what₂.FT → Submodule ℂ (AmbT (R.MW i (sg0 D A3.A)))) i π ≤ (hPart (R.MW i (sg0 D A3.A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A3.A.ok A3.A.μ0) R.pl A3.A.q (RealDat.polW (A := A3.A) p.1.1)).map (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap := by
  intro _ _ _ hcusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ π c p hc hcar i
  obtain ⟨hC, -, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have ht : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hQ : R.Q A3.A.μ0 = ∅ := (GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.lev).1
  have hSb : R.Sb = R.Pg := hP.char.allPl
  have hSF : GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) := by
    classical
    intro v
    unfold SsetF
    rw [ht, hQ, hSb, Finset.union_empty, Finset.mem_image]
    refine exists_congr fun PP => and_congr_right fun _ => ?_
    rw [← underPl_asIdeal]
    exact ⟨fun h => by rw [h], fun h => HeightOneSpectrum.ext h⟩
  have hlab := GlobalTheory.T.heckePolynomials_of_carried_eigensystem R F (GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hcusp D) hH.ok hP.char hH.aux.ex
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hcusp R.toRealDat)
    (GlobalTheory.AdjPart.adjoint_injective_on_part R ⟨hH.prim.posScal.1, fun i t p => hH.prim.posScal.2 i t p _⟩ hH.prim.thmB)
    p c hcar
  rw [Y.prtWE i π]
  refine Submodule.map_mono fun U hU => ?_
  obtain ⟨x, hx, rfl⟩ := _root_.GlobalTheory.PartTypeW.part_in_eigenpart R.toRealDat F.lv2 hH.ok.ok2 hC _ hSF Y.hF Y.PY Y.PW Y.stdPsi.1 Y.stdPsi.2
    _ ⟨0, Y.hm⟩ c hc i U hU
  exact (_root_.GlobalTheory.HeckeSplitPart.parts_in_hPart R.toRealDat F.lv2 hH.ok.ok2 hC _ hSF c _).2 i (fun P hP => (hlab P hP).2) x hx

end GlobalTheory.Mem.R3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldHostConductorIsRayClassField
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ParRayMax

@[reducible] def algQb (D : D7) (jE : D.host.E →+* Qb) : Algebra D.host.K Qb :=
  (jE.comp (algebraMap D.host.K D.host.E)).toAlgebra

def toIF (D : D7) (jE : D.host.E →+* Qb) (L : Fld) (h : KQbar D jE ≤ L) :
    @IntermediateField D.host.K Qb _ _ (algQb D jE) :=
  letI := algQb D jE
  { L.toSubfield with algebraMap_mem' := fun x => h ⟨x.1, x.2, rfl⟩ }


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_embedded (hray : GlobalTheory.Published.RayClassFieldSt) (D : D7) (jE : D.host.E →+* Qb) :
    ∃ (M : Fld) (h : KQbar D jE ≤ M) (hf : FiniteDimensional ℚ M),
      letI := GlobalTheory.ParRay.algK D jE h
      haveI := GlobalTheory.ParRay.nfOf hf
      GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host) := by
  obtain ⟨M, _, _, _, hM⟩ := GlobalTheory.Published.rayClassFieldSt_iff_isRayField.1 hray D.host.K _
    (GlobalTheory.Mem.RaySplit.condIdeal_ne_bot D.host)
  letI := algQb D jE
  let ψ : M →ₐ[D.host.K] Qb := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let M1 : Fld := (ψ : M →+* Qb).toRatAlgHom.fieldRange
  have hψ : ∀ x : D.host.K, ψ (algebraMap D.host.K M x) = jE x := fun x => ψ.commutes x
  have hK : KQbar D jE ≤ M1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨algebraMap D.host.K M ⟨x, hx⟩, hψ ⟨x, hx⟩⟩
  let e₀ : M ≃ₐ[ℚ] M1 := AlgEquiv.ofInjectiveField (ψ : M →+* Qb).toRatAlgHom
  have hf : FiniteDimensional ℚ M1 := e₀.toLinearEquiv.finiteDimensional
  refine ⟨M1, hK, hf, ?_⟩
  letI := GlobalTheory.ParRay.algK D jE hK
  haveI := GlobalTheory.ParRay.nfOf hf
  exact hM.of_algEquiv (AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) fun x => Subtype.ext (hψ x))


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem le_of_rayAdm (D : D7) (jE : D.host.E →+* Qb) (M : Fld) (h : KQbar D jE ≤ M) (hf : FiniteDimensional ℚ M)
    (hM : letI := GlobalTheory.ParRay.algK D jE h; haveI := GlobalTheory.ParRay.nfOf hf;
      GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host))
    (L : Fld) (hL : RayAdm (KQbar D jE) (D.host.QS * D.host.q * D.host.d) L) : L ≤ M := by
  have h2K := GlobalTheory.Mem.RaySplit.finrank_K D.host
  have h3K := GlobalTheory.Mem.RaySplit.isEmpty_real D.host
  letI := GlobalTheory.ParRay.algK D jE h
  haveI := GlobalTheory.ParRay.nfOf hf
  letI := algQb D jE
  obtain ⟨hKL, hfL, hspl⟩ := hL
  let mkE : ∀ (X : Fld) (hX : KQbar D jE ≤ X), X ≃+* toIF D jE X hX := fun X hX =>
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
  let R := toIF D jE M h
  let L' := toIF D jE L hKL
  let eR : M ≃ₐ[D.host.K] R := AlgEquiv.ofRingEquiv (f := mkE M h) fun x => rfl
  let eL : L ≃+* L' := mkE L hKL
  haveI : NumberField R := { to_finiteDimensional := (eR.toRingEquiv.toRatAlgEquiv).toLinearEquiv.finiteDimensional }
  haveI : NumberField L' := { to_finiteDimensional := eL.toRatAlgEquiv.toLinearEquiv.finiteDimensional }
  have hR : GlobalTheory.Mem.Fld.IsRayField D.host.K R (GlobalTheory.Mem.RaySplit.condIdeal D.host) := hM.of_algEquiv eR
  have hab : IsAbelianGalois D.host.K R := hR.1
  have key : ∀ 𝔭 : HeightOneSpectrum (𝓞 D.host.K), ¬ 𝔭.asIdeal ∣ GlobalTheory.Mem.RaySplit.condIdeal D.host →
      (𝔭.asIdeal.primesOver (𝓞 R)).ncard = Module.finrank D.host.K R →
        ∃ π : 𝓞 D.host.K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ GlobalTheory.Mem.RaySplit.condIdeal D.host :=
    fun 𝔭 h1 h2 => GlobalTheory.T.exists_span_eq_one_mod_of_splits_in_rayClassField D.host.K R _ hR 𝔭 h1 h2
  have hle : L' ≤ R := by
    refine @GlobalTheory.Bauer.le_of_finite_split_not_split D.host.K Qb _ _ _ _ R L' _ _ hab.toIsGalois
      ((Ideal.finite_factors (GlobalTheory.Mem.RaySplit.condIdeal_ne_bot D.host)).subset ?_)
    rintro 𝔭 ⟨hpr, hRs, hLs⟩
    by_contra hnd
    apply hLs
    rw [GlobalTheory.Bauer.ncard_eq_ncard_primesOver] at hRs ⊢
    obtain ⟨π, hπ, hπ1⟩ := key 𝔭 hnd hRs
    obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.RayFieldNorm.exists_mul_conj_eq_norm D.host.K h3K h2K
      (jE.comp (algebraMap D.host.K D.host.E)) π (Ideal.absNorm 𝔭.asIdeal) (congrArg Ideal.absNorm hπ).symm
    have hray : IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (Ideal.absNorm 𝔭.asIdeal) := by
      refine ⟨hpr, jE ((π : D.host.K) : D.host.E), ⟨_, (π : D.host.K).2, rfl⟩, ?_, ?_, σ, hσ⟩
      · exact (RingOfIntegers.isIntegral_coe π).map (jE.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
      · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hπ1
        have hm0 : ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) ≠ 0 := by
          exact_mod_cast GlobalTheory.Mem.RaySplit.cond_ne_zero D.host
        have e : (jE ((π : D.host.K) : D.host.E) - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) =
            (jE.comp (algebraMap D.host.K D.host.E)) (y : D.host.K) := by
          rw [div_eq_iff hm0]
          have e1 := congrArg ((jE.comp (algebraMap D.host.K D.host.E)).comp (algebraMap (𝓞 D.host.K) D.host.K)) hy
          simp only [map_mul, map_sub, map_one, map_natCast] at e1
          exact e1.symm
        rw [e]
        exact (RingOfIntegers.isIntegral_coe y).map (jE.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
    have hsp := hspl _ hray
    have h1 : ((Ideal.span {((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℤ)}).primesOver (𝓞 L')).ncard = Module.finrank ℚ L' := by
      rw [← GlobalTheory.HostSplit.ncard_placesOver L' hpr, ← finrank_eq_of_equiv eL]
      exact (ncard_places_of_equiv eL _).symm.trans hsp
    exact _root_.GlobalTheory.SplitTower.splits_completely_of_intermediate D.host.K L' _ hpr h1 𝔭 (Ideal.absNorm_mem 𝔭.asIdeal)
  exact fun x hx => hle hx

theorem rayField_isRay : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (jE : D.host.E →+* Qb),
    ∃ (h : KQbar D jE ≤ MrayC D jE) (hf : FiniteDimensional ℚ (MrayC D jE)),
      letI := GlobalTheory.ParRay.algK D jE h
      haveI := GlobalTheory.ParRay.nfOf hf
      IsGalois D.host.K (MrayC D jE) ∧ (∀ σ τ : MrayC D jE ≃ₐ[D.host.K] MrayC D jE, σ * τ = τ * σ) ∧
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr (MrayC D jE) → p ∣ D.host.QS * D.host.q * D.host.d) ∧
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn (MrayC D jE) p := by
  intro hray D jE
  obtain ⟨M, h, hf, hM⟩ := exists_embedded hray D jE
  have hsplit := GlobalTheory.T.rayClassField_splitsIn_of_isRayPrime D jE M h hf hM
  have heq : MrayC D jE = M :=
    le_antisymm (iSup₂_le fun L hL => le_of_rayAdm D jE M h hf hM L hL) (le_rayField ⟨h, hf, hsplit⟩)
  generalize MrayC D jE = X at heq ⊢
  subst heq
  refine ⟨h, hf, ?_⟩
  letI := GlobalTheory.ParRay.algK D jE h
  haveI := GlobalTheory.ParRay.nfOf hf
  exact ⟨GlobalTheory.Mem.RaySplit.isGalois_of_ray hM, GlobalTheory.Mem.RaySplit.comm_of_ray hM, GlobalTheory.Mem.RaySplit.unr_of_ray hM, hsplit⟩

end GlobalTheory.ParRayMax

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TwFin

theorem exists_over {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  first
  | exact @_root_.GlobalTheory.IsolatedTheoremFour.main
  | exact _root_.GlobalTheory.IsolatedTheoremFour.main
  | (apply _root_.GlobalTheory.IsolatedTheoremFour.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IsolatedTheoremFour.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IsolatedTheoremFour.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IsolatedTheoremFour.main ..)

theorem finite_mem {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  exact hv

theorem mul_ne_one {R : Ranks} {H : Formalism.BasicNotions.Host R} {S : Set ℕ} {p : ℕ} {δ ψ : HChar H.E} (hp : p.Prime) (hS : p ∈ S)
    (hδ : IsDelta (H := H) p δ) (hψ : Chr.IsTwist H S ψ) : δ * ψ ≠ 1 := by
  intro h
  obtain ⟨v, hv⟩ := exists_over (K := H.E) hp
  have hu : ψ.UnrAt v := by
    by_contra hn
    obtain ⟨-, hq, -, hnS⟩ := hψ.2.2.2 v hn
    have := Examples₂.PlacesToy.prime_mem_unique v hq hp (Ideal.absNorm_mem _) hv
    exact hnS (this ▸ hS)
  have h1 := (hδ.ine v hv 1).1 fun x hx => by
    have h2 : (δ * ψ).loc v x = 1 := by
      rw [h]
      rfl
    change δ.loc v x * ψ.loc v x = 1 at h2
    rw [hu x hx, mul_one] at h2
    simpa only [pow_one] using h2
  omega

theorem resChar_conj (B : Base) (w : B.places.Pl) : B.places.resChar (B.places.conj w) = B.places.resChar w := by
  refine Examples₂.PlacesToy.prime_mem_unique (B.places.conj w) (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _)
    (Examples₂.PlacesToy.resCharW_mem _) ?_
  have h := (Examples₂.PlacesToy.mem_conjW_pow w ((Examples₂.PlacesToy.resCharW w : ℕ) : 𝓞 B.LL) 1).2
    (by rw [pow_one, map_natCast]; exact Examples₂.PlacesToy.resCharW_mem w)
  rw [pow_one] at h
  exact h

theorem finite_pl (B : Base) (s : Finset ℕ) : {w : B.places.Pl | B.places.resChar w ∈ s}.Finite := by
  refine ((s.finite_toSet.subset (s := (s : Set ℕ)) (t := {p | p ∈ s ∧ p ≠ 0}) fun p hp => hp.1).biUnion
    fun p hp => finite_mem (K := B.LL) hp.2).subset fun w hw => ?_
  simp only [Set.mem_iUnion]
  exact ⟨B.places.resChar w, ⟨hw, (B.places.resChar_prime w).ne_zero⟩, Examples₂.PlacesToy.resCharW_mem w⟩

theorem tw_fin : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B), (T.set f).Finite ∧ (∀ w, T.xiTw f w ≠ 1) ∧ (∀ w, T.xiTw f (B.places.conj w) = T.xiTw f w) ∧ {w : B.places.Pl | B.places.resChar w ∈ T.pl}.Finite := by
  intro B f T
  refine ⟨?_, fun w => ?_, fun w => ?_, finite_pl B T.pl⟩
  · have h3 : ({1, f.del, f.del'} : Set (HChar B.host.E)).Finite := Set.toFinite _
    refine (h3.union ((finite_pl B T.pl).image (T.xiTw f))).subset ?_
    rintro ξ (h | ⟨w, rfl⟩)
    · exact Or.inl h
    · by_cases hw : B.places.resChar w ∈ T.pl
      · exact Or.inr ⟨w, hw, rfl⟩
      · left
        unfold TwDat.xiTw
        rw [(T.off w hw).1, mul_one]
        split_ifs
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl rfl)
  · unfold TwDat.xiTw
    split_ifs
    · exact mul_ne_one B.host.pde'_prime (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) f.isDel' (T.psi_tw w)
    · exact mul_ne_one B.host.pde_prime (Or.inr (Or.inr (Or.inl rfl))) f.isDel (T.psi_tw w)
  · unfold TwDat.xiTw
    rw [resChar_conj, (T.conj w).1]

end GlobalTheory.Mem.Top.TwFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizesEqCount
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Top

def duPre (B : Pre) (u : B.Word) : ℝ :=
  (letI := B.host.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm B.host.E B.R.k) (StandardLattice.stdLat B.host.E B.R.k)) *
    (StandardLattice.idxColLoc (B.host.g 0) B.R.k ^ B.R.f * StandardLattice.idxColLoc (B.host.g 1) B.R.k ^ B.R.f) *
    ∏ τ : Tau B.R, StandardLattice.dimV (fun i : Fin B.R.k => (((B.hcW u τ).u i : ℚ) : ℝ))

def DsPre (B : Pre) : ℝ :=
  (letI := B.host.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm B.host.E B.R.r) (StandardLattice.stdLat B.host.E B.R.r)) *
    (StandardLattice.idxRowLoc (B.host.g 0) B.R.k B.R.m ^ B.R.f * StandardLattice.idxRowLoc (B.host.g 1) B.R.k B.R.m ^ B.R.f) *
    ∏ τ : Tau B.R, Vol.trueDsig B.R (B.hc τ)

theorem Ctx.Over.sizes {K : Ctx} {B : Pre} (h : K.Over B) :
    (∀ u, (B.duStar u : ℝ) = duPre B u) ∧ B.Dstar = DsPre B := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  exact ⟨fun u => K.du_eq u, K.Ds_eq⟩

theorem sigYD_zero (R : Ranks) : 2 ≤ (sigYD R 0).1 ∧ (sigYD R 0).1 + (sigYD R 0).2 = R.r := by
  have h1 := R.two_le_m
  have h2 := R.m_add_three_le_k
  simp only [sigYD, Ranks.rankY, Ranks.r]
  omega

theorem sizes_eq_count (K : Ctx) (X : Stages) (hO : K.Over X.B.toPre) (hv : StandardLattice.VolumeEqMass₂ X.toD7)
    (hd : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)) :
    (∀ u, ((X.toD7.mem u).A.duStar : ℝ) = StandardLattice.duStarU X.toD7 u) ∧ X.toD7.what₂.Dstar = StandardLattice.DstarD X.toD7 := by
  obtain ⟨h1, h2⟩ := hO.sizes
  refine ⟨fun u => ?_, ?_⟩
  · have e : (X.toD7.mem u).A.duStar = X.B.duStar u := X.C.A_duStar u
    rw [e]
    refine (h1 u).trans ?_
    unfold duPre StandardLattice.duStarU StandardLattice.duStarP
    congr 1
  · have e : X.toD7.what₂.Dstar = X.B.Dstar := (X.toD7.Dstar_eq X.toD7.u₀).symm.trans (X.C.A_Dstar _)
    rw [e, h2]
    have hvol : StandardLattice.volY0 X.toD7 = StandardLattice.massI X.toD7 X.B.R.r := by
      letI := X.toD7.host.cmStar
      have := hv.2 (X.toD7.sp.Y 0) (sigYD X.B.R 0).1 (sigYD X.B.R 0).2 (X.toD7.sp.Y_sig 0)
        (fun τ => X.toD7.Y_sigval 0 (Nat.zero_le _) τ) (sigYD_zero _).1
      rw [(sigYD_zero _).2] at this
      exact this
    unfold DsPre StandardLattice.DstarD StandardLattice.DstarP
    rw [hvol]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => (hd τ).symm

end GlobalTheory.Mem.Top

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharEqOfTameRepCongr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem char_eq_of_tameRep_congr : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)), ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → 0 < normV P - 1 → ((normV P - 1 : ℕ) : 𝓞 E) ∉ P.asIdeal → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (normV P - 1) = 1) → ∀ (σ σ' : G E Ω) (u u' : 𝓞 E), NX.TameRep P 1 σ u → NX.TameRep P 1 σ' u' → u - u' ∈ P.asIdeal → χ σ = χ σ' := by
  intro E Ω _ _ _ _ _ P O _ _ _ _ _ hO χ hχ hm hmP hk σ σ' u u' hσ hσ' huu
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A P := exists_isPlaceOver Ω P
  obtain ⟨ρ, hs, ϖ, π, hϖ, hϖ2, hπ, hv⟩ := GlobalTheory.TameTauConj.tameRep_conj A P hA 1 σ u hσ
  obtain ⟨ρ', hs', ϖ', π', hϖ', hϖ2', hπ', hv'⟩ := GlobalTheory.TameTauConj.tameRep_conj A P hA 1 σ' u' hσ'
  have hconj : ∀ a b : G E Ω, χ (a⁻¹ * b * a) = χ b := by
    intro a b
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  rw [← hconj ρ σ, ← hconj ρ' σ']
  set s := ρ⁻¹ * σ * ρ
  set s' := ρ'⁻¹ * σ' * ρ'
  set m := normV P - 1
  rw [zpow_one] at hv hv'
  rw [← GlobalTheory.TameTau.tame_quot_indep A P hA m hm hmP ϖ ϖ' hϖ hϖ2 hϖ' hϖ2' π π' hπ hπ' s' hs'] at hv'
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hϖ2 (Submodule.zero_mem _)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne', eq_comm, map_eq_zero] at hπ
    exact hϖ0 (by exact_mod_cast hπ)
  have hroot : ∀ t : G E Ω, (t π / π) ^ m = 1 := by
    intro t
    rw [div_pow, ← map_pow, hπ, AlgEquiv.commutes, ← hπ, div_self (pow_ne_zero _ hπ0)]
  have hlt : ∀ x : 𝓞 E, A.valuation (algebraMap E Ω (x : E)) < 1 ↔ x ∈ P.asIdeal := by
    intro x
    exact hA x
  have hmv : ¬ A.valuation (m : Ω) < 1 := by
    intro h
    apply hmP
    rw [← hlt]
    simpa using h
  have hu : A.valuation (algebraMap E Ω (u : E) - algebraMap E Ω (u' : E)) < 1 := by
    have := (hlt (u - u')).2 huu
    simpa using this
  have heq : s π / π = s' π / π := by
    refine root_eq_of_close A m (hroot s) (hroot s') hmv ?_
    have e : s π / π - s' π / π = (s π / π - algebraMap E Ω (u : E))
        + (algebraMap E Ω (u : E) - algebraMap E Ω (u' : E)) - (s' π / π - algebraMap E Ω (u' : E)) := by ring
    rw [e]
    exact Valuation.map_sub_lt _ (Valuation.map_add_lt _ hv hu) hv'
  exact GlobalTheory.T.continuous_char_eq_of_inertia_condition A P hA hO χ hχ m hm hmP (hk A hA) ϖ hϖ hϖ2 π hπ s hs s' hs'
    ((div_left_inj' hπ0).1 heq)

end GlobalTheory.TameTau
end

