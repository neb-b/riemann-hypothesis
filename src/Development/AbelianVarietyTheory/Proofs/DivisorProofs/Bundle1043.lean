module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
public import ReciprocityTheory.SemistableReduction.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
section
noncomputable section

open scoped TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.PolynomialMatching

section Extend

variable {ι : Type} {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

def padFam (T S : Finset ι) (c : ∀ i, M i) (x : ∀ u : T, M u) : ∀ u : S, M u :=
  fun u => if h : u.1 ∈ T then x ⟨u.1, h⟩ else c u.1

theorem padFam_update (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) [DecidableEq T] [DecidableEq S]
    (x : ∀ u : T, M u) (i : T) (y : M i) :
    padFam T S c (Function.update x i y) = Function.update (padFam T S c x) ⟨i.1, hTS i.2⟩ y := by
  funext u
  by_cases h : u.1 ∈ T
  · by_cases hu : u.1 = i.1
    · obtain ⟨u, hu'⟩ := u
      obtain ⟨i, hi⟩ := i
      simp only at hu
      subst hu
      simp [padFam, h]
    · have h1 : (⟨u.1, h⟩ : T) ≠ i := fun e => hu (by rw [← e])
      have h2 : u ≠ ⟨i.1, hTS i.2⟩ := fun e => hu (by rw [e])
      simp only [padFam, h, dif_pos, Function.update_of_ne h1, Function.update_of_ne h2]
  · have h2 : u ≠ ⟨i.1, hTS i.2⟩ := fun e => h (by rw [e]; exact i.2)
    simp only [padFam, h, dif_neg, not_false_eq_true, Function.update_of_ne h2]

def padMultilinear (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) :
    (∀ u : T, M u) →ₘₗ[ℂ] (⨂[ℂ] u : S, M u) where
  toFun x := PiTensorProduct.tprod ℂ (padFam T S c x)
  map_update_add' x i y z := by
    simp only [padFam_update T S hTS c]
    exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
  map_update_smul' x i r y := by
    simp only [padFam_update T S hTS c]
    exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _

def padTensor (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) :
    (⨂[ℂ] u : T, M u) →ₗ[ℂ] ⨂[ℂ] u : S, M u :=
  PiTensorProduct.lift (padMultilinear T S hTS c)

theorem padTensor_tprod (T S : Finset ι) (hTS : T ⊆ S) (c : ∀ i, M i) (x : ∀ u : T, M u) :
    padTensor T S hTS c (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (padFam T S c x) := by
  simp [padTensor, padMultilinear]

end Extend

theorem polMatchOn_insert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a') (v : Pl (F := F)),
    Rf.p v (G.M.vac v) = Rf.p' v (G.M'.vac v) → ∀ (T : Finset (Pl (F := F))) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ)
    (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T Φ Φ' →
    GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf (insert v T) Φ Φ' := by
  intro F E _ _ _ _ _ σ B a a' G X R Rf v hv T Φ Φ' hM
  obtain ⟨m, m', f, φ, f', φ', hφ, hφ', hΦ, hΦ', hsum⟩ := hM
  refine ⟨m, m', f, φ, f', φ',
    fun i => ⟨(hφ i).1, (hφ i).2.1, fun w hw => (hφ i).2.2 w fun h => hw (Finset.mem_insert_of_mem h)⟩,
    fun j => ⟨(hφ' j).1, (hφ' j).2.1, fun w hw => (hφ' j).2.2 w fun h => hw (Finset.mem_insert_of_mem h)⟩,
    hΦ, hΦ', ?_⟩
  let c : ∀ u, Rf.Pi u := fun u => Rf.p u (G.M.vac u)
  have key := congrArg (LinearMap.lTensor R.Pi (padTensor T (insert v T) (Finset.subset_insert _ _) c)) hsum
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.lTensor_tmul, padTensor_tprod] at key
  have e1 : ∀ i, padFam T (insert v T) c (fun u : T => Rf.p u (φ i u)) =
      fun u : (insert v T : Finset (Pl (F := F))) => Rf.p u (φ i u) := by
    intro i
    funext u
    by_cases h : u.1 ∈ T
    · simp [padFam, h]
    · simp [padFam, h, c, (hφ i).2.2 u.1 h]
  have e2 : ∀ j, padFam T (insert v T) c (fun u : T => Rf.p' u (φ' j u)) =
      fun u : (insert v T : Finset (Pl (F := F))) => Rf.p' u (φ' j u) := by
    intro j
    funext u
    by_cases h : u.1 ∈ T
    · simp [padFam, h]
    · obtain ⟨u, hu⟩ := u
      have huv : u = v := by
        rcases Finset.mem_insert.1 hu with h' | h'
        · exact h'
        · exact absurd h' h
      subst huv
      simp [padFam, h, c, (hφ' j).2.2 u h, hv]
  simp only [e1, e2] at key
  exact key

end GlobalTheory.ThK.PolynomialMatching
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMultiplicityDvdFixFirstBlock
section
open MvPolynomial GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra

set_option autoImplicit false

namespace GlobalTheory.ChowSection

theorem totalDegree_of_isChowFormInt {k : Type} [Field k] {N e d : ℕ}
    {Q : Ideal (MvPolynomial (Fin N) k)} {g : MvPolynomial (Fin (e + 1) × Fin N) k}
    (h : IsChowFormInt Q e d g) : g.totalDegree = (e + 1) * d := by
  rw [((isMultiHomogeneous_iff_block.1 h.homog).isHomogeneous).totalDegree h.ne_zero]
  simp

end GlobalTheory.ChowSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelEigenpartsAndConjugateCharacters
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrincipalDecomp

open GlobalTheory.SphericalOps GlobalTheory.HeckeAdjoint GlobalTheory.HeckeOrthSum

theorem iSup_partH_eq_top_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) → (⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c) = ⊤ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ hS
  classical
  obtain ⟨hinj, hrange, -⟩ := hC.models.HW i σ
  have hrange' : LinearMap.range (R.HW i σ).e =
      Mult R.θ (R.MW i σ) (Lev.levG _ (R.βW i) (R.datWp i R.triv) : Set (GA D (Wc D i))) (chiW R i) := hrange
  haveI : FiniteDimensional ℂ
      (Mult R.θ (R.MW i σ) (Lev.levG _ (R.βW i) (R.datWp i R.triv) : Set (GA D (Wc D i))) (chiW R i)) := by
    rw [← hrange']; infer_instance
  obtain ⟨n, hB⟩ := hC.lev.βW i
  have key := mult_le_of_parts (J := Lev.levG _ (R.βW i) (R.datWp i R.triv)) (Sb := GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R)
    hC.models.inf (hC.models.νW i).1.1 (hC.models.νW i).2 hS (fun P d Rp h T hT => ?_)
    ((⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c).map (R.HW i σ).e) (fun c hc T hT => ?_)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, e⟩ := key (hrange' ▸ LinearMap.mem_range_self _ x)
    exact hinj e ▸ hy
  · have hN : (((1 ^ n : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
      rw [one_pow, Nat.cast_one]
      exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
    have hO : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P := by
      obtain ⟨_, _, _, _, hO, -⟩ := h
      exact hO
    have hP : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
      rintro PP (hP | hP)
      · exact GlobalTheory.HeckeOffLevel.sep_of_offS hO (by
          unfold GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF
          exact Finset.mem_image.2 ⟨PP, hP, rfl⟩)
      · exact absurd hP (Finset.notMem_empty _)
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
    refine isMultMap_heckeOn hT (fun k hk => ?_) fun v => GlobalTheory.HeckeOffLevel.hasType_heckeLin hB hN hP h (hT.lev v)
    obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩ := h
    exact (hc.1 k hk).1
  · obtain ⟨y, rfl⟩ : T ∈ LinearMap.range (R.HW i σ).e := hrange' ▸ hT.1
    exact Submodule.mem_map_of_mem
      (le_iSup₂_of_le (f := fun (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c) => partH R i σ c) c hc le_rfl hT)

end GlobalTheory.PrincipalDecomp

namespace GlobalTheory.LiftLower

theorem gW_mem_partH_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (g : G), ∀ x ∈ partH R i σ c, R.gW i σ g x ∈ partH R i σ c := by
  classical
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ c g x hx
  unfold partH at hx ⊢
  rw [Submodule.mem_comap, mem_partFull] at hx ⊢
  refine ⟨?_, fun P d Rp hR v => ?_⟩
  · have h : (R.HW i σ).e (R.gW i σ g x) ∈ LinearMap.range (R.HW i σ).e := LinearMap.mem_range_self _ _
    rw [(hC.models.HW i σ).2.1] at h
    exact h
  have hO : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P := by
    obtain ⟨_, _, _, _, h, -⟩ := hR
    exact h
  obtain ⟨-, h2⟩ := GlobalTheory.offS_not_type_places R.C.P R.Pg (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P hC.lev.Pg
    (fun PP hPP => by unfold GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF; exact Finset.mem_image.2 ⟨PP, hPP, rfl⟩) hO
  obtain ⟨a, hB⟩ := hC.lev.βW i
  have hN : (((1 ^ a : ℕ)) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
    P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h))
  have hPP : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    rintro PP (h | h)
    · exact h2 PP h
    · exact absurd h (Finset.notMem_empty _)
  have hT := ((GlobalTheory.MultMem.mem_mult_iff ..).1 hx.1).lev v
  rw [hC.models.gW i σ g x, postOn_apply, ← map_smul, ← hx.2 P d Rp hR v]
  exact (GlobalTheory.HeckeKeepsGood.sphericalOperator_commute_levelFiniteGroup hB hN hPP hR hT (R.eG g)).symm

end GlobalTheory.LiftLower

namespace GlobalTheory.ConjMuChar

theorem exists_galConj_chrEq_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ μ' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ s hσ μ' hμ
  obtain ⟨μH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D μ' hμ.1
  refine ⟨μH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have hx : infPart D ((Formalism.L2.JoinChr.locU he.1 k : (AE D)ˣ) : AE D) = 1 := by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, RingHom.map_add (f := _), RingHom.map_mul, hinf, zero_mul, add_zero,
      RingHom.map_one]
  obtain ⟨y, hy0, hy⟩ := hμ.2.2.2.1 _ hx
  have a1 := hH.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  have a2 := (hC.lev.mu0 i).2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  rw [hC.lev.xi_base, mul_one]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one]
  rw [← a1, ← a2, hy, hy0, hσ.1]

end GlobalTheory.ConjMuChar

namespace GlobalTheory.EtaConjChar

open Formalism.L2.Host Formalism.L2.JoinChr

theorem exists_galConj_eta_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR σ s hσ η' hη
  obtain ⟨ηH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1
  refine ⟨ηH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (locU he.1 (unif P)) rfl
  have h0 : ∀ u : D.host.Eˣ, P.valuation D.host.E (u : D.host.E) = 1 → R.C.eta.locK P u = 1 := fun u hu =>
    R.C.isEta.unr P _ ((P.valuedAdicCompletion_eq_valuation' (u : D.host.E)).trans hu)
  rw [twVal_half _ P (locK_eq_one hH hη.2.1 P), twVal_half _ P h0, map_zpow₀,
    ← hH.2 P e he _ (locU he.1 (unif P)) rfl, ← hR.lev.eta.2 P e he _ (locU he.1 (unif P)) rfl, ← hy1, ← hy2, hσ.1]

end GlobalTheory.EtaConjChar

namespace GlobalTheory.FiveClauseParts

theorem parts_conj_five : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) → (⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c) = ⊤) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (g : G), ∀ x ∈ partH R i σ c, R.gW i σ g x ∈ partH R i σ c) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ μ' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH) :=
  ⟨GlobalTheory.PrincipalDecomp.iSup_partH_eq_top_five, GlobalTheory.LiftLower.gW_mem_partH_five,
    GlobalTheory.ConjMuChar.exists_galConj_chrEq_five, GlobalTheory.EtaConjChar.exists_galConj_eta_five⟩

end GlobalTheory.FiveClauseParts

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.AdelicMatrixLatticeF

theorem lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ),
    IsTopologicalAddGroup (WOF F E nS nT) ∧ LocallyCompactSpace (WOF F E nS nT) ∧
    SecondCountableTopology (WOF F E nS nT) ∧ T2Space (WOF F E nS nT) ∧ DiscreteTopology (ratLF F E nS nT) ∧
    ∃ K : Set (WOF F E nS nT), IsCompact K ∧ ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈ K := by
  intro F E _ _ _ _ _ nS nT
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele _
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  have : IsTopologicalRing (AEF F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : LocallyCompactSpace (AEF F E) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AEF F E) := e.secondCountableTopology
  have : T2Space (AEF F E) := e.isEmbedding.t2Space
  have hg : IsTopologicalAddGroup (WOF F E nS nT) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin nT → Fin nS → AEF F E))
  refine ⟨hg, inferInstanceAs (LocallyCompactSpace (Fin nT → Fin nS → AEF F E)),
    inferInstanceAs (SecondCountableTopology (Fin nT → Fin nS → AEF F E)),
    inferInstanceAs (T2Space (Fin nT → Fin nS → AEF F E)), ?_, ?_⟩
  · obtain ⟨U, hU, hx⟩ := GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)
    have hN : (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => U) ∈
        nhds (0 : WOF F E nS nT) :=
      set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : ratLF F E nS nT => (x : WOF F E nS nT)) 0 :=
      continuous_subtype_val.continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
    rintro ⟨_, y, rfl⟩ hy
    have hy0 : y = 0 := by
      funext i j
      exact hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))
    subst hy0
    exact Subtype.ext (map_zero _)
  · obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleCocompact.exists_compact_adele F)
    choose c hc using hx
    refine ⟨Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K,
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK, fun x => ?_⟩
    exact ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩

end GlobalTheory.AdelicMatrixLatticeF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryCountableDiscrete
section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

namespace GlobalTheory.RatUDisc

theorem countable_ratU (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Units.val_injective.countable
  refine Function.Injective.countable (f := fun x : ratU σ J =>
    (Classical.choose (Subgroup.mem_subgroupOf.1 x.2) : GL (Fin n) E)) ?_
  intro x y h
  have hx := Classical.choose_spec (Subgroup.mem_subgroupOf.1 x.2)
  have hy := Classical.choose_spec (Subgroup.mem_subgroupOf.1 y.2)
  apply Subtype.ext; apply Subtype.ext
  rw [← hx, ← hy]
  exact congrArg _ h

theorem discrete_ratU (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) : DiscreteTopology (ratU σ J) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  obtain ⟨U, hU, h⟩ := GlobalTheory.RationalDiscrete.exists_nhds_zero_inclR (F := F) (E := E)
  refine discreteTopology_of_isOpen_singleton_one ?_
  let f : ratU σ J → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
    fun g => ((g.1.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1
  have hf : Continuous f :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      continuous_const
  have hf1 : f 1 = 0 := sub_self _
  rw [isOpen_singleton_iff_nhds_eq_pure]
  refine le_antisymm (fun s hs => Filter.mem_of_superset (x := {1}) ?_ (Set.singleton_subset_iff.2 hs)) (pure_le_nhds _)
  have hW : (⋂ i, ⋂ j, (fun g => f g i j) ⁻¹' U) ∈ 𝓝 (1 : ratU σ J) :=
    Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j =>
      (hf.matrix_elem i j).continuousAt.preimage_mem_nhds (by
        show U ∈ 𝓝 (f 1 i j)
        rw [hf1]; exact hU)
  refine Filter.mem_of_superset hW fun g hg => ?_
  obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 g.2
  have hfg : ∀ i j, f g i j =
      inclR (F := F) (AF F) (((γ : Matrix (Fin n) (Fin n) E) - 1 : Matrix (Fin n) (Fin n) E) i j) := by
    intro i j
    show (((g.1.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1) i j = _
    rw [← hγ, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply,
      apply_ite (inclR (F := F) (AF F)), map_one, map_zero]
    rfl
  have hγ1 : γ = 1 := by
    refine Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => h _ ?_))
    rw [Units.val_one, ← hfg]
    exact Set.mem_iInter.1 (Set.mem_iInter.1 hg i) j
  refine Subtype.ext (Subtype.ext ?_)
  rw [← hγ, hγ1, map_one]
  rfl

theorem countable_discrete_ratU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Countable (ratU σ J) ∧ DiscreteTopology (ratU σ J) :=
  fun F E _ _ _ _ _ σ n J => ⟨countable_ratU F E σ n J, discrete_ratU F E σ n J⟩

end GlobalTheory.RatUDisc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexProd
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.LevOpTmul

theorem finite_supp {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
    (hK : IsOpen (K : Set G)) {f : G → ℂ} (hf : HasCompactSupport f) : {q : G ⧸ K | f q.out ≠ 0}.Finite := by
  have hc : IsCompact (tsupport f) := hf
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x : G => (fun y : G => x⁻¹ * y) ⁻¹' (K : Set G))
    (fun x => hK.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [K.one_mem]⟩)
  refine (t.finite_toSet.image (fun x : G => (x : G ⧸ K))).subset ?_
  intro q hq
  have hmem : q.out ∈ tsupport f := subset_tsupport f hq
  obtain ⟨x, hx, hqx⟩ := Set.mem_iUnion₂.1 (ht hmem)
  refine ⟨x, hx, ?_⟩
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  exact QuotientGroup.eq.2 hqx

theorem levOp_apply {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K₁ : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (S : Finset (G ⧸ K₁)) (hS : ∀ q : G ⧸ K₁, f q.out ≠ 0 → q ∈ S)
    (v : V) : levOp ρ K K₁ f A v = ((K₁.relIndex K : ℕ) : ℂ)⁻¹ • ∑ q ∈ S, f q.out • ρ q.out (A v) := by
  unfold levOp
  rw [finsum_eq_sum_of_support_subset (s := S)]
  · simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
  · intro q hq
    rw [Function.mem_support] at hq
    apply hS
    intro h0
    apply hq
    rw [h0, zero_smul]

theorem term_mk {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K₁ : Subgroup G) (f : G → ℂ) (hf : ∀ k ∈ K₁, ∀ x, f (x * k) = f x) (w : V) (hw : ∀ k ∈ K₁, ρ k w = w) (g : G) :
    f (g : G ⧸ K₁).out = f g ∧ ρ (g : G ⧸ K₁).out w = ρ g w := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K₁ g
  rw [hk]
  exact ⟨hf k k.2 g, by rw [map_mul, Module.End.mul_apply, hw k k.2]⟩

end GlobalTheory.BCT.LevOpTmul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSigStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictsToQuadraticPow_of_restrictsToQuadraticSignPow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (n : ℕ),
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n → Formalism.IndefR.DatumF.ResEtaF χ n := by
  first | exact @GlobalTheory.ResEtaFOfPow.resEtaF_of_resEtaPow | exact GlobalTheory.ResEtaFOfPow.resEtaF_of_resEtaPow | (intros; apply GlobalTheory.ResEtaFOfPow.resEtaF_of_resEtaPow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentPolynomialOfIsAlgCloseStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_laurentPolynomial_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [IsAlgClosed K], IsUnit (q : K) → ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial K)) n i)) ∧ Nonempty (Ht q (sp (LaurentPolynomial K)) 1 i ≃+ ZMod q) := by
  first | (exact @GlobalTheory.EtC.gm_algClosed_cohomology) | (exact GlobalTheory.EtC.gm_algClosed_cohomology) | (intros; apply GlobalTheory.EtC.gm_algClosed_cohomology  <;> assumption)
end

