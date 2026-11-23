module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsComplMapEq
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0816
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0910
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0912
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0745
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0781
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0941
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0102
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.PairingIndexBounds.LatticeNormPowers.CloseUnitNorms.TestVectorMemSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0799
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0871
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesTwistPlacesGoodPosition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0804
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0915
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftVectorEqUnitMulDilatedFlatDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0927
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorThetaLiftOfBaseLevelLaw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0676

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardDivisionPointsHalfSplitPlaceNormPow
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.DivPtLocal


open GlobalTheory.AdelicU in
theorem mem_latO_true_iff_at : ∀ (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D) (u : WO S T), algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin q 1)) • u = u → (u ∈ latO S T LS LT (fun _ => True) ↔ u ∈ latO S T LS LT (fun v => v = q)) := by
  intro D S T LS LT q u hu
  set e0 := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin q 1)) with he0
  constructor
  · intro h
    let Ψ : WO S T →+ WO S T := AddMonoidHom.mk' (fun x => e0 • x)
      fun x y => Matrix.ext fun i j => mul_add e0 (x i j) (y i j)
    have main : latO S T LS LT (fun _ => True) ≤ (latO S T LS LT (fun v => v = q)).comap Ψ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
      refine AddSubgroup.subset_closure ⟨GlobalTheory.AdelicU.singleFin q 1 * α, fun v => ?_, fun v hv => ?_, a, ha, s, hs, t, ht, ?_⟩
      · rw [map_mul]
        by_cases hv : v = q
        · subst hv
          rw [evalV_singleFin_self]
          simpa using hα v
        · rw [evalV_singleFin_ne hv, zero_mul]
          exact zero_mem _
      · rw [map_mul, evalV_singleFin_ne hv, zero_mul]
      · ext i j
        simp only [Ψ, AddMonoidHom.mk'_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, he0,
          Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 1
        rw [Algebra.algebraMap_self, RingHom.id_apply]
        exact Prod.ext (mul_zero (0 : Ainf D.host.F)) rfl
    have := main h
    rw [AddSubgroup.mem_comap] at this
    exact hu ▸ this
  · intro h
    refine AddSubgroup.closure_mono ?_ h
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun _ h' => absurd trivial h', rest⟩

theorem isSplit_of_isIdemAt : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (P.under (𝓞 D.host.F)) := by
  intro D P e he
  rw [GlobalTheory.PtString.isSplit_iff_conj, Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  intro h
  exact GlobalTheory.ModulusNorm.conjPl_ne_of_isIdemAt he (IsDedekindDomain.HeightOneSpectrum.ext h)

theorem natCard_DQ_eq_locQ : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ N : ℕ, 0 < N → Nat.card (GlobalTheory.DivPtFourier.DQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) e N) = Nat.card (GlobalTheory.DivPtLocal.LocQ P N T.rank S.rank) := by
  intro D S T ΛS ΛT hS hT P e he N hN
  have hs := isSplit_of_isIdemAt D P e he
  obtain ⟨ι, hι⟩ := GlobalTheory.DivPtLocal.exists_isIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) hs
  have he1 := _root_.GlobalTheory.IdemIota.idemAt_eq_iota_one D P e he ι hι
  have h3 := hι.2.2.2.1
  have key : ∀ u : WO S T, e • u = u → (u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun v => v = P.under (𝓞 D.host.F))) := by
    intro u hu
    refine mem_latO_true_iff_at D S T _ _ _ u ?_
    rw [← hu, smul_smul, he1, h3]
  have hd : GlobalTheory.DivPtFourier.divPts (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) e N =
      GlobalTheory.DivPtFourier.divPts (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun v => v = P.under (𝓞 D.host.F)) e N := by
    ext y
    rw [GlobalTheory.DivPtFourier.mem_divPts, GlobalTheory.DivPtFourier.mem_divPts]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (key _ (by rw [smul_comm, h1])).1 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (key _ (by rw [smul_comm, h1])).2 h2⟩
  have hh : (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T e =
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun v => v = P.under (𝓞 D.host.F)) ⊓ GlobalTheory.PlaceModel.half S T e := by
    ext y
    rw [AddSubgroup.mem_inf, AddSubgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(key _ ((GlobalTheory.PlaceModel.mem_half S T).1 h2)).1 h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(key _ ((GlobalTheory.PlaceModel.mem_half S T).1 h2)).2 h1, h2⟩
  unfold GlobalTheory.DivPtFourier.DQ
  rw [hd, hh]
  subst he1
  exact GlobalTheory.T.card_divisionPoints_splitPlace_local_matrices D S T ΛS ΛT hS hT P hs ι hι N hN

theorem natCard_DQ : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ N : ℕ, 0 < N → Nat.card (GlobalTheory.DivPtFourier.DQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) e N) = Ideal.absNorm (P.maxPowDividing (Ideal.span {((N : ℕ) : 𝓞 D.host.E)})) ^ (S.rank * T.rank) := by
  intro D S T ΛS ΛT hS hT P e he N hN
  have hI : (Ideal.span {((N : ℕ) : 𝓞 D.host.E)}) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  rw [natCard_DQ_eq_locQ D S T ΛS ΛT hS hT P e he N hN, GlobalTheory.T.card_localMatrixDivisionPointQuotient D.host.E P N T.rank S.rank hN, mul_comm T.rank,
    ← GlobalTheory.LocalDifferentProduct.card_quot_map P hI, Ideal.map_span, Set.image_singleton, map_natCast]

end GlobalTheory.DivPtLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirichletSeriesExponentialSumConvergesStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dirichlet_series_exponential_sum_converges : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∀ x : ℝ, 1 < x → ∃ g : ℂ, HasSum (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ => ((dcoef σ σ' p.1.1 p.2 : ℝ) : ℂ) * Complex.exp (-((dexp p.1.1 p.2 : ℝ) : ℂ) * (x : ℂ))) g ∧ (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ (x : ℂ) w.1) * (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ' (x : ℂ) w.1) * (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1) * (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1) = Complex.exp g := by
  first
  | exact @GlobalTheory.RSNonvan.fourProd_eq_exp
  | exact GlobalTheory.RSNonvan.fourProd_eq_exp
  | (intros; apply GlobalTheory.RSNonvan.fourProd_eq_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSetup
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeriesTie.Complex

variable {D : D7}

def castG (Pg : Finset (Pl D.host.E)) {r r' : ℕ} (h : r' = r) : G0 Pg r ≃* G0 Pg r' :=
  MulEquiv.piCongrRight fun P => Units.mapEquiv
    (Matrix.reindexAlgEquiv (kP P.1) (kP P.1) (finCongr h.symm)).toMulEquiv

def levOf {G H : Type} [Group G] [Group H] (eG : G ≃* H) (U : Subgroup G) (χ : U →* ℂˣ) : Subgroup H × (U.map eG.toMonoidHom →* ℂˣ) :=
  (U.map eG.toMonoidHom, χ.comp (eG.subgroupMap U).symm.toMonoidHom)

theorem levOf_mem {G H : Type} [Group G] [Group H] (eG : G ≃* H) (U : Subgroup G) (χ : U →* ℂˣ) (g : G) :
    eG g ∈ (levOf eG U χ).1 ↔ g ∈ U := by
  simp [levOf, Subgroup.mem_map]

theorem levOf_chi {G H : Type} [Group G] [Group H] (eG : G ≃* H) (U : Subgroup G) (χ : U →* ℂˣ) (u : U)
    (hu : eG u ∈ (levOf eG U χ).1) : (levOf eG U χ).2 ⟨eG u, hu⟩ = χ u := by
  change χ ((eG.subgroupMap U).symm ⟨eG u, hu⟩) = χ u
  congr 1
  apply (eG.subgroupMap U).injective
  rw [MulEquiv.apply_symm_apply]
  rfl

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def eGc (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (j : Fin D.R.m) : G0g D.nd ≃* G0 Rl.Pg (Wc D j).rank :=
  cG.symm.trans (castG Rl.Pg (FWT.rank_Wc j))

end GlobalTheory.SeriesTie.Complex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVectorEqUnitMulCentralTranslateLiftVector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FlatLift

theorem unitOff_inv_mul {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v)⁻¹ := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨inv_ne_zero (mul_ne_zero hu0 hv0), n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by
      rw [pow_add, mul_inv]; ring
    rw [e]; exact hn2.mul hm2
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹⁻¹ = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by
      rw [inv_inv, pow_add]; ring
    rw [e]; exact hn1.mul hm1

theorem exists_unif (E : Type) [Field E] [NumberField E] (Q : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) :
    ∃ ϖ : 𝓞 E, ϖ ≠ 0 ∧ ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2 := by
  have hx : ∀ PP : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ∃ x ∈ PP.asIdeal, x ∉ PP.asIdeal ^ 2 := fun PP => by
    simpa using Ideal.exists_mem_pow_notMem_pow_succ PP.asIdeal PP.ne_bot PP.isPrime.ne_top 1
  choose x hx1 hx2 using hx
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Q)
    (fun PP => PP.asIdeal) (fun _ => 2) (fun PP _ => Ideal.prime_of_isPrime PP.ne_bot PP.isPrime)
    (fun PP _ PP' _ h e => h (IsDedekindDomain.HeightOneSpectrum.ext e)) (fun PP => x PP.1)
  have key : ∀ PP ∈ Q, y ∈ PP.asIdeal ∧ y ∉ PP.asIdeal ^ 2 := fun PP hPP => by
    have h1 := hy PP hPP
    have hle : PP.asIdeal ^ 2 ≤ PP.asIdeal := Ideal.pow_le_self (by norm_num)
    refine ⟨?_, fun h => hx2 PP ?_⟩
    · have := PP.asIdeal.add_mem (hle h1) (hx1 PP)
      simpa using this
    · have := (PP.asIdeal ^ 2).sub_mem h h1
      simpa using this
  by_cases hQ : Q.Nonempty
  · obtain ⟨PP, hPP⟩ := hQ
    refine ⟨y, fun h0 => (key PP hPP).2 (h0 ▸ Ideal.zero_mem _), key⟩
  · refine ⟨1, one_ne_zero, fun PP hPP => absurd ⟨PP, hPP⟩ hQ⟩

theorem flat_eq_unit_smul_om : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ f, IsFlatVec R i t f → ∃ (z : GA D (Vc D i)) (c : ℂ), IsCentAt i (R.Q t) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime R t) c ∧ f = c • R.ωP i t (z, 1) (R.vP i t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t hV f hf
  obtain ⟨eg, eQ, fg, heg, heQ, hfg, hf⟩ := hf
  obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_unif D.host.E (R.Q t)
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  obtain ⟨z, hz, hzm⟩ := GlobalTheory.CentScal.exists_isCentAt_scalar D i (R.Q t) eQ heQ (ϖ : D.host.E) hϖE
  obtain ⟨κ, hκ, hact⟩ := _root_.GlobalTheory.TupDil.om_model_eq_unit_smul_dilate D G Pl0 T0 A Ks R F hC hQG i t hV eg eQ fg heg heQ hfg ϖ hϖ0 hϖ z hzm
  obtain ⟨Gc, hG, hSB, hvP⟩ := _root_.GlobalTheory.LiftFlatModel.lift_eq_model_flat D G Pl0 T0 A Ks R F hC hQG i t hV eg eQ fg heg heQ hfg ϖ hϖ0 hϖ
  obtain ⟨Tm, hTm⟩ := hf.1
  have hfT := hf.2 Tm hTm
  have hvT := hvP Tm hTm
  refine ⟨z, (κ * Gc)⁻¹, hz, unitOff_inv_mul hκ hG, ?_⟩
  have hne : κ * Gc ≠ 0 := mul_ne_zero hκ.1 hG.1
  have hcomp : ∀ x : WO (Vc D i) (Wc D i),
      ((x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w).map fun w => incA D (ϖ : D.host.E) * w) = x := by
    intro x
    ext a b
    simp only [Matrix.map_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖE, map_one, one_mul]
  rw [hvT, hact Tm hTm _ hSB]
  simp only [hcomp]
  have hsm : (fun x : WO (Vc D i) (Wc D i) => Gc * (if IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0)) =
      Gc • (fun x : WO (Vc D i) (Wc D i) => if IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) := rfl
  rw [hsm, map_smul, ← hfT, smul_smul, smul_smul, mul_assoc (κ * Gc)⁻¹, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.FlatLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftFormAtEvaluationVectorEqRealisationLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceLift

theorem eMt_fix (D : D7) (μ : D.what₂.Tup) (j : ℕ) (x : D.what₂.MtL μ j) (hx : x ∈ Idx.TjV D μ j) :
    D.what₂.eMt μ j (D.what₂.jMt μ j x) = D.what₂.jMt μ j x := by
  have hL : ∀ y ∈ Idx.TjL D μ j, D.what₂.eMt μ j (D.what₂.jMt μ j y) = D.what₂.jMt μ j y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, -, hv⟩ := hz
      rw [← hv]
      exact LinearMap.congr_fun (D.what₂.eMt_idem μ j) _
    | zero => rw [map_zero, map_zero]
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | smul c a _ ha => rw [Idx.smul_def, LinearMap.map_smulₛₗ, map_smul, ha]
  induction hx using Submodule.span_induction with
  | mem z hz => exact hL z hz
  | zero => rw [map_zero, map_zero]
  | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, map_smul, ha]

variable {D : D7} {X : RealSide D} {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0)

theorem extV_formOf_eMt (j : Fin D.R.m) (t : X.T) (hμ : Used0 D (Y.tup t)) (c) :
    X.R.toRealDat.extV j (Y.tupT (Y.tup t)) (formOf Y hμ j (D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c))) =
      X.R.toRealDat.extV j t (X.R.jV j t (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.P0 X.F.ψ0 j t c)) :=
  (extV_formOf Y hμ j _).trans (Y.mtRead j t hμ c)

theorem idem_fix (hH : GlobalTheory.Mem.R3.Holds X.R X.F) (j : Fin D.R.m) (t : X.T) (hμ : Used0 D (Y.tup t)) (c)
    (hc : D.what₂.eMt (Y.tup t) (j.1 + 1) (D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c)) =
      D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c)) :
    X.R.jV j t (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.P0 X.F.ψ0 j t c) =
      X.R.jV j t (∑ g, (idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.P0 X.F.ψ0 j t c)) := by
  have e2 := GlobalTheory.CenTranslate.liftForm_lvlOp (A3 := X.A3) (F := X.F.lv2) hH.ok.ok2 j t (idemOf X.A3.A.X)
    (fun b => idemOf_central X.A3.A.X hH.ok.ok2.irr b) c
  have e1 := (Y.formsL j t).op_eq c
  have e3 : D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c) =
      D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t ((lE D X.A3.A X.F.P0 X.F.ψ0 j t).mulVec c)) := hc.symm.trans e1
  refine Y.hinj j t ?_
  refine (Y.mtRead j t hμ c).symm.trans ?_
  refine (congrArg (fun y => (Y.IL.jMt (Y.tup t) hμ j y).1) e3).trans ?_
  refine (Y.mtRead j t hμ _).trans ?_
  exact congrArg (fun v => X.R.toRealDat.extV j t (X.R.jV j t v)) e2

theorem isAlgV_self (j : Fin D.R.m) (t : X.T) (u : (X.A3.A.fam.L j t).S.Forms)
    (hu : X.R.jV j t u = X.R.jV j t (∑ g, (idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g u))
    (κ : X.Γ → (GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.levV X.R.toRealDat j t).Q) (hκ : ∀ g, GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.IsLiftV X.R.toRealDat j t g (κ g)) :
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.IsAlgV X.R.toRealDat j t (RealDat.eC (A := X.A3.A) (sg0 D X.A3.A)) κ (X.R.jV j t u) (X.R.jV j t u) := by
  have hs : sg0 D X.A3.A = D.what₂.embLL := sgAt_mk _ X.R.hv0
  refine (congrArg (X.R.HV j t).e hu).trans ?_
  have e3 := map_sum (X.R.jV j t) (fun g => (idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g u) Finset.univ
  have e4 := map_sum (X.R.HV j t).e (fun g => (X.R.jV j t) ((idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g u)) Finset.univ
  refine ((congrArg (X.R.HV j t).e e3).trans e4).trans ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  have e5 := map_smulₛₗ (X.R.jV j t) ((idemOf X.A3.A.X).coeff g) ((X.A3.A.fam.L j t).r g u)
  have e6 := LinearMap.map_smul (X.R.HV j t).e (D.what₂.embLL ((idemOf X.A3.A.X).coeff g)) (X.R.jV j t ((X.A3.A.fam.L j t).r g u))
  refine ((congrArg (X.R.HV j t).e e5).trans e6).trans ?_
  have hT := GlobalTheory.RationalFormsAction.isTranslate_act_V X.R.toRealDat X.char.grp.red_L X.char.models.jV j t g u
  have e7 : (X.R.HV j t).e (X.R.jV j t ((X.A3.A.fam.L j t).r g u)) =
      Bridge.g0Act (GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.levV X.R.toRealDat j t).ch (κ g) ((X.R.HV j t).e (X.R.jV j t u)) :=
    funext fun h => hT.2 (κ g) (hκ g) h
  have e8 : D.what₂.embLL ((idemOf X.A3.A.X).coeff g) = RealDat.eC (A := X.A3.A) (sg0 D X.A3.A) g := by
    rw [RealDat.eC, hs]
  rw [e7, e8]

theorem lift_read (hP : GlobalTheory.Mem.R3.Pins X.R X.F X.cG) (hH : GlobalTheory.Mem.R3.Holds X.R X.F) (j : Fin D.R.m) (μ : D.what₂.Tup) (hμ : Used0 D μ)
    (x : D.what₂.MtL μ (j.1 + 1)) (hx : x ∈ Idx.TjV D μ (j.1 + 1)) (v : (X.R.MW j (sg0 D X.A3.A)).Vec) :
    (X.R.HW j (sg0 D X.A3.A)).e (Y.mj.eW j (D.what₂.thetaP μ (j.1 + 1) (D.what₂.jMt μ (j.1 + 1) x))) v =
      X.R.thF j (Y.tupT μ) (formOf Y hμ j (D.what₂.jMt μ (j.1 + 1) x)) v := by
  obtain ⟨t, rfl⟩ : ∃ t, Y.tup t = μ := ⟨_, Y.tupTie μ hμ⟩
  obtain ⟨c, rfl⟩ := (Y.eMt j t).surjective x
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  choose κ hκ using GlobalTheory.ProjLiftLaw.liftV_exists_core hC j t
  have h1 := GlobalTheory.Mem.ThetaRead3.thetaP_read_plain D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.F X.cG X0 Y hP hH j t c
  have h2 := GlobalTheory.ProjLiftLaw.thG_apply_eq hC j t κ hκ _ _
    (isAlgV_self j t _ (idem_fix Y hH j t hμ c (eMt_fix D _ _ _ hx)) κ hκ) v
  have h3 := GlobalTheory.Mem.ThetaRead3.thF_congr X.R.toRealDat Y.hinj j t (Y.tupT (Y.tup t)) (Y.tupT_tup t) _ _ (extV_formOf_eMt Y j t hμ c)
  exact ((congrArg (fun y => (X.R.HW j (sg0 D X.A3.A)).e y v) h1).trans h2).trans (congrArg (fun U => U v) h3).symm

theorem lift_read_at : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1),
  (X.R.HW j (sg0 D X.A3.A)).e (Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) (X.geo.v₀ j (sg0 D X.A3.A)) =
    X.R.thF j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) (X.geo.v₀ j (sg0 D X.A3.A)) :=
  fun _ _ _ Y _ _ _ _ _ j H x hx => lift_read Y H.pins H.intersectionNumber_baseChange j _ (used_of_tw H.tw) x hx _

end GlobalTheory.PlaceLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergSameDegreeMeromorphicContinuationStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_sameDegree_meromorphic_continuation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), IsGood T → UnrOutside T σ → UnrOutside T σ' → ∃ F : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ F (x : ℂ)) ∧ (σ ≠ σ' → F 1 = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => lfac σ σ' (x : ℂ) w.1) (F x / ((x : ℂ) - 1)) := by
  first
  | exact @GlobalTheory.RSNonvan.samedeg_continuation
  | exact GlobalTheory.RSNonvan.samedeg_continuation
  | (intros; apply GlobalTheory.RSNonvan.samedeg_continuation <;> assumption)
end

