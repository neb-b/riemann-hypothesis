module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0912
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0913
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondField
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormsBaseChangeSecondFieldNeBot
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseChangeNonzero

theorem cuspOver_ne_bot : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T0 : Type) (A : FamIn D.what₂.LL Γ Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ (j : Fin D.R.m), OMPins T R κ v₀ O j → OneMapRow0 T R κ v₀ O j → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥ → GlobalTheory.OneMapAll.cuspOver (O j) (κ j) ≠ ⊥ := by
  intro D Γ _ _ Pl0 T0 A T _ R F κ v₀ O hnV hC hFW hIo j hP hrow hne
  obtain ⟨tie⟩ := hFW
  have hT : LawsJ T := tie.laws
  have hj : InR D ((j : ℕ) + 1) := ⟨Nat.le_add_left _ _, j.2⟩
  have hn : (κ j).n = (Vc D j).rank :=
    (tie.kap j (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) j.2).symm
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hsec := cusp_le_sec _ _ _ _ _ hf
  have hBC := GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ (O j).hle _ (T.U ((j : ℕ) + 1)) _ _ f hsec
  have hmem : GlobalTheory.FieldBC.rulBC (O j).hle f ∈ GlobalTheory.OneMapAll.cuspOver (O j) (κ j) := by
    unfold GlobalTheory.OneMapAll.cuspOver
    rw [← hn]
    exact hBC.2.2 hf
  intro hbot
  rw [hbot, Submodule.mem_bot] at hmem
  obtain ⟨σ', hσ'⟩ := GlobalTheory.FieldBC.exists_emb_ext (O j).hle T.toCore.σ₀
  have hrd := hBC.1 σ'
  rw [hmem, map_zero] at hrd
  have hgood : GoodEmb T.Q.c (σ'.comp (incF T.Q.c (O j).c' (O j).hle)) := hσ' ▸ T.toCore.good_σ₀
  have hU : IsUnf (T.U ((j : ℕ) + 1) (σ'.comp (incF T.Q.c (O j).c' (O j).hle))) := hT.unf _ hj _ hgood
  refine hf0 ((GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ _ T.Q.c _ _
    (Formalism.L2.PjFree.Unf.ofPj (T.U ((j : ℕ) + 1) (σ'.comp (incF T.Q.c (O j).c' (O j).hle))))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU) _ _).2 f hsec (fun k x _ => ?_))
  show rdU (T.U ((j : ℕ) + 1) (σ'.comp (incF T.Q.c (O j).c' (O j).hle))) f k x = 0
  exact (congrFun (congrFun hrd k) x).symm

end GlobalTheory.BaseChangeNonzero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DictionaryCharacterRightInvariantCoreLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MuLevelMul


set_option maxHeartbeats 1000000 in
theorem mu_mul_level : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, T.mu ((j : ℕ) + 1) T.σ₀ (g * k) = T.mu ((j : ℕ) + 1) T.σ₀ g := by
  intro D Γ _ _ Pl0 I0 T0 A3 _ T _ Rl cG S YS F κ v₀ O hJ hC _ hT _ _ _ _ _ _ j hV _ _ k hk g
  have hj := inR j
  have hσ : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  obtain ⟨τ, hτ⟩ := GlobalTheory.MuLevel.exists_ext (L := D.what₂.LL) T.σ₀
  obtain ⟨hf, hk'⟩ := (hJ.levelK _ hj _ hσ k).1 hk
  have hodd : Odd (D.host.g 0 * D.host.g 1) := hJ.pins.2.1.1 ▸ T.Q.l.odd
  obtain ⟨y, hy, hu, hc⟩ := GlobalTheory.MuLevel.exists_root_of_level _ _ hodd k hf hk'
  have hm := Rl.C.isMu0 j
  have h1 : Rl.mu0 ((j : ℕ) + 1) y = 1 := by
    refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D _ _ (hC.lev.mu0 j) hm.tame _
      (fun P hP => hm.unr P fun a ha => hP ?_) y hu hc
    rw [Nat.cast_mul]
    fin_cases a
    · exact Ideal.mul_mem_right _ _ ha
    · exact Ideal.mul_mem_left _ _ ha
  have hg : GoodEmb T.Q.c (τ.comp (algebraMap T.Q.c.F D.what₂.LL)) := hτ ▸ hσ
  obtain ⟨z, hz1, hz2⟩ := (hT.chiR j τ hg).2.2.2.1 y hu.1
  have h2 : algebraMap T.Q.c.F D.what₂.LL z = 1 :=
    D.what₂.embLL.injective (by rw [← hz1, h1, map_one, Circle.coe_one])
  have hχ : T.chiW ((j : ℕ) + 1) T.σ₀ y = 1 := by
    rw [hτ] at hz2
    apply Subtype.ext
    rw [hz2, h2, map_one, Circle.coe_one]
  have hMV := hJ.muVal _ hj _ hσ
  obtain ⟨x, hx⟩ := hMV.1 g
  have hxy : IsDetRoot _ (g * k) (x * y) := (GlobalTheory.Member.isDetRoot_laws D _).2.2.2 g k x y hx hy
  rw [hMV.2 _ _ hxy, hMV.2 g x hx, map_mul, hχ, mul_one]

end GlobalTheory.MuLevelMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexLinearExtensionCoefficientMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExtCoeff

open TensorProduct

theorem exists_ext_map {K' : Type} [Field K'] (σ' : K' →+* ℂ) {X : Type} (V : Submodule K' (MvPolynomial X K'))
    (V' : Submodule ℂ (MvPolynomial X ℂ)) {W : Type*} [AddCommGroup W] [Module ℂ W] (c0 : V →ₛₗ[σ'] W) :
    ∃ c : V' →ₗ[ℂ] W, ∀ (v : V) (v' : V'), (v' : MvPolynomial X ℂ) = MvPolynomial.map σ' (v : MvPolynomial X K') → c v' = c0 v := by
  letI : Algebra K' ℂ := σ'.toAlgebra
  letI : Module K' W := Module.compHom W σ'
  haveI : IsScalarTower K' ℂ W := ⟨fun k a w => by
    show (σ' k * a) • w = σ' k • a • w
    rw [mul_smul]⟩
  let c0l : V →ₗ[K'] W := { toFun := c0, map_add' := c0.map_add, map_smul' := fun k v => c0.map_smulₛₗ k v }
  let F : ℂ ⊗[K'] V →ₗ[ℂ] W := c0l.liftBaseChange ℂ
  let ψ : ℂ ⊗[K'] V →ₗ[ℂ] MvPolynomial X ℂ :=
    (MvPolynomial.algebraTensorAlgEquiv K' ℂ).toLinearMap.comp (V.subtype.baseChange ℂ)
  have hψ1 : ∀ v : V, ψ (1 ⊗ₜ v) = MvPolynomial.map σ' (v : MvPolynomial X K') := by
    intro v
    simp [ψ, MvPolynomial.algebraTensorAlgEquiv_tmul]
    rfl
  have hinj : Function.Injective ψ := by
    refine (MvPolynomial.algebraTensorAlgEquiv K' ℂ).injective.comp ?_
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ) V.subtype V.injective_subtype
  let e := LinearEquiv.ofInjective ψ hinj
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (F.comp e.symm.toLinearMap)
  refine ⟨g.comp V'.subtype, fun v v' h => ?_⟩
  have hmem : (v' : MvPolynomial X ℂ) ∈ LinearMap.range ψ := ⟨1 ⊗ₜ v, (hψ1 v).trans h.symm⟩
  have key : g (v' : MvPolynomial X ℂ) = F (e.symm ⟨_, hmem⟩) := LinearMap.congr_fun hg ⟨_, hmem⟩
  have he : e.symm ⟨_, hmem⟩ = 1 ⊗ₜ v := by
    rw [LinearEquiv.symm_apply_eq]
    ext
    simp [e, LinearEquiv.ofInjective_apply, hψ1, h]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, key, he, F, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

theorem exists_extC : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T1 : Type) (A : FamIn D.what₂.LL G Pl0 T1 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (j : Fin D.R.m) (Tp : Type) (tup : Tp → T1) (O : OMDat T.toCore R j Tp tup), ∃ c : VsV D j ℂ →ₗ[ℂ] (R.cV j).W, ExtC R j (inC O.c') O.c0' c := by
  intro D G _ _ Pl0 T1 A T _ R j Tp tup O
  obtain ⟨c, hc⟩ := exists_ext_map (inC O.c') (VV O.c'.F (lamV D j)) (VV ℂ (lamV D j)) O.c0'
  exact ⟨c, fun v v' h => hc v v' h⟩

end GlobalTheory.ExtCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftDatumThetaSeriesRightInvariantCoreLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.SeriesTie.LevelInv

theorem cast_mul {D : D7} {V W : HSp D} (e : V = W) (a b : GA D V) :
    cast (congrArg (GA D) e) (a * b) = cast (congrArg (GA D) e) a * cast (congrArg (GA D) e) b := by
  subst e
  rfl

theorem apply_eq_castDict {D : D7} {V W : HSp D} (e : V = W) (φ : GA D V → ℂ) (x : GA D V) :
    φ x = castDict e φ (cast (congrArg (GA D) e) x) := by
  subst e
  rfl

theorem thetaKO_mul_right {D : D7} {V W : HSp D} (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (h : GA D V)
    (g κ : GA D W) (f : WO V W → ℂ) : thetaKO om h (g * κ) f = thetaKO om h g (om (1, κ) f) := by
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem ser_right_inv_levelK : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → ∀ (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ) (h : GA D (Vc D j)), h ∈ GfC (Vc D j) → ∀ (w : (Rl.cV j).W) (a : ℂ) (φ : GA D (T.V ((j : ℕ) + 1) T.σ₀) → ℂ), castDict hV φ = (fun g => a * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h w g) → ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, φ (g * k) = φ g := by
  intro D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp
    u h hh w a φ hφ k hk g
  have hpb : T.pb = Rl.toRealDat.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore Rl.toRealDat hT.toLawsM hcore.lev (hpins.2.tuple ()).half
  set k' : GA D (Wc D j) := cast (congrArg (GA D) hV) k with hk'def
  have hkk : cast (congrArg (GA D) hV.symm) k' = k := by rw [hk'def]; simp
  have hlift : Formalism.IndefR.Lev.IsLevelLift (Wc D j) (Rl.toRealDat.βW j) (Rl.toRealDat.datWp j Rl.toRealDat.triv) 1 k' :=
    (_root_.GlobalTheory.LiftLevel.isLift_one_iff_mem_level T Rl.toRealDat κ v₀ hcore.lev hti hpb j T.σ₀ T.toCore.good_σ₀ hV k').2 (by rw [hkk]; exact hk)
  have hv : Rl.toRealDat.ωP j A3.A.μ0 (1, k') (Rl.toRealDat.vP j A3.A.μ0) = (1 : ℂ) • Rl.toRealDat.vP j A3.A.μ0 := by
    have e := _root_.GlobalTheory.VecInv.omega_lifts_vP Rl.toRealDat hcore.lev hcore.models.inf hcore.thP.ωP hcore.thP.vP j A3.A.μ0 1 1 k'
      (GlobalTheory.RawLift.LevelFix.realDatum_identity_lifts_identity Rl.toRealDat j A3.A.μ0) hlift
    rw [e, GlobalTheory.RawLift.LevelFix.levChi_flag_one Rl.toRealDat j A3.A.μ0, inv_one]
  have hP : ∀ P, Rl.toRealDat.ωP j A3.A.μ0 (1, k') (Rl.toRealDat.ptP j A3.A.μ0 P) = Rl.toRealDat.ptP j A3.A.μ0 P := by
    intro P
    have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite Rl.toRealDat.ψ Rl.toRealDat.θ (Vc D j) (Wc D j) _ _
      (Rl.toRealDat.ωP j A3.A.μ0) hcore.models.inf (hcore.thP.ωP j A3.A.μ0) _ _ _ _ _ (hcore.thP.pt_theta j A3.A.μ0) 1
      (Subgroup.one_mem _) k' hlift.1 1 hv P
    exact this.trans (one_smul ℂ _)
  have hser : ∀ x, ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h w (x * k') = ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h w x := by
    intro x
    rw [ser_vP, ser_vP, thetaKO_mul_right, hP]
  have e1 : φ (g * k) = castDict hV φ (cast (congrArg (GA D) hV) g * k') := by
    exact (apply_eq_castDict hV φ (g * k)).trans (congrArg (castDict hV φ) (cast_mul hV g k))
  have e2 : φ g = castDict hV φ (cast (congrArg (GA D) hV) g) := apply_eq_castDict hV φ g
  rw [e1, e2, hφ]
  exact congrArg (fun z => a * z) (hser _)

end GlobalTheory.SeriesTie.LevelInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsOfReadingBoundedCuspidalHolomorphic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspOfReading


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem mem_cuspA_of_rdU_mem_holSub0 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ w : WeightFamilies.Wt D j, w.LastPos → 8 * D.R.f * D.R.r + 4 ≤ w.n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n, rdU (T.U j T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) → f ∈ T.cuspA j (wtA w) w.n := by
  intro D T h j hj w hw hn f hf hfh
  classical
  set S := T.cuspA j (wtA w) w.n with hS
  haveI : FiniteDimensional T.Q.c.F S := h.toLawsM.cuspFD j hj (wtA w) w.n (dom_wtA w)
  haveI : Module.Free T.Q.c.F S := Module.Free.of_divisionRing _ _
  let b := Module.finBasis T.Q.c.F S
  let b' : Fin (Module.finrank T.Q.c.F S) → T.R j := fun i => (b i : T.R j)
  have hb'S : Submodule.span T.Q.c.F (Set.range b') ≤ S := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (b i).2
  have hSb' : S ≤ Submodule.span T.Q.c.F (Set.range b') := by
    intro x hx
    have h1 : (⟨x, hx⟩ : S) ∈ Submodule.span T.Q.c.F (Set.range b) := by rw [b.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := S.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  by_contra hfS
  have hli : LinearIndependent T.Q.c.F (Fin.cons f b' : Fin (Module.finrank T.Q.c.F S + 1) → T.R j) := by
    rw [linearIndependent_finCons]
    exact ⟨b.linearIndependent.map' S.subtype (Submodule.ker_subtype _), fun hm => hfS (hb'S hm)⟩
  have hsec : ∀ i, (Fin.cons f b' : Fin (Module.finrank T.Q.c.F S + 1) → T.R j) i ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := by
    intro i
    refine Fin.cases hf (fun i => ?_) i
    exact cusp_le_sec _ _ _ _ _ (b i).2
  have hC := GlobalTheory.rdIndep_of_lawsM D T.toCore h.toLawsM j hj T.σ₀ T.toCore.good_σ₀ (wtA w) w.n (dom_wtA w) _ _ hsec hli
  have hC' : LinearIndependent ℂ (Fin.cons (rdU (T.U j T.σ₀) f) (fun i => rdU (T.U j T.σ₀) (b' i)) :
      Fin (Module.finrank T.Q.c.F S + 1) → _) := by
    convert hC using 1
    funext i
    refine Fin.cases rfl (fun i => rfl) i
  rw [linearIndependent_finCons] at hC'
  apply hC'.2
  have hspan := GlobalTheory.OntoCore.holSub0_le_span_cuspA D T h j hj w hw hn T.σ₀ T.toCore.good_σ₀ hfh
  refine (Submodule.span_le.2 ?_) hspan
  rintro _ ⟨x, hx, rfl⟩
  have hx' := hSb' hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

end GlobalTheory.CuspOfReading
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlaceResidueCharactersValuesMemSmallField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeChar

theorem chi_mem_smallField : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 ↥T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m), ∀ PP ∈ Rl.Pg, ∀ x : (kP PP)ˣ, ((Rl.chi ((j : ℕ) + 1) PP x : ℂˣ) : ℂ) ∈ (embLL0 D).fieldRange := by
  classical
  intro D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG S YS F _ hCore _ _ hroot j PP hPP x
  obtain ⟨k, hk⟩ := (hCore.lev.Pg PP).1 hPP
  have hov := Rl.C.P.overP hk
  obtain ⟨hn, -, -⟩ := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) PP hov
  have hcard : Nat.card (kP PP) = D.host.g k := by
    rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (D.host.g_prime k).ne_zero)
  have : Fintype (kP PP) := Fintype.ofFinite _
  have hu : Nat.card (kP PP)ˣ = D.host.g k - 1 := by
    rw [← hcard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have : NeZero (Nat.card (kP PP)ˣ) := ⟨Nat.card_pos.ne'⟩
  have h1 : ((Rl.chi ((j : ℕ) + 1) PP x : ℂˣ) : ℂ) ^ Nat.card (kP PP)ˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  rw [hu] at h1
  refine hroot k _ ?_
  rw [mul_comm, pow_mul, h1, one_pow]

end GlobalTheory.TypeChar
end

