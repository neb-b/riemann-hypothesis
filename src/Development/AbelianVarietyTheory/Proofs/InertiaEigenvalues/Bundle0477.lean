module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0271
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonOfWachBasis
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.NygaardExtension

theorem map_incl_smul {O R R' M : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra O R]
    [Algebra O R'] [AddCommGroup M] [Module O M] (f : R →ₐ[O] R') (a : R) (y : R ⊗[O] M) :
    TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) (a • y) =
      f a • TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [smul_add, map_add (f := _), hx, hx']
  | tmul r u => simp [TensorProduct.smul_tmul']

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem TAinf_smul (T : LocLat G Qp LL O) (a : RA) {z : TW RW T} (hz : z ∈ TAinf inclR T) :
    inclR a • z ∈ TAinf inclR T := by
  obtain ⟨y, rfl⟩ := hz
  exact ⟨a • y, map_incl_smul inclR a y⟩

theorem NAinf_smul (T : LocLat G Qp LL O) (a : RA) {z : TW RW T} (hz : z ∈ NAinf W E T) :
    inclR a • z ∈ NAinf W E T := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a', x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨a * a', x, hx, ?_⟩
    rw [smul_smul, map_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ o hx

theorem p5inf_of_sand (T : LocLat G Qp LL O) (c : RW) (m : ℕ) (hc : c = inclR (E.io W.X) ^ m)
    (h1 : ∀ x ∈ W.N T, ∃ y : TW RA T, TWincl inclR T y =
        TensorProduct.map (LinearMap.mulLeft O c) LinearMap.id (E.jD T x))
    (h2 : ∀ t : ↥T.L.T, (c ⊗ₜ[O] t : TW RW T) ∈ Submodule.span O {z : TW RW T | ∃ a : RA, ∃ y ∈ W.N T,
        z = TensorProduct.map (LinearMap.mulLeft O (inclR a)) LinearMap.id (E.jD T y)}) :
    wachInfiniteLevelJumpBound W E T m m := by
  subst hc
  simp only [GlobalTheory.NL.SandArb.map_mulLeft] at h1 h2
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨y, rfl⟩ := hz
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x x' hx hx' => rw [map_add (f := _), smul_add]; exact add_mem hx hx'
    | tmul r t =>
      have e : inclR (E.io W.X) ^ m • TensorProduct.map inclR.toLinearMap LinearMap.id (r ⊗ₜ[O] t) =
          inclR r • ((inclR (E.io W.X) ^ m) ⊗ₜ[O] t : TW RW T) := by
        simp [TensorProduct.smul_tmul', mul_comm]
      rw [e]
      exact NAinf_smul E T r (h2 t)
  · induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, x, hx, rfl⟩ := hz
      obtain ⟨y, hy⟩ := h1 x hx
      rw [smul_comm]
      exact TAinf_smul T a ⟨y, hy⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ o hx

theorem etale_comparison_of_wach_basis (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {r : ℕ}
    (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T))
    (hφ : ∀ y : TW RW T, TWmap φR T y = y ↔ ∃ t : ↥T.L.T, y = (1 : RW) ⊗ₜ[O] t) : p1et W E T := by
  obtain ⟨c, hc⟩ := GlobalTheory.WachTensor.exists_basis_jD E T ((W.N_base T hT).basis b)
  have hc' : ∀ j, c j = E.jD T (b j : W.DD T) := fun j => by
    rw [hc, IsBaseChange.basis_apply b (W.N_base T hT) j]; rfl
  refine ⟨⟨r, fun j => (b j : W.DD T), fun j => (b j).2, fun x hx => ?_, fun y => ?_⟩, hφ⟩
  · have key : ∀ a : Fin r → LetA O n, x = ∑ j, a j • (b j : W.DD T) ↔
        (⟨x, hx⟩ : ↥(W.N T)) = ∑ j, a j • b j := by
      intro a
      rw [Subtype.ext_iff]
      simp
    refine ⟨fun j => b.repr ⟨x, hx⟩ j, (key _).2 (b.sum_repr ⟨x, hx⟩).symm, fun a ha => ?_⟩
    rw [(key a).1 ha, b.repr_sum_self]
  · refine ⟨fun j => c.repr y j, ?_, fun a ha => ?_⟩
    · show y = _
      simp only [← hc']
      exact (c.sum_repr y).symm
    · have ha' : y = ∑ j, a j • c j := by simpa only [← hc'] using ha
      rw [ha', c.repr_sum_self]

end Generic


set_option maxHeartbeats 1600000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    p1eL D.loc D.locA HW F := by
  intro D HW F l _ K s LL h T hT
  refine ⟨?_, ?_⟩
  · obtain ⟨b⟩ := N_basis D HW F l K s LL h T hT
    exact etale_comparison_of_wach_basis _ T hT b (GlobalTheory.WittTensorFixed.main l K LL T).2.1
  · obtain ⟨m, h1, h2⟩ := GlobalTheory.NL.SandArb.sandwich D HW F l K s LL h T hT
    exact ⟨m, p5inf_of_sand _ T _ m rfl h1 h2⟩

end GlobalTheory.NL.NygaardExtension
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgEquivExtendingWittTiltFrobenius
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.TameFrob

theorem exists_algEquiv_iotaO_sigma : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a], ∃ Φ : Om l ≃ₐ[ℚ_[l]] Om l,
    ∀ w : Wq l a, Φ (GlobalTheory.TameFrob.iotaO l a w) = GlobalTheory.TameFrob.iotaO l a (sigma l a w) := by
  intro l _ a _
  letI : Algebra (Wq l a) ↥(Kunr l a) := algK l a
  letI : IsFractionRing (Wq l a) ↥(Kunr l a) := by
    refine (isLocalization_iff (nonZeroDivisors (Wq l a)) ↥(Kunr l a)).2 ⟨?_, ?_, ?_⟩
    · intro s
      refine IsUnit.mk0 _ fun h => nonZeroDivisors.coe_ne_zero s (iota_injective l a ?_)
      rw [← algebraMap_K, h, map_zero]
    · intro y
      obtain ⟨w, s, hs, h⟩ := exists_frac l a y
      exact ⟨⟨w, ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩⟩, Subtype.ext (by simpa [algebraMap_K] using h)⟩
    · intro x y h
      exact ⟨1, by rw [iota_injective l a h]⟩
  let fr : ↥(Kunr l a) →+* Om l :=
    IsFractionRing.lift (g := (iotaO l a).comp (sigma l a).toRingEquiv.toRingHom)
      ((iotaO_injective l a).comp (sigma l a).injective)
  have hfr (w : Wq l a) : fr (iota l a w) = iotaO l a (sigma l a w) :=
    IsFractionRing.lift_algebraMap _ w
  let f : ↥(Kunr l a) →ₐ[ℚ_[l]] Om l := {
    toRingHom := fr
    commutes' := by
      intro r
      have h : fr.comp (algebraMap ℚ_[l] ↥(Kunr l a)) = algebraMap ℚ_[l] (Om l) := by
        refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext fun u => ?_)
        have h1 : algebraMap ℚ_[l] ↥(Kunr l a) (algebraMap ℤ_[l] ℚ_[l] u) =
            iota l a (algebraMap ℤ_[l] (Wq l a) u) :=
          Subtype.ext (by rw [coe_iota, iotaO_algebraMap]; rfl)
        simp only [RingHom.comp_apply]
        rw [h1, hfr, AlgEquiv.commutes, iotaO_algebraMap]
        rfl
      exact RingHom.congr_fun h r }
  let φ : Om l →ₐ[ℚ_[l]] Om l := f.liftNormal (Om l)
  refine ⟨AlgEquiv.ofBijective φ φ.normal_bijective, fun w => ?_⟩
  have h := AlgHom.liftNormal_commutes f (Om l) (iota l a w)
  rw [AlgEquiv.ofBijective_apply]
  exact h.trans (hfr w)

end GlobalTheory.TameFrob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeToDeRhamMap
section
set_option synthInstance.maxHeartbeats 400000

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.BKGal.CrisTensDR

variable {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
  {LL : FinExt l} (T : QLat LL)

theorem coe_smul_lat (o : ↥(OL LL)) (x : ↥T.L.T) :
    ((o • x : ↥T.L.T) : T.V) = (o : ↥LL.1) • (x : T.V) := by
  rw [Submodule.coe_smul]
  exact (algebraMap_smul (↥LL.1) o (x : T.V)).symm

def gx (o : ↥(OL LL)) (b : Per.Bcris l) : ↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR :=
  AddMonoidHom.mk' (fun x => ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b)
    (fun x y => by
      simp only [Submodule.coe_add, smul_add, TensorProduct.add_tmul])

def gb (o : ↥(OL LL)) : Per.Bcris l →+ (↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
  AddMonoidHom.mk' (fun b => gx Td T o b)
    (fun b c => by
      ext x
      simp only [gx, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add (f := _), TensorProduct.tmul_add])

def g : ↥(OL LL) →+ Per.Bcris l →+ (↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
  AddMonoidHom.mk' (fun o => gb Td T o)
    (fun o o' => by
      ext b x
      simp only [gb, gx, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Subalgebra.coe_add, add_smul,
        TensorProduct.add_tmul])

theorem cB_smul (z : ℤ_[l]) (b : Per.Bcris l) :
    GlobalTheory.BKGal.JumpDR.cB Td (z • b) = (z : ℚ_[l]) • GlobalTheory.BKGal.JumpDR.cB Td b := by
  rw [Algebra.smul_def, map_mul, GlobalTheory.BKGal.JumpDR.cB_algebraMap, ← Algebra.smul_def]

theorem zsmul_lat (z : ℤ_[l]) (o : ↥(OL LL)) (x : ↥T.L.T) :
    (((z • o : ↥(OL LL)) : ↥LL.1) • (x : T.V)) = (z : ℚ_[l]) • ((o : ↥LL.1) • (x : T.V)) := by
  show ((z : ℚ_[l]) • (o : ↥LL.1)) • (x : T.V) = _
  exact smul_assoc _ _ _

theorem g_balanced (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.Bcris l) : g Td T (z • o) b = g Td T o (z • b) := by
  ext x
  have h1 := congrArg (fun v => v ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) (zsmul_lat T z o x)
  have h2 := congrArg (fun w => ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] w) (cB_smul Td z b)
  exact h1.trans ((TensorProduct.smul_tmul _ _ _).trans h2.symm)

def f1 : OB l ↥(OL LL) →+ (↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
  TensorProduct.liftAddHom (g Td T) (g_balanced Td T)

theorem mul_smul_lat (o o' : ↥(OL LL)) (x : ↥T.L.T) :
    (((o * o' : ↥(OL LL)) : ↥LL.1) • (x : T.V)) = (o' : ↥LL.1) • ((o • x : ↥T.L.T) : T.V) := by
  rw [coe_smul_lat, smul_smul, Subalgebra.coe_mul, mul_comm]

theorem crisTensorDRLiftFromCoeffBcris_smul_comm (o : ↥(OL LL)) :
    (f1 Td T).comp (DistribSMul.toAddMonoidHom (OB l ↥(OL LL)) o) =
      (AddMonoidHom.compHom' (DistribSMul.toAddMonoidHom (↥T.L.T) o)).comp (f1 Td T) := by
  refine AddMonoidHom.ext fun u => ?_
  induction u using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul o' b =>
    refine AddMonoidHom.ext fun x => ?_
    show g Td T (o * o') b x = g Td T o' b (o • x)
    exact congrArg (fun v => v ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) (mul_smul_lat T o o' x)
  | add u v hu hv => exact (map_add _ u v).trans ((congrArg₂ (· + ·) hu hv).trans (map_add _ u v).symm)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL), ∃ X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR, ∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b := by
  intro l _ Pl AI Td LL T
  exact ⟨TensorProduct.liftAddHom (f1 Td T) fun o u x =>
    DFunLike.congr_fun (DFunLike.congr_fun (crisTensorDRLiftFromCoeffBcris_smul_comm Td T o) u) x, fun o b x => rfl⟩

end GlobalTheory.BKGal.CrisTensDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffDeRhamPlusActionOnVTensorBdR
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.JumpDR


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem exists_odAction : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI)
    (LL : FinExt l) (T : QLat LL), ∃ A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR),
    ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR),
      A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c) := by
  intro l _ Pl AI Td LL T
  let φ : ↥(OL LL) → T.V →ₗ[ℚ_[l]] T.V := fun o =>
    { toFun := fun v => (o : ↥LL.1) • v
      map_add' := fun v w => smul_add _ v w
      map_smul' := fun q v => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (↥LL.1) q v, ← algebraMap_smul (↥LL.1) q ((o : ↥LL.1) • v), smul_smul, smul_smul,
          mul_comm] }
  let F : ↥(OL LL) → Per.BdRp l → (T.V ⊗[ℚ_[l]] Pl.R.BdR →ₗ[ℚ_[l]] T.V ⊗[ℚ_[l]] Pl.R.BdR) := fun o b =>
    TensorProduct.map (φ o) (LinearMap.mulLeft ℚ_[l] (cD Td b))
  have hF : ∀ o b v c, F o b (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (cD Td b * c) := fun o b v c => rfl
  have hb : ∀ o b b', F o (b + b') = F o b + F o b' := fun o b b' => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, map_add (f := _), add_mul, tmul_add]
  have ho : ∀ o o' b, F (o + o') b = F o b + F o' b := fun o o' b => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, Subalgebra.coe_add, add_smul, add_tmul]
  let f : ↥(OL LL) →+ Per.BdRp l →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
    AddMonoidHom.mk' (fun o => AddMonoidHom.mk' (fun b => (F o b).toAddMonoidHom)
      (fun b b' => AddMonoidHom.ext fun x => by
        show F o (b + b') x = F o b x + F o b' x
        rw [hb]; rfl))
      (fun o o' => AddMonoidHom.ext fun b => AddMonoidHom.ext fun x => by
        show F (o + o') b x = F o b x + F o' b x
        rw [ho]; rfl)
  have hbal : ∀ (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.BdRp l), f (z • o) b = f o (z • b) := by
    intro z o b
    apply AddMonoidHom.ext
    intro x
    show F (z • o) b x = F o (z • b) x
    congr 1
    apply TensorProduct.ext'
    intro v c
    rw [hF, hF, Algebra.smul_def z b, map_mul, cD_algebraMap, mul_assoc, ← Algebra.smul_def,
      ← TensorProduct.smul_tmul (R := ℚ_[l])]
    congr 1
    show ((z : ℚ_[l]) • (o : ↥LL.1)) • v = (z : ℚ_[l]) • ((o : ↥LL.1) • v)
    rw [smul_assoc]
  refine ⟨TensorProduct.liftAddHom f hbal, fun o b v c => ?_⟩
  rw [TensorProduct.liftAddHom_tmul]
  rfl

end GlobalTheory.BKGal.JumpDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousComplementFamily
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.PtCore

theorem exists_continuous_complementFamily {D : D7} (h : GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.Complement_at D) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r) :
    ∃ ρ : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i)),
      (∀ π, Continuous
        (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))) ∧
      ∀ π ∈ D.nd.Z i, GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.IsComplement D.nd i (r π) (ρ π) := by
  have key : ∀ π : D.nd.X i, ∃ ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i),
      Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) ∧
      (π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple.IsComplement D.nd i (r π) ρ) := by
    intro π
    by_cases hπ : π ∈ D.nd.Z i
    · obtain ⟨ρ, hρ⟩ := h i π hπ (r π) (hr π)
      exact ⟨ρ, hρ.cont, fun _ => hρ⟩
    · exact ⟨1, continuous_const, fun h' => absurd h' hπ⟩
  choose ρ h1 h2 using key
  exact ⟨ρ, h1, h2⟩

theorem exists_ptFam : GlobalTheory.TwSys.Cheb → ∀ (D : D7), GlobalTheory.BlockComplement.GaloisRepsCusp D →
    (∀ i, ∃ r, GoodR D.nd i r) → ∃ r ρ, PtFam D r ρ := by
  intro hC D hG hr
  choose r hr using hr
  choose ρ h1 h2 using fun i =>
    exists_continuous_complementFamily (GlobalTheory.BlockComplement.complement_at hC D hG) i (r i) (hr i)
  exact ⟨r, ρ, hr, h1, h2⟩

end GlobalTheory.PtCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCoordsUnramifiedFrobenius
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem coef_unr_continuous : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (W : GL (Fin r) ↥(MaximalUnramifiedExtension l)),
    (∀ m k : Fin r, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k = fr l m (ω k)) ∧ (∀ k, fr l r (ω k) = ω k) ∧
    ∀ (X : Type) [TopologicalSpace X] (x : X → ↥(MaximalUnramifiedExtension l)), (∀ t, fr l r (x t) = x t) →
      Continuous (fun t => ((x t : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      ∃ a : X → Fin r → ℚ_[l], Continuous a ∧ ∀ t (m : Fin r),
        fr l m (x t) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a t k) := by
  intro l _ r hr
  obtain ⟨E, ω, -, -, -, hω, hli, hspan, hdet⟩ := UnrDeg.fixed_field_deg l r hr
  refine ⟨ω, Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, fun m k => rfl, hω, ?_⟩
  intro X _ x hx hcont

  set v : Fin r → Om l := fun k => ((ω k : ↥(MaximalUnramifiedExtension l)) : Om l) with hv
  have hliv : LinearIndependent ℚ_[l] v := by
    have := hli.map' (MaximalUnramifiedExtension l).val.toLinearMap (LinearMap.ker_eq_bot.2 (fun a b h => Subtype.ext h))
    exact this
  set ψ : (Fin r → ℚ_[l]) →ₗ[ℚ_[l]] Om l := Fintype.linearCombination ℚ_[l] v with hψ
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    rw [hψ, Fintype.linearCombination_apply] at hg
    funext i
    exact Fintype.linearIndependent_iff.1 hliv g hg i
  let e := LinearEquiv.ofInjective ψ hinj
  haveI : FiniteDimensional ℚ_[l] ↥(LinearMap.range ψ) := LinearEquiv.finiteDimensional e
  have hmem : ∀ t, ((x t : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ LinearMap.range ψ := by
    intro t
    obtain ⟨a, ha⟩ := hspan (x t) (hx t)
    refine ⟨a, ?_⟩
    rw [hψ, Fintype.linearCombination_apply, ha]
    simp [hv]
  refine ⟨fun t => e.symm ⟨((x t : ↥(MaximalUnramifiedExtension l)) : Om l), hmem t⟩, ?_, ?_⟩
  · exact (LinearMap.continuous_of_finiteDimensional (e.symm : ↥(LinearMap.range ψ) →ₗ[ℚ_[l]] (Fin r → ℚ_[l]))).comp
      (hcont.subtype_mk _)
  · intro t m
    have key : ψ (e.symm ⟨((x t : ↥(MaximalUnramifiedExtension l)) : Om l), hmem t⟩) = ((x t : ↥(MaximalUnramifiedExtension l)) : Om l) := by
      have h1 := congrArg Subtype.val (e.apply_symm_apply ⟨((x t : ↥(MaximalUnramifiedExtension l)) : Om l), hmem t⟩)
      rw [LinearEquiv.ofInjective_apply] at h1
      exact h1
    set a := e.symm ⟨((x t : ↥(MaximalUnramifiedExtension l)) : Om l), hmem t⟩
    have hxt : x t = ∑ k, a k • ω k := by
      apply Subtype.ext
      rw [← key, hψ, Fintype.linearCombination_apply]
      simp [hv]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hxt, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, fr_q, mul_comm]
    rfl

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoversTameOfFrobeniusTeichmuller
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CoverGen

open GlobalTheory.KinfCover

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]

theorem covers_of_sigma_teich {k : GQ l} (s : ZMod a) (z : Fq l a) (hze : z ^ e = 1)
    (hs : ∀ w : Wq l a, Per.σA k (wA l a w) = wA l a ((sigma l a ^ s.val) w))
    (hz : ϖ.kummer k = Fq.val l a z) : ∃ γ : TameGal K l e a, Covers K t ϖ k γ := by
  let ζ : rootsOfUnity e K := rootsOfUnity.mkOfPowEq (algebraMap O K (t (WittVector.teichmuller l z))) (by
    rw [← map_pow, ← map_pow, ← map_pow, hze, map_one, map_one, map_one])
  refine ⟨⟨ζ, Multiplicative.ofAdd s⟩, fun f f' hf' => ?_⟩
  set m : ℕ := s.val with hmdef
  have hms : ((m : ℕ) : ZMod a) = s := ZMod.natCast_zmod_val s
  set c : ZMod a → O := fun τ => emb t τ (WittVector.teichmuller l z) with hc
  have hroot : ∀ τ, TameGal.root (⟨ζ, Multiplicative.ofAdd s⟩ : TameGal K l e a) τ =
      algebraMap O K (c τ) := fun τ => by
    have h1 : c τ = t (WittVector.teichmuller l z) ^ l ^ (-τ).val := by
      change t ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z)) = _
      rw [sigma_pow_teich, map_pow]
    rw [h1, map_pow]
    change (((ζ ^ l ^ (-τ).val : rootsOfUnity e K) : Kˣ) : K) = _
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, rootsOfUnity.coe_mkOfPowEq]
  have hf'' : ∀ τ, f' τ = equivA O K (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := fun τ => by
    refine Subtype.ext ?_
    rw [hf' τ, ringAct_apply, hroot, coe_equivA, ← rescale_map, ← coe_equivA, AlgEquiv.apply_symm_apply, hms]
    rfl
  have hRHS : ϖ.iTot t K f' =
      ∑ τ, idem (constA t) τ * ϖ.evO O (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := by
    rw [PiSys.iTot, glue_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hf'' τ, PiSys.iA_equivA]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hRHS, PiSys.iTot, glue_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.addRight (m : ZMod a)) _ _ fun σ => ?_
  rw [map_mul, galOA_idem t hs, Equiv.coe_addRight, add_sub_cancel_right]
  change _ * galOA O k (ϖ.evO O ((equivA O K).symm (f σ))) = _
  rw [galOA_evO t ϖ z hz.symm, idem_mul_glue]

end GlobalTheory.CoverGen

theorem GlobalTheory.CoverGen.exists_covers_of_sigma_teich : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (k : GQ l) (s : ZMod a) (z : Fq l a), z ^ e = 1 → (∀ w : Wq l a, Per.σA k (wA l a w) = wA l a ((sigma l a ^ s.val) w)) → ϖ.kummer k = Fq.val l a z → ∃ γ : TameGal K l e a, Covers K t ϖ k γ :=
  fun _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ _ _ t ϖ _ s z hze hs hz => GlobalTheory.CoverGen.covers_of_sigma_teich t ϖ K s z hze hs hz
end
end

