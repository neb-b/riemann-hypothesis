module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisComparisonTransferBasisCoordinates
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem sum_through_tensor_basis {O A B M V ι κ : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
    [AddCommGroup M] [Module O M] [AddCommGroup V] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : A →ₐ[O] B) (jB : (ι → B) ≃ₗ[B] B ⊗[O] M) (X : B ⊗[O] M →+ V) (F : A → V → V)
    (hF : ∀ (c : A) (y : B ⊗[O] M), X (f c • y) = F c (X y))
    (c : ι → A) (r : κ → A) (x : κ → M)
    (h : jB (fun i => f (c i)) = TensorProduct.map f.toLinearMap LinearMap.id (∑ k, r k ⊗ₜ[O] x k)) :
    ∑ j, F (c j) (X (jB (Pi.single j 1))) = ∑ k, F (r k) (X ((1 : B) ⊗ₜ[O] x k)) := by
  have e1 : (fun i => f (c i)) = ∑ j, f (c j) • (Pi.single j 1 : ι → B) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have e2 : TensorProduct.map f.toLinearMap LinearMap.id (∑ k, r k ⊗ₜ[O] x k) =
      ∑ k, f (r k) • ((1 : B) ⊗ₜ[O] x k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [TensorProduct.smul_tmul']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, e2, map_sum] at h
  have h2 := congrArg X h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hF] at h2
  exact h2

theorem _root_.UpperTheory.KN.crisComparison_transfer_basis_coordinates :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (κ : Type) [Fintype κ] (c : ι → OA l ↥(OL LL)) (r : κ → OA l ↥(OL LL)) (x : κ → ↥T.L.T), I.j (inclL (thetaW a LL) ϖ P c) = TWincl (inclO l ↥(OL LL)) T (∑ k, r k ⊗ₜ[↥(OL LL)] x k) → ∑ j, act (toOD l ↥(OL LL) (c j)) (X (jB (Pi.single j 1))) = ∑ k, act (toOD l ↥(OL LL) (r k)) (((x k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I jB Pl AI Td hcmp X hX act hact κ _ c r x h
  have hF := UpperTheory.KN.crisComparison_toB_smul_eq_deRham_act l LL T Pl AI Td X hX act hact
  have h1 := hcmp c _ h
  have h2 := sum_through_tensor_basis (toB l ↥(OL LL)) jB X (fun c v => act (toOD l ↥(OL LL) c) v) hF c r x h1
  refine h2.trans (Finset.sum_congr rfl fun k _ => ?_)
  have h3 : X ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x k) =
      ((x k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR) := by
    refine (hX 1 1 (x k)).trans ?_
    rw [map_one, OneMemClass.coe_one, one_smul]
  exact congrArg (fun v => act (toOD l ↥(OL LL) (r k)) v) h3
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisInclIBEqDeRhamInclID
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.crisIncl_iB_eq_deRhamIncl_iD :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (f : ZMod a → invL l (S O K e)),
    iotaO O C (ϖ.iB t K f) = dRO l O (ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (f τ : K⟦X⟧))) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ C f
  have hS : ∀ τ, ϖ.iSD O K (f τ) = ϖ.iHat O K (GlobalTheory.GalStep.hatR O (f τ : K⟦X⟧)) := fun τ => by
    have hm : ((f τ : invL l (S O K e)) : K⟦X⟧) ∈ Rpi O K l e := invL_S_le_Rpi l e (f τ).2
    refine GlobalTheory.BKReal.TwoMaps.iSD_eq_iHat_of_hat l a e O K t ϖ (f τ) _ ?_
    rw [GlobalTheory.GalStep.hatR_of_mem (O := O) hm]
    exact hat_coe_Rpi l e ⟨_, hm⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PiSys.iB, PiSys.iD, glue_apply, glue_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hI : iotaO O C (idem (constB t) τ) = dRO l O (idem (constD t) τ) :=
    iotaO_toB C (constA t (Pi.single τ 1))
  rw [map_mul, hI, iotaO_iSl ϖ C (f τ), hS, map_mul]
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsTensorBdRActionOnLatticeBdR
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.exists_tensorBdR_action_on_latticeBdR :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), ∃ B : OdR l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR),
    ∀ (o : ↥(OL LL)) (b : Per.BdR l) (v : T.V) (c : Pl.R.BdR), B (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (Td.eD.symm b * c) := by
  intro l _ LL T Pl AI Td
  have hz : ∀ z : ℤ_[l], Td.eD.symm (algebraMap ℤ_[l] (Per.BdR l) z) = algebraMap ℚ_[l] Pl.R.BdR (z : ℚ_[l]) :=
    fun z => GlobalTheory.BKGal.JumpDR.cD_algebraMap Td z
  let φ : ↥(OL LL) → T.V →ₗ[ℚ_[l]] T.V := fun o =>
    { toFun := fun v => (o : ↥LL.1) • v
      map_add' := fun v w => smul_add _ v w
      map_smul' := fun q v => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (↥LL.1) q v, ← algebraMap_smul (↥LL.1) q ((o : ↥LL.1) • v), smul_smul, smul_smul,
          mul_comm] }
  let F : ↥(OL LL) → Per.BdR l → (T.V ⊗[ℚ_[l]] Pl.R.BdR →ₗ[ℚ_[l]] T.V ⊗[ℚ_[l]] Pl.R.BdR) := fun o b =>
    TensorProduct.map (φ o) (LinearMap.mulLeft ℚ_[l] (Td.eD.symm b))
  have hF : ∀ o b v c, F o b (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (Td.eD.symm b * c) := fun o b v c => rfl
  have hb : ∀ o b b', F o (b + b') = F o b + F o b' := fun o b b' => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, map_add (f := _), add_mul, tmul_add]
  have ho : ∀ o o' b, F (o + o') b = F o b + F o' b := fun o o' b => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, Subalgebra.coe_add, add_smul, add_tmul]
  let f : ↥(OL LL) →+ Per.BdR l →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
    AddMonoidHom.mk' (fun o => AddMonoidHom.mk' (fun b => (F o b).toAddMonoidHom)
      (fun b b' => AddMonoidHom.ext fun x => by
        show F o (b + b') x = F o b x + F o b' x
        rw [hb]; rfl))
      (fun o o' => AddMonoidHom.ext fun b => AddMonoidHom.ext fun x => by
        show F (o + o') b x = F o b x + F o' b x
        rw [ho]; rfl)
  have hbal : ∀ (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.BdR l), f (z • o) b = f o (z • b) := by
    intro z o b
    apply AddMonoidHom.ext
    intro x
    show F (z • o) b x = F o (z • b) x
    congr 1
    apply TensorProduct.ext'
    intro v c
    rw [hF, hF, Algebra.smul_def z b, map_mul, hz, mul_assoc, ← Algebra.smul_def,
      ← TensorProduct.smul_tmul (R := ℚ_[l])]
    congr 1
    show ((z : ℚ_[l]) • (o : ↥LL.1)) • v = (z : ℚ_[l]) • ((o : ↥LL.1) • v)
    rw [smul_assoc]
  refine ⟨TensorProduct.liftAddHom f hbal, fun o b v c => ?_⟩
  rw [TensorProduct.liftAddHom_tmul]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LatticeTensorDeRhamCrysRelationGaloisStable
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

private noncomputable def gdR {l : ℕ} [Fact l.Prime] (g : GQ l) : Per.BdR l →ₐ[ℤ_[l]] Per.BdR l where
  toRingHom := Per.σD g
  commutes' z := (GlobalTheory.MemLoc.FilLaws.σD_alg g (algebraMap ℤ_[l] (Per.BdRp l) z)).trans
    (congrArg (algebraMap (Per.BdRp l) (Per.BdR l)) ((GlobalTheory.GalStep.galD g).commutes z))

private noncomputable def gOdR {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (g : GQ l) :
    OdR l O →ₐ[O] OdR l O := Algebra.TensorProduct.map (AlgHom.id _ _) (gdR g)

private theorem gOdR_dRO {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (g : GQ l) (x : OD l O) :
    gOdR O g (dRO l O x) = dRO l O (GlobalTheory.GalStep.galOD O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Per.BdR l => o ⊗ₜ[ℤ_[l]] y) (GlobalTheory.MemLoc.FilLaws.σD_alg g w)
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem gOdR_iotaO {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (C : GlobalTheory.MemLoc.Core l) (g : GQ l) (x : OB l O) :
    gOdR O g (iotaO O C x) = iotaO O C (galOB O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Per.BdR l => o ⊗ₜ[ℤ_[l]] y) (GlobalTheory.BKGal.FilStable.ι_σB C g w).symm
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem act_incl {O G Qp LL R R' : Type} [CommRing O] [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
    [Algebra Qp LL] [Algebra O LL] [TopologicalSpace LL] [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (i : R →ₐ[O] R') (f : R →ₐ[O] R) (f' : R' →ₐ[O] R') (h : ∀ r, f' (i r) = i (f r))
    (T : LocLat G Qp LL O) (g : G) (z : TW R T) :
    TWact f' T g (TWincl i T z) = TWincl i T (TWact f T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    simp only [TWact, TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem _root_.UpperTheory.KN.latticeTensor_deRham_crys_relation_galois_stable :
    ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] (T : LocLat (Gl l) ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (g : Gl l) (y : TW (OD l O) T) (b : TW (OB l O) T) (x : OD l O),
    TWincl (dRO l O) T y = dRO l O x • TWincl (iotaO O C) T b →
    TWincl (dRO l O) T (TWact (GlobalTheory.GalStep.galOD O (sQ l g)) T g y) =
      dRO l O (GlobalTheory.GalStep.galOD O (sQ l g) x) • TWincl (iotaO O C) T (TWact (galOB O (sQ l g)) T g b) := by
  intro l _ O K _ _ _ _ _ _ _ T C g y b x h
  have h1 := act_incl (dRO l O) (GlobalTheory.GalStep.galOD O (sQ l g)) (gOdR O (sQ l g)) (gOdR_dRO O (sQ l g)) T g y
  have h2 := act_incl (iotaO O C) (galOB O (sQ l g)) (gOdR O (sQ l g)) (gOdR_iotaO O C (sQ l g)) T g b
  have h3 := GlobalTheory.GalStep.TWact_smul_of (gOdR O (sQ l g)) T g (dRO l O x) (TWincl (iotaO O C) T b)
  have h4 := gOdR_dRO O (sQ l g) x
  refine h1.symm.trans ((congrArg (TWact (gOdR O (sQ l g)) T g) h).trans (h3.trans ?_))
  rw [h4, h2]
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LatticeTensorInclDeRhamInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.latticeTensorIncl_deRham_injective :
    ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] (T : LocLat (Gl l) ℚ_[l] K O), Function.Injective (TWincl (dRO l O) T) := by
  intro l _ O K _ _ _ _ _ _ _ T
  classical
  have h0 : Function.Injective (bdRpToBdR l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1
  have h1 : Function.Injective (dRO l O) := by
    intro r s h
    let b := Module.Free.chooseBasis ℤ_[l] O
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext k
    apply h0
    rw [← equivFinsuppOfBasisLeft_map_id, ← equivFinsuppOfBasisLeft_map_id]
    exact congrArg (fun y => TensorProduct.equivFinsuppOfBasisLeft b y k) h
  intro w z h
  haveI := T.L.free
  let bT := Module.Free.chooseBasis O ↥T.L.T
  apply (TensorProduct.equivFinsuppOfBasisRight bT).injective
  refine Finsupp.ext (fun j => ?_)
  apply h1
  rw [← equivFinsuppOfBasisRight_map_id, ← equivFinsuppOfBasisRight_map_id]
  exact congrArg (fun y => TensorProduct.equivFinsuppOfBasisRight bT y j) h
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.PhiModCoefficientsEqSumOfInverseMatrix
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

private theorem hat_mulVec' {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
    {ι : Type} [Fintype ι] {Y : Matrix ι ι K⟦X⟧} (hY : ∀ i j, Y i j ∈ RpiE O K l e) {m : ι → K⟦X⟧}
    (hm : ∀ j, m j ∈ RpiE O K l e) (i : ι) :
    hat O l e ((Y *ᵥ m) i) = ∑ j, hat O l e (Y i j) * hat O l e (m j) := by
  have : (Y *ᵥ m) i = ((∑ j, ⟨Y i j, hY i j⟩ * ⟨m j, hm j⟩ : RpiE O K l e) : K⟦X⟧) := by
    simp [Matrix.mulVec, dotProduct]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, hat_coe, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hat_of_mem l e (hY i j), hat_of_mem l e (hm j)]

theorem _root_.UpperTheory.KN.phiMod_coefficients_eq_sum_of_inverse_matrix :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (n : ℕ) (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → P.MMl) (c : ZMod a → ι → Ahat O K l e),
    (∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) = ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) →
    ∀ j, (fun τ => c τ j) = ∑ k, s k * fun τ => GlobalTheory.GalStep.hatR O (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P n s m c h j
  funext τ
  apply algebraMap_AhatE_injective l e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h τ j, Finset.sum_apply, map_sum]
  simp only [GlobalTheory.BKGal.JumpDR.hsum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc (i : ι) : (coordL P (invL l (S O K e)) (m k) i τ : K⟦X⟧) ∈ Rpi O K l e :=
    invL_S_le_Rpi l e (coordL P (invL l (S O K e)) (m k) i τ).2
  have hm (i : ι) : (m k).1 τ i ∈ RpiE O K l e := by
    have := congrFun (mx_mulVec_coordL P (invL l (S O K e)) (m k) τ) i
    rw [← this]
    exact Subalgebra.sum_mem _ fun i' _ =>
      mul_mem (invE_A_le_RpiE l e (P.mx_mem τ i i')) (le_away _ _ (hc i'))
  have h1 : (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧) = (P.mxInv τ *ᵥ (m k).1 τ) j := rfl
  rw [Pi.mul_apply, map_mul, GlobalTheory.GalStep.hatR_of_mem (hc j), ← hat_coe_Rpi]
  change _ = _ * hat O l e (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧)
  rw [h1, hat_mulVec' (fun i i' => invE_A_le_RpiE l e (P.mxInv_mem τ i i')) hm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.PhiModDeRhamImageCoordExpansion
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.phiMod_deRham_image_coord_expansion :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ) (hx : ∀ τ i j, E K l e ^ α * P.mx τ i j ∈ A O K) (σ : P.MMl),
    GlobalTheory.GalStep.YD t ϖ (E K l e ^ α • σ.1) = ∑ j, ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (coordL P (invL l (S O K e)) σ j τ : K⟦X⟧)) •
      fun i => toOD l O (ϖ.iTot t K (fun τ => ⟨E K l e ^ α * P.mx τ i j, hx τ i j⟩)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P α hx σ
  funext i
  simp only [GlobalTheory.GalStep.YD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [← PiSys.iD_ofA, ← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  congr 1
  funext τ
  have hw' : ∀ k, (coordL P (invL l (S O K e)) σ k τ : K⟦X⟧) ∈ Rpi O K l e := fun k =>
    invL_S_le_Rpi l e (coordL P (invL l (S O K e)) σ k τ).2
  have hb' : ∀ k, E K l e ^ α * P.mx τ i k ∈ Rpi O K l e := fun k => A_le_Rpi l e (hx τ i k)
  have hs : E K l e ^ α * σ.1 τ i =
      ∑ k, (coordL P (invL l (S O K e)) σ k τ : K⟦X⟧) * (E K l e ^ α * P.mx τ i k) := by
    rw [← mx_mulVec_coordL P (invL l (S O K e)) σ τ]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hm : (∑ k, (coordL P (invL l (S O K e)) σ k τ : K⟦X⟧) * (E K l e ^ α * P.mx τ i k)) ∈ Rpi O K l e :=
    Subalgebra.sum_mem _ fun k _ => mul_mem (hw' k) (hb' k)
  have hA : ∀ k, ofA O K l e ⟨E K l e ^ α * P.mx τ i k, hx τ i k⟩ = toHat O K l e ⟨_, hb' k⟩ := fun k =>
    (toHat_eq_ofAl l e rfl).symm
  rw [hs, GlobalTheory.GalStep.hatR_of_mem (O := O) hm, Finset.sum_apply]
  simp only [Pi.mul_apply, GlobalTheory.GalStep.hatR_of_mem (O := O) (hw' _), hA, ← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  congr 1
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  rfl
end

