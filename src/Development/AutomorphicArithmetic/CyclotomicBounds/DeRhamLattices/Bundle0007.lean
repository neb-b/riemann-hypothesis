module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0004
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparison
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisComparisonImageEisensteinPowPhiInvColumns
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

private theorem tensor_inclusion_smul_sum {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [NormedAlgebra ℚ_[l] K] {G : Type} [Group G] [TopologicalSpace G]
    {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    (f : R →ₐ[O] R') (T : LocLat G ℚ_[l] K O) (s : R) {κ : Type} [Fintype κ] (r : κ → R) (x : κ → ↥T.L.T) :
    TWincl f T (∑ k, (s * r k) ⊗ₜ[O] x k) = f s • TWincl f T (∑ k, r k ⊗ₜ[O] x k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [TWincl, TensorProduct.smul_tmul']

private theorem ennreal_volume_ratio_step_cancel {R W ι : Type} [CommRing R] [AddCommGroup W] [Fintype ι] (act : R →+ (W →+ W))
    (hmul : ∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) (hone : ∀ w : W, act 1 w = w)
    (u : R) (hu : IsUnit u) (y z y' z' : ι → R) (v w : ι → W) (hy : ∀ j, y' j = u * y j)
    (hz : ∀ j, z' j = u * z j) (h : ∑ j, act (y' j) (v j) = ∑ k, act (z' k) (w k)) :
    ∑ j, act (y j) (v j) = ∑ k, act (z k) (w k) := by
  obtain ⟨u, rfl⟩ := hu
  have h2 := congrArg (act ((u⁻¹ : Rˣ) : R)) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hy, hz, ← hmul, ← mul_assoc, Units.inv_mul, one_mul] at h2
  exact h2

private theorem tame_lattice_inclusion (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι)
    (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (i : ι) (y : ι → OA l O) (s u : OA l O)
    (r : ι → OA l O) (x : ι → ↥T.L.T) (hI : inclL t ϖ P y = Pi.single i (inclO l O s))
    (hj : I.j (inclV l O ι (Pi.single i u)) = TWincl (inclO l O) T (∑ k, r k ⊗ₜ[O] x k)) :
    I.j (inclL t ϖ P (fun j => u * y j)) = TWincl (inclO l O) T (∑ k, (s * r k) ⊗ₜ[O] x k) := by
  have h1 : inclL t ϖ P (fun j => u * y j) = inclO l O s • inclV l O ι (Pi.single i u) := by
    have h2 : inclL t ϖ P (fun j => u * y j) = inclO l O u • inclL t ϖ P y := by
      rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
      congr 1
      funext j
      simp
    rw [h2, hI]
    funext j
    change inclO l O u * _ = inclO l O s * inclO l O ((Pi.single i u : ι → OA l O) j)
    by_cases hij : j = i
    · subst hij
      rw [Pi.single_eq_same, Pi.single_eq_same, mul_comm]
    · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij, map_zero, mul_zero, mul_zero]
  rw [h1, I.j.map_smul, hj]
  exact (tensor_inclusion_smul_sum (inclO l O) T s r x).symm

private theorem cancel_unit_in_sum_action {A R W ι : Type} [CommRing A] [CommRing R] [AddCommGroup W] [Fintype ι]
    (f : A → R) (hf : ∀ x y, f (x * y) = f x * f y) (act : R →+ (W →+ W))
    (hmul : ∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) (hone : ∀ w : W, act 1 w = w)
    (u s : A) (s' : R) (hs : f s = s') (hu : IsUnit (f u)) (y r : ι → A) (m : ι → R)
    (hr : ∀ k, f (r k) = f u * m k) (v w : ι → W)
    (h : ∑ j, act (f (u * y j)) (v j) = ∑ k, act (f (s * r k)) (w k)) :
    ∑ j, act (f (y j)) (v j) = ∑ k, act (s' * m k) (w k) :=
  ennreal_volume_ratio_step_cancel act hmul hone (f u) hu _ _ _ _ v w (fun j => hf _ _)
    (fun k => by rw [hf, hs, hr, mul_left_comm]) h

theorem _root_.UpperTheory.KN.crisComparison_image_eisensteinPow_phiInvColumns :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (b : Module.Basis ι ↥(OL LL) ↥T.L.T) (m : Matrix ι ι (OD l ↥(OL LL))) (u : OA l ↥(OL LL)) (r : ι → ι → OA l ↥(OL LL)), IsUnit (toOD l ↥(OL LL) u) → (∀ i, I.j (inclV l ↥(OL LL) ι (Pi.single i u)) = TWincl (inclO l ↥(OL LL)) T (∑ k, r i k ⊗ₜ[↥(OL LL)] b k)) → (∀ i k, toOD l ↥(OL LL) (r i k) = toOD l ↥(OL LL) u * m i k) → ∀ (β : ℕ) (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1) (i : ι), ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩))) (X (jB (Pi.single j 1))) = ∑ k, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β * m i k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I jB Pl AI Td hcmp X hX act hact b m u r hu hj hr β hβ i
  have hact' := GlobalTheory.BKGal.JumpDR.odAct_mul_one l LL T Pl AI Td act hact
  have hI := UpperTheory.KN.inclL_eisensteinPow_phiInv_eq_single l a e ϖ LL ι P β hβ i
  have hE := UpperTheory.KN.iTot_eisensteinPow_eq_iD_eisensteinHatPow l a e ϖ LL β
  have h3 := tame_lattice_inclusion l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P T I i _ _ u (r i) (fun k => b k) hI (hj i)
  have h4 := UpperTheory.KN.crisComparison_transfer_basis_coordinates l a e ϖ LL ι P T I jB Pl AI Td hcmp X hX act hact ι _ _ _ h3
  have h5 := cancel_unit_in_sum_action (toOD l ↥(OL LL)) (map_mul (toOD l ↥(OL LL))) act hact'.1 hact'.2 u _ _ hE hu _ (r i) (m i)
    (hr i) _ _ h4
  exact h5
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrysLatticeBdRPlusActionCompat
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

private theorem actDRG {Z Q O P D V R : Type} [CommRing Z] [CommRing Q] [CommRing O] [Algebra Z O]
    [CommRing P] [Algebra Z P] [CommRing D] [Algebra Z D] [AddCommGroup V] [Module Q V]
    [CommRing R] [Algebra Q R] (s : O → V → V) (g : P → D) (cD : P → R) (e : D → R)
    (hg : ∀ b, cD b = e (g b)) (d : O ⊗[Z] P →+ O ⊗[Z] D)
    (hd : ∀ o b, d (o ⊗ₜ[Z] b) = o ⊗ₜ[Z] g b)
    (A : O ⊗[Z] P →+ (V ⊗[Q] R →+ V ⊗[Q] R))
    (hA : ∀ (o : O) (b : P) (v : V) (c : R), A (o ⊗ₜ[Z] b) (v ⊗ₜ[Q] c) = (s o v) ⊗ₜ[Q] (cD b * c))
    (B : O ⊗[Z] D →+ (V ⊗[Q] R →+ V ⊗[Q] R))
    (hB : ∀ (o : O) (b : D) (v : V) (c : R), B (o ⊗ₜ[Z] b) (v ⊗ₜ[Q] c) = (s o v) ⊗ₜ[Q] (e b * c))
    (y : O ⊗[Z] P) (w : V ⊗[Q] R) : A y w = B (d y) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add (f := _), hv, hw]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, AddMonoidHom.zero_apply]
    | add x x' hx hx' => simp only [map_add (f := _), AddMonoidHom.add_apply, hx, hx']
    | tmul o b => rw [hd, hA, hB, hg]

private theorem actCrisG {Z Q O P D M V R : Type} [CommRing Z] [CommRing Q] [CommRing O] [Algebra Z O]
    [CommRing P] [Algebra Z P] [CommRing D] [Algebra Z D] [AddCommGroup V] [Module Q V]
    [AddCommGroup M] [Module O M]
    [CommRing R] [Algebra Q R] (s : O → V → V) (hs : ∀ o o' v, s (o * o') v = s o (s o' v))
    (j : M → V) (g : P → D) (cB : P →+* R) (e : D → R)
    (hg : ∀ b, cB b = e (g b)) (d : O ⊗[Z] P →+ O ⊗[Z] D)
    (hd : ∀ o b, d (o ⊗ₜ[Z] b) = o ⊗ₜ[Z] g b)
    (Y : (O ⊗[Z] P) ⊗[O] M →+ V ⊗[Q] R)
    (hY : ∀ (o : O) (b : P) (x : M), Y ((o ⊗ₜ[Z] b) ⊗ₜ[O] x) = (s o (j x)) ⊗ₜ[Q] cB b)
    (B : O ⊗[Z] D →+ (V ⊗[Q] R →+ V ⊗[Q] R))
    (hB : ∀ (o : O) (b : D) (v : V) (c : R), B (o ⊗ₜ[Z] b) (v ⊗ₜ[Q] c) = (s o v) ⊗ₜ[Q] (e b * c))
    (b : O ⊗[Z] P) (z : (O ⊗[Z] P) ⊗[O] M) : Y (b • z) = B (d b) (Y z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add v w hv hw => simp only [smul_add, map_add (f := _), hv, hw]
  | tmul u x =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    induction b using TensorProduct.induction_on with
    | zero => simp only [zero_mul, zero_tmul, map_zero, AddMonoidHom.zero_apply]
    | add y y' hy hy' => simp only [add_mul, add_tmul, map_add (f := _), AddMonoidHom.add_apply, hy, hy']
    | tmul o' b' =>
      induction u using TensorProduct.induction_on with
      | zero => simp only [mul_zero, zero_tmul, map_zero]
      | add y y' hy hy' => simp only [mul_add, add_tmul, map_add (f := _), hy, hy']
      | tmul o b =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hY, hY, hd, hB, map_mul, hs, hg b']

private theorem hcB {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
    (C : GlobalTheory.MemLoc.Core l) (β : Per.Bcris l) : GlobalTheory.BKGal.JumpDR.cB Td β = Td.eD.symm (C.ι β) := by
  have e0 := GlobalTheory.FundSeq.eq_core_of_isCrisDR Td.incl C
  rw [← e0]
  exact (Td.eD.symm_apply_apply _).symm

private theorem hcD {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
    (β : Per.BdRp l) : GlobalTheory.BKGal.JumpDR.cD Td β = Td.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) β) := rfl

private theorem hdR {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (o : O) (b : Per.BdRp l) :
    dRO l O (o ⊗ₜ[ℤ_[l]] b) = o ⊗ₜ[ℤ_[l]] algebraMap (Per.BdRp l) (Per.BdR l) b := rfl

private theorem hio {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) (o : O) (b : Per.Bcris l) :
    iotaO O C (o ⊗ₜ[ℤ_[l]] b) = o ⊗ₜ[ℤ_[l]] C.ι b := rfl

private theorem mainG {l : ℕ} [Fact l.Prime] {O M V : Type} [CommRing O] [Algebra ℤ_[l] O]
    [AddCommGroup V] [Module ℚ_[l] V] [AddCommGroup M] [Module O M]
    {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
    (s : O → V → V) (hs : ∀ o o' v, s (o * o') v = s o (s o' v)) (j : M → V)
    (Y : OB l O ⊗[O] M →+ V ⊗[ℚ_[l]] Pl.R.BdR)
    (hY : ∀ (o : O) (b : Per.Bcris l) (x : M), Y ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[O] x) = (s o (j x)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b)
    (act : OD l O →+ (V ⊗[ℚ_[l]] Pl.R.BdR →+ V ⊗[ℚ_[l]] Pl.R.BdR))
    (hact : ∀ (o : O) (b : Per.BdRp l) (v : V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (s o v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c))
    (B : OdR l O →+ (V ⊗[ℚ_[l]] Pl.R.BdR →+ V ⊗[ℚ_[l]] Pl.R.BdR))
    (hB : ∀ (o : O) (b : Per.BdR l) (v : V) (c : Pl.R.BdR), B (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (s o v) ⊗ₜ[ℚ_[l]] (Td.eD.symm b * c))
    (C : GlobalTheory.MemLoc.Core l) (b : OB l O) (y : OD l O) (hby : iotaO O C b = dRO l O y) (z : OB l O ⊗[O] M) :
    Y (b • z) = act y (Y z) := by
  have h1 : act y (Y z) = B (dRO l O y) (Y z) :=
    actDRG s (algebraMap (Per.BdRp l) (Per.BdR l))
      (GlobalTheory.BKGal.JumpDR.cD Td) Td.eD.symm (hcD Td) (AddMonoidHom.mk' (dRO l O) (map_add _))
      hdR act hact B hB y (Y z)
  have h2 : Y (b • z) = B (iotaO O C b) (Y z) :=
    actCrisG s hs j C.ι
      (GlobalTheory.BKGal.JumpDR.cB Td) Td.eD.symm (hcB Td C) (AddMonoidHom.mk' (iotaO O C) (map_add _))
      (hio C) Y hY B hB b z
  exact h2.trans (hby ▸ h1.symm)

theorem _root_.UpperTheory.KN.crysLattice_bdRPlus_action_compat :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (Y : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR),
    (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), Y ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) →
    ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)),
    (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) →
    ∀ (C : GlobalTheory.MemLoc.Core l) (b : OB l ↥(OL LL)) (y : OD l ↥(OL LL)), iotaO ↥(OL LL) C b = dRO l ↥(OL LL) y → ∀ z : TW (OB l ↥(OL LL)) T, Y (b • z) = act y (Y z) := by
  intro l _ LL T Pl AI Td Y hY act hact C b y hby z
  obtain ⟨B, hB⟩ := UpperTheory.KN.exists_tensorBdR_action_on_latticeBdR l LL T Pl AI Td
  exact mainG Td (fun (o : ↥(OL LL)) (v : T.V) => (o : ↥LL.1) • v)
    (fun o o' v => mul_smul (o : ↥LL.1) (o' : ↥LL.1) v) (fun x : ↥T.L.T => (x : T.V)) Y hY act hact B hB C b y hby z
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsUnitIdentificationSingleIntegral
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem UpperTheory.KN.tame_identification_unit (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) :
    ∃ u : OA l O, IsUnit (toOD l O u) ∧ ∀ i : ι, ∃ z : TW (OA l O) T,
      I.j (inclV l O ι (Pi.single i u)) = TWincl (inclO l O) T z := by
  obtain ⟨⟨ε, hε⟩, hεall⟩ := _root_.GlobalTheory.MuOfEps.main l
  set δ : OCb l := (frobeniusEquiv (OCb l) l).symm ε with hδdef
  have hδ : δ ^ l = ε := frobeniusEquiv_symm_pow_p (OCb l) l ε
  obtain ⟨-, -, hθ, -⟩ := hεall ε δ hε hδ
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  obtain ⟨hK1, hK2, -, -⟩ := _root_.GlobalTheory.BKExp.exponents l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ
  set ν : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] muOf δ with hν
  have hpow : ∀ k : ℕ, (1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ k) = ν ^ k := fun k => by
    rw [hν, Algebra.TensorProduct.tmul_pow, one_pow]
  simp only [hpow] at hK1 hK2
  have hu : IsUnit (toOD l O ν) := by
    have h1 : IsUnit (ainfToBdRp l (muOf δ)) := (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
      change Per.θD l (GlobalTheory.MemLoc.aDp l (muOf δ)) ≠ 0
      rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
      intro h
      exact hθ (Subtype.ext h))
    have h2 : toOD l O ν = (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)
        (ainfToBdRp l (muOf δ)) := by
      simp [hν, toOD]
    rw [h2]
    exact h1.map _
  choose z hz using fun i => hK2 (inclV l O ι (Pi.single i 1)) ⟨_, rfl⟩
  refine ⟨ν ^ α, ?_, fun i => ⟨z i, ?_⟩⟩
  · rw [map_pow]
    exact hu.pow α
  · have hc : inclV l O ι (Pi.single i (ν ^ α)) = inclO l O (ν ^ α) • inclV l O ι (Pi.single i 1) := by
      rw [← GlobalTheory.DeRhamIdent.inclV_smul]
      congr 1
      funext j
      simp [Pi.single_apply]
    rw [hc, hz i]

theorem _root_.UpperTheory.KN.exists_unit_identification_single_integral :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), ∃ u : OA l ↥(OL LL), IsUnit (toOD l ↥(OL LL) u) ∧ ∀ i : ι, ∃ z : TW (OA l ↥(OL LL)) T, I.j (inclV l ↥(OL LL) ι (Pi.single i u)) = TWincl (inclO l ↥(OL LL)) T z := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I
  exact UpperTheory.KN.tame_identification_unit l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P T I
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.TamePhiModuleCrystallineBasisCompat
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.tame_phiModule_crystalline_basis_compat :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (jD : (ι → OD l O) ≃ₗ[OD l O] TW (OD l O) T) (C : GlobalTheory.MemLoc.Core l) (ε : OCb l), IsEps ε → IsCrisCmp I jB →
    (∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z → jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z) →
    ∀ α : ℕ, (∀ v ∈ P.L, E K l e ^ α • v ∈ P.M) →
    ∀ (hx : ∀ τ i j, E K l e ^ α * P.mx τ i j ∈ A O K) (j : ι),
    TWincl (dRO l O) T (jD (fun i => toOD l O (ϖ.iTot t K (fun τ => ⟨E K l e ^ α * P.mx τ i j, hx τ i j⟩)))) =
      dRO l O (GlobalTheory.GalStep.ED K t ϖ) ^ α • TWincl (iotaO O C) T (jB (Pi.single j 1)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I jB jD C ε hε hB hD α hα hx j
  set c : ι → OA l O := fun i => ϖ.iTot t K (fun τ => ⟨E K l e ^ α * P.mx τ i j, hx τ i j⟩) with hc
  set E0 : OA l O := ϖ.iTot t K (fun _ => EIn l e (A O K)) with hE0
  have hED : GlobalTheory.GalStep.ED K t ϖ = toOD l O E0 :=
    PiSys.iD_ofA t K ϖ (fun _ => EIn l e (A O K))
  have h1 : inclV l O ι c = inclL t ϖ P (fun i => E0 ^ α * (Pi.single j 1 : ι → OA l O) i) := by
    funext i
    rw [inclL_apply]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single j (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero, map_zero, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one]
    change inclO l O (c i) = _
    rw [hc, hE0, ← map_pow]
    simp only [← ϖ.iW_of_mem t K, frobMat, Matrix.map_apply, Matrix.of_apply, ← map_mul]
    refine congrArg _ (funext fun τ => Subtype.ext ?_)
    change E K l e ^ α * P.mx τ i j = P.mx τ i j * ((EIn l e (A O K) ^ α : A O K) : K⟦X⟧)
    rw [mul_comm, SubmonoidClass.coe_pow]
    rfl
  obtain ⟨-, β, -, hβ⟩ := P.exists_exponents
  obtain ⟨δ, hδ, hδ1⟩ := hε.2
  obtain ⟨-, hK2, -, -⟩ := _root_.GlobalTheory.BKExp.exponents l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ
  obtain ⟨z, hz⟩ := hK2 (inclV l O ι c) ⟨c, rfl⟩
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ α) with hm
  have hV : inclV l O ι (fun i => m * c i) = inclO l O m • inclV l O ι c := by
    funext i
    change inclO l O (m * c i) = inclO l O m * inclO l O (c i)
    rw [map_mul]
  have h3 := hD (fun i => m * c i) z (by rw [hV, hz])
  have h4 := hB (fun i => m * (E0 ^ α * (Pi.single j 1 : ι → OA l O) i)) z (by
    rw [inclL_smul_coord, ← h1, hz])
  have e3 : (fun i => toOD l O (m * c i)) = toOD l O m • fun i => toOD l O (c i) :=
    funext fun i => by simp only [map_mul, Pi.smul_apply, smul_eq_mul]
  have e4 : (fun i => toB l O (m * (E0 ^ α * (Pi.single j 1 : ι → OA l O) i))) =
      toB l O (m * E0 ^ α) • (Pi.single j 1 : ι → OB l O) := by
    funext i
    by_cases h : i = j
    · subst h
      simp only [Pi.single_eq_same, mul_one, Pi.smul_apply, smul_eq_mul]
    · simp only [Pi.single_eq_of_ne h, mul_zero, map_zero, Pi.smul_apply, smul_eq_mul]
  rw [e3, map_smul] at h3
  rw [e4, map_smul] at h4
  have h5 : ∀ y : TW (OA l O) T, TWincl (dRO l O) T (TWincl (toOD l O) T y) =
      TWincl (iotaO O C) T (TWincl (toB l O) T y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul s x =>
      simp only [TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, iotaO_toB]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h6 := h5 z
  rw [← h3, ← h4, BasisCoord.tWincl_smul', BasisCoord.tWincl_smul', iotaO_toB, map_mul, map_mul, mul_smul,
    map_pow, map_pow, ← hED] at h6
  have hν : IsUnit (ainfToBdRp l (muOf δ)) := by
    apply (GlobalTheory.MemLoc.thetaD_props l).2.2.1
    change Per.θD l (GlobalTheory.MemLoc.aDp l (muOf δ)) ≠ 0
    rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
    intro h
    have h0 : Per.θ l (muOf δ) = 0 := Subtype.ext h
    rw [muOf, map_sub, map_one, WittVector.fontaineTheta_teichmuller, sub_eq_zero] at h0
    exact hδ1 h0
  have hu : IsUnit (dRO l O (toOD l O m)) := by
    have h2 : toOD l O m = (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)
        (ainfToBdRp l (muOf δ) ^ α) := by
      rw [hm, toOD, Algebra.TensorProduct.map_tmul, map_one, map_pow]
      rfl
    rw [h2]
    exact ((hν.pow α).map _).map _
  exact hu.smul_left_cancel.1 h6
end

