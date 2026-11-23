module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003
public import Formalism.CoboundaryTransfers.Statement
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfTensorLatticeSpecialisation
section
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem specPhi_coord {Z N C : Type} [CommRing Z] [AddCommGroup N] [Module Z N] [CommRing C]
    (φ : Z →+* C) {d : ℕ} (b : Module.Basis (Fin d) Z N) (u : N →ₗ[Z] N)
    (U : Matrix (Fin d) (Fin d) C) (hU : ∀ i j, U i j = φ (b.repr (u (b j)) i)) (t : N) :
    (fun i => φ (b.repr (u t) i)) = U.mulVec (fun i => φ (b.repr t i)) := by
  funext i
  conv_lhs => rw [← b.sum_repr t]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, map_mul, Matrix.mulVec, dotProduct, hU]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem specPhi_coord_smul {Z O N C : Type} [CommRing Z] [CommRing O] [Algebra Z O] [AddCommGroup N]
    [Module O N] [Module Z N] (hs : ∀ (x : Z) (t : N), x • t = algebraMap Z O x • t) [CommRing C]
    (φ : Z →+* C) {d : ℕ} (b : Module.Basis (Fin d) Z N) (a : O)
    (U : Matrix (Fin d) (Fin d) C) (hU : ∀ i j, U i j = φ (b.repr (a • b j) i)) (t : N) :
    (fun i => φ (b.repr (a • t) i)) = U.mulVec (fun i => φ (b.repr t i)) := by
  have hlin : ∀ (x : Z) (s : N), a • (x • s) = x • (a • s) := by
    intro x s
    rw [hs, hs, smul_smul, smul_smul, mul_comm]
  let u : N →ₗ[Z] N :=
    { toFun := fun s => a • s
      map_add' := fun x y => smul_add a x y
      map_smul' := fun x s => hlin x s }
  exact specPhi_coord φ b u U hU t

theorem specPhi_generic {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d : ℕ}
    (L : R → Matrix (Fin d) (Fin d) C) (hL0 : L 0 = 0) (hLa : ∀ x y, L (x + y) = L x + L y)
    (hLm : ∀ x y, L (x * y) = L x * L y) (co : ↥T.L.T →+ (Fin d → C))
    (hco : ∀ (a : O) t, co (a • t) = (L (algebraMap O R a)).mulVec (co t)) :
    ∃ Φ : TW R T →+ (Fin d → C), (∀ (r : R) (t : ↥T.L.T), Φ (r ⊗ₜ[O] t) = (L r).mulVec (co t)) ∧
      ∀ (r : R) (z : TW R T), Φ (r • z) = (L r).mulVec (Φ z) := by
  let f : R →+ ↥T.L.T →+ (Fin d → C) :=
    { toFun := fun r =>
        { toFun := fun t => (L r).mulVec (co t)
          map_zero' := by simp
          map_add' := fun x y => by simp [Matrix.mulVec_add] }
      map_zero' := by ext t : 1; simp [hL0]
      map_add' := fun x y => by ext t : 1; simp [hLa, Matrix.add_mulVec] }
  have hf : ∀ (a : O) (r : R) (t : ↥T.L.T), f (a • r) t = f r (a • t) := by
    intro a r t
    show (L (a • r)).mulVec (co t) = (L r).mulVec (co (a • t))
    rw [Algebra.smul_def, mul_comm, hLm, hco, Matrix.mulVec_mulVec]
  refine ⟨TensorProduct.liftAddHom f hf, fun r t => rfl, fun r z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    show (L (r * x)).mulVec (co t) = (L r).mulVec ((L x).mulVec (co t))
    rw [hLm, Matrix.mulVec_mulVec]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, Matrix.mulVec_add]

theorem specPhi_equiv {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d : ℕ}
    (Φ : TW R T →+ (Fin d → C)) (u : R →ₐ[O] R) (g : G) (U : Matrix (Fin d) (Fin d) C)
    (σ : C ≃+* C)
    (h : ∀ (r : R) (t : ↥T.L.T), Φ (u r ⊗ₜ[O] T.actT g t) =
      U.mulVec (fun i => σ (Φ (r ⊗ₜ[O] t) i))) (z : TW R T) :
    Φ (TWact u T g z) = U.mulVec (fun i => σ (Φ z i)) := by
  unfold TWact
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Pi.zero_apply]
    exact (Matrix.mulVec_zero U).symm
  | tmul r t => exact h r t
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy, ← Matrix.mulVec_add]
    congr 1
    funext i
    simp [map_add (f := _)]

theorem specPhi_norm {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d : ℕ}
    (Φ : TW R T →+ (Fin d → C)) (S : AddSubmonoid C)
    (h : ∀ (r : R) (t : ↥T.L.T) i, Φ (r ⊗ₜ[O] t) i ∈ S) (z : TW R T) (i : Fin d) :
    Φ z i ∈ S := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r t => exact h r t i
  | add x y hx hy => simpa using S.add_mem hx hy

variable {l : ℕ} [Fact l.Prime]


set_option synthInstance.maxHeartbeats 400000 in
theorem specPhi_co (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (h : IsMat K LL T M A)
    {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (hact : IsActC act) :
    ∃ co : ↥T.L.T →+ (Fin d → PadicComplex l), (∀ t i, co t i ∈ (PadicComplexInt l).toSubring) ∧
      (∀ (g : ↥(GK K)) t i, act (g : GQ l) (co t i) = co t i) ∧
      (∀ (a : ↥(OL LL)) (t : ↥T.L.T), co (a • t) = (A a).mulVec (co t)) ∧
      (∀ (g : ↥(GK K)) (t : ↥T.L.T), co (T.actT g t) = (M (g : GQ l)).mulVec (co t)) ∧
      ∀ j, ∃ t, co t = Pi.single j 1 := by
  obtain ⟨b, hM, hA⟩ := h
  letI := zlMod LL T
  let φ : ℤ_[l] →+* PadicComplex l :=
    (algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom
  let co : ↥T.L.T →+ (Fin d → PadicComplex l) :=
    { toFun := fun t i => zC (b.repr t i)
      map_zero' := by funext i; simp [zC]
      map_add' := fun x y => by funext i; simp [zC] }
  refine ⟨co, fun t i => ?_, fun g t i => act_zC hact _ _, fun a t => ?_, fun g t => ?_,
    fun j => ⟨b j, ?_⟩⟩
  · exact (mem_OC _).2 ((norm_zC _).le.trans (PadicInt.norm_le_one _))
  · have hs : ∀ (x : ℤ_[l]) (s : ↥T.L.T), x • s = algebraMap ℤ_[l] ↥(OL LL) x • s :=
      fun x s => rfl
    exact specPhi_coord_smul hs φ b a (A a) (fun i j => hA a i j) t
  · exact specPhi_coord φ b (actTZ LL T g) (M g) (fun i j => hM g i j) t
  · funext i
    show zC (b.repr (b j) i) = (Pi.single j (1 : PadicComplex l) : Fin d → PadicComplex l) i
    rw [b.repr_self]
    by_cases hij : i = j
    · subst hij
      simp [zC]
    · simp [zC, hij]

theorem specPhi_abstract {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d f : ℕ}
    (S : Subring C) (A : O → Matrix (Fin d) (Fin d) C) (M : G → Matrix (Fin d) (Fin d) C)
    (σ : G → C ≃+* C) (u : G → R →ₐ[O] R) (o : Fin f → O) (κ : R → Fin f → C)
    (L : R → Matrix (Fin d) (Fin d) C) (hL : ∀ r, L r = ∑ k, κ r k • A (o k))
    (hL0 : L 0 = 0) (hLa : ∀ x y, L (x + y) = L x + L y)
    (hLm : ∀ x y, L (x * y) = L x * L y) (hal : ∀ a, L (algebraMap O R a) = A a) (hone : A 1 = 1)
    (hκS : ∀ r k, κ r k ∈ S) (hκ : ∀ g r k, κ (u g r) k = σ g (κ r k))
    (co : ↥T.L.T →+ (Fin d → C)) (hS : ∀ t i, co t i ∈ S) (hσ : ∀ g t i, σ g (co t i) = co t i)
    (hcoA : ∀ (a : O) t, co (a • t) = (A a).mulVec (co t))
    (hcoM : ∀ g t, co (T.actT g t) = (M g).mulVec (co t)) :
    ∃ Φ : TW R T →+ (Fin d → C), (∀ (r : R) (z : TW R T), Φ (r • z) = (L r).mulVec (Φ z)) ∧
      (∀ z i, Φ z i ∈ S) ∧
      (∀ g z, Φ (TWact (u g) T g z) = (M g).mulVec (fun i => σ g (Φ z i))) ∧
      ∀ t : ↥T.L.T, Φ ((1 : R) ⊗ₜ[O] t) = co t := by
  obtain ⟨Φ, hΦt, hΦs⟩ := specPhi_generic T L hL0 hLa hLm co (fun a t => by rw [hcoA, hal])
  have hLco : ∀ r t, (L r).mulVec (co t) = ∑ k, κ r k • co (o k • t) := by
    intro r t
    rw [hL, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mulVec, hcoA]
  refine ⟨Φ, hΦs, fun z i => specPhi_norm T Φ S.toAddSubmonoid (fun r t i => ?_) z i,
    fun g z => specPhi_equiv T Φ (u g) g (M g) (σ g) (fun r t => ?_) z, fun t => ?_⟩
  · show _ ∈ S
    rw [hΦt, hLco, Finset.sum_apply]
    refine S.sum_mem fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact S.mul_mem (hκS r k) (hS _ i)
  · rw [hΦt, hΦt, hLco, hLco]
    have h1 : ∀ k, co (o k • T.actT g t) = (M g).mulVec (co (o k • t)) := fun k => by
      rw [← map_smul (T.actT g) (o k) t, hcoM]
    have h2 : (fun i => σ g ((∑ k, κ r k • co (o k • t)) i)) =
        ∑ k, κ (u g r) k • co (o k • t) := by
      funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hσ, ← hκ]
    rw [h2, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h1, Matrix.mulVec_smul]
  · have h1 : L 1 = 1 := by rw [← map_one (algebraMap O R), hal, hone]
    rw [hΦt, h1, Matrix.one_mulVec]

set_option synthInstance.maxHeartbeats 400000 in
theorem specPhi_thR_alg (LL : FinExt l) (θ : Ainf l →ₐ[ℤ_[l]] OC l) (a : ↥(OL LL)) :
    thR LL θ (algebraMap ↥(OL LL) (RA LL) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a := by
  rw [Algebra.TensorProduct.algebraMap_apply, thR_tmul, map_one]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem exists_specPhi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f n : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (θ : Ainf l →ₐ[ℤ_[l]] OC l), IsMat K LL T M A → IsThetaShift AI n θ → ∃ Φ : TW (RA LL) T →+ (Fin d → PadicComplex l), (∀ (r : RA LL) (z : TW (RA LL) T), Φ (r • z) = (lam o A (thR LL θ r)).mulVec (Φ z)) ∧ (∀ z i, ‖Φ z i‖ ≤ 1) ∧ (∀ (g : ↥(GK K)) (z : TW (RA LL) T), Φ (TWact (gRA AI LL (g : GQ l)) T g z) = (M (g : GQ l)).mulVec (fun i => AI.actC (g : GQ l) (Φ z i))) ∧ ∀ j, ∃ t : ↥T.L.T, Φ ((1 : RA LL) ⊗ₜ[↥(OL LL)] t) = Pi.single j 1 := by
  intro l _ P AI K LL T d f n M A o θ hM hθ
  have hact : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  obtain ⟨co, hS, hσ, hcoA, hcoM, hsingle⟩ := specPhi_co K LL T M A hM hact
  have hmul := lam_mul_of_isMat l K LL T d f M A o hM
  have hL : ∀ r : RA LL, lam o A (thR LL θ r) = ∑ k, kap o (thR LL θ r) k • A (o k) :=
    fun r => rfl
  have hL0 : lam o A (thR LL θ 0) = 0 := by rw [map_zero, lamMul_lam_zero]
  have hLa : ∀ x y : RA LL, lam o A (thR LL θ (x + y)) =
      lam o A (thR LL θ x) + lam o A (thR LL θ y) := fun x y => by
    rw [map_add (f := _), lamMul_lam_add]
  have hLm : ∀ x y : RA LL, lam o A (thR LL θ (x * y)) =
      lam o A (thR LL θ x) * lam o A (thR LL θ y) := fun x y => by
    rw [map_mul, hmul.2.2.2]
  have hal : ∀ a : ↥(OL LL), lam o A (thR LL θ (algebraMap ↥(OL LL) (RA LL) a)) = A a :=
    fun a => by rw [specPhi_thR_alg, hmul.1]; simp
  have hκS : ∀ (r : RA LL) (k : Fin f), kap o (thR LL θ r) k ∈ (PadicComplexInt l).toSubring :=
    fun r k => (mem_OC _).2 (norm_kap_le o _ k)
  have hκ : ∀ (g : ↥(GK K)) (r : RA LL) (k : Fin f),
      kap o (thR LL θ (gRA AI LL (g : GQ l) r)) k = AI.actC (g : GQ l) (kap o (thR LL θ r) k) :=
    fun g r k => kap_thR_gRA AI o hθ _ r k
  have keyA := specPhi_abstract (R := RA LL) T (PadicComplexInt l).toSubring
    A (fun g => M (g : GQ l)) (fun g => AI.actC (g : GQ l)) (fun g => gRA AI LL (g : GQ l)) o
    (fun r k => kap o (thR LL θ r) k) (fun r => lam o A (thR LL θ r)) hL hL0 hLa hLm hal
    hmul.2.1 hκS hκ co hS hσ hcoA hcoM
  obtain ⟨Φ, hΦs, hΦS, hΦg, hΦ1⟩ := keyA
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · exact hΦs
  · intro z i
    exact (mem_OC _).1 (hΦS z i)
  · intro g z
    convert hΦg g z using 3
  · intro j
    obtain ⟨t, ht⟩ := hsingle j
    exact ⟨t, (hΦ1 t).trans ht⟩

end GlobalTheory.Cyc.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisDD
section
noncomputable section

namespace GlobalTheory.WachTensor

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts GlobalTheory.EtaleExact

section Ext

variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R] {M M' M'' : Type}
    [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] [AddCommGroup M''] [Module O M'']

theorem map_smul_alg (f : R →ₐ[O] R) (a : M →ₗ[O] M) (r : R) (x : R ⊗[O] M) :
    TensorProduct.map f.toLinearMap a (r • x) = f r • TensorProduct.map f.toLinearMap a x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [smul_add, map_add (f := _), hx, hx']
  | tmul r' u => simp [TensorProduct.smul_tmul']

end Ext

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

def Descends : Prop :=
  ∀ (ι : Type) [Fintype ι] (M : ι → ι → W.EE) (w : ι → RW),
    (∀ g : G, W.resΓ g = 1 → ∀ i, gR g (w i) = w i) →
    (∀ i, w i = ∑ j, E.ioE (M i j) * φR (w j)) → ∀ i, ∃ e : W.EE, E.ioE e = w i

theorem nontrivial_EE (W : LocWach PD LL O v n) : Nontrivial W.EE :=
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  W.EE_inj.nontrivial

theorem exists_basis_jD (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (e : Module.Basis ι W.EE (W.DD T)) :
    ∃ c : Module.Basis ι RW (TW RW T), ∀ i, c i = E.jD T (e i) := by
  classical
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  haveI := nontrivial_EE W
  haveI : Nontrivial RW := (ioE_injective E).nontrivial
  haveI := T.L.free
  have hsp : ⊤ ≤ Submodule.span RW (Set.range fun i => E.jD T (e i)) := by
    rw [← E.jD_span T, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [E.jD_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨basisOfTopLeSpanOfCardEqFinrank (fun i => E.jD T (e i)) hsp ?_,
    fun i => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) i⟩
  rw [Module.finrank_baseChange, ← (W.DD_free T).2, Module.finrank_eq_card_basis e]

include E in
theorem exists_basis_DD (T : LocLat G Qp LL O) :
    Nonempty (Module.Basis (Fin (Module.finrank O ↥T.L.T)) W.EE (W.DD T)) := by
  haveI := nontrivial_EE W
  haveI := (W.DD_free T).1
  haveI := finite_DD E T
  exact ⟨Module.finBasisOfFinrankEq _ _ (W.DD_free T).2⟩

theorem jD_fixed (T : LocLat G Qp LL O) (g : G) (hg : W.resΓ g = 1) (x : W.DD T) :
    TWact (gR g) T g (E.jD T x) = E.jD T x := by
  rw [← E.jD_act, hg, W.γD_one]

theorem exists_frob_inv (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (hφ : Function.Surjective φR) (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (e : Module.Basis ι W.EE (W.DD T)) :
    Submodule.span W.EE (Set.range fun i => W.φD T (e i)) = ⊤ := by
  refine eq_top_DD E hm T _ ?_
  obtain ⟨c, hc⟩ := exists_basis_jD E T e
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ : ∃ x, TWmap φR T x = y :=
    TensorProduct.map_surjective (g := φR.toLinearMap) hφ Function.surjective_id y
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← c.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [TWmap, map_smul_alg]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨W.φD T (e i),
    Submodule.subset_span ⟨i, rfl⟩, ?_⟩)
  rw [E.jD_φ, hc]
  rfl

theorem mem_range_jD (hd : Descends E) (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (U : ι → ι → W.EE) (z : ι → TW RW T)
    (hz : ∀ g : G, W.resΓ g = 1 → ∀ a, TWact (gR g) T g (z a) = z a)
    (hU : ∀ a, z a = ∑ b, E.ioE (U a b) • TWmap φR T (z b)) (a : ι) :
    ∃ x, E.jD T x = z a := by
  classical
  obtain ⟨e⟩ := exists_basis_DD E T
  obtain ⟨c, hc⟩ := exists_basis_jD E T e
  have h := hd (ι × Fin (Module.finrank O ↥T.L.T))
    (fun p q => U p.1 q.1 * e.repr (W.φD T (e q.2)) p.2) (fun p => c.repr (z p.1) p.2) ?_ ?_
  · choose u hu using h
    refine ⟨∑ k, u (a, k) • e k, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← c.sum_repr (z a)]
    exact Finset.sum_congr rfl fun k _ => by rw [E.jD_smul, hu, hc]
  · rintro g hg ⟨a, k⟩
    have h1 := hz g hg a
    conv_lhs at h1 => rw [← c.sum_repr (z a), map_sum]
    simp only [GlobalTheory.Cyc.Decomp.TWact_smul, hc, jD_fixed E T g hg] at h1
    simp only [← hc] at h1
    conv_rhs => rw [← h1]
    simp [Finsupp.single_apply]
  · rintro ⟨a, k⟩
    have h2 : ∀ q, TWmap φR T (c q) = ∑ r, E.ioE (e.repr (W.φD T (e q)) r) • c r := by
      intro q
      rw [hc, ← E.jD_φ]
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← e.sum_repr (W.φD T (e q)), map_sum]
      simp only [E.jD_smul, hc]
    have h3 : ∀ b, c.repr (TWmap φR T (z b)) k =
        ∑ q, E.ioE (e.repr (W.φD T (e q)) k) * φR (c.repr (z b) q) := by
      intro b
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← c.sum_repr (z b), map_sum, map_sum, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [TWmap, map_smul_alg]
      change c.repr (_ • TWmap φR T (c q)) k = _
      rw [h2, map_smul, Finsupp.smul_apply, c.repr_sum_self, smul_eq_mul, mul_comm]
    change c.repr (z a) k = _
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [hU a, map_sum, Finsupp.finsetSum_apply]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, Finsupp.smul_apply, h3, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [map_mul, mul_assoc]

theorem ioE_φE (hO : Function.Injective (algebraMap O LL)) (a : W.EE) :
    E.ioE (W.φE a) = φR (E.ioE a) := by
  obtain ⟨e, e₀, h₀, hj, -⟩ := E.one_e
  obtain ⟨e₁, he₁, hT⟩ := W.one_line
  have he₁T : e₁ ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self e₁
  have h1 : TWmap φR W.one ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by simp [TWmap]
  have h2 := E.jD_φ W.one (a • e)
  rw [W.φD_smul, E.jD_smul, E.jD_smul, E.jD_φ, hj, h1, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h2
  exact GlobalTheory.Cyc.Decomp.tmul_gen_cancel hO W.one e₁ he₁ he₁T e₀ h₀ _ _ h2

theorem ioE_γE (hO : Function.Injective (algebraMap O LL)) (g : G) (a : W.EE) :
    E.ioE (W.γE (W.resΓ g) a) = gR g (E.ioE a) := by
  obtain ⟨e, e₀, h₀, hj, -⟩ := E.one_e
  obtain ⟨e₁, he₁, hT⟩ := W.one_line
  have he₁T : e₁ ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self e₁
  have hact : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g e₀)
  have h1 : TWact (gR g) W.one g ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by
    simp [TWact, hact]
  have h2 := E.jD_act W.one g (a • e)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, hj, GlobalTheory.Cyc.Decomp.TWact_smul, h1,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at h2
  exact GlobalTheory.Cyc.Decomp.tmul_gen_cancel hO W.one e₁ he₁ he₁T e₀ h₀ _ _ h2

end Generic

end GlobalTheory.WachTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCongruenceFiltrationGaloisRep
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory

theorem congrFilt_le_all_eq_zero (l : ℕ) [hl : Fact l.Prime] (x : ℝ) (hx0 : 0 ≤ x)
    (h : ∀ k : ℕ, x ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) : x = 0 := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  by_contra hne
  have hpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hne)
  have hinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hpos hinv
  have h1 : (l : ℝ) ^ (-((k : ℤ) + 2)) ≤ (l : ℝ) ^ (-(k : ℤ)) :=
    zpow_le_zpow_right₀ hl1.le (by omega)
  have h2 : (l : ℝ) ^ (-(k : ℤ)) = ((l : ℝ)⁻¹) ^ k := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  linarith [h k]

theorem congrFiltration : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]), (∀ i j, Continuous fun g => (ρ g : Matrix n n ℚ_[l]) i j) → ∃ N : ℕ → Subgroup ↥(GK K), (∀ k g, g ∈ N k ↔ ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) ∧ Antitone N ∧ (∀ k, IsOpen (N k : Set ↥(GK K))) ∧ (∀ k g, g ∈ N k → g ^ l ∈ N (k + 1)) ∧ (∀ k g, g ∈ N 0 → g ^ l ∈ N (k + 1) → g ∈ N k) ∧ ∀ g, (∀ k, g ∈ N k) → ρ g = 1 := by
  intro l _ n _ _ K ρ hcont
  obtain ⟨Γ, hΓ⟩ := _root_.GlobalTheory.congruenceSubgroups_GL_padic l n
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  have hmem : ∀ k g, g ∈ (Γ k).comap ρ ↔ ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
    intro k g
    rw [Subgroup.mem_comap, hΓ]
  refine ⟨fun k => (Γ k).comap ρ, hmem, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab g hg
    rw [hmem] at hg ⊢
    intro i j
    have hab' : (a : ℤ) ≤ b := by exact_mod_cast hab
    exact le_trans (hg i j) (zpow_le_zpow_right₀ hl1 (by omega))
  · intro k
    have hset : (((Γ k).comap ρ : Subgroup ↥(GK K)) : Set ↥(GK K)) =
        ⋂ i, ⋂ j, (fun g => ((ρ g : Matrix n n ℚ_[l]) - 1) i j) ⁻¹'
          Metric.closedBall (0 : ℚ_[l]) ((l : ℝ) ^ (-((k : ℤ) + 2))) := by
      ext g
      simp only [SetLike.mem_coe, hmem, Set.mem_iInter, Set.mem_preimage, mem_closedBall_zero_iff]
    rw [hset]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    have hc : Continuous fun g => ((ρ g : Matrix n n ℚ_[l]) - 1) i j := by
      simp only [Matrix.sub_apply]
      exact (hcont i j).sub continuous_const
    exact (IsUltrametricDist.isOpen_closedBall (0 : ℚ_[l])
      (zpow_pos (by linarith) _).ne').preimage hc
  · intro k g hg
    rw [hmem] at hg ⊢
    have := _root_.GlobalTheory.pow_prime_sub_one_norm_le l n (ρ g : Matrix n n ℚ_[l]) k hg
    simpa [map_pow, Units.val_pow_eq_pow_val] using this
  · intro k g h0 hk
    rw [hmem] at h0 hk ⊢
    have h0' : ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-2 : ℤ) := by
      simpa using h0
    have hk' : ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) := by
      simpa [map_pow, Units.val_pow_eq_pow_val] using hk
    exact _root_.GlobalTheory.matrix_near_one_pow_prime_deep l n _ k h0' hk'
  · intro g hg
    apply Units.ext
    ext i j
    have hz : ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ = 0 :=
      congrFilt_le_all_eq_zero l _ (norm_nonneg _) fun k => (hmem k g).1 (hg k) i j
    rw [norm_eq_zero, Matrix.sub_apply, sub_eq_zero] at hz
    simpa using hz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weak_topology_witt_tilt_tensor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ Continuous (fun p : ↥(GK K) × TW (RW LL) T => TWact (AI.gRW LL (p.1 : GQ l)) T p.1 p.2) ∧ Topology.IsEmbedding (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ CompactSpace ↥T.L.T ∧ ∀ U ∈ nhds (0 : ↥T.L.T), ∃ k : ℕ, ∀ t : ↥T.L.T, l ^ k • t ∈ U := by
  first | exact @GlobalTheory.WeakTop.exists_weakTop | exact GlobalTheory.WeakTop.exists_weakTop | (intros; apply GlobalTheory.WeakTop.exists_weakTop <;> assumption)
end

