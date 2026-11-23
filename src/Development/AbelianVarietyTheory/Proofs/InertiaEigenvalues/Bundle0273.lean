module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrderPreservingPowerHomAlgClosurePrimeFiel
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.PowAut

theorem exists_coprime_lift (N k a : ℕ) (hN : 0 < N) (hk : 0 < k) (ha : a.Coprime N) :
    ∃ b : ℕ, b.Coprime (N * k) ∧ b ≡ a [MOD N] := by
  haveI : NeZero (N * k) := ⟨(Nat.mul_pos hN hk).ne'⟩
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (Dvd.intro k rfl : N ∣ N * k)
    (ZMod.unitOfCoprime a ha)
  refine ⟨(u : ZMod (N * k)).val, ZMod.val_coe_unit_coprime u, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  have h := congrArg (fun v : (ZMod N)ˣ => (v : ZMod N)) hu
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply,
    ZMod.coe_unitOfCoprime] at h
  rw [← h, ZMod.natCast_val]

theorem exists_exponents (M n : ℕ) (hM : 0 < M) (hn : n.Coprime M) :
    ∃ a : ℕ → ℕ, a 0 = n ∧ (∀ j, (a j).Coprime (M * j.factorial)) ∧
      ∀ i j, i ≤ j → a j ≡ a i [MOD M * i.factorial] := by
  have step : ∀ j : ℕ, ∀ a : {a : ℕ // a.Coprime (M * j.factorial)},
      ∃ b : {b : ℕ // b.Coprime (M * (j + 1).factorial)}, b.1 ≡ a.1 [MOD M * j.factorial] := by
    intro j a
    obtain ⟨b, hb, hb'⟩ := exists_coprime_lift (M * j.factorial) (j + 1) a.1
      (Nat.mul_pos hM j.factorial_pos) j.succ_pos a.2
    refine ⟨⟨b, ?_⟩, hb'⟩
    rw [Nat.factorial_succ, mul_comm (j + 1), ← mul_assoc]
    exact hb
  choose f hf using step
  let s : ∀ j : ℕ, {a : ℕ // a.Coprime (M * j.factorial)} := fun j =>
    Nat.rec (motive := fun j => {a : ℕ // a.Coprime (M * j.factorial)})
      ⟨n, by simpa using hn⟩ f j
  have hs : ∀ j, s (j + 1) = f j (s j) := fun j => rfl
  refine ⟨fun j => (s j).1, rfl, fun j => (s j).2, ?_⟩
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact Nat.ModEq.refl _
  | succ j hij ih =>
    have h1 : (s (j + 1)).1 ≡ (s j).1 [MOD M * j.factorial] := by rw [hs]; exact hf j (s j)
    exact (h1.of_dvd (Nat.mul_dvd_mul_left M (Nat.factorial_dvd_factorial hij))).trans ih

theorem orderOf_pos_of_ne_zero (g : ℕ) [Fact g.Prime] (x : AlgebraicClosure (ZMod g))
    (hx : x ≠ 0) : 0 < orderOf x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  haveI := Fintype.ofFinite (IntermediateField.adjoin (ZMod g) {x})
  let y : IntermediateField.adjoin (ZMod g) {x} :=
    ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have h1 := FiniteField.pow_card_sub_one_eq_one y hy
  have h2 : x ^ (Fintype.card (IntermediateField.adjoin (ZMod g) {x}) - 1) = 1 :=
    congrArg Subtype.val h1
  exact orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨_, Nat.sub_pos_of_lt Fintype.one_lt_card, h2⟩)

theorem exists_powHom {K : Type*} [Field K] (hK : ∀ x : K, x ≠ 0 → 0 < orderOf x)
    (M n : ℕ) (hM : 0 < M) (hn : n.Coprime M) :
    ∃ θ : K →* K, Function.Injective θ ∧ (∀ x, orderOf (θ x) = orderOf x) ∧
      ∀ x, x ^ M = 1 → θ x = x ^ n := by
  classical
  obtain ⟨a, ha0, hac, ha⟩ := exists_exponents M n hM hn
  let t : K → K := fun x => if x = 0 then 0 else x ^ a (orderOf x)
  have t0 : t 0 = 0 := if_pos rfl
  have ht : ∀ x : K, x ≠ 0 → ∀ j, orderOf x ≤ j → t x = x ^ a j := by
    intro x hx j hj
    have : t x = x ^ a (orderOf x) := if_neg hx
    rw [this]
    have h := (ha _ _ hj).of_dvd
      (Dvd.dvd.mul_left (Nat.dvd_factorial (hK x hx) le_rfl) M)
    rw [← pow_mod_orderOf x (a j), ← pow_mod_orderOf x (a (orderOf x)), h]
  let θ : K →* K :=
    { toFun := t
      map_one' := by rw [ht 1 one_ne_zero _ le_rfl, one_pow]
      map_mul' := by
        intro x y
        by_cases hx : x = 0
        · rw [hx, zero_mul, t0, zero_mul]
        by_cases hy : y = 0
        · rw [hy, mul_zero, t0, mul_zero]
        rw [ht x hx (orderOf x + orderOf y + orderOf (x * y)) (by omega),
          ht y hy (orderOf x + orderOf y + orderOf (x * y)) (by omega),
          ht _ (mul_ne_zero hx hy) (orderOf x + orderOf y + orderOf (x * y)) (by omega),
          mul_pow] }
  have hθ : ∀ x, θ x = t x := fun _ => rfl
  have hord : ∀ x, orderOf (θ x) = orderOf x := by
    intro x
    by_cases hx : x = 0
    · rw [hθ, hx, t0]
    rw [hθ, ht x hx _ le_rfl]
    exact Nat.Coprime.orderOf_pow ((hac (orderOf x)).coprime_dvd_right
      (Dvd.dvd.mul_left (Nat.dvd_factorial (hK x hx) le_rfl) M)).symm
  have hne : ∀ x : K, x ≠ 0 → θ x ≠ 0 := by
    intro x hx
    rw [hθ, ht x hx _ le_rfl]
    exact pow_ne_zero _ hx
  refine ⟨θ, ?_, hord, ?_⟩
  · intro x y hxy
    by_cases hy : y = 0
    · by_contra h
      exact hne x (hy ▸ h) (by rw [hxy, hy, hθ, t0])
    have h1 : θ (x * y⁻¹) * θ y = 1 * θ y := by
      rw [← map_mul, inv_mul_cancel_right₀ hy, one_mul, hxy]
    have h2 := mul_right_cancel₀ (hne y hy) h1
    have h3 : orderOf (x * y⁻¹) = 1 := by rw [← hord, h2, orderOf_one]
    rw [orderOf_eq_one_iff, mul_inv_eq_one₀ hy] at h3
    exact h3
  · intro x hxM
    have hx : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hM.ne'] at hxM
      exact zero_ne_one hxM
    have h := (ha 0 (orderOf x) (Nat.zero_le _)).of_dvd
      (Dvd.dvd.mul_right (orderOf_dvd_of_pow_eq_one hxM) _)
    rw [hθ, ht x hx _ le_rfl, ← ha0, ← pow_mod_orderOf x (a 0),
      ← pow_mod_orderOf x (a (orderOf x)), h]

theorem exists_powHom_fbar : ∀ (g : ℕ) [Fact g.Prime] (M n : ℕ), 0 < M → n.Coprime M →
    ∃ θ : Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar g, Function.Injective θ ∧
      (∀ x, orderOf (θ x) = orderOf x) ∧ ∀ x, x ^ M = 1 → θ x = x ^ n :=
  fun g _ M n hM hn => exists_powHom (orderOf_pos_of_ne_zero g) M n hM hn

end GlobalTheory.PowAut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableTensorPairingOfDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon.StPairing

section

variable {F : Type} [Field F] {B : Type} [CommRing B] [Algebra F B]
  {V V' : Type} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']

def tensorPairing (m : V →ₗ[F] V' →ₗ[F] F) : V ⊗[F] B →ₗ[F] V' ⊗[F] B →ₗ[F] B :=
  (TensorProduct.map₂ m (LinearMap.mul F B)).compr₂ (TensorProduct.lid F B).toLinearMap

@[simp] theorem tensorPairing_tmul (m : V →ₗ[F] V' →ₗ[F] F) (v : V) (a : B) (v' : V') (b : B) :
    tensorPairing m (v ⊗ₜ[F] a) (v' ⊗ₜ[F] b) = m v v' • (a * b) := by
  simp [tensorPairing, TensorProduct.map₂_apply_tmul]

theorem tensorPairing_one (m : V →ₗ[F] V' →ₗ[F] F) (v : V) (y : V' ⊗[F] B) :
    tensorPairing m (v ⊗ₜ[F] (1 : B)) y = TensorProduct.lid F B (LinearMap.rTensor B (m v) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b => simp [tensorPairing_tmul]
  | add y y' hy hy' => simp only [map_add (f := _), hy, hy']

theorem induction_two {p : V ⊗[F] B → V' ⊗[F] B → Prop} (h0 : ∀ y, p 0 y) (h0' : ∀ x, p x 0)
    (ht : ∀ v a v' b, p (v ⊗ₜ[F] a) (v' ⊗ₜ[F] b))
    (ha : ∀ x x' y, p x y → p x' y → p (x + x') y)
    (ha' : ∀ x y y', p x y → p x y' → p x (y + y')) (x : V ⊗[F] B) (y : V' ⊗[F] B) : p x y := by
  induction x using TensorProduct.induction_on with
  | zero => exact h0 y
  | tmul v a =>
    induction y using TensorProduct.induction_on with
    | zero => exact h0' _
    | tmul v' b => exact ht v a v' b
    | add y y' hy hy' => exact ha' _ _ _ hy hy'
  | add x x' hx hx' => exact ha _ _ _ hx hx'

end

theorem exists_stPairing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → ∃ pr : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] Bst P, (∀ x y, pr (phiV P ℚ_[l] V x) (phiV P ℚ_[l] V' y) = phiSt P (pr x y)) ∧ (∀ x y, pr (monV P ℚ_[l] V x) y + pr x (monV P ℚ_[l] V' y) = monSt P (pr x y)) ∧ (∀ (g : ↥(GK K)) x y, pr (stRep P ρ g x) (stRep P ρ' g y) = ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) • actSt P (g : GQ l) (pr x y)) ∧ (∀ a x y, pr (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x) y = a * pr x y) ∧ ∀ y, (∀ v : V, pr (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) y = 0) → y = 0 := by
  intro l _ P K V _ _ _ V' _ _ _ ρ ρ' m hm
  obtain ⟨hg, -, hr, -⟩ := hm
  have hcyc : ∀ g : ↥(GK K), ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) =
      ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) := fun g => by
    have h := P.PD_χ K g
    simp [cycLL, h]
  refine ⟨tensorPairing m, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    refine induction_two (p := fun x y => tensorPairing m (phiV P ℚ_[l] V x) (phiV P ℚ_[l] V' y) =
      phiSt P (tensorPairing m x y)) (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v a v' b
      simp [tensorPairing_tmul, map_mul, map_smul]
    · intro x x' y hx hx'
      simp only [map_add (f := _), LinearMap.add_apply, hx, hx']
    · intro x y y' hy hy'
      simp only [map_add (f := _), hy, hy']
  · intro x y
    refine induction_two (p := fun x y => tensorPairing m (monV P ℚ_[l] V x) y +
      tensorPairing m x (monV P ℚ_[l] V' y) = monSt P (tensorPairing m x y)) (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v a v' b
      simp only [monV_tmul, tensorPairing_tmul]
      rw [map_smul, ← smul_add]
      congr 1
      simp only [monSt_apply, Polynomial.derivative_mul]
      ring
    · intro x x' y hx hx'
      simp only [map_add (f := _), LinearMap.add_apply, ← hx, ← hx']
      abel
    · intro x y y' hy hy'
      simp only [map_add (f := _), ← hy, ← hy']
      abel
  · intro g x y
    refine induction_two (p := fun x y => tensorPairing m (stRep P ρ g x) (stRep P ρ' g y) =
      ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) • actSt P (g : GQ l) (tensorPairing m x y))
      (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v a v' b
      rw [stRep_tmul, stRep_tmul, tensorPairing_tmul, tensorPairing_tmul, hg, hcyc, map_smul, map_mul,
        smul_smul]
    · intro x x' y hx hx'
      simp only [map_add (f := _), LinearMap.add_apply, hx, hx', smul_add]
    · intro x y y' hy hy'
      simp only [map_add (f := _), hy, hy', smul_add]
  · intro a x y
    refine induction_two (p := fun x y => tensorPairing m (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x) y =
      a * tensorPairing m x y) (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v b v' c
      rw [onB_tmul, tensorPairing_tmul, tensorPairing_tmul, LinearMap.mulLeft_apply, mul_smul_comm,
        mul_assoc]
    · intro x x' y hx hx'
      simp only [map_add (f := _), LinearMap.add_apply, hx, hx', mul_add]
    · intro x y y' hy hy'
      simp only [map_add (f := _), hy, hy', mul_add]
  · intro y hy
    refine _root_.GlobalTheory.rTensor_pairing_eq_zero_of_flip_injective ℚ_[l] (Bst P) V V' m hr y fun v => ?_
    rw [← tensorPairing_one]
    exact hy v

end GlobalTheory.PMon.StPairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesLimitLatStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_series_limit_Lat_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (M : ℕ) (c : ℕ → P.R.BdR), (∀ k, c k ∈ FilB P 0) → (∀ n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, c k ∈ Lat AI M n) → ∃ b ∈ FilB P 0, ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀, b - ∑ k ∈ Finset.range R, c k ∈ Lat AI M n := by
  first | exact @GlobalTheory.ExpImage.exists_series_limit_Lat | exact GlobalTheory.ExpImage.exists_series_limit_Lat | (intros; apply GlobalTheory.ExpImage.exists_series_limit_Lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableLatticeCompactGroupStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_lattice_compact_group : ∀ {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {Qp LL O : Type} [Field Qp] [TopologicalSpace Qp] [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O → ∀ (A : GRep G Qp LL O), Nonempty (Lattice (O := O) A.ρ) := by
  first | exact @GlobalTheory.StableLat.exists_lattice | exact GlobalTheory.StableLat.exists_lattice | (intros; apply GlobalTheory.StableLat.exists_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateTwistDualPerfectPairing
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

noncomputable section
namespace GlobalTheory.DualTwist

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l)
  {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]

def dualEquiv : (Fin (finrank ℚ_[l] V) → ℚ_[l]) ≃ₗ[ℚ_[l]] Module.Dual ℚ_[l] V :=
  (Module.finBasis ℚ_[l] V).dualBasis.equivFun.symm

theorem dualEquiv_basis (z : Fin (finrank ℚ_[l] V) → ℚ_[l]) (i : Fin (finrank ℚ_[l] V)) :
    dualEquiv z (Module.finBasis ℚ_[l] V i) = z i := by
  simp [dualEquiv, Basis.equivFun_symm_apply, Finset.sum_apply, Basis.dualBasis_apply_self, Finsupp.single_apply]

theorem dualEquiv_symm_apply (f : Module.Dual ℚ_[l] V) (i : Fin (finrank ℚ_[l] V)) :
    (dualEquiv (V := V)).symm f i = f (Module.finBasis ℚ_[l] V i) := by
  conv_rhs => rw [← (dualEquiv (V := V)).apply_symm_apply f]
  rw [dualEquiv_basis]

def chiS (g : ↥(GK K)) : ℚ_[l] := ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])

theorem chiS_mul (g h : ↥(GK K)) : chiS P K (g * h) = chiS P K g * chiS P K h := by
  simp [chiS]

theorem chiS_one : chiS P K 1 = 1 := by simp [chiS]

def dualOp (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) :
    (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) where
  toFun y := chiS P K g • (dualEquiv (V := V)).symm ((dualEquiv y).comp (ρ g⁻¹))
  map_add' y z := by simp [LinearMap.add_comp, smul_add]
  map_smul' c y := by simp [LinearMap.smul_comp, smul_comm c]

theorem dualEquiv_dualOp (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) (y) :
    dualEquiv (dualOp P K ρ g y) = chiS P K g • (dualEquiv y).comp (ρ g⁻¹) := by
  simp [dualOp]

def dualRep (ρ : Representation ℚ_[l] ↥(GK K) V) :
    Representation ℚ_[l] ↥(GK K) (Fin (finrank ℚ_[l] V) → ℚ_[l]) where
  toFun g := dualOp P K ρ g
  map_one' := by
    refine LinearMap.ext fun y => ?_
    apply (dualEquiv (V := V)).injective
    rw [dualEquiv_dualOp]
    simp [chiS_one, Module.End.one_eq_id]
  map_mul' g h := by
    refine LinearMap.ext fun y => ?_
    apply (dualEquiv (V := V)).injective
    rw [Module.End.mul_apply, dualEquiv_dualOp, dualEquiv_dualOp, dualEquiv_dualOp, chiS_mul,
      mul_inv_rev, map_mul, Module.End.mul_eq_comp, LinearMap.smul_comp, smul_smul, LinearMap.comp_assoc]

def dualPair : V →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] ℚ_[l] :=
  (dualEquiv (V := V)).toLinearMap.flip

theorem dualPair_apply (x : V) (y : Fin (finrank ℚ_[l] V) → ℚ_[l]) : dualPair x y = dualEquiv y x := rfl

end GlobalTheory.DualTwist

namespace GlobalTheory.DualTwist
variable {l : ℕ} [Fact l.Prime]

theorem chiS_eq (P : LocPrime l) (K : FinExt l) (g : ↥(GK K)) :
    chiS P K g = (P.χQ (g : GQ l) : ℚ_[l]) := by
  simp [chiS, cycLL, P.PD_χ]

theorem chiS_cont (P : LocPrime l) (K : FinExt l) : Continuous (chiS P K) := by
  have h : chiS P K = fun g : ↥(GK K) => (P.χQ (g : GQ l) : ℚ_[l]) := funext (chiS_eq P K)
  rw [h]
  exact (GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc).comp continuous_subtype_val

theorem exists_dual1 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → ∃ (ρ' : Representation ℚ_[l] ↥(GK K) (Fin (finrank ℚ_[l] V) → ℚ_[l])) (m : V →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] ℚ_[l]), (∀ y, Continuous fun g => ρ' g y) ∧ IsDual1 (P.PD K) ρ ρ' m := by
  intro l _ P K V _ _ _ _ _ _ _ ρ hc
  refine ⟨dualRep P K ρ, dualPair, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    apply continuous_pi
    intro i
    have h : (fun g : ↥(GK K) => dualRep P K ρ g y i) =
        fun g => chiS P K g * dualEquiv y (ρ g⁻¹ (Module.finBasis ℚ_[l] V i)) := by
      funext g
      change dualOp P K ρ g y i = _
      simp [dualOp, dualEquiv_symm_apply]
    rw [h]
    have hy : Continuous (dualEquiv (V := V) y) :=
      IsModuleTopology.continuous_of_linearMap (dualEquiv (V := V) y)
    exact (chiS_cont P K).mul (hy.comp ((hc _).comp continuous_inv))
  · intro g x y
    change dualEquiv (dualOp P K ρ g y) (ρ g x) = chiS P K g * dualEquiv y x
    rw [dualEquiv_dualOp, LinearMap.smul_apply, LinearMap.comp_apply, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, smul_eq_mul]
  · intro x hx
    apply (Module.finBasis ℚ_[l] V).forall_coord_eq_zero_iff.mp
    intro i
    have := hx ((dualEquiv (V := V)).symm ((Module.finBasis ℚ_[l] V).coord i))
    rwa [dualPair_apply, LinearEquiv.apply_symm_apply] at this
  · intro y hy
    funext i
    exact (dualEquiv_basis y i).symm.trans (hy _)
  · simp

end GlobalTheory.DualTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFilZeroSurjective
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ThetaFil

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

def fil0 : Subring P.R.BdR :=
  (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)).range.comap T.eD.toRingHom

theorem mem_deRhamFilZeroSubringPreimage_iff (x : P.R.BdR) : x ∈ fil0 T ↔ x ∈ Fil P 0 := by
  change (∃ z, algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) z = T.eD x) ↔ _
  exact (GlobalTheory.ThetaTie.fil_zero T x).symm

def theta : ↥(fil0 T) →+* ℂ_[l] where
  toFun x := (GlobalTheory.ThetaTie.thetaL T).θ x
  map_one' := (GlobalTheory.ThetaTie.thetaL T).θ_one
  map_mul' x y := (GlobalTheory.ThetaTie.thetaL T).θ_mul _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 x.2) _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 y.2)
  map_zero' := by
    have h0 : (0 : P.R.BdR) ∈ Fil P 0 := (mem_deRhamFilZeroSubringPreimage_iff T 0).1 (zero_mem _)
    have h := (GlobalTheory.ThetaTie.thetaL T).θ_add _ h0 _ h0
    rw [add_zero] at h
    change (GlobalTheory.ThetaTie.thetaL T).θ 0 = 0
    exact left_eq_add.1 h
  map_add' x y := (GlobalTheory.ThetaTie.thetaL T).θ_add _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 x.2) _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 y.2)

theorem theta_apply (x : ↥(fil0 T)) : theta T x = (GlobalTheory.ThetaTie.thetaL T).θ x := rfl

theorem act_mem (g : GQ l) (x : P.R.BdR) (hx : x ∈ fil0 T) : P.actQdR g x ∈ fil0 T := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨Formalism.Per.σDp g a, ?_⟩
  change _ = T.eD (P.actQdR g x)
  rw [T.actD]
  change _ = Formalism.Per.σD g (T.eD x)
  have ha' : algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) a = T.eD x := ha
  rw [← ha']
  exact (GlobalTheory.MemLoc.ActLaws.σD_alg g a).symm

end GlobalTheory.PMon.ThetaFil

namespace GlobalTheory.PMon


open GlobalTheory.PMon.ThetaFil in
theorem exists_theta_deRhamFilZero_surjective_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ Function.Surjective θ ∧
      (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧
      (∀ y : Om l, ∃ h, θ ⟨algebraMap (Om l) P.R.BdR y, h⟩ = (y : ℂ_[l])) ∧
      ∀ (g : GQ l) (x : ↥S), ∃ h, θ ⟨P.actQdR g x, h⟩ = Formalism.Per.σC g (θ x) := by
  intro l _ P AI T
  refine ⟨fil0 T, theta T, mem_deRhamFilZeroSubringPreimage_iff T, ?_, ?_, ?_, ?_⟩
  · intro c
    obtain ⟨x, hx, e⟩ := (GlobalTheory.ThetaTie.thetaL T).θ_onto c
    exact ⟨⟨x, (mem_deRhamFilZeroSubringPreimage_iff T x).2 hx⟩, e⟩
  · intro x
    exact (GlobalTheory.ThetaTie.thetaL T).θ_ker _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 x.2)
  · intro y
    obtain ⟨z, h1, -⟩ := T.om y
    exact ⟨⟨z, h1.symm⟩, (GlobalTheory.ThetaTie.thetaL T).θ_Om y⟩
  · intro g x
    refine ⟨act_mem T g x x.2, ?_⟩
    rw [theta_apply, theta_apply, (GlobalTheory.ThetaTie.thetaL T).θ_act g _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 x.2)]
    exact GlobalTheory.ThetaTie.actC_eq AI g _

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIndexOfIsOpenAbsGaloisFinExt
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory.OpenFiniteIndex

theorem compactSpace_fixing (l : ℕ) [Fact l.Prime] (K : FinExt l) : CompactSpace ↥(GK K) := by
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  have hc : IsClosed ((K.1.fixingSubgroup : Subgroup (GQ l)) : Set (GQ l)) :=
    IntermediateField.fixingSubgroup_isClosed K.1
  exact isCompact_iff_compactSpace.mp hc.isCompact

theorem finiteIndex_of_isOpen : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (H : Subgroup ↥(GK K)),
    IsOpen (H : Set ↥(GK K)) → H.FiniteIndex := by
  intro l _ K H hH
  haveI := compactSpace_fixing l K
  haveI : Finite (↥(GK K) ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  exact Subgroup.finiteIndex_of_finite_quotient

end GlobalTheory.OpenFiniteIndex
end

