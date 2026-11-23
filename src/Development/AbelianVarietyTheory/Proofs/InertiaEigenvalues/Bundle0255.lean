module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0204
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0237
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneWittTensorLatticeSurjectiveFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.WittTensorFixed

theorem tensor_flat {R W T : Type} [CommRing R] [CommRing W] [Algebra R W] [AddCommGroup T]
    [Module R T] [Module.Flat R T] (f : W →ₐ[R] W) (hs : ∀ y, ∃ b, f b - b = y)
    (hk : ∀ b, f b = b → ∃ z, b = algebraMap R W z)
    (hi : Function.Injective (algebraMap R W)) :
    (∀ y : W ⊗[R] T, ∃ b, TensorProduct.map f.toLinearMap LinearMap.id b - b = y) ∧
    (∀ b : W ⊗[R] T, TensorProduct.map f.toLinearMap LinearMap.id b = b ↔
      ∃ t : T, b = (1 : W) ⊗ₜ[R] t) ∧
    Function.Injective (fun t : T => (1 : W) ⊗ₜ[R] t) := by

  let g : W →ₗ[R] W := f.toLinearMap - LinearMap.id
  let i : R →ₗ[R] W := Algebra.linearMap R W
  have key : ∀ b : W ⊗[R] T,
      TensorProduct.map f.toLinearMap LinearMap.id b - b = g.rTensor T b := by
    intro b
    simp only [g, LinearMap.rTensor_sub, LinearMap.rTensor_id, LinearMap.sub_apply,
      LinearMap.id_apply]
    rfl
  have gsurj : Function.Surjective g := fun y => by
    obtain ⟨b, hb⟩ := hs y
    exact ⟨b, by simpa [g] using hb⟩
  have hex : Function.Exact i g := by
    intro y
    constructor
    · intro hy
      have hfy : f y = y := by
        have h2 : f y - y = 0 := by simpa [g] using hy
        exact sub_eq_zero.mp h2
      obtain ⟨z, rfl⟩ := hk y hfy
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      simp [g, i]
  have hexT := rTensor_exact T hex gsurj
  have emb : ∀ t : T, (1 : W) ⊗ₜ[R] t = i.rTensor T ((1 : R) ⊗ₜ[R] t) := by
    intro t
    simp [i]
  have hrange : ∀ x : R ⊗[R] T, i.rTensor T x = (1 : W) ⊗ₜ[R] TensorProduct.lid R T x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r t =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, i, Algebra.linearMap_apply]
      rw [Algebra.algebraMap_eq_smul_one (A := W) r, TensorProduct.smul_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, TensorProduct.tmul_add]
  refine ⟨fun y => ?_, fun b => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := LinearMap.rTensor_surjective T gsurj y
    exact ⟨b, by rw [key]; exact hb⟩
  · have hiff : TensorProduct.map f.toLinearMap LinearMap.id b = b ↔ g.rTensor T b = 0 := by
      rw [← key, sub_eq_zero]
    rw [hiff, hexT]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨TensorProduct.lid R T x, hrange x⟩
    · rintro ⟨t, rfl⟩
      exact ⟨(1 : R) ⊗ₜ t, (emb t).symm⟩
  · have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := T) i hi
    intro t t' h
    have h' : i.rTensor T ((1 : R) ⊗ₜ[R] t) = i.rTensor T ((1 : R) ⊗ₜ[R] t') := by
      rw [← emb, ← emb]
      exact h
    simpa using congrArg (TensorProduct.lid R T) (hinj h')

theorem baseChange_flat {R W O : Type} [CommRing R] [CommRing W] [Algebra R W] [CommRing O]
    [Algebra R O] [Module.Flat R O] (f : W →ₐ[R] W) (hs : ∀ y, ∃ b, f b - b = y)
    (hk : ∀ b, f b = b → ∃ z, b = algebraMap R W z)
    (hi : Function.Injective (algebraMap R W)) :
    (∀ y : O ⊗[R] W, ∃ b, Algebra.TensorProduct.map (AlgHom.id O O) f b - b = y) ∧
    (∀ b : O ⊗[R] W, Algebra.TensorProduct.map (AlgHom.id O O) f b = b →
      ∃ z, b = algebraMap O (O ⊗[R] W) z) ∧
    Function.Injective (algebraMap O (O ⊗[R] W)) := by

  let g : W →ₗ[R] W := f.toLinearMap - LinearMap.id
  let i : R →ₗ[R] W := Algebra.linearMap R W
  have key : ∀ b : O ⊗[R] W,
      Algebra.TensorProduct.map (AlgHom.id O O) f b - b = g.lTensor O b := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul o w => simp [g, TensorProduct.tmul_sub]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), ← hx, ← hy]; abel
  have gsurj : Function.Surjective g := fun y => by
    obtain ⟨b, hb⟩ := hs y
    exact ⟨b, by simpa [g] using hb⟩
  have hex : Function.Exact i g := by
    intro y
    constructor
    · intro hy
      have hfy : f y = y := by
        have h2 : f y - y = 0 := by simpa [g] using hy
        exact sub_eq_zero.mp h2
      obtain ⟨z, rfl⟩ := hk y hfy
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      simp [g, i]
  have hexT := lTensor_exact O hex gsurj
  have emb : ∀ z : O, algebraMap O (O ⊗[R] W) z = i.lTensor O (z ⊗ₜ[R] (1 : R)) := by
    intro z
    simp [i]
  have hrange : ∀ x : O ⊗[R] R,
      i.lTensor O x = algebraMap O (O ⊗[R] W) (TensorProduct.rid R O x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, i, Algebra.linearMap_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
      rw [Algebra.algebraMap_eq_smul_one (A := W) r, ← TensorProduct.smul_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  refine ⟨fun y => ?_, fun b hb => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := LinearMap.lTensor_surjective O gsurj y
    exact ⟨b, by rw [key]; exact hb⟩
  · have h0 : g.lTensor O b = 0 := by rw [← key, hb, sub_self]
    obtain ⟨x, rfl⟩ := (hexT b).mp h0
    exact ⟨TensorProduct.rid R O x, hrange x⟩
  · have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := O) i hi
    intro z z' h
    rw [emb, emb] at h
    simpa using congrArg (TensorProduct.rid R O) (hinj h)

theorem algebraMap_WCb_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (algebraMap ℤ_[l] (WCb l)) := by

  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hker : RingHom.ker (algebraMap ℤ_[l] (WCb l)) ≠ ⊥ := by
    intro h
    apply hne
    have hxk : x ∈ RingHom.ker (algebraMap ℤ_[l] (WCb l)) := hx
    rw [h] at hxk
    exact (Submodule.mem_bot _).mp hxk
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hmem : (l : ℤ_[l]) ^ n ∈ RingHom.ker (algebraMap ℤ_[l] (WCb l)) := by
    rw [hn]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [RingHom.mem_ker, map_pow, map_natCast] at hmem
  exact pow_ne_zero n (WittVector.p_nonzero l (Cb l)) hmem

theorem flat_lattice {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsDomain O]
    [IsBezout O] (hO : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) :
    Module.Flat O ↥T.L.T := by

  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_torsion_iff] at hx
  obtain ⟨⟨a, ha⟩, hax⟩ := hx
  have hax' : a • x = 0 := hax
  rw [Submodule.mem_bot]
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hLL : algebraMap O LL a ≠ 0 := fun h => ha0 (hO (by rw [h, map_zero]))
  have hx0 : (algebraMap O LL a) • (x : T.V) = 0 := by
    rw [algebraMap_smul, ← Submodule.coe_smul, hax']
    rfl
  exact Subtype.ext ((smul_eq_zero.mp hx0).resolve_left hLL)

theorem lattice_fixed {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsDomain O]
    [IsBezout O] (hO : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O)
    {R : Type} [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (hs : ∀ y, ∃ b, f b - b = y)
    (hk : ∀ b, f b = b → ∃ z, b = algebraMap O R z)
    (hi : Function.Injective (algebraMap O R)) :
    (∀ y : TW R T, ∃ b, TWmap f T b - b = y) ∧
    (∀ b : TW R T, TWmap f T b = b ↔ ∃ t : ↥T.L.T, b = (1 : R) ⊗ₜ[O] t) ∧
    Function.Injective (fun t : ↥T.L.T => (1 : R) ⊗ₜ[O] t) := by
  haveI := flat_lattice hO T
  unfold TW TWmap
  exact tensor_flat f hs hk hi

theorem ring_fixed (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    (∀ y : RW LL, ∃ b, φRW LL b - b = y) ∧
    (∀ b : RW LL, φRW LL b = b → ∃ z, b = algebraMap ↥(OL LL) (RW LL) z) ∧
    Function.Injective (algebraMap ↥(OL LL) (RW LL)) := by
  obtain ⟨_, -, -, -, hfree, -, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  haveI : Module.Flat ℤ_[l] ↥(OL LL) := Module.Flat.of_free
  obtain ⟨hs, hk, -⟩ := GlobalTheory.ArtinSchreierWitt.main l
  unfold RW φRW
  exact baseChange_flat (frobW l) hs hk (algebraMap_WCb_injective l)


set_option maxHeartbeats 1600000 in
theorem main : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∀ y : TW (RW LL) T, ∃ b, TWmap (φRW LL) T b - b = y) ∧ (∀ b : TW (RW LL) T, TWmap (φRW LL) T b = b ↔ ∃ t : ↥T.L.T, b = (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ Function.Injective (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) := by
  intro l _ K LL T
  obtain ⟨hdvr, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := fun a b h => Subtype.ext h
  obtain ⟨hs, hk, hi⟩ := ring_fixed l LL
  exact lattice_fixed hO T (φRW LL) hs hk hi

end GlobalTheory.WittTensorFixed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodOfComplete
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl.LAdic

def Good (p : ℕ) (R : Type) [CommRing R] : Prop :=
  (∀ x : R, (p : R) * x = 0 → x = 0) ∧ (∀ x : R, (∀ k : ℕ, ∃ r, x = (p : R) ^ k * r) → x = 0) ∧
    ∀ x : ℕ → R, ∃ s, ∀ k : ℕ, ∃ r, s - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r

theorem good_of_complete (p : ℕ) (R : Type) [CommRing R] (h : ∀ x : R, (p : R) * x = 0 → x = 0)
    [hc : IsAdicComplete (Ideal.span {(p : R)}) R] : Good p R := by
  have mem : ∀ (k : ℕ) (x : R), x ∈ (Ideal.span {(p : R)} ^ k • ⊤ : Submodule R R) ↔
      ∃ r, x = (p : R) ^ k * r := by
    intro k x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rfl
  refine ⟨h, fun x hx => ?_, fun x => ?_⟩
  · refine IsHausdorff.haus (I := Ideal.span {(p : R)}) hc.toIsHausdorff x fun k => ?_
    rw [SModEq.zero, mem]
    exact hx k
  · obtain ⟨s, hs⟩ := IsPrecomplete.prec (I := Ideal.span {(p : R)}) hc.toIsPrecomplete
      (f := fun k => ∑ i ∈ Finset.range k, (p : R) ^ i * x i) (by
        intro m n hmn
        rw [SModEq.sub_mem, mem]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        refine ⟨-∑ i ∈ Finset.range k, (p : R) ^ i * x (m + i), ?_⟩
        rw [Finset.sum_range_add, mul_neg, Finset.mul_sum]
        simp only [pow_add, mul_assoc]
        ring)
    refine ⟨s, fun k => ?_⟩
    have := (hs k).symm
    rwa [SModEq.sub_mem, mem] at this

theorem good_tensor {Z O : Type} [CommRing Z] [CommRing O] [Algebra Z O] {I : Type} [Fintype I]
    (b : Module.Basis I Z O) {W : Type} [CommRing W] [Algebra Z W] (p : ℕ) (h : Good p W) :
    Good p (O ⊗[Z] W) := by
  have hp : ∀ (k : ℕ) (i : I) (x : O ⊗[Z] W),
      crd b i ((p : O ⊗[Z] W) ^ k * x) = (p : W) ^ k * crd b i x := by
    intro k i x
    rw [← Nat.cast_pow, crd_natCast_mul, Nat.cast_pow]
  refine ⟨fun x hx => ext_crd b fun i => ?_, fun x hx => ext_crd b fun i => ?_, fun x => ?_⟩
  · rw [map_zero]
    apply h.1
    rw [← crd_natCast_mul, hx, map_zero]
  · rw [map_zero]
    refine h.2.1 _ fun k => ?_
    obtain ⟨r, hr⟩ := hx k
    exact ⟨crd b i r, by rw [← hp, ← hr]⟩
  · choose s r hs using fun i => h.2.2 fun k => crd b i (x k)
    refine ⟨∑ j, b j ⊗ₜ[Z] s j, fun k => ⟨∑ j, b j ⊗ₜ[Z] r j k, ext_crd b fun i => ?_⟩⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, hp, crd_sum, crd_sum b (fun j => r j k), map_sum, ← hs]
    simp only [hp]

theorem good_witt (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    Good p (WittVector p k) :=
  good_of_complete p _ fun x hx => WittVector.eq_zero_of_p_mul_eq_zero x (by rw [mul_comm]; exact hx)

theorem ladic_RW (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    (∀ x : RW LL, (l : RW LL) * x = 0 → x = 0) ∧
    (∀ x : RW LL, (∀ k : ℕ, ∃ r, x = (l : RW LL) ^ k * r) → x = 0) ∧
    ∀ x : ℕ → RW LL, ∃ s, ∀ k : ℕ, ∃ r,
      s - ∑ i ∈ Finset.range k, (l : RW LL) ^ i * x i = (l : RW LL) ^ k * r :=
  good_tensor (W := WCb l) (basisO LL) l (good_witt l (Cb l))

end GlobalTheory.Decompl.LAdic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughOfPolyPow
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.PassPolyPow

theorem aeval_mul_apply {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (p q : L[X]) (x : M) : Polynomial.aeval f (p * q) x = Polynomial.aeval f p (Polynomial.aeval f q x) := by
  rw [map_mul, Module.End.mul_apply]

theorem eigen_of_pow_of_separable {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (c : L) (m : ℕ) (r : L[X]) (hr : r.Separable) (x : M)
    (h1 : Polynomial.aeval f ((X - C c) ^ m) x = 0) (h2 : Polynomial.aeval f r x = 0) :
    Polynomial.aeval f (X - C c) x = 0 := by
  obtain ⟨t, hrt, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr.ne_zero c
  have hle := Polynomial.rootMultiplicity_le_one_of_separable hr c
  have hcop : IsCoprime ((X - C c) ^ m) t :=
    ((Polynomial.irreducible_X_sub_C c).coprime_iff_not_dvd.2 hnd).pow_left
  obtain ⟨A, B', hAB⟩ := hcop
  have hs : ∃ s : L[X], (X - C c) * t = s * r := by
    interval_cases hj : r.rootMultiplicity c
    · exact ⟨X - C c, by rw [hrt]; ring⟩
    · exact ⟨1, by rw [hrt]; ring⟩
  obtain ⟨s, hs⟩ := hs
  have : (X - C c) = (A * (X - C c)) * (X - C c) ^ m + (B' * s) * r := by
    rw [mul_assoc (B') s r, ← hs]
    linear_combination (-(X - C c)) * hAB
  rw [this, map_add (f := _), LinearMap.add_apply, aeval_mul_apply, h1, map_zero, aeval_mul_apply, h2, map_zero, add_zero]

theorem mem_iSup_eigen_pow {L M ι : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (D : Submodule L M) (hD : ∀ x ∈ D, f x ∈ D) (r : L[X]) (hr : r.Separable)
    (hrD : ∀ x ∈ D, Polynomial.aeval f r x = 0) (c : ι → L) (m : ℕ) (s : Finset ι) :
    (∀ a ∈ s, ∀ b ∈ s, c a = c b → a = b) → ∀ d ∈ D,
      Polynomial.aeval f ((∏ a ∈ s, (X - C (c a))) ^ m) d = 0 →
      d ∈ ⨆ a ∈ s, (D ⊓ LinearMap.ker (f - c a • LinearMap.id)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ d _ h
    simp at h
    simp [h]
  | insert a t hat ih =>
    intro hinj d hd h
    rw [Finset.prod_insert hat, mul_pow] at h
    have hcop : IsCoprime ((X - C (c a)) ^ m) ((∏ b ∈ t, (X - C (c b))) ^ m) := by
      refine IsCoprime.pow (IsCoprime.prod_right fun b hb => ?_)
      refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub (IsUnit.mk0 _ (sub_ne_zero.2 fun e => hat ?_))
      rw [hinj a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb) e]
      exact hb
    obtain ⟨u, v, huv⟩ := hcop
    set Q := (∏ b ∈ t, (X - C (c b))) ^ m with hQ
    have hdec : d = Polynomial.aeval f (u * (X - C (c a)) ^ m) d + Polynomial.aeval f (v * Q) d := by
      rw [← LinearMap.add_apply, ← map_add (f := _), huv, map_one, Module.End.one_apply]
    rw [Finset.iSup_insert, hdec, add_comm]
    refine Submodule.add_mem_sup ?_ ?_
    · have hmem := GlobalTheory.PassPoly.aeval_mem_of_stable f D hD (v * Q) d hd
      refine ⟨hmem, ?_⟩
      have h1 : Polynomial.aeval f ((X - C (c a)) ^ m) (Polynomial.aeval f (v * Q) d) = 0 := by
        rw [← aeval_mul_apply, show (X - C (c a)) ^ m * (v * Q) = v * ((X - C (c a)) ^ m * Q) by ring,
          aeval_mul_apply, h, map_zero]
      have := eigen_of_pow_of_separable f (c a) m r hr _ h1 (hrD _ hmem)
      simpa [Module.algebraMap_end_apply] using this
    · refine ih (fun x hx y hy => hinj x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)) _
        (GlobalTheory.PassPoly.aeval_mem_of_stable f D hD _ d hd) ?_
      rw [← aeval_mul_apply, show Q * (u * (X - C (c a)) ^ m) = u * ((X - C (c a)) ^ m * Q) by ring,
        aeval_mul_apply, h, map_zero]

section
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem actVB_pow (g : G) (n : ℕ) (x : V ⊗[Qp] B) :
    (actVB PC.PD ρ g ^ n) x = actVB PC.PD ρ (g ^ n) x := by
  induction n generalizing x with
  | zero => simp [GlobalTheory.PassPoly.actVB_one']
  | succ n ih => rw [pow_succ, Module.End.mul_apply, ih, pow_succ, GlobalTheory.PassPoly.actVB_mul']

theorem aeval_index_kill (g : G) : ∀ x ∈ PC.Dpcris ρ,
    Polynomial.aeval (actVB PC.PD ρ g) (X ^ PC.H.index - C (1 : LL)) x = 0 := by
  intro x hx
  haveI := PC.normal
  have hg : g ^ PC.H.index ∈ PC.H := Subgroup.pow_index_mem PC.H g
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply]
  rw [actVB_pow, (GlobalTheory.PassPoly.mem_Dpcris_iff PC ρ x).1 hx _ hg, sub_self]

theorem separable_index [CharZero LL] : (X ^ PC.H.index - C (1 : LL)).Separable := by
  haveI := PC.finiteIndex
  exact Polynomial.separable_X_pow_sub_C 1 (Nat.cast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero) one_ne_zero

theorem inertiaThrough_of_poly_pow [CharZero LL] (Sig : Finset (PC.Iner →* LLˣ))
    (h1 : ∀ a ∈ Sig, ∀ g : PC.Iner, (g : G) ∈ PC.H → a g = 1)
    (h2 : ∀ a ∈ Sig, Nat.Coprime (orderOf a) PC.PD.p)
    (h3 : ∀ (g : PC.Iner), ∃ m : ℕ, ∀ d ∈ PC.Dpcris ρ, (Polynomial.aeval (actVB PC.PD ρ (g : G))
      ((∏ a ∈ Sig, (X - C ((a g : LLˣ) : LL))) ^ m)) d = 0)
    (h4 : ∃ γ : PC.Iner, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧
      ∀ g : PC.Iner, ∃ (n : ℕ) (u : PC.Iner), (∀ a ∈ Sig, a u = 1) ∧ g = γ ^ n * u) :
    PC.InertiaThrough ρ Sig := by

  have htriv : ∀ u : PC.Iner, (∀ a ∈ Sig, a u = 1) → ∀ x ∈ PC.Dpcris ρ,
      actVB PC.PD ρ (u : G) x = x := by
    intro u hu x hx
    obtain ⟨m, hm⟩ := h3 u
    have hprod : (∏ a ∈ Sig, (X - C ((a u : LLˣ) : LL))) ^ m = (X - C (1 : LL)) ^ (Sig.card * m) := by
      rw [Finset.prod_congr rfl (fun a ha => by rw [hu a ha, Units.val_one]), Finset.prod_const, pow_mul]
    have hk := hm x hx
    rw [hprod] at hk
    have := eigen_of_pow_of_separable _ 1 _ _ (separable_index PC) x hk (aeval_index_kill PC ρ _ x hx)
    simpa [Module.algebraMap_end_apply, sub_eq_zero] using this
  refine ⟨h1, h2, le_antisymm ?_ ?_⟩
  · obtain ⟨γ, hsep, hgen⟩ := h4
    intro d hd
    obtain ⟨m, hm⟩ := h3 γ
    have := mem_iSup_eigen_pow (actVB PC.PD ρ (γ : G)) (PC.Dpcris ρ) (GlobalTheory.PassPoly.Dpcris_stable PC ρ γ)
      _ (separable_index PC) (aeval_index_kill PC ρ _)
      (fun a : PC.Iner →* LLˣ => ((a γ : LLˣ) : LL)) m Sig
      (fun a ha b hb e => hsep a ha b hb (Units.ext e)) d hd (hm d hd)
    refine (iSup₂_mono (fun a ha => ?_) : _ ≤ ⨆ a ∈ Sig, PC.Eig ρ PC.Iner a) this
    rintro x ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    have hγ : actVB PC.PD ρ (γ : G) x = ((a γ : LLˣ) : LL) • x := by
      simpa [sub_eq_zero] using hx'
    have hn : ∀ n : ℕ, actVB PC.PD ρ ((γ : G) ^ n) x = ((a γ : LLˣ) : LL) ^ n • x := by
      intro n
      induction n with
      | zero => simp [GlobalTheory.PassPoly.actVB_one']
      | succ n ih => rw [pow_succ, GlobalTheory.PassPoly.actVB_mul', hγ, map_smul, ih, smul_smul, pow_succ, mul_comm]
    simp only [Submodule.coe_iInf, Set.mem_iInter, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    intro g
    obtain ⟨n, u, hu, rfl⟩ := hgen g
    rw [map_mul, hu a ha, mul_one, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, GlobalTheory.PassPoly.actVB_mul',
      htriv u hu x hx, hn, Units.val_pow_eq_pow_val]
  · exact iSup₂_le fun a _ => inf_le_left

end

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)), (∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK K)) ∈ (pc P h hN hF hS).H → a g = 1) → (∀ a ∈ Sig, Nat.Coprime (orderOf a) l) → (∀ (g : (pc P h hN hF hS).Iner), ∃ m : ℕ, ∀ d ∈ (pc P h hN hF hS).Dpcris ρ, (Polynomial.aeval (actVB (P.PD K) ρ (g : ↥(GK K))) ((∏ a ∈ Sig, (X - C ((a g : (↥LL.1)ˣ) : ↥LL.1))) ^ m)) d = 0) → (∃ γ : (pc P h hN hF hS).Iner, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧ ∀ g : (pc P h hN hF hS).Iner, ∃ (n : ℕ) (u : (pc P h hN hF hS).Iner), (∀ a ∈ Sig, a u = 1) ∧ g = γ ^ n * u) → (pc P h hN hF hS).InertiaThrough ρ Sig := by
  intro l _ P K K' LL h hN hF hS V _ _ _ _ ρ Sig h1 h2 h3 h4
  haveI : CharZero ↥LL.1 := charZero_of_injective_algebraMap (algebraMap ℚ_[l] ↥LL.1).injective
  refine inertiaThrough_of_poly_pow (pc P h hN hF hS) ρ Sig h1 ?_ h3 h4
  have hp : (pc P h hN hF hS).PD.p = l := P.PD_p K
  rw [hp]
  exact h2

end GlobalTheory.PassPolyPow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeModPowActionIsLocallyConstant
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Pointwise

namespace GlobalTheory.InertiaEigenvalues

theorem actQ_pow_isLocallyConstant : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep G ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), IsLocallyConstant fun g : G => actQ LA _ hI g x := by
  intro l _ G _ _ LL _ _ _ O _ _ hG A LA r hI x
  obtain ⟨_, _, _, hTR, hO⟩ := hG
  haveI := hTR
  haveI : CharZero LL := charZero_of_injective_algebraMap (algebraMap ℚ_[l] LL).injective
  haveI := IsModuleTopology.topologicalAddGroup LL A.V
  set c : LL := ((l : ℕ) : LL) ^ r with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hT : IsOpen (LA.T : Set A.V) :=
    GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hO LA.T LA.fg LA.span
  have hcT : IsOpen (c • (LA.T : Set A.V)) := hT.smul₀ hc0
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [IsLocallyConstant.iff_exists_open]
  intro g0
  refine ⟨(fun g => A.ρ g t - A.ρ g0 t) ⁻¹' (c • (LA.T : Set A.V)),
    hcT.preimage ((A.cont _).sub continuous_const), ?_, ?_⟩
  · show A.ρ g0 t - A.ρ g0 t ∈ c • (LA.T : Set A.V)
    rw [sub_self]
    exact ⟨0, LA.T.zero_mem, smul_zero c⟩
  · intro g hg
    obtain ⟨w, hw, hwe⟩ := hg
    simp only [actQ, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨⟨w, hw⟩, Submodule.mem_top, ?_⟩
    apply Subtype.ext
    simp only [Submodule.coe_smul, Submodule.coe_sub, actT, LinearMap.restrict_coe_apply,
      LinearMap.coe_restrictScalars]
    rw [← algebraMap_smul LL ((l : O) ^ r) w, map_pow, map_natCast]
    exact hwe

end GlobalTheory.InertiaEigenvalues
end

