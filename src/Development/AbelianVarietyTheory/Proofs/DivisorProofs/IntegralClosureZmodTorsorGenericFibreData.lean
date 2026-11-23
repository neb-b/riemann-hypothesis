module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ClosureData

open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth

section
variable (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]

theorem algebraMap_mem_nonZeroDivisors [Module.Flat A R] {a : A} (ha : a ≠ 0) :
    algebraMap A R a ∈ nonZeroDivisors R := by
  have h : IsSMulRegular R a :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha)
  refine mem_nonZeroDivisors_iff_right.mpr fun x hx => h ?_
  simp only [Algebra.smul_def, smul_zero]
  rw [mul_comm, mul_zero]; exact hx

theorem genFib_injective [Module.Flat A R] : Function.Injective (algebraMap R (GenFib A R)) := by
  apply IsLocalization.injective (M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
  rintro _ ⟨a, ha, rfl⟩
  exact algebraMap_mem_nonZeroDivisors A R (nonZeroDivisors.ne_zero ha)

theorem isUnit_genFib {a : A} (ha : a ≠ 0) :
    IsUnit (algebraMap R (GenFib A R) (algebraMap A R a)) :=
  IsLocalization.map_units (M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (GenFib A R)
    ⟨algebraMap A R a, ⟨a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩⟩
end

section
variable {A R D : Type} [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
  [Algebra (GenFib A R) D]

theorem baseHom_apply (r : R) :
    baseHom A R D r = algebraMap (GenFib A R) D (algebraMap R (GenFib A R) r) := rfl

theorem map_mem (σ : D →ₐ[GenFib A R] D) {d : D} (hd : d ∈ closure A R D) :
    σ d ∈ closure A R D := by
  letI := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact IsIntegral.map (σ.restrictScalars R) (show IsIntegral R d from hd)

def restr (σ : D ≃ₐ[GenFib A R] D) :
    letI := closureAlg A R D
    closure A R D ≃ₐ[R] closure A R D :=
  letI := closureAlg A R D
  { toFun := fun c => ⟨σ c.1, map_mem σ.toAlgHom c.2⟩
    invFun := fun c => ⟨σ.symm c.1, map_mem σ.symm.toAlgHom c.2⟩
    left_inv := fun c => Subtype.ext (σ.symm_apply_apply (c : D))
    right_inv := fun c => Subtype.ext (σ.apply_symm_apply (c : D))
    map_mul' := fun c c' => Subtype.ext (map_mul σ (c : D) (c' : D))
    map_add' := fun c c' => Subtype.ext (map_add σ (c : D) (c' : D))
    commutes' := fun r => Subtype.ext (σ.commutes (algebraMap R (GenFib A R) r)) }

end

section
variable {A R D : Type} [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
  [Algebra (GenFib A R) D]

theorem trace_mem (hIC : ∀ f : GenFib A R, IsIntegral R f → ∃ r : R, algebraMap R (GenFib A R) r = f)
    (hinj : Function.Injective (algebraMap (GenFib A R) D))
    (τ : D →ₗ[GenFib A R] GenFib A R) (q : ℕ) [NeZero q]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[GenFib A R] D))
    (hτ : ∀ d, algebraMap _ D (τ d) = ∑ g, act g d) {c : D} (hc : c ∈ closure A R D) :
    ∃ r : R, algebraMap R (GenFib A R) r = τ c := by
  apply hIC
  letI := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom R (GenFib A R) D) hinj]
  show IsIntegral R (algebraMap (GenFib A R) D (τ c))
  rw [hτ]
  exact (sum_mem fun g _ => map_mem (act g).toAlgHom hc : ∑ g, act g c ∈ GlobalTheory.KeyOriginNoeth.closure A R D)

theorem smul_coe (r : R) (c : closure A R D) :
    ((letI := closureAlg A R D; r • c : closure A R D) : D) =
      algebraMap R (GenFib A R) r • (c : D) := by
  letI := closureAlg A R D
  rw [Algebra.smul_def, Algebra.smul_def]; rfl

end

theorem closureData : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [Nontrivial R] [Module.Flat A R] [IsNoetherianRing R],
    GlobalTheory.GoodEtale.Hart A R R →
    (∀ f : GlobalTheory.LocAcyc.GenFib A R, IsIntegral R f → ∃ r : R, algebraMap R (GlobalTheory.LocAcyc.GenFib A R) r = f) →
    ∀ (q : ℕ) [NeZero q] (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] D)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) D q act →
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D;
    ∃ (act' : Multiplicative (ZMod q) →* (GlobalTheory.KeyOriginNoeth.closure A R D ≃ₐ[R] GlobalTheory.KeyOriginNoeth.closure A R D))
      (T : GlobalTheory.KeyOriginNoeth.closure A R D →ₗ[R] R),
      (∀ c, algebraMap R _ (T c) = ∑ g, act' g c) ∧
      (∃ a : A, a ≠ 0 ∧ ∃ (n : ℕ) (x y : Fin n → GlobalTheory.KeyOriginNoeth.closure A R D),
        ∀ g, ∑ i, x i * act' g (y i) = if g = 1 then algebraMap R _ (algebraMap A R a) else 0) ∧
      GlobalTheory.GoodEtale.TorsionFreeOver A R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      GlobalTheory.GoodEtale.Hart A R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      Algebra.IsIntegral R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      Nontrivial (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  intro A R _ _ _ _ _ _ _ _ hHart hIC q _ D _ _ act hT
  classical
  letI := closureAlg A R D
  obtain ⟨hinj, ⟨τ, hτ⟩, n, x, y, hxy⟩ := GlobalTheory.TorsorTrace.injective_trace_galoisData _ D q act hT
  have hRinj := genFib_injective A R
  have htr : ∀ c ∈ closure A R D, ∃ r : R, algebraMap R (GenFib A R) r = τ c :=
    fun c hc => trace_mem hIC hinj τ q act hτ hc
  haveI : Module.Finite (GenFib A R) D := hT.1
  obtain ⟨a, ha, hmem⟩ := GlobalTheory.T.exists_mul_mem_integralClosureOverGenericFibre A R D (Finset.univ.image x ∪ Finset.univ.image y)
  set b := baseHom A R D (algebraMap A R a) with hbdef
  have hb : ∀ g, act g b = b := fun g => (act g).commutes _
  let x' : Fin n → closure A R D := fun i => ⟨b * x i, hmem _ (by simp)⟩
  let y' : Fin n → closure A R D := fun i => ⟨b * y i, hmem _ (by simp)⟩
  let act' : Multiplicative (ZMod q) →* (closure A R D ≃ₐ[R] closure A R D) :=
    { toFun := fun g => restr (act g)
      map_one' := by
        apply AlgEquiv.ext
        intro c
        apply Subtype.ext
        change act 1 (c : D) = (c : D)
        rw [map_one, AlgEquiv.one_apply]
      map_mul' := fun g h => by
        apply AlgEquiv.ext
        intro c
        apply Subtype.ext
        change act (g * h) (c : D) = act g (act h (c : D))
        rw [map_mul, AlgEquiv.mul_apply] }
  have hact' : ∀ g c, ((act' g c : closure A R D) : D) = act g c := fun _ _ => rfl
  let Tf : closure A R D → R := fun c => Classical.choose (htr c c.2)
  have hT' : ∀ c, algebraMap R (GenFib A R) (Tf c) = τ c := fun c => Classical.choose_spec (htr c c.2)
  let T : closure A R D →ₗ[R] R :=
    { toFun := Tf
      map_add' := fun c c' => hRinj (by simp [hT'])
      map_smul' := fun r c => hRinj (by
        rw [hT', smul_coe, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul, map_mul, hT']) }
  have key : ∀ g, ∑ i, (x' i : D) * act g (y' i) = b * b * ∑ i, x i * act g (y i) := by
    intro g
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show b * x i * act g (b * y i) = _
    rw [map_mul, hb]; ring
  have h1 : ∀ g, ∑ i, (x' i : D) * act g (y' i) = if g = 1 then b * b else 0 := by
    intro g; rw [key, hxy]; split_ifs <;> simp
  have hbb : b * b = baseHom A R D (algebraMap A R (a * a)) := by simp [hbdef, map_mul]
  refine ⟨act', T, ?_, ⟨a * a, mul_ne_zero ha ha, n, x', y', ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro c
    apply Subtype.ext
    show baseHom A R D (Tf c) = _
    rw [baseHom_apply, hT', hτ]
    simp [hact']
  · intro g
    apply Subtype.ext
    split_ifs with hg
    · simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, hact']
      rw [h1, if_pos hg, hbb]
      rfl
    · simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, hact']
      rw [h1, if_neg hg]
      rfl
  · intro a' ha' c hc
    apply Subtype.ext
    have h1 := congrArg Subtype.val hc
    rw [smul_coe, Algebra.smul_def] at h1
    simpa using ((isUnit_genFib A R ha').map (algebraMap (GenFib A R) D)).mul_right_eq_zero.mp h1
  · have hrec (d : D) : ∑ i, (x' i : D) * algebraMap (GenFib A R) D (τ (y' i * d)) =
        baseHom A R D (algebraMap A R (a * a)) * d := by
      simp only [hτ, map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [← mul_assoc, ← Finset.sum_mul, h1]
      simp [hbb]
    letI : Algebra R D := (baseHom A R D).toAlgebra
    have hτmul (f : GenFib A R) (d : D) :
        τ (algebraMap (GenFib A R) D f * d) = f * τ d := by
      rw [← Algebra.smul_def, τ.map_smul, smul_eq_mul]
    -- Bound the submodule of elements whose products with the closure have trace in R.
    let N : Submodule R D :=
      { carrier := {d | ∀ z ∈ closure A R D, ∃ r : R, algebraMap R (GenFib A R) r = τ (d * z)}
        add_mem' := by
          intro d e hd he z hz
          obtain ⟨r, hr⟩ := hd z hz
          obtain ⟨s, hs⟩ := he z hz
          exact ⟨r + s, by rw [map_add, hr, hs, add_mul, map_add]⟩
        zero_mem' := by
          intro z _
          exact ⟨0, by simp⟩
        smul_mem' := by
          intro r d hd z hz
          obtain ⟨s, hs⟩ := hd z hz
          refine ⟨r * s, ?_⟩
          change _ = τ ((algebraMap (GenFib A R) D (algebraMap R (GenFib A R) r) * d) * z)
          rw [mul_assoc, hτmul, ← hs, map_mul] }
    obtain ⟨v, hv⟩ := isUnit_genFib A R (mul_ne_zero ha ha)
    let w (i : Fin n) : D := algebraMap (GenFib A R) D (↑v⁻¹) * x' i
    let S := Submodule.span R (Set.range w)
    have hNS : N ≤ S := by
      intro d hd
      have hr : ∀ i, ∃ r : R, algebraMap R (GenFib A R) r = τ (y' i * d) := by
        intro i
        obtain ⟨r, hr⟩ := hd (y' i) (y' i).2
        exact ⟨r, by rw [hr, mul_comm]⟩
      choose r hr using hr
      have hd' : d = ∑ i, r i • w i := calc
        d = algebraMap (GenFib A R) D (↑v⁻¹) *
            (baseHom A R D (algebraMap A R (a * a)) * d) := by
          rw [baseHom_apply, ← mul_assoc, ← map_mul, ← hv, Units.inv_mul, map_one, one_mul]
        _ = ∑ i, r i • w i := by
          rw [← hrec, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hr i]
          change _ = algebraMap (GenFib A R) D (algebraMap R (GenFib A R) (r i)) * w i
          dsimp [w]
          ring
      rw [hd']
      exact Submodule.sum_mem S fun i _ => S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    have hS : IsNoetherian R S :=
      isNoetherian_of_fg_of_noetherian S (Submodule.fg_span (Set.finite_range w))
    intro a₀ ha₀ m hm
    obtain ⟨u, hu⟩ := isUnit_genFib A R ha₀
    let ξ : D := algebraMap (GenFib A R) D (↑u⁻¹) * m
    have hξN (d : D) (hd : d ∈ N) : ξ * d ∈ N := by
      intro z hz
      obtain ⟨r, hr⟩ := hd ((m : D) * z) ((closure A R D).mul_mem m.2 hz)
      have hdiv : ∃ s : R, r = algebraMap A R a₀ • s := by
        apply hHart a₀ ha₀ r
        intro p hp hheight
        obtain ⟨t, ht, m', hm'⟩ := hm p hp hheight
        obtain ⟨s, hs⟩ := hd ((m' : D) * z) ((closure A R D).mul_mem m'.2 hz)
        refine ⟨t, ht, s, hRinj ?_⟩
        have hmD := congrArg Subtype.val hm'
        rw [smul_coe, smul_coe, Algebra.smul_def, Algebra.smul_def] at hmD
        rw [smul_eq_mul, smul_eq_mul, map_mul, map_mul, hr, hs, ← hτmul, ← hτmul]
        congr 1
        linear_combination (d * z) * hmD
      obtain ⟨s, hs⟩ := hdiv
      refine ⟨s, ?_⟩
      have heq : ξ * d * z = algebraMap (GenFib A R) D (↑u⁻¹) * (d * ((m : D) * z)) := by
        dsimp [ξ]
        ring
      rw [heq, hτmul, ← hr, hs, smul_eq_mul, map_mul, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    have hpow (k : ℕ) : ξ ^ k ∈ N := by
      induction k with
      | zero =>
        rw [pow_zero]
        intro z hz
        simpa only [one_mul] using htr z hz
      | succ k ih => rw [pow_succ']; exact hξN _ ih
    have hadj : (Algebra.adjoin R {ξ}).toSubmodule ≤ S := by
      rw [Algebra.adjoin_eq_span]
      apply le_trans _ hNS
      rw [Submodule.span_le]
      intro d hd
      obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hd
      exact hpow k
    have hfg := isNoetherian_submodule.mp hS _ hadj
    have hξ : ξ ∈ closure A R D :=
      IsIntegral.of_mem_of_fg _ hfg ξ (Algebra.self_mem_adjoin_singleton R ξ)
    refine ⟨⟨ξ, hξ⟩, Subtype.ext ?_⟩
    rw [smul_coe, Algebra.smul_def]
    change (m : D) = algebraMap (GenFib A R) D (algebraMap R (GenFib A R) (algebraMap A R a₀)) * ξ
    dsimp [ξ]
    rw [← mul_assoc, ← map_mul, ← hu, Units.mul_inv, map_one, one_mul]
  · refine ⟨fun c => ?_⟩
    letI := (baseHom A R D).toAlgebra
    let f : closure A R D →ₐ[R] D := { (closure A R D).subtype with commutes' := fun _ => rfl }
    exact (isIntegral_algHom_iff f Subtype.val_injective).mp c.2
  · haveI : Nontrivial (GenFib A R) := hRinj.nontrivial
    haveI : Nontrivial D := hinj.nontrivial
    exact ⟨⟨0, 1, fun h => zero_ne_one (α := D) (by simpa using congrArg Subtype.val h)⟩⟩

end GlobalTheory.ClosureData
