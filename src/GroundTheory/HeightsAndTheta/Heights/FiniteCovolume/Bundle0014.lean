module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0011

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCoordLatticeFullRank
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

noncomputable section

variable {E : Type*} [Field E] [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]

theorem CoordLatticeFullRank.proof (v : Basis ι E W) : CoordLatticeFullRank.Statement v := by
  intro La hL
  set f : W →ₗ[E] ι → E := (v.equivFun : W →ₗ[E] ι → E) with hf
  refine ⟨?_, ?_⟩
  · classical
    letI := hL.fg
    infer_instance
  set S : Set (ι → E) := ((La.map f.toAddMonoidHom : AddSubgroup (ι → E)) : Set (ι → E)) with hS
  set T : Submodule ℚ (ι → E) := Submodule.span ℚ S with hT

  have key : ∀ (a : E), ∀ s ∈ S, a • s ∈ T := by
    intro a s hs
    obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ ({a} : Finset E)
    have hda : IsIntegral ℤ (d • a) := hint a (Finset.mem_singleton_self a)
    obtain ⟨x, hx, rfl⟩ := (AddSubgroup.mem_map).mp hs
    let b : 𝓞 E := ⟨d • a, hda⟩
    have hbx : ((b : E) • x) ∈ La := hL.smul_mem b x hx
    have hfb : f ((b : E) • x) ∈ S := (AddSubgroup.mem_map).mpr ⟨_, hbx, rfl⟩
    have hd' : ((d : ℚ)) ≠ 0 := by exact_mod_cast hd
    have heq : a • f.toAddMonoidHom x = ((d : ℚ)⁻¹) • f ((b : E) • x) := by
      rw [map_smul]
      show a • f x = ((d : ℚ)⁻¹) • ((d • a) • f x)
      rw [zsmul_eq_mul, mul_smul, Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [heq]
    exact T.smul_mem _ (Submodule.subset_span hfb)

  have stable : ∀ (a : E), ∀ y ∈ T, a • y ∈ T := by
    intro a y hy
    induction hy using Submodule.span_induction with
    | mem s hs => exact key a s hs
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact T.add_mem hy hz
    | smul q y _ hy =>
      rw [smul_comm]
      exact T.smul_mem q hy
  let T' : Submodule E (ι → E) :=
    { carrier := T
      add_mem' := fun hy hz => T.add_mem hy hz
      zero_mem' := T.zero_mem
      smul_mem' := fun a y hy => stable a y hy }
  have hspan : Submodule.span E S = ⊤ := by
    have hSim : S = f '' (La : Set W) := by
      rw [hS, AddSubgroup.coe_map]; rfl
    rw [hSim, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact v.equivFun.surjective
  have hle : Submodule.span E S ≤ T' := Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
  rw [hspan] at hle
  exact eq_top_iff.mpr fun y _ => hle (Submodule.mem_top)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDualLatticeMultiple
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

theorem inverseDifferent_multiple (E : Type*) [Field E] [NumberField E] :
    ∃ δ : ℤ, δ ≠ 0 ∧ ∀ z : E, (∀ a : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E ((a : E) * z) = n) →
      IsIntegral ℤ ((δ : E) * z) := by
  classical
  set b := integralBasis E
  set bd := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b
  obtain ⟨δ, hδ, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image bd)
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have hsum := bd.sum_repr z
  have key : (δ : E) * z = ∑ i, (bd.repr z i) • ((δ : E) * bd i) := by
    conv_lhs => rw [← hsum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def]; ring
  rw [key]
  refine IsIntegral.sum _ fun i _ => ?_
  obtain ⟨n, hn⟩ := hz (RingOfIntegers.basis E i)
  have hr : bd.repr z i = (n : ℚ) := by
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, integralBasis_apply,
      mul_comm, hn]
  rw [hr, show ((n : ℚ) • ((δ : E) * bd i)) = (n : ℤ) • ((δ : E) * bd i) by
    rw [← Int.cast_smul_eq_zsmul ℚ]]
  refine IsIntegral.smul _ ?_
  have := hint (bd i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rwa [zsmul_eq_mul] at this

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem DualLatticeMultiple.proof (h : HermitianForm F E W) : DualLatticeMultiple.Statement h := by
  intro D
  obtain ⟨δ, hδ, hdiff⟩ := inverseDifferent_multiple E
  refine ⟨δ * (D.factorial : ℤ), mul_ne_zero hδ (by exact_mod_cast D.factorial_ne_zero),
    fun La hLa => ⟨fun x hx y hy => ?_, fun y hy => ?_⟩⟩
  · have hi : IsIntegral ℤ (Algebra.trace ℚ E (h.toSesq x y)) :=
      Algebra.isIntegral_trace ((mem_integralClosure_iff ℤ E).mp (hLa.integral x hx y hy))
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    exact ⟨n, by rw [← hn]; simp⟩
  ·
    have hdual : δ • y ∈ dualLattice h La := by
      intro x hx
      rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
      refine (mem_integralClosure_iff ℤ E).mpr (hdiff _ fun a => ?_)
      obtain ⟨n, hn⟩ := hy _ (hLa.isLattice.smul_mem a x hx)
      exact ⟨n, by rw [← hn, LinearMap.map_smul, smul_eq_mul]⟩

    have hm := AddSubgroup.nsmul_relIndex_mem La hdual
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hLa.index_ne_zero) hLa.index_le
    have : (D.factorial : ℤ) • (δ • y) ∈ La := by
      rw [hc, natCast_zsmul, mul_comm, mul_nsmul]
      rw [smul_comm]
      exact AddSubgroup.nsmul_mem _ hm _
    rwa [smul_smul, mul_comm] at this

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PGramDetermines
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]

namespace GramDetermines


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem sesq_linearCombination (h : HermitianForm F E W) {n : ℕ} {e e' : Fin n → W}
    (hG : ∀ a b, h.toSesq (e a) (e b) = h.toSesq (e' a) (e' b)) (c d : Fin n → E) :
    h.toSesq (Fintype.linearCombination E e' c) (Fintype.linearCombination E e' d) =
      h.toSesq (Fintype.linearCombination E e c) (Fintype.linearCombination E e d) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ,
    LinearMap.smul_apply, hG]


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem linearCombination_surjective {n : ℕ} {e : Fin n → W}
    (hL : IsLattice E (AddSubgroup.closure (Set.range e))) :
    Function.Surjective (Fintype.linearCombination E e) := by
  have hle : AddSubgroup.closure (Set.range e) ≤
      (LinearMap.range (Fintype.linearCombination E e)).toAddSubgroup := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨Pi.single a 1, by simp⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
  intro x hx
  exact hle hx


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem linearCombination_eq_zero (h : HermitianForm F E W) {n : ℕ} {e e' : Fin n → W}
    (hL' : IsLattice E (AddSubgroup.closure (Set.range e')))
    (hG : ∀ a b, h.toSesq (e a) (e b) = h.toSesq (e' a) (e' b)) (c : Fin n → E)
    (hc : Fintype.linearCombination E e c = 0) : Fintype.linearCombination E e' c = 0 := by
  apply h.nonsingular.1
  refine LinearMap.ext fun y => ?_
  obtain ⟨d, rfl⟩ := linearCombination_surjective hL' y
  rw [sesq_linearCombination h hG, hc, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]

theorem proof (h : HermitianForm F E W) : GramDetermines.Statement h := by
  intro n e e' hL hL' hG
  have hG' : ∀ a b, h.toSesq (e' a) (e' b) = h.toSesq (e a) (e b) := fun a b => (hG a b).symm
  have hs := linearCombination_surjective hL
  have hs' := linearCombination_surjective hL'
  have hker : LinearMap.ker (Fintype.linearCombination E e) =
      LinearMap.ker (Fintype.linearCombination E e') := by
    ext c
    simp only [LinearMap.mem_ker]
    exact ⟨linearCombination_eq_zero h hL' hG c, linearCombination_eq_zero h hL hG' c⟩
  let γ : W ≃ₗ[E] W := ((Fintype.linearCombination E e).quotKerEquivOfSurjective hs).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans
      ((Fintype.linearCombination E e').quotKerEquivOfSurjective hs'))
  have hγ : ∀ c, γ (Fintype.linearCombination E e c) = Fintype.linearCombination E e' c :=
    fun c => by simp [γ, Submodule.quotEquivOfEq_mk]
  refine ⟨⟨γ, fun x y => ?_⟩, fun a => ?_⟩
  · obtain ⟨c, rfl⟩ := hs x
    obtain ⟨d, rfl⟩ := hs y
    rw [hγ, hγ]
    exact sesq_linearCombination h hG c d
  · simpa using hγ (Pi.single a 1)

end GramDetermines

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIsotropicScaling
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

namespace IsotropicScaling

section Maps

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def scalingMap (h : HermitianForm F E W) (v w : W) (α β : E) : W →ₗ[E] W :=
  LinearMap.id + α • (h.toSesq w).smulRight v + β • (h.toSesq v).smulRight w

variable (h : HermitianForm F E W) {v w : W}

theorem scalingMap_apply (α β : E) (x : W) :
    scalingMap h v w α β x = x + (α * h.toSesq w x) • v + (β * h.toSesq v x) • w := by
  simp [scalingMap, mul_smul]

theorem scalingMap_zero : scalingMap h v w 0 0 = LinearMap.id := by
  simp [scalingMap]

theorem pairing_left (hww : h.toSesq w w = 0) (hwv : h.toSesq w v = 1) (α β : E) (x : W) :
    h.toSesq w (scalingMap h v w α β x) = (1 + α) * h.toSesq w x := by
  rw [scalingMap_apply, map_add (f := _), map_add (f := _), map_smul, map_smul, hwv, hww, smul_eq_mul, smul_eq_mul]
  ring

theorem pairing_right (hvv : h.toSesq v v = 0) (hvw : h.toSesq v w = 1) (α β : E) (x : W) :
    h.toSesq v (scalingMap h v w α β x) = (1 + β) * h.toSesq v x := by
  rw [scalingMap_apply, map_add (f := _), map_add (f := _), map_smul, map_smul, hvv, hvw, smul_eq_mul, smul_eq_mul]
  ring

variable (hvv : h.toSesq v v = 0) (hww : h.toSesq w w = 0) (hvw : h.toSesq v w = 1)
  (hwv : h.toSesq w v = 1)
include hvv hww hvw hwv

theorem scalingMap_comp (α β α' β' : E) :
    scalingMap h v w α β ∘ₗ scalingMap h v w α' β' =
      scalingMap h v w (α + α' + α * α') (β + β' + β * β') := by
  ext x
  rw [LinearMap.comp_apply, scalingMap_apply h α β, pairing_left h hww hwv,
    pairing_right h hvv hvw, scalingMap_apply, scalingMap_apply]
  module

theorem scalingMap_isometry {α β : E} (hαβ : α + conj F E β + α * conj F E β = 0) (x y : W) :
    h.toSesq (scalingMap h v w α β x) (scalingMap h v w α β y) = h.toSesq x y := by
  have hαβ' : conj F E α + β + conj F E α * β = 0 := by
    simpa [conj_conj] using congrArg (conj F E) hαβ
  have hc : ∀ z, conjHom F E z = conj F E z := fun _ => rfl
  have hxv : h.toSesq x v = conj F E (h.toSesq v x) := (h.isSymm.eq v x).symm
  have hxw : h.toSesq x w = conj F E (h.toSesq w x) := (h.isSymm.eq w x).symm
  rw [scalingMap_apply, scalingMap_apply]
  simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hvv, hww, hvw, hwv, hxv, hxw, hc, map_mul]
  linear_combination (h.toSesq w y * conj F E (h.toSesq v x)) * hαβ +
    (h.toSesq v y * conj F E (h.toSesq w x)) * hαβ'

end Maps

theorem sub_one_add_inv_sub_one_add_mul_eq_zero {E : Type*} [Field E] {u : E} (hu : u ≠ 0) :
    u - 1 + (u⁻¹ - 1) + (u - 1) * (u⁻¹ - 1) = 0 := by
  field_simp
  ring

section Lattice

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem exists_nsmul_mem {La : AddSubgroup W} (hLa : IsLattice E La) (w : W) :
    ∃ N : ℕ, 0 < N ∧ N • w ∈ La := by
  let S : Submodule E W :=
    { carrier := {w | ∃ N : ℕ, 0 < N ∧ N • w ∈ La}
      add_mem' := by
        rintro a b ⟨M, hM, ha⟩ ⟨N, hN, hb⟩
        refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
        rw [smul_add, mul_smul, mul_comm, mul_smul]
        exact add_mem (La.nsmul_mem ha N) (La.nsmul_mem hb M)
      zero_mem' := ⟨1, one_pos, by simp⟩
      smul_mem' := by
        rintro c a ⟨N, hN, ha⟩
        have hc : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ c)
        obtain ⟨m, s, hm, hs⟩ := hc.exists_nsmul_eq (𝓞 E)
        refine ⟨m * N, Nat.mul_pos (Nat.pos_of_ne_zero hm) hN, ?_⟩
        have : (m * N) • (c • a) = (algebraMap (𝓞 E) E s) • (N • a) := by
          rw [← hs]
          module
        rw [this]
        exact hLa.smul_mem s _ ha }
  have hS : Submodule.span E (La : Set W) ≤ S :=
    Submodule.span_le.2 fun x hx => ⟨1, one_pos, by simpa using hx⟩
  exact (hS (hLa.span_eq_top ▸ Submodule.mem_top : w ∈ Submodule.span E (La : Set W)))

omit [NumberField E] in
theorem conj_mem_integralClosure {z : E}
    (hz : z ∈ integralClosure ℤ E) : conj F E z ∈ integralClosure ℤ E :=
  IsIntegral.map ((conj F E : E ≃ₐ[F] E) : E →+* E).toIntAlgHom hz


omit [NumberField E] in
theorem scalingMap_mem (h : HermitianForm F E W) {La : AddSubgroup W} (hLa : IsLattice E La)
    (hint : IsIntegralOn h La) {v w : W} (hv : v ∈ La) {N : ℕ} (hNw : N • w ∈ La)
    {u : (𝓞 E)ˣ} (hu : u ∈ congruenceUnits E N) {x : W} (hx : x ∈ La) :
    scalingMap h v w (((u : 𝓞 E) : E) - 1) ((conj F E ((u : 𝓞 E) : E))⁻¹ - 1) x ∈ La := by
  have smem : ∀ z ∈ integralClosure ℤ E, ∀ y ∈ La, z • y ∈ La :=
    fun z hz y hy => hLa.smul_mem ⟨z, hz⟩ y hy
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (mem_congruenceUnits.1 hu)
  have ht' : ((u : 𝓞 E) : E) - 1 = (t : E) * N := by exact_mod_cast ht.symm
  have hu0 : conj F E ((u : 𝓞 E) : E) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast u.ne_zero
  have hinv : (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = ((u : 𝓞 E) : E)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    exact_mod_cast u.inv_mul
  have hN : h.toSesq (N • w) x = N * h.toSesq w x := by
    rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  have e2 : ((conj F E ((u : 𝓞 E) : E))⁻¹ - 1) * h.toSesq v x =
      (-conj F E (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) * conj F E (t : E) * h.toSesq v x) * N := by
    have hct : conj F E ((u : 𝓞 E) : E) - 1 = conj F E (t : E) * N := by
      rw [← map_one (conj F E), ← map_sub, ht', map_mul, map_natCast]
    rw [hinv, map_inv₀]
    field_simp
    linear_combination (-h.toSesq v x) * hct
  have key : scalingMap h v w (((u : 𝓞 E) : E) - 1) ((conj F E ((u : 𝓞 E) : E))⁻¹ - 1) x =
      x + ((t : E) * h.toSesq (N • w) x) • v +
        (-conj F E (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) * conj F E (t : E) * h.toSesq v x) • (N • w) := by
    rw [scalingMap_apply, e2, ht', hN, ← Nat.cast_smul_eq_nsmul E]
    module
  rw [key]
  refine add_mem (add_mem hx (smem _ ?_ v hv)) (smem _ ?_ _ hNw)
  · exact mul_mem t.2 (hint _ hNw x hx)
  · exact mul_mem (mul_mem (neg_mem (conj_mem_integralClosure (u⁻¹ : (𝓞 E)ˣ).val.2))
      (conj_mem_integralClosure t.2)) (hint v hv x hx)

end Lattice

section Main

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem proof (h : HermitianForm F E W) (h₁ : WittPartner.Statement h) :
    IsotropicScaling.Statement h := by
  intro La x₀ hLa hint hx₀ hne hiso
  obtain ⟨w₀, hvw, hww⟩ := h₁ x₀ hne hiso
  have hwv : h.toSesq w₀ x₀ = 1 := by rw [← h.isSymm.eq x₀ w₀, hvw, map_one]
  obtain ⟨N, hN, hNw⟩ := exists_nsmul_mem hLa w₀
  refine ⟨N, hN, fun ε hε => ?_⟩
  have he : ((ε : 𝓞 E) : E) ≠ 0 := by exact_mod_cast ε.ne_zero
  have hce : conj F E ((ε : 𝓞 E) : E) ≠ 0 := (map_ne_zero _).2 he
  have hinv : (((ε⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = ((ε : 𝓞 E) : E)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by exact_mod_cast ε.inv_mul)
  set e : E := ((ε : 𝓞 E) : E)
  have hcinv : (conj F E e⁻¹)⁻¹ = conj F E e := by rw [map_inv₀, inv_inv]
  have k1 : e - 1 + (e⁻¹ - 1) + (e - 1) * (e⁻¹ - 1) = 0 := sub_one_add_inv_sub_one_add_mul_eq_zero he
  have k2 : (conj F E e)⁻¹ - 1 + (conj F E e - 1) + ((conj F E e)⁻¹ - 1) * (conj F E e - 1) = 0 := by
    have := sub_one_add_inv_sub_one_add_mul_eq_zero (inv_ne_zero hce); rwa [inv_inv] at this
  have k3 : e⁻¹ - 1 + (e - 1) + (e⁻¹ - 1) * (e - 1) = 0 := by
    have := sub_one_add_inv_sub_one_add_mul_eq_zero (inv_ne_zero he); rwa [inv_inv] at this
  have k4 : conj F E e - 1 + ((conj F E e)⁻¹ - 1) + (conj F E e - 1) * ((conj F E e)⁻¹ - 1) = 0 :=
    sub_one_add_inv_sub_one_add_mul_eq_zero hce
  have h1 : scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) ∘ₗ
      scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) = LinearMap.id := by
    rw [scalingMap_comp h hiso hww hvw hwv, k1, k2, scalingMap_zero]
  have h2 : scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) ∘ₗ
      scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) = LinearMap.id := by
    rw [scalingMap_comp h hiso hww hvw hwv, k3, k4, scalingMap_zero]
  let γ : W ≃ₗ[E] W := LinearEquiv.ofLinearMap _ _ h1 h2
  have hγU : γ ∈ h.unitaryGroup := HermitianForm.mem_unitaryGroup.2 fun x y =>
    scalingMap_isometry h hiso hww hvw hwv
      (by rw [map_sub, map_inv₀, conj_conj, map_one]; exact k1) x y
  have memT : ∀ x ∈ La, scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) x ∈ La :=
    fun x hx => scalingMap_mem h hLa hint hx₀ hNw hε hx
  have memT' : ∀ x ∈ La, scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) x ∈ La := fun x hx => by
    have := scalingMap_mem h hLa hint hx₀ hNw (inv_mem hε) hx
    rwa [hinv, hcinv] at this
  refine ⟨⟨γ, hγU⟩, ?_, ?_⟩
  · rw [latticeStab, MulAction.mem_stabilizer_iff]
    ext y
    refine ⟨fun hy => ?_, fun hy => ⟨_, memT' y hy, ?_⟩⟩
    · obtain ⟨x, hx, rfl⟩ := hy
      exact memT x hx
    change scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1)
      (scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) y) = y
    rw [← LinearMap.comp_apply, h1, LinearMap.id_apply]
  · change scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) x₀ = e • x₀
    rw [scalingMap_apply, hwv, hiso]
    module

end Main

end IsotropicScaling

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTraceHermNondegenerate
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]


omit [NumberField E] in
theorem HermitianForm.eq_zero_of_toSesq_eq_zero (h : HermitianForm F E W) {x : W}
    (hx : ∀ w, h.toSesq x w = 0) : x = 0 := by
  apply h.nonsingular.1
  rw [map_zero]
  exact LinearMap.ext hx

theorem TraceHermNondegenerate.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    TraceHermNondegenerate.Statement h v := by
  have hT := (traceForm_nondegenerate ℚ E).1
  constructor
  · intro y hy
    have key : ∀ w, h.toSesq (v.equivFun.symm y) w = 0 := by
      intro w
      apply hT
      intro a
      have := hy (v.equivFun (a • w))
      rw [traceHerm_apply, LinearEquiv.symm_apply_apply, LinearMap.map_smul, smul_eq_mul] at this
      rw [Algebra.traceForm_apply, mul_comm]
      exact this
    have h0 := HermitianForm.eq_zero_of_toSesq_eq_zero h key
    exact (map_eq_zero_iff _ v.equivFun.symm.injective).1 h0
  · intro z hz
    have key : ∀ w, h.toSesq w (v.equivFun.symm z) = 0 := by
      intro w
      apply hT
      intro a
      have := hz (v.equivFun (conj F E a • w))
      rw [traceHerm_apply, LinearEquiv.symm_apply_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul] at this
      rw [Algebra.traceForm_apply, mul_comm]
      simpa [conj_conj] using this
    have key' : ∀ w, h.toSesq (v.equivFun.symm z) w = 0 := by
      intro w
      have e := (LinearMap.isSymm_def.1 h.isSymm) (v.equivFun.symm z) w
      rw [key w] at e
      exact (map_eq_zero_iff _ (conjHom F E).injective).1 e
    have h0 := HermitianForm.eq_zero_of_toSesq_eq_zero h key'
    exact (map_eq_zero_iff _ v.equivFun.symm.injective).1 h0

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

