module

public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.CompactFixesLattice
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.CoordMulTmul
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def coord {ι : Type} (b : Module.Basis ι F E) (i : ι) : AE F E →ₗ[F] AF F :=
  (TensorProduct.lid F (AF F)).toLinearMap ∘ₗ LinearMap.rTensor (AF F) (b.coord i)

theorem coord_tmul {ι : Type} (b : Module.Basis ι F E) (i : ι) (e : E) (a : AF F) :
    coord b i (e ⊗ₜ[F] a) = b.repr e i • a := by
  simp [coord, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Module.Basis.coord_apply]

theorem sum_coord {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (x : AE F E) :
    ∑ i, b i ⊗ₜ[F] coord b i x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    simp only [coord_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← TensorProduct.sum_tmul,
      Module.Basis.sum_repr]
  | add x y hx hy =>
    simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

theorem coord_mul_tmul {ι : Type} (b : Module.Basis ι F E) (i : ι) (x : AE F E) (a : AF F) :
    coord b i (x * ((1 : E) ⊗ₜ[F] a)) = coord b i x * a := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e a' =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, coord_tmul, coord_tmul, smul_mul_assoc]
  | add x y hx hy =>
    rw [add_mul, map_add (f := _), map_add (f := _), hx, hy, add_mul]

theorem continuous_coord {ι : Type} (b : Module.Basis ι F E) (i : ι) :
    letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    Continuous (coord b i) := by
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  letI : Algebra (AF F) (AE F E) := Algebra.TensorProduct.rightAlgebra
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  let f : AE F E →ₗ[AF F] AF F :=
    { toFun := coord b i
      map_add' := map_add _
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [Algebra.smul_def, mul_comm,
          show algebraMap (AF F) (AE F E) r = (1 : E) ⊗ₜ[F] r from rfl, coord_mul_tmul, mul_comm] }
  exact IsModuleTopology.continuous_of_linearMap f

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompactAdele
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isOpen_intAd : IsOpen ((intAd F : Subring (AF F)) : Set (AF F)) :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

theorem algebraMap_mem_intAd (m : 𝓞 F) : algebraMap F (AF F) (m : F) ∈ intAd F :=
  fun v => Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.int_R v m

theorem smul_mem_intAd (m : 𝓞 F) {a : AF F} (ha : a ∈ intAd F) : (m : F) • a ∈ intAd F := by
  rw [Algebra.smul_def]
  exact mul_mem (algebraMap_mem_intAd m) ha

theorem exists_sub_mem_intAd (a : AF F) : ∃ u : F, a - algebraMap F (AF F) u ∈ intAd F :=
  Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx_adele (R := 𝓞 F) (K := F) a

theorem mem_range_of_mem_intAd (u : F) (h : algebraMap F (AF F) u ∈ intAd F) :
    u ∈ (algebraMap (𝓞 F) F).range :=
  Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.mem_of_isInt (R := 𝓞 F) u h

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.Imports
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_basis (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) F E) (D : 𝓞 F), D ≠ 0 ∧ (∀ i, b i ∈ intOE E) ∧
      ∀ e ∈ intOE E, ∀ i, (D : F) * b.repr e i ∈ (algebraMap (𝓞 F) F).range := by
  classical
  let β : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → E := fun j =>
    algebraMap (𝓞 E) E (NumberField.RingOfIntegers.basis E j)
  have hspanQ : Submodule.span ℚ (Set.range β) = ⊤ := by
    have h := (NumberField.integralBasis E).span_eq
    have hr : Set.range (NumberField.integralBasis E) = Set.range β := by
      ext x
      simp [β, NumberField.integralBasis_apply]
    rw [hr] at h
    exact h
  have hspan : Submodule.span F (Set.range β) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℚ (Set.range β) := by rw [hspanQ]; exact Submodule.mem_top
    exact Submodule.span_le_restrictScalars ℚ F _ hx
  obtain ⟨B, hBsub, hBspan, hBli⟩ := exists_linearIndependent F (Set.range β)
  have hBfin : B.Finite := (Set.finite_range β).subset hBsub
  haveI := hBfin.fintype
  let e := Fintype.equivFin B
  let b0 : Module.Basis B F E := Module.Basis.mk hBli (by rw [Subtype.range_coe, hBspan, hspan])
  let b : Module.Basis (Fin (Fintype.card B)) F E := b0.reindex e
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
    ((Finset.univ : Finset (Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin (Fintype.card B))).image
      fun p => b.repr (β p.1) p.2)
  refine ⟨Fintype.card B, b, (D : 𝓞 F), nonZeroDivisors.ne_zero D.2, ?_, ?_⟩
  · intro i
    have hbi : b i = ((e.symm i : B) : E) := by simp [b, b0]
    obtain ⟨j, hj⟩ := hBsub (e.symm i).2
    rw [hbi, ← hj]
    exact RingHom.mem_range.mpr ⟨_, rfl⟩
  · intro x hx i
    obtain ⟨y, rfl⟩ := RingHom.mem_range.mp hx
    have key : ∀ j, ((D : 𝓞 F) : F) * b.repr (β j) i ∈ (algebraMap (𝓞 F) F).range := by
      intro j
      obtain ⟨z, hz⟩ := hD (b.repr (β j) i) (Finset.mem_image.mpr ⟨(j, i), Finset.mem_univ _, rfl⟩)
      refine RingHom.mem_range.mpr ⟨z, ?_⟩
      rw [hz, Algebra.smul_def]
    have hxe : algebraMap (𝓞 E) E y = ∑ j, ((NumberField.RingOfIntegers.basis E).repr y j) • β j := by
      conv_lhs => rw [← (NumberField.RingOfIntegers.basis E).sum_repr y]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp [β, map_zsmul]
    rw [hxe]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, Finset.mul_sum, mul_smul_comm]
    exact Subring.sum_mem _ fun j _ => Subring.zsmul_mem _ (key j) _

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
end

