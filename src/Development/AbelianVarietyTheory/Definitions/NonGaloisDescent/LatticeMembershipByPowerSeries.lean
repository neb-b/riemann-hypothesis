module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv

@[expose] public section

noncomputable section
namespace GlobalTheory.PhiGam.Model
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam

section
variable (k : Type) [Field k]

theorem algebraMap_eq (c : k) : algebraMap k k⸨X⸩ c = HahnSeries.C c := by rw [HahnSeries.algebraMap_apply', ← HahnSeries.ofPowerSeries_C]; rfl

theorem smul_eq (c : k) (x : k⸨X⸩) : c • x = algebraMap k k⸨X⸩ c * x := by rw [algebraMap_eq, HahnSeries.C_mul_eq_smul]

instance towerA : IsScalarTower k k⸨X⸩ k⸨X⸩ := ⟨fun c x y => by
  rw [smul_eq, smul_eq k c, smul_eq_mul, smul_eq_mul, mul_assoc]⟩

instance towerB : IsScalarTower k k⟦X⟧ k⸨X⸩ := ⟨fun c a y => by
  rw [smul_eq k c, Algebra.smul_def (c • a), Algebra.smul_def a, Algebra.smul_def c, map_mul, mul_assoc]
  rfl⟩

end

section
variable {k : Type} [Field k]

end

section
variable {k : Type} [Field k]

theorem gmult_top_bot {U : Type} [AddCommGroup U] [Module k U] (T : Module.End k U) (x : k) :
    gmult T ⊤ ⊥ x = Module.finrank k (T.maxGenEigenspace x) := by
  have hS : (⨆ m : ℕ, (⊥ : Submodule k U).comap ((T - algebraMap k (Module.End k U) x) ^ m))
      = T.maxGenEigenspace x := by
    apply le_antisymm
    · refine iSup_le fun m y hy => ?_
      rw [Submodule.mem_comap, Submodule.mem_bot, Algebra.algebraMap_eq_smul_one] at hy
      exact (Module.End.mem_maxGenEigenspace T x y).mpr ⟨m, hy⟩
    · intro y hy
      obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace T x y).mp hy
      refine Submodule.mem_iSup_of_mem m ?_
      rw [Submodule.mem_comap, Submodule.mem_bot, Algebra.algebraMap_eq_smul_one]
      exact hm
  unfold gmult
  rw [top_inf_eq, hS]
  have hb : (⊥ : Submodule k U).submoduleOf (T.maxGenEigenspace x) = ⊥ := by
    ext y
    simp [Submodule.submoduleOf]
  rw [hb]
  exact (Submodule.quotEquivOfEqBot _ rfl).finrank_eq

end

end GlobalTheory.PhiGam.Model
