module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CokerDual
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.cokerDual :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (g : Module.End ℤ_[l] M) (t : Module.End ℤ_[l] (M →ₗ[ℤ_[l]] QZ l)), (∀ x φ, t x φ = x (g φ)) →
        cokerLen t = Module.length ℤ_[l] (LinearMap.ker g) := by
  intro l _ M _ _ g t h
  have ht : t = LinearMap.lcomp ℤ_[l] (QZ l) g := LinearMap.ext fun x => LinearMap.ext fun φ => h x φ
  obtain ⟨h1, h2⟩ := UpperTheory.V.Tower.dualKer l M M g
  have hr : LinearMap.range t
      = LinearMap.ker (LinearMap.lcomp ℤ_[l] (QZ l) (LinearMap.ker g).subtype) := by
    rw [ht]; exact h1
  rw [← UpperTheory.V.Tower.lenDual l (LinearMap.ker g)]
  exact ((Submodule.quotEquivOfEq _ _ hr).trans
    (LinearMap.quotKerEquivOfSurjective _ (h2 (LinearMap.ker g)))).length_eq
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.LayerGen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.layerGen :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], HasMuQ l L → (∀ m, (layU l L Ω m).index = l ^ m) ∧
        ∀ γ : G L Ω, IsGen l ⊤ γ → PropA.IsLevel l (cycZ L Ω l γ : ℤ_[l]ˣ) (cZero l L) ∧ γ ∈ levU l ⊤ 1 ∧ ∀ m, IsGen l (layU l L Ω m) (γ ^ l ^ m) := by
  intro L Ω _ _ _ _ _ l _ hmu
  obtain ⟨-, h2, h3, -⟩ := muQ L Ω l
  have hq := h3.1 hmu
  have hr := cycRange L Ω l hmu
  obtain ⟨p1, p2, p3⟩ := princGen l _ hq
  have h0 : ∀ g, cycZ L Ω l g ∈ KStar.TotallyRealRoots.princ l (cZero l L) := fun g => hr ▸ ⟨g, rfl⟩
  have hU : ∀ n, Un L Ω l n = (KStar.TotallyRealRoots.princ l n).comap (cycZ L Ω l) := fun n =>
    Subgroup.ext fun g => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  have h1 : 1 ≤ cZero l L := by
    refine le_trans ?_ hq
    unfold qExp
    split_ifs <;> omega
  refine ⟨fun m => ?_, fun γ hγ => ?_⟩
  · rw [layU, hU, Subgroup.index_comap, hr, p3]
  · have hn : cycZ L Ω l γ ∉ KStar.TotallyRealRoots.princ l (cZero l L + 1) := by
      refine (p1 _ (h0 γ)).1 ?_
      rw [← hr, MonoidHom.range_eq_map]
      exact hγ.2
    obtain ⟨q1, q2⟩ := p2 _ (h0 γ) hn
    refine ⟨q1, ?_, fun m => ⟨?_, ?_⟩⟩
    · have : γ ∈ Un L Ω l 1 := by rw [(h2 1).2 h1]; trivial
      exact this
    · rw [layU, hU, Subgroup.mem_comap, map_pow]
      exact (q2 m).1
    · rw [layU, hU, map_pow]
      exact (Subgroup.map_comap_le _ _).trans
        (((princGen l (cZero l L + m) (hq.trans (Nat.le_add_right _ _))).1 _ (q2 m).1).2 (q2 m).2)
end

