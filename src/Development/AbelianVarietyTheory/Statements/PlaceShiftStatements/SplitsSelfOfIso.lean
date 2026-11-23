module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.GalV

def VFin : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], IsUnit (l : k) → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (n i : ℤ),
  Module.Finite ℤ_[l] (Hl l (sch.obj X) n i) ∧ FiniteDimensional ℚ_[l] (HQ l (sch.obj X) n i)

def VInv : Prop := ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, Function.Injective (pullHQ l (sch.map f) n i) ∧
  LinearMap.range (pullHQ l (sch.map f) n i) = ⨅ g, LinearMap.ker (pullHQ l (sch.map (a g)) n i - LinearMap.id)

end GlobalTheory.GalV

namespace GlobalTheory.GalV.GaloisTowerConditions

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

theorem geomMap_isIso {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k)}
    (u : X ⟶ Y) [IsIso u] (hu : u ≫ q = p) : IsIso (GlobalTheory.Et.geomMap Ω p u hu) := by
  refine ⟨⟨GlobalTheory.Et.geomMap Ω q (inv u) (by simp [← hu]), ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
    · simp only [GlobalTheory.Et.geomMap, Category.assoc, pullback.lift_snd, Category.id_comp]

instance isIso_idTower_sΩ (g : (HTower.idTower k).Γ) : IsIso ((HTower.idTower k).sΩ Ω g) :=
  geomMap_isIso Ω (k := k) (𝟙 _) rfl

theorem splits_self_of_iso {Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsIso s] : Splits s s (fun _ : Unit => 𝟙 Y) := by
  refine ⟨fun _ => Category.id_comp _, ?_⟩
  have hl : IsIso (pullback.lift (𝟙 Y) (𝟙 Y) (by simp) : Y ⟶ pullback s s) := by
    have : IsIso (pullback.lift (𝟙 Y) (𝟙 Y) (by simp) ≫ pullback.fst s s) := by
      rw [pullback.lift_fst]; infer_instance
    exact IsIso.of_isIso_comp_right _ (pullback.fst _ _)
  refine ⟨⟨inv (pullback.lift (𝟙 Y) (𝟙 Y) rfl : Y ⟶ pullback s s) ≫ Sigma.ι (fun _ : Unit => Y) (), ?_, ?_⟩⟩
  · apply Sigma.hom_ext; intro j; cases j; simp
  · simp

theorem idTower_isCorrOp (l : ℕ) [Fact l.Prime] (g : (HTower.idTower k).Γ) :
    IsCorrOp l ((HTower.idTower k).sΩ Ω g) ((HTower.idTower k).tΩ Ω g) LinearMap.id := by
  refine ⟨_, (HTower.idTower k).sΩ Ω g, Unit, inferInstance, inferInstance, fun _ => 𝟙 _, Unit, inferInstance,
    fun _ => 𝟙 _, ⟨inferInstance, inferInstance, inferInstance, rfl, fun _ _ => (Category.id_comp _).symm,
      splits_self_of_iso _⟩, splits_self_of_iso _, fun x => ?_⟩
  simp only [LinearMap.id_apply, Finset.univ_unique, Finset.sum_singleton, Category.id_comp] <;> rfl

end GlobalTheory.GalV.GaloisTowerConditions

end
