module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KisinCrystalline.TypeSt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc UpperTheory.V.Lit

section
open TensorProduct GlobalTheory.Pst Polynomial Matrix

private theorem zpow_fix {Q R : Type} [Field Q] [CommRing R] [Algebra Q R] (f : R →ₐ[Q] R) (T : Rˣ) (c : Qˣ)
    (h : f (T : R) = (c : Q) • T) (m : ℤ) :
    ((c ^ m : Qˣ) : Q) • f ((T ^ (-m) : Rˣ) : R) = ((T ^ (-m) : Rˣ) : R) := by
  have e : Units.map (f : R →* R) T = Units.map (algebraMap Q R : Q →* R) c * T := by
    ext; simpa [Algebra.smul_def] using h
  have e' : Units.map (algebraMap Q R : Q →* R) (c ^ m) * Units.map (f : R →* R) (T ^ (-m)) = T ^ (-m) := by
    rw [map_zpow, map_zpow, e, mul_zpow, ← mul_assoc, ← _root_.zpow_add]; simp
  rw [Algebra.smul_def]
  exact congrArg Units.val e'

private theorem exists_phi {Q B R : Type} [Field Q] [CommRing B] [Algebra Q B] [CommRing R] [Algebra Q R]
    (n : ℕ) (u : Rˣ) :
    ∃ Φ : (Fin n → B) ⊗[Q] R ≃ₗ[Q] ((Fin n → B) →ₗ[B] B ⊗[Q] R),
      ∀ v r w, Φ (v ⊗ₜ r) w = (v ⬝ᵥ w) ⊗ₜ ((u : R) * r) := by
  refine ⟨(LinearEquiv.lTensor (Fin n → B) (u.mulLeftLinearEquiv Q R)).trans
    ((TensorProduct.piLeft Q R (fun _ : Fin n => B)).trans ((Pi.basisFun B (Fin n)).constr Q)), fun v r w => ?_⟩
  simp [Module.Basis.constr_apply_fintype, dotProduct, sum_tmul, smul_tmul', mul_comm, TensorProduct.piLeft]

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {B : Type} [CommRing B] [Algebra ℚ_[l] B]

private theorem transfer {V W : Type} [AddCommGroup V] [Module B V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] B V]
    [AddCommGroup W] [Module B W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] B W]
    (ρ : Representation B ↥(GK K) V) (σ : Representation B ↥(GK K) W)
    (Φ : V ⊗[ℚ_[l]] Bst (PP l) ≃+ (W →ₗ[B] B ⊗[ℚ_[l]] Bst (PP l)))
    (h1 : ∀ (g : ↥(GK K)) x, Φ (stRep (PP l) (resCoef ℚ_[l] ρ) g x) =
      (actBst (g : GQ l)).comp ((Φ x).comp (σ g⁻¹)))
    (h2 : ∀ c x, Φ (Thick.sm V (Bst (PP l)) c x) = (LinearMap.mulLeft B (toSt c)).comp (Φ x))
    (n : ℕ) (t : ↥(GK K) → B) : TypeSt K ρ n t ↔ TypeLit K σ n t := by
  have h3 : ∀ x, x ∈ Dpst (PP l) (resCoef ℚ_[l] ρ) ↔ Φ x ∈ DpstHom K σ := by
    intro x
    rw [mem_Dpst]
    refine exists_congr fun K' => forall_congr' fun g => imp_congr_right fun _ => ?_
    rw [← Φ.injective.eq_iff, h1]
    constructor
    · intro h v
      conv_lhs => rw [← h]
      simp
    · intro h
      ext1 v
      simp [← h]
  have h4 : ∀ (y : V ⊗[ℚ_[l]] Bst (PP l)) (c : Fin n → B ⊗[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) (x : Fin n → V ⊗[ℚ_[l]] Bst (PP l)),
      y = ∑ a, Thick.sm V (Bst (PP l)) (c a) (x a) ↔
        Φ y = ∑ a, (LinearMap.mulLeft B (toSt (c a))).comp (Φ (x a)) := by
    intro y c x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Φ.injective.eq_iff, map_sum]
    simp only [h2]
  unfold TypeSt TypeLit
  refine (Equiv.piCongrRight fun _ : Fin n => Φ.toEquiv).exists_congr fun x => ?_
  refine and_congr (forall_congr' fun a => h3 _) (and_congr ?_ ?_)
  · refine Φ.toEquiv.forall_congr fun y => imp_congr (h3 _) (existsUnique_congr fun c => h4 _ _ _)
  · refine forall_congr' fun γ => imp_congr_right fun _ => forall_congr' fun M => imp_congr_left
      (forall_congr' fun b => ?_)
    rw [h4 _ (fun a => M a b), h1]
    rfl

end

