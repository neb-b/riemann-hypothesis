module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsJetPointsOfIsLieBasis
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetPoint

open GlobalTheory.SqZero

variable {R : Type} [CommRing R]

theorem jetTruncR_surjective (κ : Type) (m : ℕ) : Function.Surjective (jetTruncR R κ m) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

theorem jetAug_comp_jetTruncR (κ : Type) (m : ℕ) :
    (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) :=
  jet_ext fun j => by
    rw [jetAug_zR]
    exact jetAug_zR (R := R) m j

theorem ker_jetTruncR_isNilpotent (κ : Type) (m : ℕ) :
    IsNilpotent (RingHom.ker (jetTruncR R κ m)) := by
  have hle : RingHom.ker (jetTruncR R κ m) ≤ RingHom.ker (jetAug R κ (m + 1)) := by
    intro a ha
    have ha' : jetTruncR R κ m a = 0 := ha
    change jetAug R κ (m + 1) a = 0
    rw [← jetAug_comp_jetTruncR, AlgHom.comp_apply, ha', map_zero]
  refine ⟨m + 1 + 1, ?_⟩
  rw [Ideal.zero_eq_bot, ← le_bot_iff, ← ker_jetAug_pow (R := R) κ (m + 1)]
  exact Ideal.pow_right_mono hle _

theorem jetZeroR_comp_jetTruncR (κ : Type) (m : ℕ) :
    (jetZeroR R κ m).comp (jetTruncR R κ m) = jetZeroR R κ (m + 1) :=
  jet_ext fun _ => rfl

theorem zR_zero_eq_zero {κ : Type} (j : κ) : zR (R := R) 0 j = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (by
    rw [zero_add, pow_one]
    exact Ideal.subset_span ⟨j, rfl⟩)

theorem zR_one_mul_self {κ : Type} (j : κ) : zR (R := R) 1 j * zR (R := R) 1 j = 0 :=
  mul_eq_zero_of_sq (ker_jetAug_pow (R := R) κ 1) (zR_mem_ker 1 j) (zR_mem_ker 1 j)

end GlobalTheory.JetPoint

namespace GlobalTheory

open SqZero JetPoint

theorem exists_jetPoints_of_isLieBasis :
    ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∃ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) ∧ (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) ∧ (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) := by
  intro R _ G _ _ hG d v hv
  have htan : ∀ i, IsTan (v i) := fun i => (isTan_iff _).2 (hv.1 i)
  choose L hL using fun m => ptsMap_surjective_of_isNilpotent (G := G) hv (jetTruncR R (Fin d) m)
    (jetTruncR_surjective _ m) (ker_jetTruncR_isNilpotent _ m)
  let x₁ : sp (R₀ := R) (JetR R (Fin d) 1) ⟶ G :=
    lieExp v (fun j => zR (R := R) 1 j) zR_one_mul_self
  let y : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) (m + 1)) ⟶ G :=
    fun m => Nat.rec (motive := fun m => sp (R₀ := R) (JetR R (Fin d) (m + 1)) ⟶ G) x₁
      (fun k z => L (k + 1) z) m
  let x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G :=
    fun m => Nat.casesOn (motive := fun m => sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) m 1 y
  have h₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m := by
    rintro (_ | m)
    · change spMap _ ≫ lieExp v _ _ = 1
      rw [comp_lieExp, lieExp]
      exact Finset.prod_eq_one fun i _ => epsTo_zero_comp (htan i) _ (zR_zero_eq_zero i) _
    · exact hL (m + 1) (y m)
  refine ⟨x, h₁, fun m => ?_, fun j => ?_⟩
  · induction m with
    | zero => exact comp_one' _
    | succ m ih => rw [← jetZeroR_comp_jetTruncR, ← spMap_comp, Category.assoc, h₁, ih]
  · change spMap _ ≫ lieExp v _ _ = _
    rw [comp_lieExp, lieExp, Finset.prod_eq_single j]
    · have : ∀ (t : DualNumber R) (ht : t * t = 0), t = DualNumber.eps →
          epsTo R t ht = AlgHom.id R _ := fun t ht e =>
        DualNumber.algHom_ext (by rw [epsTo_eps, e]; rfl)
      rw [this _ _ (by rw [dualLift_zR, Pi.single_eq_same]; rfl), spMap_id]
      exact Category.id_comp _
    · intro i _ hi
      exact epsTo_zero_comp (htan i) _
        (by rw [dualLift_zR, Pi.single_eq_of_ne hi, TrivSqZeroExt.inr_zero]) _
    · simp

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FirstJetEqProdTangent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open SqZero TrivSqZeroExt

theorem firstJet_eq_aug_add_sum {R : Type} [CommRing R] {d : ℕ} (a : JetR R (Fin d) 1) :
    a = algebraMap R _ (jetAug R (Fin d) 1 a) +
      ∑ j, algebraMap R _ (dualLift (Pi.single j (1 : R)) a).snd * zR 1 j := by
  let Φ : JetR R (Fin d) 1 →ₐ[R] TrivSqZeroExt R (Fin d → R) :=
    jetLift (R := R) (RingHom.ker (fstHom R R (Fin d → R))) (ker_fst_sq _)
      (fun j => inr (Pi.single j 1)) (fun _ => (RingHom.mem_ker).mpr rfl)
  have hΦ : ∀ j, Φ (zR 1 j) = inr (Pi.single j 1) := fun j => jetLift_zR _ _ _ _ j
  have hz : ∀ i j : Fin d, zR (R := R) 1 i * zR 1 j = 0 := fun i j =>
    mul_eq_zero_of_sq (ker_jetAug_pow (R := R) (Fin d) 1) (zR_mem_ker 1 i) (zR_mem_ker 1 j)
  have h₁ : (vecTo (Algebra.ofId R _) (zR 1) hz).comp Φ = AlgHom.id R _ :=
    jet_ext fun j => by rw [AlgHom.comp_apply, hΦ, vecTo_single, AlgHom.id_apply]
  have h₂ : (fstHom R R (Fin d → R)).comp Φ = jetAug R (Fin d) 1 :=
    jet_ext fun j => by rw [AlgHom.comp_apply, hΦ, jetAug_zR]; rfl
  have h₃ : ∀ j, (TrivSqZeroExt.map (LinearMap.proj j : (Fin d → R) →ₗ[R] R)).comp Φ =
      dualLift (Pi.single j (1 : R)) := fun j => jet_ext fun i => by
    rw [AlgHom.comp_apply, hΦ, dualLift_zR, map_inr, LinearMap.proj_apply, Pi.single_apply,
      Pi.single_apply]
    simp only [eq_comm]
  conv_lhs => rw [← AlgHom.id_apply (R := R) a, ← h₁, AlgHom.comp_apply, vecTo_apply]
  simp only [← h₂, ← h₃, AlgHom.comp_apply, snd_map, LinearMap.proj_apply]
  rfl

theorem firstJet_eq_prod_tangent : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)),
    IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G),
    (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) →
    (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) →
    ∀ (A : Type) [CommRing A] [Algebra R A] (ψ : JetR R (Fin d) 1 →ₐ[R] A)
      (e : Fin d → (DualNumber R →ₐ[R] A)), (∀ j, e j (TrivSqZeroExt.inr 1) = ψ (zR 1 j)) →
      spMap ψ ≫ x 1 = ∏ j, (spMap (e j) ≫ v j : sp (R₀ := R) A ⟶ G) := by
  set_option maxHeartbeats 200000 in
    intro R _ G _ _ hG d v hv x hx0 hx1 A _ _ ψ e he
    have haug : spMap (jetAug R (Fin d) 1) ≫ x 1 = 1 := by
      have e : jetAug R (Fin d) 1 = (jetAug R (Fin d) 0).comp (jetZeroR R (Fin d) 1) :=
        jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact (jetAug_zR (R := R) 0 j).symm
      rw [e, ← spMap_comp, Category.assoc, hx0 1, comp_one']
    letI : Smooth G.hom := hG
    let J := RingHom.ker (jetAug R (Fin d) 1)
    have hJ : J ^ 2 = ⊥ := ker_jetAug_pow (R := R) (Fin d) 1
    obtain ⟨c', hc'⟩ := (expHom_bijective (A := JetR R (Fin d) 1) hv hJ).2
      ⟨x 1, mem_redKer_of_section _ (Algebra.ofId R _) (fun a => (jetAug R (Fin d) 1).commutes a) haug⟩
    let c : Fin d → JetR R (Fin d) 1 := fun i => c' i
    have hcJ : ∀ i, c i ∈ J := fun i => (c' i).2
    have hc : ∀ i, c i * c i = 0 := fun i => mul_eq_zero_of_sq hJ (hcJ i) (hcJ i)
    have hxc : x 1 = lieExp v c hc := by
      have h := congrArg (fun y : Additive (redKer (R := R) G J) =>
        ((y.toMul : redKer (R := R) G J) : sp (R₀ := R) (JetR R (Fin d) 1) ⟶ G)) hc'
      rw [expHom_apply] at h
      exact h.symm
    have hs : ∀ j i : Fin d, dualLift (Pi.single j (1 : R)) (c i) =
        inr ((Pi.single j (1 : R) : Fin d → R) i) := fun j => by
      have h₁ := hx1 j
      rw [hxc, comp_lieExp] at h₁
      have h₂ : lieExp v (fun i => (inr ((Pi.single j (1 : R) : Fin d → R) i) : DualNumber R))
          (fun _ => inr_mul_inr _ _ _) = v j := by
        rw [lieExp, Finset.prod_eq_single j]
        · rw [← scaleD_eq, Pi.single_eq_same, scaleD_one, spMap_id]
          exact Category.id_comp _
        · intro i _ hi
          exact epsTo_zero_comp ((isTan_iff _).2 (hv.1 i)) _
            (by rw [Pi.single_eq_of_ne hi, inr_zero]) _
        · exact fun h => absurd (Finset.mem_univ j) h
      have h₃ : ∀ i, dualLift (Pi.single j (1 : R)) (c i) ∈ RingHom.ker (fstD R) := fun i => by
        rw [RingHom.mem_ker, ← AlgHom.comp_apply, fstD_comp_dualLift]
        exact hcJ i
      intro i
      have heq : expHom hv.1 (J := RingHom.ker (fstD R)) kerD_sq (fun i => ⟨dualLift (Pi.single j (1 : R)) (c i), h₃ i⟩) =
          expHom hv.1 (J := RingHom.ker (fstD R)) kerD_sq (fun i => ⟨inr ((Pi.single j (1 : R) : Fin d → R) i), inr_mem_kerD _⟩) := by
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [expHom_apply, expHom_apply]
        exact h₁.trans h₂.symm
      have heq' := congrFun ((expHom_bijective (A := DualNumber R) (J := RingHom.ker (fstD R)) hv kerD_sq).1 heq) i
      exact congrArg Subtype.val heq'

    have hcz : ∀ i, c i = zR 1 i := fun i => by
      rw [firstJet_eq_aug_add_sum (c i), (hcJ i : jetAug R (Fin d) 1 (c i) = 0), map_zero, zero_add,
        Finset.sum_eq_single i]
      · rw [hs, snd_inr, Pi.single_eq_same, map_one, _root_.one_mul]
      · intro j _ hj
        rw [hs, snd_inr, Pi.single_eq_of_ne hj.symm, map_zero, zero_mul]
      · exact fun h => absurd (Finset.mem_univ i) h
    rw [hxc, comp_lieExp, lieExp]
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 2
    exact DualNumber.algHom_ext (by rw [epsTo_eps, hcz]; exact (he j).symm)

end GlobalTheory
end
end

