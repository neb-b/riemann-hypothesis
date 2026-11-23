module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0027

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.RhoFfEqUnitMul
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {Λ κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}

theorem rho_ff_eq_unit_mul [IsDomain O] (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) {j M g η : ℕ} {kind : ℕ → Kind} {b : ℕ → ℕ}
    (hk1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b)
    (hU : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt) (hj : j ≤ ell)
    (s : ℕ) (hs : s < ell) :
    ∃ ε : (PowerSeries (KsW W s))ˣ, rhoL hR c s ((baseIdOf hR).Bs.ff' ell j M g) =
      (ε : PowerSeries (KsW W s)) * PowerSeries.X ^ ordF ell j (baseIdOf hR).Bs.ℓ M g s := by
  obtain ⟨u, hu⟩ := filtration_shape_holds O (baseIdOf hR).Bs ell j M g hj (frobenius_uniformizer_identity hR)
  obtain ⟨ε, hε⟩ := hk1b s hs
  have hε' : rhoL hR c s ((baseIdOf hR).Bs.p s) = (ε : PowerSeries (KsW W s)) * PowerSeries.X := hε
  have hX : IsUnit (rhoL hR c s PowerSeries.X) := (hU s hs).1
  have hp : ∀ s' < ell, s' ≠ s → IsUnit (rhoL hR c s ((baseIdOf hR).Bs.p s')) := (hU s hs).2
  have hV : IsUnit (rhoL hR c s (u : PowerSeries O) * rhoL hR c s PowerSeries.X ^ M *
      ∏ s' ∈ (Finset.range ell).erase s,
        rhoL hR c s ((baseIdOf hR).Bs.p s' ^ ordF ell j (baseIdOf hR).Bs.ℓ M g s')) := by
    refine ((u.isUnit.map (rhoL hR c s)).mul (hX.pow M)).mul
      (Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun s' hs' => ?_)
    rw [map_pow]
    exact (hp s' (Finset.mem_range.1 (Finset.mem_of_mem_erase hs')) (Finset.ne_of_mem_erase hs')).pow _
  refine ⟨hV.unit * ε ^ ordF ell j (baseIdOf hR).Bs.ℓ M g s, ?_⟩
  rw [hu, map_mul, map_mul, map_pow, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs), map_pow,
    hε', Units.val_mul, IsUnit.unit_spec, Units.val_pow_eq_pow_val]
  ring

theorem rho_sub_mem [IsDomain O] (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) {j M g η : ℕ} {kind : ℕ → Kind} {b : ℕ → ℕ}
    (hk1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b)
    (hU : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt) (hj : j ≤ ell)
    (h3g : 3 * g ≤ ((baseIdOf hR).Bs.ℓ - 1) * M) (s : ℕ) (hs : s < ell) :
    ∀ z ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T c) ((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ)),
      ∃ y ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T c) 0),
        z = HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s ((baseIdOf hR).Bs.ff' ell j M g)) • y := by
  intro z hz
  obtain ⟨ε, hε⟩ := rho_ff_eq_unit_mul Hy hk1b hU hj s hs
  have hle : ordF ell j (baseIdOf hR).Bs.ℓ M g s ≤ ((baseIdOf hR).Bs.ℓ - 1) * M := by
    unfold ordF
    split_ifs <;> omega
  have hTw : (fun i : ℤ => Tw (LL := LL) (D := Dc W T c) 0 (i + -((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ))) =
      Tw (LL := LL) (D := Dc W T c) ((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ) := by
    funext i
    unfold Tw
    by_cases h : ((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ) ≤ i
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  have hz' : tp (KsW W s) (-((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ)) • z ∈
      Xi (KsW W s) (Tw (LL := LL) (D := Dc W T c) 0) :=
    (xi_shift_holds LL (KsW W s) (Dc W T c) _ _ z).2 (by rw [hTw]; exact hz)
  refine ⟨HahnSeries.ofPowerSeries ℤ (KsW W s) ((↑ε⁻¹ : PowerSeries (KsW W s)) *
      PowerSeries.X ^ (((baseIdOf hR).Bs.ℓ - 1) * M - ordF ell j (baseIdOf hR).Bs.ℓ M g s)) •
      (tp (KsW W s) (-((((baseIdOf hR).Bs.ℓ - 1) * M : ℕ) : ℤ)) • z),
    xi_module_structure LL (KsW W s) (Dc W T c) _ (tw_mono 0) _ _ hz', ?_⟩
  have hmul : (ε : PowerSeries (KsW W s)) * PowerSeries.X ^ ordF ell j (baseIdOf hR).Bs.ℓ M g s *
      ((↑ε⁻¹ : PowerSeries (KsW W s)) *
        PowerSeries.X ^ (((baseIdOf hR).Bs.ℓ - 1) * M - ordF ell j (baseIdOf hR).Bs.ℓ M g s)) =
      PowerSeries.X ^ (((baseIdOf hR).Bs.ℓ - 1) * M) := by
    rw [mul_mul_mul_comm, Units.mul_inv, one_mul, ← pow_add, Nat.add_sub_cancel' hle]
  rw [hε, ← mul_smul, ← map_mul, hmul, ← mul_smul, HahnSeries.ofPowerSeries_X_pow, tp,
    HahnSeries.single_mul_single, add_neg_cancel, one_mul, HahnSeries.single_zero_one, one_smul]

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.TensorSumSingleEval
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

section Free

variable {LL D ι : Type} [Field LL] [AddCommGroup D] [Module LL D] [Fintype ι] [DecidableEq ι]

def evK (i : ι) : (ι → LL) ⊗[LL] D →ₗ[LL] D :=
  (TensorProduct.lid LL D).toLinearMap ∘ₗ LinearMap.rTensor D (LinearMap.proj i)

theorem evaluation_tmul (i : ι) (b : ι → LL) (d : D) : evK i (b ⊗ₜ[LL] d) = b i • d := by
  simp [evK]

theorem evaluation_smul (i : ι) (a : ι → LL) (z : (ι → LL) ⊗[LL] D) :
    evK i (a • z) = a i • evK i z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b d =>
    rw [TensorProduct.smul_tmul', evaluation_tmul, evaluation_tmul, smul_eq_mul, Pi.mul_apply,
      mul_smul]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem tensor_sum_single_eval (z : (ι → LL) ⊗[LL] D) :
    z = ∑ i, (Pi.single i (1 : LL) : ι → LL) ⊗ₜ[LL] evK i z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b d =>
    have hb : ∑ i, b i • (Pi.single i (1 : LL) : ι → LL) = b := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    simp_rw [evaluation_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, hb]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib]

theorem mem_baseChange_iff (X : Submodule LL D) (z : (ι → LL) ⊗[LL] D) :
    z ∈ X.baseChange (ι → LL) ↔ ∀ i, evK i z ∈ X := by
  constructor
  · intro h i
    have h' : z ∈ Submodule.span (ι → LL)
        ((X.map (TensorProduct.mk LL (ι → LL) D 1) : Submodule LL _) : Set ((ι → LL) ⊗[LL] D)) := by
      rw [← Submodule.baseChange_eq_span]; exact h
    clear h
    induction h' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      simpa [evaluation_tmul] using hm
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact X.add_mem hx hy
    | smul a x _ hx => rw [evaluation_smul]; exact X.smul_mem _ hx
  · intro h
    rw [tensor_sum_single_eval z]
    exact Submodule.sum_mem _ fun i _ => Submodule.tmul_mem_baseChange_of_mem _ (h i)

theorem xi_iff (X : ℤ → Submodule LL D) (f : Amb LL (ι → LL) D) :
    f ∈ Xi (ι → LL) X ↔ ∀ i k, evK i (cf f k) ∈ X k := by
  change (∀ k, cf f k ∈ (X k).baseChange (ι → LL)) ↔ _
  simp only [mem_baseChange_iff]
  exact forall_comm

theorem xi_unit_tp (X : ℤ → Submodule LL D) (hX : Monotone X) (a b : PowerSeries (ι → LL)) (hab : a * b = 1)
    (g : ℤ) (f : Amb LL (ι → LL) D) :
    (HahnSeries.ofPowerSeries ℤ (ι → LL) a * tp (ι → LL) g) • f ∈ Xi (ι → LL) X ↔
      f ∈ Xi (ι → LL) (fun i => X (i + g)) := by
  rw [mul_smul, ← xi_shift_holds LL (ι → LL) D X g f]
  constructor
  · intro h
    have h2 := xi_module_structure LL (ι → LL) D X hX b _ h
    rwa [← mul_smul, ← map_mul, show b * a = 1 by rw [mul_comm]; exact hab, map_one, one_smul] at h2
  · intro h
    exact xi_module_structure LL (ι → LL) D X hX a _ h

end Free

end Formalism.MainNotions.N.Ln03.K8
end
end

