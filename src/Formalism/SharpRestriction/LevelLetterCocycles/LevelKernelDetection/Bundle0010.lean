module

public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvBasisCmp
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0007

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.ConstantCoeffPi0EqZeroOfP9ring
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem cf_sub_level_kernel_detection {Ks D : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (f g : Amb LL Ks D) (i : ℤ) : cf (f - g) i = cf f i - cf g i := by
  simp [cf]

theorem constSeries_add {Ks D : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (d d' : D) : cstD (LL := LL) Ks (d + d') = cstD Ks d + cstD Ks d' := by
  simp [cstD, TensorProduct.tmul_add]

theorem constSeries_sum {Ks D : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    {q : ℕ} (d : Fin q → D) : cstD (LL := LL) Ks (∑ k, d k) = ∑ k, cstD Ks (d k) := by
  classical
  induction (Finset.univ : Finset (Fin q)) using Finset.induction_on with
  | empty => simp [cstD]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, constSeries_add, ih]

theorem constSeries_C_smul {Ks D : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (r : LL) (d : D) :
    HahnSeries.ofPowerSeries ℤ Ks (PowerSeries.C (algebraMap LL Ks r)) • cstD (LL := LL) Ks d =
      cstD Ks (r • d) := by
  rw [HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnModule.single_zero_smul_eq_smul]
  simp only [cstD]
  rw [← HahnModule.of_smul]
  congr 1
  ext j
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs
  · rw [algebraMap_smul, TensorProduct.tmul_smul]
  · rw [smul_zero]

theorem coeff_constSeries {Ks D : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (d : D) (i : ℤ) : cf (cstD (LL := LL) Ks d) i = if i = 0 then (1 : Ks) ⊗ₜ[LL] d else 0 := by
  simp [cf, cstD, HahnSeries.coeff_single]

theorem Q_eq_unit_mul_qP (hs1 : W.s = 1)
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) :
    ∃ u : (LetA O n)ˣ, W.Q = (u : LetA O n) * qP W := by
  obtain ⟨u, hu⟩ := hp9.2.2.2.2.1
  refine ⟨u, ?_⟩
  have hQq : W.Q = W.q := by
    show (W.φA ^ (W.s - 1)) W.q = W.q
    rw [hs1, Nat.sub_self, pow_zero]
    rfl
  rw [hQq, hu]
  congr 1
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qP]

theorem constantCoeff_pi0_eq_zero_of_p9ring
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (j : ZMod n) : PowerSeries.constantCoeff (W.π₀ j) = 0 := by
  obtain ⟨w, hw⟩ := hp9.2.2.1
  have hp1 : PD.p - 1 ≠ 0 := by have := PD.hp.two_le; omega
  rw [hw]
  simp [letπ, zero_pow hp1]

def comparisonOnLetter {T : LocLat G Qp LL O} (C : Coord W (baseIdOf hR) T) (i : ZMod n) :
    ↥((latOf C).N i) →+ T.V ⊗[Qp] B where
  toFun y := W.cmp T ⟨C.t i y, y.2⟩
  map_zero' := by
    rw [← map_zero (W.cmp T)]
    exact lvBasis_cmp_congr _ _ (C.t_zero i)
  map_add' y y' := by
    rw [← lvBasis_cmp_add y.2 y'.2 ((W.N T).add_mem y.2 y'.2)]
    exact lvBasis_cmp_congr _ _ (C.t_add i _ _)

theorem comparison_of_reduction {T : LocLat G Qp LL O} (C : Coord W (baseIdOf hR) T) (i : ZMod n)
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    {r : ℕ} (e : Fin r → C.V) (he : ∀ k, e k ∈ (latOf C).N i) (x : C.V) (hx : x ∈ (latOf C).N i)
    (a : Fin r → O) (hred : x - ∑ k, PowerSeries.C (a k) • e k ∈ E.sm (PowerSeries.X : PowerSeries O) ((latOf C).N i)) :
    W.cmp T ⟨C.t i x, hx⟩ = ∑ k, algebraMap O LL (a k) • W.cmp T ⟨C.t i (e k), he k⟩ := by
  obtain ⟨z, hz, hzeq⟩ := Submodule.mem_map.1 hred
  rw [LinearMap.lsmul_apply] at hzeq
  have key : (⟨x, hx⟩ : ↥((latOf C).N i)) =
      ∑ k, PowerSeries.C (a k) • (⟨e k, he k⟩ : ↥((latOf C).N i)) + (PowerSeries.X : PowerSeries O) • ⟨z, hz⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul]
    rw [hzeq]
    abel
  have hF := congrArg (comparisonOnLetter C i) key
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum] at hF
  have hC : ∀ k, comparisonOnLetter C i (PowerSeries.C (a k) • (⟨e k, he k⟩ : ↥((latOf C).N i))) =
      algebraMap O LL (a k) • W.cmp T ⟨C.t i (e k), he k⟩ := by
    intro k
    have hm : (baseIdOf hR).d (PowerSeries.C (a k)) • C.t i (e k) ∈ W.N T := by
      rw [← C.t_smul]
      exact (PowerSeries.C (a k) • (⟨e k, he k⟩ : ↥((latOf C).N i))).2
    have h0 : comparisonOnLetter C i (PowerSeries.C (a k) • (⟨e k, he k⟩ : ↥((latOf C).N i))) =
        W.cmp T ⟨(baseIdOf hR).d (PowerSeries.C (a k)) • C.t i (e k), hm⟩ :=
      lvBasis_cmp_congr (a := C.t i (PowerSeries.C (a k) • e k))
        (PowerSeries.C (a k) • (⟨e k, he k⟩ : ↥((latOf C).N i))).2 hm (C.t_smul i _ _)
    rw [h0]
    refine lvBasis_cmp_smul_const (he k) _ (a k) (fun j => ?_) hm
    rw [BaseId.d_apply]
    have h1 : (baseIdOf hR).ι (PowerSeries.C (a k)) = PowerSeries.C (a k) :=
      (baseIdOf hR).ι.commutes (a k)
    rw [h1, PowerSeries.constantCoeff_C]
  have hX : comparisonOnLetter C i ((PowerSeries.X : PowerSeries O) • (⟨z, hz⟩ : ↥((latOf C).N i))) = 0 := by
    have hm : W.π₀ • C.t i z ∈ W.N T := by
      rw [← BaseId.d_X, ← C.t_smul]
      exact ((PowerSeries.X : PowerSeries O) • (⟨z, hz⟩ : ↥((latOf C).N i))).2
    have h0 : comparisonOnLetter C i ((PowerSeries.X : PowerSeries O) • (⟨z, hz⟩ : ↥((latOf C).N i))) =
        W.cmp T ⟨W.π₀ • C.t i z, hm⟩ :=
      lvBasis_cmp_congr (a := C.t i ((PowerSeries.X : PowerSeries O) • z))
        ((PowerSeries.X : PowerSeries O) • (⟨z, hz⟩ : ↥((latOf C).N i))).2 hm
        (by rw [C.t_smul, BaseId.d_X])
    rw [h0, lvBasis_cmp_smul_const hz W.π₀ 0 (constantCoeff_pi0_eq_zero_of_p9ring hp9) hm, map_zero, zero_smul]
  rw [hX, add_zero, Finset.sum_congr rfl (fun k _ => hC k)] at hF
  exact hF

theorem gamma_reduction_pi0_pow {T : LocLat G Qp LL O} (C : Coord W (baseIdOf hR) T) (i : ZMod n) (hs1 : W.s = 1)
    (hp2 : PD.p ≠ 2) (x : C.V) (hx : x ∈ (latOf C).N i) (M : ℕ)
    (hγ : (latOf C).γ i x - x ∈ E.sm ((PowerSeries.X : PowerSeries O) ^ M) ((latOf C).N i)) :
    ∃ (y : ↥(W.N T)) (_ : W.γD T W.gam (C.t i x) ∈ W.N T),
      W.γD T W.gam (C.t i x) - C.t i x = W.π₀ ^ M • (y : W.DD T) := by
  obtain ⟨z, hz, hzeq⟩ := Submodule.mem_map.1 hγ
  rw [LinearMap.lsmul_apply] at hzeq
  have hg : W.gamK = W.gam := W.gamK_eq_one hs1 hp2
  have h1 : C.t i ((latOf C).γ i x) = W.γD T W.gam (C.t i x) := by rw [t_γ, hg]
  have h2 : W.γD T W.gam (C.t i x) - C.t i x = W.π₀ ^ M • C.t i z := by
    rw [← h1, ← C.t_sub, ← hzeq, C.t_smul, map_pow, BaseId.d_X]
  refine ⟨⟨C.t i z, hz⟩, ?_, h2⟩
  have h3 : W.γD T W.gam (C.t i x) = W.π₀ ^ M • C.t i z + C.t i x := by rw [← h2]; abel
  rw [h3]
  exact (W.N T).add_mem ((W.N T).smul_mem _ hz) hx

end Formalism.MainNotions.N.Ln03.Pf
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.EvaluationExpansionAtRoot
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

theorem inverse_unit_mul_X_pow {Ks : Type} [CommRing Ks] (w : (PowerSeries Ks)ˣ) (m : ℕ) :
    Ring.inverse (HahnSeries.ofPowerSeries ℤ Ks ((w : PowerSeries Ks) * PowerSeries.X ^ m)) =
      HahnSeries.ofPowerSeries ℤ Ks (↑w⁻¹ : PowerSeries Ks) * tp Ks (-(m : ℤ)) := by
  have h1 : HahnSeries.ofPowerSeries ℤ Ks (↑w : PowerSeries Ks) *
      HahnSeries.ofPowerSeries ℤ Ks (↑w⁻¹ : PowerSeries Ks) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have ht : tp Ks (m : ℤ) * tp Ks (-(m : ℤ)) = 1 := by
    rw [tp, tp, HahnSeries.single_mul_single, add_neg_cancel, mul_one]
    rfl
  let U : (HahnSeries ℤ Ks)ˣ :=
    { val := HahnSeries.ofPowerSeries ℤ Ks (↑w : PowerSeries Ks) * tp Ks (m : ℤ)
      inv := HahnSeries.ofPowerSeries ℤ Ks (↑w⁻¹ : PowerSeries Ks) * tp Ks (-(m : ℤ))
      val_inv := by linear_combination (tp Ks (m : ℤ) * tp Ks (-(m : ℤ))) * h1 + ht
      inv_val := by linear_combination (tp Ks (m : ℤ) * tp Ks (-(m : ℤ))) * h1 + ht }
  have hU : HahnSeries.ofPowerSeries ℤ Ks ((w : PowerSeries Ks) * PowerSeries.X ^ m) = ↑U := by
    rw [map_mul, HahnSeries.ofPowerSeries_X_pow]
    rfl
  rw [hU, Ring.inverse_unit]
  rfl

theorem evaluation_comm_tensor {LL D ι : Type} [Field LL] [AddCommGroup D] [Module LL D] [Fintype ι]
    [DecidableEq ι] (i : ι) (z : D ⊗[LL] (ι → LL)) :
    evK i (TensorProduct.comm LL D (ι → LL) z) = TensorProduct.piScalarRight LL LL D ι z i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul d f =>
    rw [TensorProduct.comm_tmul, evaluation_tmul, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
  | add z z' hz hz' => rw [map_add (f := _), map_add (f := _), hz, hz', map_add (f := _), Pi.add_apply]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}


open Classical in
theorem evaluation_expansion_at_root (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D]
    (g : Rs LL PD.p s → D) (ζ : Rs LL PD.p s) : evK ζ (toKsD W s D g) = g ζ := by
  rw [toKsD, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, evaluation_comm_tensor,
    LinearEquiv.apply_symm_apply]

theorem rho_product_unit_mul {ell : ℕ}
    (hk1b : ∀ s < ell, ∃ ε : (PowerSeries (KsW W s))ˣ,
      rhoL hR c s ((baseIdOf hR).Bs.p s) = (ε : PowerSeries (KsW W s)) * PowerSeries.X)
    (hunits : ∀ s < ell, IsUnit (rhoL hR c s PowerSeries.X) ∧
      ∀ s' < ell, s' ≠ s → IsUnit (rhoL hR c s ((baseIdOf hR).Bs.p s')))
    (E : ℕ → ℕ) (s : ℕ) (hs : s < ell) :
    ∃ w : (PowerSeries (KsW W s))ˣ,
      rhoL hR c s (∏ s' ∈ Finset.range ell, (baseIdOf hR).Bs.p s' ^ E s') =
        (w : PowerSeries (KsW W s)) * PowerSeries.X ^ E s := by
  obtain ⟨ε, hε⟩ := hk1b s hs
  have hrest : IsUnit (rhoL hR c s
      (∏ s' ∈ (Finset.range ell).erase s, (baseIdOf hR).Bs.p s' ^ E s')) := by
    rw [map_prod]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun s' hs' => ?_
    rw [map_pow]
    obtain ⟨hne, hlt⟩ := Finset.mem_erase.1 hs'
    exact ((hunits s hs).2 s' (Finset.mem_range.1 hlt) hne).pow _
  obtain ⟨u, hu⟩ := hrest
  refine ⟨ε ^ E s * u, ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs), map_mul, ← hu, map_pow, hε]
  push_cast
  ring


open Classical in
theorem levelCond_iff (ell : ℕ)
    (hk1b : ∀ s < ell, ∃ ε : (PowerSeries (KsW W s))ˣ,
      rhoL hR c s ((baseIdOf hR).Bs.p s) = (ε : PowerSeries (KsW W s)) * PowerSeries.X)
    (hunits : ∀ s < ell, IsUnit (rhoL hR c s PowerSeries.X) ∧
      ∀ s' < ell, s' ≠ s → IsUnit (rhoL hR c s ((baseIdOf hR).Bs.p s')))
    (E : ℕ → ℕ) (s : ℕ) (hs : s < ell) (x : C.V) (hx : x ∈ (latOf C).N c)
    (hFil : ∀ s, Antitone (FilD W T c s)) :
    Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s)
        (rhoL hR c s (∏ s' ∈ Finset.range ell, (baseIdOf hR).Bs.p s' ^ E s'))) •
      expN Lb s T c ⟨C.t c x, hx⟩ ∈ Xi (KsW W s) (fun i => FilD W T c s (-i)) ↔
    ∀ (ζ : Rs LL PD.p s) (k : ℤ),
      (⟨Lb.levB T c ζ ⟨C.t c x, hx⟩ k, Lb.mem T c ζ ⟨C.t c x, hx⟩ k⟩ : Dc W T c) ∈
        FilD W T c s ((E s : ℤ) - k) := by
  obtain ⟨w, hw⟩ := rho_product_unit_mul hk1b hunits E s hs
  have hX : Monotone fun i : ℤ => FilD W T c s (-i) := fun i j hij => hFil s (neg_le_neg hij)
  rw [hw, inverse_unit_mul_X_pow, xi_unit_tp _ hX _ _ (Units.inv_mul w), xi_iff]
  refine forall_congr' fun ζ => forall_congr' fun k => ?_
  have hc : cf (expN Lb s T c ⟨C.t c x, hx⟩) k = coefN Lb s T c ⟨C.t c x, hx⟩ k := rfl
  rw [hc, coefN, evaluation_expansion_at_root, show -(k + -(E s : ℤ)) = (E s : ℤ) - k by ring]

end Formalism.MainNotions.N.Ln03.K8
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.GaloisActionFrobeniusComm
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
    {hR : Ring9 W}

section Letters

variable {T : LocLat G Qp LL O}

theorem galois_action_frobenius_comm (g : G) (z : T.V ⊗[Qp] B) :
    actVB PD T.ρ g (φVB PD (LL := LL) (V := T.V) z) = φVB PD (LL := LL) (V := T.V) (actVB PD T.ρ g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [actVB, φVB, PD.φ_comm]
  | add x y hx hy =>
    simp only [map_add (f := _)]
    rw [hx, hy]

theorem scalar_mul_frobenius_comm (k : K₀) (z : T.V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) (PD.σ k) (φVB PD (LL := LL) (V := T.V) z) =
      φVB PD (LL := LL) (V := T.V) (mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) k z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [mulVB, φVB, map_mul, PD.φ_K₀]
  | add x y hx hy =>
    simp only [map_add (f := _)]
    rw [hx, hy]

theorem frobenius_maps_letter_succ (i : ZMod n) (z : T.V ⊗[Qp] B) (hz : z ∈ DcrisL PD T.ρ (W.emb i)) :
    φVB PD (LL := LL) (V := T.V) z ∈ DcrisL PD T.ρ (W.emb (i + 1)) := by
  rw [DcrisL, Submodule.mem_inf] at hz ⊢
  obtain ⟨hz1, hz2⟩ := hz
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hz1 hz2 ⊢
  refine ⟨fun g => ?_, fun k => ?_⟩
  · rw [galois_action_frobenius_comm, hz1 g]
  · obtain ⟨k', rfl⟩ := PD.σ_bij.2 k
    have he : W.emb (i + 1) (PD.σ k') = W.emb i k' := by
      have := congrArg (fun f : K₀ →ₐ[Qp] LL => f k') (W.emb_σ i)
      simpa only [AlgHom.comp_apply] using this
    rw [scalar_mul_frobenius_comm, hz2 k', map_smul, he]

theorem frobenius_pow_maps_letter (m : ℕ) (i : ZMod n) (z : T.V ⊗[Qp] B) (hz : z ∈ DcrisL PD T.ρ (W.emb i)) :
    ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ m) z ∈
      DcrisL PD T.ρ (W.emb (i + (m : ZMod n))) := by
  induction m with
  | zero => simpa using hz
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, Nat.cast_succ, ← add_assoc]
    exact frobenius_maps_letter_succ _ _ ih

theorem lambda_mem_dcris_letter (C : Coord W (baseIdOf hR) T) (c : ZMod n) (ell : ℕ) (x : C.V)
    (hx : C.t (c - (ell : ZMod n)) x ∈ W.N T) :
    ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ ell) (W.cmp T ⟨_, hx⟩) ∈
      DcrisL PD T.ρ (W.emb c) := by
  have h1 : (⟨_, hx⟩ : ↥(W.N T)) = (letE (c - (ell : ZMod n)) : LetA O n) • ⟨_, hx⟩ :=
    Subtype.ext (C.t_letter _ x).symm
  have h2 := frobenius_pow_maps_letter ell _ _ (W.cmp_letter T (c - (ell : ZMod n)) ⟨_, hx⟩)
  rw [sub_add_cancel] at h2
  rw [h1]
  exact h2

theorem lambda_coe_eq_frobenius_pow (C : Coord W (baseIdOf hR) T) (c : ZMod n) (ell : ℕ) {r : ℕ} (e : Fin r → C.V)
    (k : Fin r) (hk : C.t (c - (ell : ZMod n)) (e k) ∈ W.N T) :
    ((lamOf C c ell e k : Dc W T c) : T.V ⊗[Qp] B) =
      ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ ell) (W.cmp T ⟨_, hk⟩) := by
  unfold lamOf
  rw [dite_eq_left hk, dite_eq_left (lambda_mem_dcris_letter C c ell (e k) hk)]

end Letters

section Coords

variable {T : LocLat G Qp LL O}

theorem coord_t_sum (C : Coord W (baseIdOf hR) T) (i : ZMod n) {ι : Type} (s : Finset ι) (g : ι → C.V) :
    C.t i (∑ l ∈ s, g l) = ∑ l ∈ s, C.t i (g l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Coord.t_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Coord.t_add, ih]

theorem coord_t_const_smul (C : Coord W (baseIdOf hR) T) (i : ZMod n) (a : O) (x : C.V) :
    C.t i (PowerSeries.C a • x) = a • C.t i x := by
  rw [C.t_smul, show PowerSeries.C a = algebraMap O (PowerSeries O) a from rfl, AlgHom.commutes,
    algebraMap_smul]

theorem exists_pi0_eq_letPi_mul (hR : Ring9 W) : ∃ u : LetA O n, W.π₀ = (letπ : LetA O n) * u := by
  obtain ⟨w, -, hw⟩ := π₀₁_eq hR
  have hp : 1 ≤ PD.p - 1 := by
    have := PD.hp.two_le
    omega
  refine ⟨fun _ => w * PowerSeries.X ^ (PD.p - 1 - 1), ?_⟩
  funext j
  show W.π₀₁ = PowerSeries.X * (w * PowerSeries.X ^ (PD.p - 1 - 1))
  rw [hw]
  conv_lhs => rw [← Nat.sub_add_cancel hp, pow_succ]
  ring

theorem comparison_pi0_smul_eq_zero (hR : Ring9 W) (y : ↥(W.N T)) : W.cmp T (W.π₀ • y) = 0 := by
  obtain ⟨u, hu⟩ := exists_pi0_eq_letPi_mul hR
  rw [hu, mul_smul]
  exact W.cmp_π T (u • y)

end Coords

section ThetaShiftProofs

variable {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
  {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {r₁ r₂ : ℕ}

theorem lambda_of_matrixCongruences (hC : CoordHom C₁ C₂ F) (hD : MemD W F c) (e₁ : Fin r₁ → C₁.V)
    (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (he₁ : ∀ k, e₁ k ∈ (latOf C₁).N (c - (ell : ZMod n)))
    (he₂ : ∀ l, e₂ l ∈ (latOf C₂).N (c - (ell : ZMod n)))
    (prLIs : ∀ k, (latHomOf hC).f (e₁ k) -
        ∑ l, PowerSeries.C (LinearMap.toMatrix' P l k) • e₂ l ∈
      E.sm (PowerSeries.X : PowerSeries O) ((latOf C₂).N (c - (ell : ZMod n)))) :
    ∀ k, dmapOf hD (lamOf C₁ c ell e₁ k) =
      ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) • lamOf C₂ c ell e₂ l := by
  intro k
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 (prLIs k)
  have hX := hyx
  rw [LinearMap.lsmul_apply] at hX
  change (PowerSeries.X : PowerSeries O) • y = hC.f (e₁ k) - ∑ l, PowerSeries.C (LinearMap.toMatrix' P l k) • e₂ l at hX
  have hfe : hC.f (e₁ k) =
      ∑ l, PowerSeries.C (LinearMap.toMatrix' P l k) • e₂ l + (PowerSeries.X : PowerSeries O) • y := by
    rw [hX]
    abel
  have ht : C₂.t (c - (ell : ZMod n)) (hC.f (e₁ k)) =
      ∑ l, (LinearMap.toMatrix' P l k) • C₂.t (c - (ell : ZMod n)) (e₂ l) +
        W.π₀ • C₂.t (c - (ell : ZMod n)) y := by
    rw [hfe, Coord.t_add, coord_t_sum, C₂.t_smul, BaseId.d_X]
    simp only [coord_t_const_smul]
  have hy' : C₂.t (c - (ell : ZMod n)) y ∈ W.N T₂ := hy
  have hx : W.map F (C₁.t (c - (ell : ZMod n)) (e₁ k)) ∈ W.N T₂ :=
    W.map_N F hC.crys hC.crys' _ (he₁ k)
  have hsplit : (⟨W.map F (C₁.t (c - (ell : ZMod n)) (e₁ k)), hx⟩ : ↥(W.N T₂)) =
      ∑ l, (LinearMap.toMatrix' P l k) •
          (⟨C₂.t (c - (ell : ZMod n)) (e₂ l), he₂ l⟩ : ↥(W.N T₂)) +
        W.π₀ • (⟨C₂.t (c - (ell : ZMod n)) y, hy'⟩ : ↥(W.N T₂)) := by
    apply Subtype.ext
    show W.map F (C₁.t (c - (ell : ZMod n)) (e₁ k)) = _
    rw [← hC.coord_hom_map_trace, ht]
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  have hcmp : W.cmp T₂ ⟨W.map F (C₁.t (c - (ell : ZMod n)) (e₁ k)), hx⟩ =
      ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) •
        W.cmp T₂ ⟨C₂.t (c - (ell : ZMod n)) (e₂ l), he₂ l⟩ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsplit, map_add (f := _), map_sum, comparison_pi0_smul_eq_zero hR, add_zero]
    simp only [W.cmp_smul]
  have hL : ∀ l, ((lamOf C₂ c ell e₂ l : Dc W T₂ c) : T₂.V ⊗[Qp] B) =
      ((φVB PD (LL := LL) (V := T₂.V) : Module.End LL (T₂.V ⊗[Qp] B)) ^ ell)
        (W.cmp T₂ ⟨_, he₂ l⟩) := fun l => lambda_coe_eq_frobenius_pow C₂ c ell e₂ l (he₂ l)
  apply Subtype.ext
  calc ((dmapOf hD (lamOf C₁ c ell e₁ k) : Dc W T₂ c) : T₂.V ⊗[Qp] B)
      = pfMapFl_Fb F (((φVB PD (LL := LL) (V := T₁.V) : Module.End LL (T₁.V ⊗[Qp] B)) ^ ell)
          (W.cmp T₁ ⟨_, he₁ k⟩)) := by
        rw [← lambda_coe_eq_frobenius_pow C₁ c ell e₁ k (he₁ k)]
        rfl
    _ = ((φVB PD (LL := LL) (V := T₂.V) : Module.End LL (T₂.V ⊗[Qp] B)) ^ ell)
          (W.cmp T₂ ⟨W.map F (C₁.t (c - (ell : ZMod n)) (e₁ k)), hx⟩) := by
        rw [← pfMapFl_φpow F ell, ← W.cmp_map F hC.crys hC.crys' ⟨_, he₁ k⟩ hx]
    _ = ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) •
          ((φVB PD (LL := LL) (V := T₂.V) : Module.End LL (T₂.V ⊗[Qp] B)) ^ ell)
            (W.cmp T₂ ⟨_, he₂ l⟩) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hcmp, map_sum]
        simp only [map_smul]
    _ = _ := by
        rw [Submodule.coe_sum]
        simp only [Submodule.coe_smul, hL]

end ThetaShiftProofs

end Formalism.MainNotions.N.Ln03.Pf
end
end

