module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0011
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfA
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0009

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.AevalEndApply
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def twA (uE' : LetA O n) (h' : ℕ) : LetA O n →ₗ[O] LetA O n :=
  (LinearMap.mulRight O (uE' ^ h')).comp (W.γA W.gam).toLinearMap

variable {W}

theorem twA_apply (uE' : LetA O n) (h' : ℕ) (a : LetA O n) :
    twA W uE' h' a = W.γA W.gam a * uE' ^ h' := rfl

theorem aeval_end_apply {M : Type*} [AddCommGroup M] [Module O M] (f : Module.End O M) (P : Polynomial O)
    (x : M) : Polynomial.aeval f P x = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • (f ^ i) x := by
  first
  | (rw [Polynomial.aeval_eq_sum_range, LinearMap.coeFn_sum, Finset.sum_apply]
     simp only [LinearMap.smul_apply])
  | (simp [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]; done)

private theorem gammaA_mem_AΔ (g : W.Gam) {a : LetA O n} (ha : a ∈ W.AΔ) : W.γA g a ∈ W.AΔ := by
  have hc : ∀ (g h : W.Gam) (a : LetA O n), W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
    intro g h a
    funext i
    show W.γ₀ g (W.γ₀ h (a i)) = W.γ₀ h (W.γ₀ g (a i))
    rw [← AlgHom.mul_apply, ← map_mul, mul_comm, map_mul, AlgHom.mul_apply]
  intro δ hδ
  rw [hc, ha δ hδ]

theorem twA_pow_mem (uE' : LetA O n) (h' : ℕ) (huΔ : uE' ∈ W.AΔ) (k : ℕ) {a : LetA O n}
    (ha : a ∈ W.AΔ) : (twA W uE' h' ^ k) a ∈ W.AΔ := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, twA_apply]
    exact Subalgebra.mul_mem _ (gammaA_mem_AΔ _ ih) (Subalgebra.pow_mem _ huΔ _)

private theorem gammaA_letE_eq_letE (g : W.Gam) (c : ZMod n) : W.γA g (letE c : LetA O n) = letE c := by
  funext i
  show W.γ₀ g ((letE c : LetA O n) i) = (letE c : LetA O n) i
  unfold letE
  by_cases h : i = c
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem twA_pow_letE (uE' : LetA O n) (h' : ℕ) (c : ZMod n) (k : ℕ) (a : LetA O n) :
    (twA W uE' h' ^ k) ((letE c : LetA O n) * a) = (letE c : LetA O n) * (twA W uE' h' ^ k) a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, twA_apply, twA_apply, map_mul,
      gammaA_letE_eq_letE, mul_assoc]

theorem aeval_twA_mem (uE' : LetA O n) (h' : ℕ) (huΔ : uE' ∈ W.AΔ) (P : Polynomial O) {a : LetA O n}
    (ha : a ∈ W.AΔ) : Polynomial.aeval (twA W uE' h') P a ∈ W.AΔ := by
  rw [aeval_end_apply]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (twA_pow_mem uE' h' huΔ i ha) _

theorem aeval_twA_letE (uE' : LetA O n) (h' : ℕ) (c : ZMod n) (P : Polynomial O) (a : LetA O n) :
    Polynomial.aeval (twA W uE' h') P ((letE c : LetA O n) * a) =
      (letE c : LetA O n) * Polynomial.aeval (twA W uE' h') P a := by
  rw [aeval_end_apply, aeval_end_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [twA_pow_letE, mul_smul_comm]

theorem ev_twA (c : ZMod n) (ζ : LL) (Eπ : LetA O n) (h' : ℕ)
    (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (uE uE' : LetA O n) (huu : uE' * uE = 1) (hγE : W.γA W.gam Eπ = uE * Eπ) (u : LL) (hu : u ≠ 0)
    (hlevγ : ∀ a, W.lev c ζ (W.γA W.gam a) = rescale u (W.lev c ζ a)) (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (twA W uE' h' a) i = u ^ i * ev W c ζ Eπ h' a i := by
  obtain ⟨V, hVdef⟩ : ∃ V, V = Vs W c ζ Eπ := ⟨_, rfl⟩
  have hEV : W.lev c ζ Eπ = PowerSeries.X * V := by
    ext k
    rcases k with _ | k
    · simp [h0]
    · rw [PowerSeries.coeff_succ_X_mul, hVdef]
      unfold Vs
      rw [PowerSeries.coeff_mk]
  have hV0 : PowerSeries.constantCoeff V ≠ 0 := by
    rw [hVdef, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Vs
    simpa [PowerSeries.coeff_mk] using h1
  have hVinv : V * V⁻¹ = 1 := PowerSeries.mul_inv_cancel V hV0
  have hlevu : W.lev c ζ uE * V = PowerSeries.C u * PowerSeries.rescale u V := by
    have h2 : W.lev c ζ (W.γA W.gam Eπ) = W.lev c ζ uE * W.lev c ζ Eπ := by rw [hγE, map_mul]
    rw [hlevγ, hEV, map_mul, PowerSeries.rescale_X] at h2
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := LL))
    calc PowerSeries.X * (W.lev c ζ uE * V) = W.lev c ζ uE * (PowerSeries.X * V) := by ring
      _ = PowerSeries.C u * PowerSeries.X * PowerSeries.rescale u V := h2.symm
      _ = PowerSeries.X * (PowerSeries.C u * PowerSeries.rescale u V) := by ring
  have hW' : W.lev c ζ uE' * W.lev c ζ uE = 1 := by rw [← map_mul, huu, map_one]
  have hR : PowerSeries.rescale u V * PowerSeries.rescale u V⁻¹ = 1 := by
    rw [← map_mul, hVinv, map_one]
  have hC : PowerSeries.C u * PowerSeries.C u⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hu, map_one]
  have hkey : W.lev c ζ uE' * V⁻¹ = PowerSeries.C u⁻¹ * PowerSeries.rescale u V⁻¹ := by
    calc W.lev c ζ uE' * V⁻¹
        = W.lev c ζ uE' * V⁻¹ * (PowerSeries.C u * PowerSeries.C u⁻¹) *
            (PowerSeries.rescale u V * PowerSeries.rescale u V⁻¹) := by rw [hC, hR]; ring
      _ = PowerSeries.C u⁻¹ * PowerSeries.rescale u V⁻¹ *
            (W.lev c ζ uE' * (PowerSeries.C u * PowerSeries.rescale u V) * V⁻¹) := by ring
      _ = PowerSeries.C u⁻¹ * PowerSeries.rescale u V⁻¹ *
            ((W.lev c ζ uE' * W.lev c ζ uE) * (V * V⁻¹)) := by rw [← hlevu]; ring
      _ = PowerSeries.C u⁻¹ * PowerSeries.rescale u V⁻¹ := by rw [hW', hVinv]; ring
  have hmain : W.lev c ζ (twA W uE' h' a) * Ui W c ζ Eπ h' =
      PowerSeries.C (u⁻¹ ^ h') * PowerSeries.rescale u (W.lev c ζ a * Ui W c ζ Eπ h') := by
    rw [twA_apply, map_mul, map_pow, hlevγ]
    unfold Ui
    rw [← hVdef]
    simp only [map_mul, map_pow]
    calc PowerSeries.rescale u (W.lev c ζ a) * W.lev c ζ uE' ^ h' * V⁻¹ ^ h'
        = PowerSeries.rescale u (W.lev c ζ a) * (W.lev c ζ uE' * V⁻¹) ^ h' := by ring
      _ = PowerSeries.rescale u (W.lev c ζ a) *
            (PowerSeries.C u⁻¹ * PowerSeries.rescale u V⁻¹) ^ h' := by rw [hkey]
      _ = PowerSeries.C u⁻¹ ^ h' * (PowerSeries.rescale u (W.lev c ζ a) *
            PowerSeries.rescale u V⁻¹ ^ h') := by ring
  unfold ev
  split_ifs with hih
  · rw [hmain, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]
    have hm : (((i + h').toNat : ℕ) : ℤ) = i + h' := Int.toNat_of_nonneg hih
    have hu' : u⁻¹ ^ h' * u ^ (i + h').toNat = u ^ i := by
      rw [← zpow_natCast u, hm, zpow_add₀ hu, zpow_natCast, inv_pow, mul_comm, mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ hu), mul_one]
    rw [← mul_assoc, hu']
  · simp

theorem ev_twA_pow (c : ZMod n) (ζ : LL) (Eπ : LetA O n) (h' : ℕ)
    (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (uE uE' : LetA O n) (huu : uE' * uE = 1) (hγE : W.γA W.gam Eπ = uE * Eπ) (u : LL) (hu : u ≠ 0)
    (hlevγ : ∀ a, W.lev c ζ (W.γA W.gam a) = rescale u (W.lev c ζ a)) (k : ℕ) (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' ((twA W uE' h' ^ k) a) i = (u ^ i) ^ k * ev W c ζ Eπ h' a i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ev_twA c ζ Eπ h' h0 h1 uE uE' huu hγE u hu hlevγ, ih]
    ring

theorem ev_aeval_twA (c : ZMod n) (ζ : LL) (Eπ : LetA O n) (h' : ℕ)
    (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (uE uE' : LetA O n) (huu : uE' * uE = 1) (hγE : W.γA W.gam Eπ = uE * Eπ) (u : LL) (hu : u ≠ 0)
    (hlevγ : ∀ a, W.lev c ζ (W.γA W.gam a) = rescale u (W.lev c ζ a)) (P : Polynomial O)
    (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (Polynomial.aeval (twA W uE' h') P a) i =
      Polynomial.aeval (u ^ i) P * ev W c ζ Eπ h' a i := by
  have hzero : ev W c ζ Eπ h' 0 i = 0 := by
    unfold ev; split_ifs <;> simp
  have hadd : ∀ x y : LetA O n, ev W c ζ Eπ h' (x + y) i = ev W c ζ Eπ h' x i + ev W c ζ Eπ h' y i := by
    intro x y; unfold ev; split_ifs <;> simp [map_add (f := _), add_mul]
  have hsmul : ∀ (r : O) (x : LetA O n),
      ev W c ζ Eπ h' (r • x) i = algebraMap O LL r * ev W c ζ Eπ h' x i := by
    intro r x
    unfold ev
    split_ifs
    · first
      | (simp only [map_smul, smul_mul_assoc, PowerSeries.coeff_smul, Algebra.smul_def]; done)
      | (rw [map_smul, smul_mul_assoc, PowerSeries.coeff_smul, Algebra.smul_def])
      | (simp [Algebra.smul_def, mul_assoc]; done)
    · simp
  have hsum : ∀ (s : Finset ℕ) (g : ℕ → LetA O n),
      ev W c ζ Eπ h' (∑ k ∈ s, g k) i = ∑ k ∈ s, ev W c ζ Eπ h' (g k) i := by
    intro s g
    classical
    refine Finset.induction_on s ?_ ?_
    · simpa using hzero
    · intro k s hk ih
      rw [Finset.sum_insert hk, Finset.sum_insert hk, hadd, ih]
  rw [aeval_end_apply, Polynomial.aeval_eq_sum_range, Finset.sum_mul, hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hsmul, ev_twA_pow c ζ Eπ h' h0 h1 uE uE' huu hγE u hu hlevγ, Algebra.smul_def]
  ring

theorem EE_aeval (Eπ : LetA O n) (h' : ℕ) (uE uE' : LetA O n) (huu : uE' * uE = 1)
    (hγE : W.γA W.gam Eπ = uE * Eπ) (P : Polynomial O) (f : W.EE) (a : LetA O n)
    (h : algebraMap (LetA O n) W.EE (Eπ ^ h') * f = algebraMap (LetA O n) W.EE a) :
    algebraMap (LetA O n) W.EE (Eπ ^ h') * Polynomial.aeval (W.γE W.gam).toLinearMap P f =
      algebraMap (LetA O n) W.EE (Polynomial.aeval (twA W uE' h') P a) := by
  have hγ : W.γE W.gam (algebraMap (LetA O n) W.EE (Eπ ^ h')) =
      algebraMap (LetA O n) W.EE (uE ^ h') * algebraMap (LetA O n) W.EE (Eπ ^ h') := by
    rw [W.γE_ext, ← map_mul, ← mul_pow, ← hγE]
    congr 1
    exact map_pow (W.γA W.gam) Eπ h'
  have hk : ∀ k : ℕ, algebraMap (LetA O n) W.EE (Eπ ^ h') * (((W.γE W.gam).toLinearMap ^ k) f) =
      algebraMap (LetA O n) W.EE ((twA W uE' h' ^ k) a) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have h2 := congrArg (W.γE W.gam) ih
      rw [map_mul, hγ, W.γE_ext] at h2
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, twA_apply,
        AlgHom.toLinearMap_apply]
      calc algebraMap (LetA O n) W.EE (Eπ ^ h') * W.γE W.gam (((W.γE W.gam).toLinearMap ^ k) f)
          = algebraMap (LetA O n) W.EE (uE' ^ h') * (algebraMap (LetA O n) W.EE (uE ^ h') *
              algebraMap (LetA O n) W.EE (Eπ ^ h') * W.γE W.gam (((W.γE W.gam).toLinearMap ^ k) f)) := by
            rw [← mul_assoc, ← mul_assoc, ← map_mul, ← mul_pow, huu, one_pow, map_one, one_mul]
        _ = algebraMap (LetA O n) W.EE (uE' ^ h') *
              algebraMap (LetA O n) W.EE (W.γA W.gam ((twA W uE' h' ^ k) a)) := by
            rw [h2]; rfl
        _ = algebraMap (LetA O n) W.EE (W.γA W.gam ((twA W uE' h' ^ k) a) * uE' ^ h') := by
            rw [map_mul, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [aeval_end_apply, aeval_end_apply, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, hk i, Algebra.smul_def, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply]

theorem aeval_γLA_tmul (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n) (P : Polynomial O)
    (e : W.EE) (z : LcQ W T π' c) :
    Polynomial.aeval (γLA W T π' c) P (e ⊗ₜ z) = Polynomial.aeval (W.γE W.gamK).toLinearMap P e ⊗ₜ z := by
  have hp : ∀ i : ℕ, (γLA W T π' c ^ i) (e ⊗ₜ z) = (((W.γE W.gamK).toLinearMap ^ i) e) ⊗ₜ z := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      simp [γLA]
  rw [aeval_end_apply, aeval_end_apply, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hp, TensorProduct.smul_tmul']

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ConstantCoeffUniformiserZero
section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section U2C

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem constantCoeff_uniformiser_zero {s' : ℕ} {π' : LetA O n} (w : (LetA O n)ˣ) (hw : π' = (w : LetA O n) * letπ ^ s')
    (hs : 1 ≤ s') (i : ZMod n) : PowerSeries.constantCoeff (π' i) = 0 := by
  have : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
  rw [this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]

theorem u2ringPfC_subΔ {π' : LetA O n} (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0) :
    ∀ δ ∈ W.DelF, ∀ i (F : PowerSeries O),
      W.γ₀ δ (PowerSeries.subst (π' i) F) = PowerSeries.subst (π' i) F := by
  intro δ hδ i F
  rw [DualFramesAlt.EigenUniformiser.algHom_subst (W.γ₀ δ) (W.γ₀_X δ).1 (hπ0 i)]
  congr 1
  exact congrFun (hπΔ δ hδ) i

theorem u2ringPfC_inj {π' : LetA O n} (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hsub : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O,
      ∀ i, a i = PowerSeries.subst (π' i) (f i))
    (hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0) (c : ZMod n) (F F' : PowerSeries O)
    (hFF : PowerSeries.subst (π' c) F = PowerSeries.subst (π' c) F') : F = F' := by
  have hsub0 : ∀ i, PowerSeries.subst (π' i) (0 : PowerSeries O) = 0 := fun i => by
    rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)), map_zero]
  have hmem := u2ringPfB_single_mem W c (PowerSeries.subst (π' c) F)
    (fun δ hδ => u2ringPfC_subΔ W hπΔ hπ0 δ hδ c F)
  obtain ⟨f, -, huniq⟩ := hsub _ hmem
  have key : ∀ H, PowerSeries.subst (π' c) H = PowerSeries.subst (π' c) F →
      (Pi.single c H : ZMod n → PowerSeries O) = f := fun H hH => huniq _ (fun i => by
    by_cases hi : i = c
    · subst hi; simp only [Pi.single_eq_same]; exact hH.symm
    · simp only [Pi.single_eq_of_ne hi, hsub0])
  have := congrFun ((key F rfl).trans (key F' hFF.symm).symm) c
  simpa using this

theorem u2ringPfC_pre {π' : LetA O n}
    (hsub : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O,
      ∀ i, a i = PowerSeries.subst (π' i) (f i)) (c : ZMod n) (x : PowerSeries O)
    (hx : ∀ δ ∈ W.DelF, W.γ₀ δ x = x) : ∃ F : PowerSeries O, PowerSeries.subst (π' c) F = x := by
  obtain ⟨f, hf, -⟩ := hsub _ (u2ringPfB_single_mem W c x hx)
  refine ⟨f c, ?_⟩
  have := hf c
  simp only [Pi.single_eq_same] at this
  exact this.symm

theorem u2ringPfC_nu [IsDomain O] [CharZero O] {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs : 1 ≤ s') (hK : W.gamK = W.gam) (h' : ℕ) :
    ∃ ν : LetA O n, ν ∈ W.AΔ ∧
      ν * W.γA W.gamK (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h' := by
  obtain ⟨hπΔ, -, ⟨w, hw⟩, -, ⟨w₁, hq⟩, -, ⟨w₂, hγ⟩, -⟩ := hR
  have hπ0 := constantCoeff_uniformiser_zero w hw hs
  set Ê := Formalism.MainNotions.DeltaInvariantLattices.Eat E π' with hÊdef
  have hq₀ := u2ringPfB_q₀_ne_zero W PD.hp.ne_zero
  have hÊ0 : ∀ i, Ê i ≠ 0 := by
    intro i h
    apply hq₀
    have e1 : W.q₀ = (w₁ : LetA O n) i * Ê i := congrFun hq i
    rw [e1, h, mul_zero]
  have hπΔ' : ∀ δ ∈ W.DelF, ∀ i, W.γ₀ δ (π' i) = π' i := fun δ hδ i => congrFun (hπΔ δ hδ) i
  have hÊΔ : ∀ δ ∈ W.DelF, ∀ i, W.γ₀ δ (Ê i) = Ê i := by
    intro δ hδ i
    show W.γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply, hπΔ' δ hδ i]
  have hU : ∀ i, ∃ u : PowerSeries O, IsUnit u ∧ W.γ₀ W.gam (Ê i) = Ê i * u := by
    intro i
    have hγi : W.γ₀ W.gam (π' i) - π' i = (w₂ : LetA O n) i * π' i * Ê i := congrFun hγ i
    obtain ⟨D, hD⟩ := Polynomial.sub_dvd_eval_sub (W.γ₀ W.gam (π' i)) (π' i)
      ((E i).map (algebraMap O (PowerSeries O)))
    refine ⟨1 + (w₂ : LetA O n) i * π' i * D, ?_, ?_⟩
    · rw [PowerSeries.isUnit_iff_constantCoeff]
      simp [hπ0 i]
    · have e2 : W.γ₀ W.gam (Ê i) = Polynomial.aeval (W.γ₀ W.gam (π' i)) (E i) :=
        (Polynomial.aeval_algHom_apply (W.γ₀ W.gam) (π' i) (E i)).symm
      have e3 : Ê i = Polynomial.aeval (π' i) (E i) := rfl
      have hD' : Polynomial.aeval (W.γ₀ W.gam (π' i)) (E i) - Polynomial.aeval (π' i) (E i) =
          (W.γ₀ W.gam (π' i) - π' i) * D := by
        rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
          Polynomial.eval₂_eq_eval_map]
        exact hD
      rw [e3] at hγi
      rw [hγi] at hD'
      rw [e2, e3]
      linear_combination hD'
  choose U hUu hUeq using hU
  have hUunit : IsUnit (U : LetA O n) := Pi.isUnit_iff.2 hUu
  set V : LetA O n := ((hUunit.unit⁻¹ : (LetA O n)ˣ) : LetA O n) with hV
  have hVU : V * U = 1 := by rw [hV]; exact hUunit.val_inv_mul
  have hUΔ : ∀ δ ∈ W.DelF, ∀ i, W.γ₀ δ (U i) = U i := by
    intro δ hδ i
    have h1 := congrArg (W.γ₀ δ) (hUeq i)
    rw [u2ringPfB_γ₀_comm, map_mul, hÊΔ δ hδ i, hUeq i] at h1
    exact (mul_left_cancel₀ (hÊ0 i) h1).symm
  refine ⟨V ^ h', ?_, ?_⟩
  · intro δ hδ
    funext i
    show W.γ₀ δ ((V ^ h') i) = (V ^ h') i
    rw [Pi.pow_apply, map_pow]
    congr 1
    have hVi : V i * U i = 1 := congrFun hVU i
    have h1 := congrArg (W.γ₀ δ) hVi
    rw [map_mul, hUΔ δ hδ i, map_one] at h1
    exact mul_right_cancel₀ (hUu i).ne_zero (h1.trans hVi.symm)
  · have hγÊ : W.γA W.gam Ê = Ê * U := funext fun i => hUeq i
    rw [hK, map_pow, hγÊ]
    calc V ^ h' * (Ê * U) ^ h' = (V * U) ^ h' * Ê ^ h' := by ring
      _ = Ê ^ h' := by rw [hVU, one_pow, one_mul]

end U2C

end Formalism.MainNotions.N.Ln34
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfB
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

theorem serC_mul {LL V' : Type} [Field LL] [AddCommGroup V'] [Module LL V'] (f g : PowerSeries LL)
    (d : V') (i : ℤ) :
    serC (f * g) d i = ∑ k ∈ Finset.range (i.toNat + 1), PowerSeries.coeff k f • serC g d (i - k) := by
  by_cases hi : 0 ≤ i
  · have hsum : ∀ k ∈ Finset.range (i.toNat + 1),
        PowerSeries.coeff k f • serC g d (i - k) =
          (PowerSeries.coeff k f * PowerSeries.coeff (i.toNat - k) g) • d := by
      intro k hk
      rw [Finset.mem_range] at hk
      have h1 : 0 ≤ i - (k : ℤ) := by omega
      have h2 : (i - (k : ℤ)).toNat = i.toNat - k := by omega
      simp only [serC, if_pos h1, h2, mul_smul]
    rw [Finset.sum_congr rfl hsum, ← Finset.sum_smul]
    simp only [serC, if_pos hi]
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  · have h0 : i.toNat = 0 := by omega
    simp only [serC, if_neg hi, h0, zero_add, Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero,
      sub_zero, smul_zero]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem expS_mul (c : ZMod n) (ζ : LL) (f : LetA O n) {m : ℕ} (a : Fin m → LetA O n)
    (y : Fin m → W.DD T) (i : ℤ) :
    expS W T c ζ (fun j => f * a j) y i =
      ∑ k ∈ Finset.range (i.toNat + 1), PowerSeries.coeff k (W.lev c ζ f) • expS W T c ζ a y (i - k) := by
  simp only [expS, map_mul, serC_mul, Finset.smul_sum]
  exact Finset.sum_comm

def GoodF (τ : K →ₐ[Qp] LL) (h' : ℕ) (F : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  ∀ i : ℤ, F i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (h' - i)

theorem goodF_mul (c : ZMod n) (ζ : LL) (τ : K →ₐ[Qp] LL) (h' : ℕ) (f : LetA O n) {m : ℕ}
    (a : Fin m → LetA O n) (y : Fin m → W.DD T) (hg : GoodF (PD := PD) T τ h' (expS W T c ζ a y)) :
    GoodF (PD := PD) T τ h' (expS W T c ζ (fun j => f * a j) y) := by
  intro i
  rw [expS_mul]
  refine Submodule.sum_mem _ (fun k hk => Submodule.smul_mem _ _ ?_)
  exact u3upPf_FilC_anti (PD := PD) T τ (by omega) (hg (i - k))

end Generic

end Formalism.MainNotions.N.Ln34.MLB

end
end

