module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0019
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPosConstLagrangeCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0021
public import Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.InvariantLetterPolynomialDerivation
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Op

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def uniformizerInverse : W.EE := Ring.inverse (algebraMap (LetA O n) W.EE W.π₀)

def derivationOnWachModule : W.DD T →ₗ[O] W.DD T := Formalism.MainNotions.LiftingTheory.lifta_δ W T (uniformizerInverse W)

theorem derivation_on_wach_module_apply (x : W.DD T) : derivationOnWachModule W T x = uniformizerInverse W • (W.γ T x - x) := rfl

variable {W} in
theorem algebraMap_uniformizer_mul_inverse (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) :
    algebraMap (LetA O n) W.EE W.π₀ * uniformizerInverse W = 1 :=
  Ring.mul_inverse_cancel _ hU

theorem uniformizer_smul_derivation (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (x : W.DD T) :
    W.π₀ • derivationOnWachModule W T x = W.γ T x - x := by
  rw [derivation_on_wach_module_apply, ← smul_assoc, Algebra.smul_def, algebraMap_uniformizer_mul_inverse hU, one_smul]

theorem inverse_smul_uniformizer_smul (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (x : W.DD T) :
    uniformizerInverse W • (W.π₀ • x) = x := by
  rw [← algebraMap_smul W.EE W.π₀ x, smul_smul, mul_comm, algebraMap_uniformizer_mul_inverse hU, one_smul]

theorem smul_comm_letA_EE (a : LetA O n) (e : W.EE) (x : W.DD T) : a • (e • x) = e • (a • x) := by
  rw [← smul_assoc a e x, Algebra.smul_def a e, mul_comm, mul_smul, algebraMap_smul W.EE a x]

theorem gammaA_idempotent (g : W.Gam) (c : ZMod n) : W.γA g (letE c : LetA O n) = letE c := by
  funext i
  show W.γ₀ g ((Pi.single c (1 : PowerSeries O) : LetA O n) i) = (Pi.single c (1 : PowerSeries O) : LetA O n) i
  rw [Pi.single_apply]
  split_ifs <;> simp

theorem idempotent_smul_gamma (c : ZMod n) (x : W.DD T) :
    (letE c : LetA O n) • W.γ T x = W.γ T ((letE c : LetA O n) • x) := by
  show (letE c : LetA O n) • W.γD T W.gam x = W.γD T W.gam ((letE c : LetA O n) • x)
  rw [← algebraMap_smul W.EE (letE c : LetA O n) x, W.γD_smul, W.γE_ext,
    show letγ (W.γ₀ W.gam) (letE c : LetA O n) = letE c from gammaA_idempotent W W.gam c, algebraMap_smul]

theorem gammaD_gamma_comm (δ : W.Gam) (x : W.DD T) : W.γD T δ (W.γ T x) = W.γ T (W.γD T δ x) := by
  show W.γD T δ (W.γD T W.gam x) = W.γD T W.gam (W.γD T δ x)
  rw [← W.γD_mul, ← W.γD_mul, mul_comm]

theorem delta_fixes_inverse (a : LetA O n) (ha : a ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE a))
    (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE a)) = Ring.inverse (algebraMap (LetA O n) W.EE a) := by
  have ha' : ∀ δ ∈ W.DelF, W.γA δ a = a := ha
  have hfix : W.γE δ (algebraMap (LetA O n) W.EE a) = algebraMap (LetA O n) W.EE a := by
    rw [W.γE_ext]
    exact congrArg (algebraMap (LetA O n) W.EE) (ha' δ hδ)
  obtain ⟨u, hu⟩ := hU
  rw [← hu] at hfix ⊢
  rw [Ring.inverse_unit]
  have h1 : (u : W.EE) * W.γE δ ↑u⁻¹ = 1 := by
    rw [← hfix, ← map_mul, Units.mul_inv, map_one]
  exact (Units.inv_eq_of_mul_eq_one_right h1).symm

theorem invariantLetter_fixed_smul {c : ZMod n} (e : W.EE) (he : ∀ δ ∈ W.DelF, W.γE δ e = e) {x : W.DD T}
    (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (e • x) := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [smul_comm_letA_EE, h.1]
  · rw [W.γD_smul, he δ hδ, h.2 δ hδ]

theorem invariantLetter_gamma_sub {c : ZMod n} {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (W.γ T x - x) := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [smul_sub, idempotent_smul_gamma, h.1]
  · rw [map_sub, gammaD_gamma_comm, h.2 δ hδ]

theorem invariantLetter_derivation (hπΔ : W.π₀ ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    {c : ZMod n} {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (derivationOnWachModule W T x) := by
  rw [derivation_on_wach_module_apply]
  exact invariantLetter_fixed_smul W T (uniformizerInverse W)
    (fun δ hδ => delta_fixes_inverse W W.π₀ hπΔ hU δ hδ) (invariantLetter_gamma_sub W T h)

theorem invariantLetter_derivation_pow (hπΔ : W.π₀ ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    {c : ZMod n} (k : ℕ) {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c ((derivationOnWachModule W T ^ k) x) := by
  induction k with
  | zero => rw [pow_zero, Module.End.one_apply]; exact h
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact invariantLetter_derivation W T hπΔ hU ih

theorem invariantLetter_polynomial_derivation (hπΔ : W.π₀ ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    {c : ZMod n} (P : Polynomial O) {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (Polynomial.aeval (derivationOnWachModule W T) P x) := by
  induction P using Polynomial.induction_on'
  next p q hp hq =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact ⟨by rw [smul_add, hp.1, hq.1], fun δ hδ => by rw [map_add (f := _), hp.2 δ hδ, hq.2 δ hδ]⟩
  next k a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    have hk := invariantLetter_derivation_pow W T hπΔ hU k h
    exact ⟨by rw [smul_comm _ a, hk.1], fun δ hδ => by rw [map_smul, hk.2 δ hδ]⟩

def DerivationPreservesQLattice [NeZero n] : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (k : ℤ) (x : W.DD T),
    Formalism.MainNotions.CrystallineLiftingInputs.InQN W T i k x → Formalism.MainNotions.CrystallineLiftingInputs.InQN W T i k (Formalism.MainNotions.CrystallineLiftingInputs.dOp W T x)

def QLattice (c : ZMod n) (k : ℕ) (x : W.DD T) : Prop :=
  Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x ∧ Formalism.MainNotions.LiftingTheory.qp W ^ k • x ∈ W.N T

theorem qLattice_iff (c : ZMod n) (k : ℕ) (x : W.DD T) :
    Formalism.MainNotions.CrystallineLiftingInputs.InQN W T c (k : ℤ) x ↔ QLattice W T c k x := by
  unfold Formalism.MainNotions.CrystallineLiftingInputs.InQN QLattice
  simp

theorem qLattice_add {c : ZMod n} {k : ℕ} {x y : W.DD T} (hx : QLattice W T c k x)
    (hy : QLattice W T c k y) : QLattice W T c k (x + y) := by
  refine ⟨⟨?_, fun δ hδ => ?_⟩, ?_⟩
  · rw [smul_add, hx.1.1, hy.1.1]
  · rw [map_add (f := _), hx.1.2 δ hδ, hy.1.2 δ hδ]
  · rw [smul_add]
    exact add_mem hx.2 hy.2

theorem qLattice_smul {c : ZMod n} {k : ℕ} (a : O) {x : W.DD T} (hx : QLattice W T c k x) :
    QLattice W T c k (a • x) := by
  refine ⟨⟨?_, fun δ hδ => ?_⟩, ?_⟩
  · rw [smul_comm _ a, hx.1.1]
  · rw [map_smul, hx.1.2 δ hδ]
  · rw [smul_comm _ a, ← algebraMap_smul (LetA O n) a]
    exact Submodule.smul_mem _ _ hx.2

theorem qLattice_mono {c : ZMod n} {k k' : ℕ} (hk : k ≤ k') {x : W.DD T} (hx : QLattice W T c k x) :
    QLattice W T c k' x := by
  refine ⟨hx.1, ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ hx.2

theorem qLattice_derivation [NeZero n] (hDS : DerivationPreservesQLattice W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hT : IsCrys PD T.ρ) (c : ZMod n) (k : ℕ)
    {x : W.DD T} (h : QLattice W T c k x) : QLattice W T c k (derivationOnWachModule W T x) := by
  rw [← qLattice_iff] at h ⊢
  rw [derivation_on_wach_module_apply]
  exact hDS hA T hT c (k : ℤ) x h

theorem qLattice_polynomial_derivation [NeZero n] (hDS : DerivationPreservesQLattice W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hT : IsCrys PD T.ρ) (c : ZMod n) (k : ℕ)
    (P : Polynomial O) {x : W.DD T} (h : QLattice W T c k x) :
    QLattice W T c k (Polynomial.aeval (derivationOnWachModule W T) P x) := by
  have hpow : ∀ j : ℕ, QLattice W T c k ((derivationOnWachModule W T ^ j) x) := by
    intro j
    induction j with
    | zero => rw [pow_zero, Module.End.one_apply]; exact h
    | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact qLattice_derivation W T hDS hA hT c k ih
  induction P using Polynomial.induction_on'
  next p q hp hq =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact qLattice_add W T hp hq
  next j a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact qLattice_smul W T a (hpow j)

end Op

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LengthCokerLe
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

def π0N (T : LocLat G Qp LL O) (i : ZMod n) : Submodule O ↥(NDl W T i) :=
  ((NDl W T i).map (W.π₀ • (LinearMap.id : W.DD T →ₗ[O] W.DD T))).comap (NDl W T i).subtype

def IsRed (T : LocLat G Qp LL O) (i : ZMod n) {r : ℕ} (red : ↥(NDl W T i) →ₗ[O] (Fin r → O)) : Prop :=
  Function.Surjective red ∧ LinearMap.ker red = π0N W T i

theorem length_coker_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r : ℕ}
    (QQ : Matrix (Fin r) (Fin r) O) (l : O) (hl : l ≠ 0) (V : ℕ) (hd : QQ.det ∣ l ^ V) :
    Module.length O ((Fin r → O) ⧸ LinearMap.range (Matrix.toLin' QQ)) ≤
      (V : ℕ∞) * Module.length O (O ⧸ Ideal.span {l}) := by
  classical
  have hdet0 : QQ.det ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hd
    exact pow_ne_zero V hl hd
  have hL := Formalism.KernelCokernelLengths.length_theorems_all_hold.1 O (Fin r → O) (Matrix.toLin' QQ) (by rwa [LinearMap.det_toLin'])
  rw [hL, LinearMap.det_toLin', ← Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.len_pow l hl V]
  have hle : Ideal.span {l ^ V} ≤ Ideal.span {QQ.det} := Ideal.span_singleton_le_span_singleton.2 hd
  first
    | exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
    | exact Module.length_le_of_surjective (Ideal.Quotient.factorₐ O hle).toLinearMap
        (Ideal.Quotient.factor_surjective hle)

theorem lemmaDN_core {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ}
    (hS : SetCS W d T₁ T₂ F b S η m) (i : ZMod n) {r : ℕ} (red : ↥(NDl W T₂ i) →ₗ[O] (Fin r → O))
    (hsurj : Function.Surjective red) (hker : LinearMap.ker red = π0N W T₂ i) {m' : ℕ} (hm' : m' ≤ m)
    (g : Fin m' → W.DD T₂) (hgN : ∀ j, g j ∈ NDl W T₂ i) (cols : Fin r → ↥(NDl W T₂ i))
    (hcols : ∀ k, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) ∈ QhP W T₂ i (b i + S) ∨
      ∃ j, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) = g j)
    (V : ℕ) (hV : V ≤ finrank LL T₂.V * S + 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ * m)
    (hdet : (Matrix.of fun l k => red (cols k) l).det ∣ ((PD.p : ℕ) : O) ^ V) :
    ∃ s : Finset (W.DD T₂), s.card ≤ m ∧ (↑s : Set (W.DD T₂)) ⊆ NDl W T₂ i ∧
      ∃ L kO : ℕ, Module.length O (↥(NDl W T₂ i) ⧸
          ((NDl W T₂ i).map (W.π₀ • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            (PhiPullΔ W T₂ i).map
              ((Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S)) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            Submodule.span O (↑s : Set (W.DD T₂))).comap (NDl W T₂ i).subtype) ≤ (L : ℕ∞) ∧
        lenOl PD (O := O) = kO ∧
        (L : ℝ) ≤ lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S * kO := by
  classical
  obtain ⟨hdom, hdvr, -⟩ := hS.2.2.2.1
  haveI := hdom
  haveI := hdvr
  obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
  have hp11 : 11 ≤ PD.p := hS.2.1
  haveI : NeZero PD.p := ⟨by omega⟩
  have hpL : ((PD.p : ℕ) : LL) ≠ 0 := (hζ.neZero').out
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    apply hpL
    have := congrArg (algebraMap O LL) h
    rwa [map_natCast, map_zero] at this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := by
    first
      | exact hϖ.maximalIdeal_eq
      | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hlen1 : Module.length O (O ⧸ Ideal.span {ϖ}) = 1 := by
    rw [← hm]
    first
      | exact Module.length_eq_one_iff.2
          (isSimpleModule_iff_isCoatom.2 (IsLocalRing.maximalIdeal.isMaximal O).out)
      | exact Module.length_eq_one_iff.2
          (isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal O)))
  have hlenp : Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)}) = (k : ℕ∞) := by
    rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit,
      Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.len_pow ϖ hϖ.ne_zero k, hlen1, mul_one]
  let s : Finset (W.DD T₂) := Finset.univ.image g
  refine ⟨s, ?_, ?_, V * k, k, ?_, ?_, ?_⟩
  · exact Finset.card_image_le.trans (by simpa using hm')
  · intro x hx
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨j, rfl⟩ := hx
    exact hgN j
  · set X := (((NDl W T₂ i).map (W.π₀ • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            (PhiPullΔ W T₂ i).map
              ((Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S)) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            Submodule.span O (↑s : Set (W.DD T₂))).comap (NDl W T₂ i).subtype) with hX
    have hkerX : LinearMap.ker red ≤ X := by
      rw [hker]
      exact Submodule.comap_mono (le_sup_left.trans le_sup_left)
    have hcolX : ∀ k', cols k' ∈ X := by
      intro k'
      rw [hX, Submodule.mem_comap, Submodule.coe_subtype]
      rcases hcols k' with h | ⟨j, hj⟩
      · exact Submodule.mem_sup_left (Submodule.mem_sup_right h)
      · rw [hj]
        exact Submodule.mem_sup_right (Submodule.subset_span (by simp [s]))
    let QQ : Matrix (Fin r) (Fin r) O := Matrix.of fun l k' => red (cols k') l
    let e := LinearMap.quotKerEquivOfSurjective red hsurj
    let f : (Fin r → O) →ₗ[O] (↥(NDl W T₂ i) ⧸ X) := (Submodule.factor hkerX) ∘ₗ e.symm.toLinearMap
    have hf : Function.Surjective f := (Submodule.factor_surjective hkerX).comp e.symm.surjective
    have hrange : LinearMap.range (Matrix.toLin' QQ) ≤ LinearMap.ker f := by
      rintro _ ⟨v, rfl⟩
      rw [LinearMap.mem_ker]
      have hv : Matrix.toLin' QQ v = red (∑ k', v k' • cols k') := by
        ext l'
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_smul, QQ, mul_comm]
      have he : e.symm (red (∑ k', v k' • cols k')) =
          Submodule.Quotient.mk (∑ k', v k' • cols k') := by
        rw [LinearEquiv.symm_apply_eq]
        first
          | rfl
          | exact (LinearMap.quotKerEquivOfSurjective_apply_mk red hsurj _).symm
      simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hv, he,
        Submodule.factor_mk, Submodule.Quotient.mk_eq_zero]
      first
        | rw [Submodule.factor_mk, Submodule.Quotient.mk_eq_zero]
        | (change Submodule.Quotient.mk (p := X) (∑ k', v k' • cols k') = 0
           rw [Submodule.Quotient.mk_eq_zero])
      exact Submodule.sum_mem _ fun k' _ => Submodule.smul_mem _ _ (hcolX k')
    let g' := (LinearMap.range (Matrix.toLin' QQ)).liftQ f hrange
    have hg' : Function.Surjective g' := by
      intro z
      obtain ⟨y, rfl⟩ := hf z
      exact ⟨Submodule.Quotient.mk y, rfl⟩
    calc Module.length O (↥(NDl W T₂ i) ⧸ X)
        ≤ Module.length O ((Fin r → O) ⧸ LinearMap.range (Matrix.toLin' QQ)) :=
          Module.length_le_of_surjective g' hg'
      _ ≤ (V : ℕ∞) * Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)}) :=
          length_coker_le QQ _ hp0 V hdet
      _ = ((V * k : ℕ) : ℕ∞) := by rw [hlenp, Nat.cast_mul]
  · unfold Formalism.WeaklyAdmissibleFiltrations.lenOl
    exact hlenp
  · have hp1 : (1 : ℝ) < (PD.p : ℝ) := by exact_mod_cast (by omega : 1 < PD.p)
    have hcD : 0 ≤ Formalism.MainNotions.RamifiedCoefficientChains.cD PD.p (hpar n b S + η) := by
      unfold Formalism.MainNotions.RamifiedCoefficientChains.cD
      have h1 : 0 < (PD.p : ℝ) - 1 := by linarith
      have h2 : 0 ≤ ((hpar n b S + η : ℕ) : ℝ) + 1 := by positivity
      have := div_nonneg h2 h1.le
      linarith
    have hfl := Nat.floor_le hcD
    have hV' : (V : ℝ) ≤ (finrank LL T₂.V : ℝ) * S + 2 * m * Formalism.MainNotions.RamifiedCoefficientChains.cD PD.p (hpar n b S + η) := by
      have h := (Nat.cast_le (α := ℝ)).2 hV
      push_cast at h
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith [h, hfl, hm0]
    unfold Formalism.MainNotions.RamifiedCoefficientChains.S9.lenC
    push_cast
    exact mul_le_mul_of_nonneg_right hV' (Nat.cast_nonneg k)

def DetColsE : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∃ (r : ℕ) (red : ↥(NDl W T₂ i) →ₗ[O] (Fin r → O)) (_ : IsRed W T₂ i red)
        (m' : ℕ) (_ : m' ≤ m) (g : Fin m' → W.DD T₂) (_ : ∀ j, g j ∈ NDl W T₂ i)
        (cols : Fin r → ↥(NDl W T₂ i)),
        (∀ k, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) ∈ QhP W T₂ i (b i + S) ∨
          ∃ j, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) = g j) ∧
        ∃ V : ℕ, V ≤ finrank LL T₂.V * S + 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ * m ∧
          (Matrix.of fun l k => red (cols k) l).det ∣ ((PD.p : ℕ) : O) ^ V

theorem lemmaDN_of_detE (h : DetColsE W) : LemmaDN W := by
  intro d T₁ T₂ F b S η m hS i hi
  obtain ⟨r, red, hred, m', hm', g, hgN, cols, hcols, V, hV, hdet⟩ := h d T₁ T₂ F b S η m hS i hi
  obtain ⟨hsurj, hker⟩ := hred
  exact lemmaDN_core W hS i red hsurj hker hm' g hgN cols hcols V hV hdet

end Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD
end
end

