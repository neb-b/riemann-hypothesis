module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfOpENeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProperTriple
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.ProperTriple

open MeasureTheory ValuativeRel Matrix in
private lemma unipotent_block_entries_eq_one_zero {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {c ρ : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ _root_.GlobalTheory.RootEx.N k n c (ρ + 1)) :
    (∀ t t' : n, (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl t) (Sum.inl t') =
      (1 : Matrix n n k) t t') ∧
    (∀ (t : n) (i : Fin c), (i : ℕ) + 1 = ρ + 1 →
      (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl t) (Sum.inr i) = 0) ∧
    (∀ (t : n) (i : Fin c), (i : ℕ) + 1 = ρ + 1 →
      (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inl t) = 0) := by
  have h := _root_.GlobalTheory.RootEx.Model.mem_N_iff.1 hu
  unfold _root_.GlobalTheory.RootEx.InN _root_.GlobalTheory.RootEx.lev at h
  refine ⟨fun t t' => ?_, fun t i hi => ?_, fun t i hi => ?_⟩
  · rw [h _ _ (by simp)]
    simp [Matrix.one_apply]
  · rw [h _ _ (by simp [hi])]
    simp
  · rw [h _ _ (by simp [hi])]
    simp

open MeasureTheory ValuativeRel Matrix in
private lemma recover_colE_vec_from_embX_product {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {c ρ : ℕ} (hρc : ρ < c) (x : GL n k) (u : _root_.GlobalTheory.RootEx.N k n c (ρ + 1))
    (β : n → k) (r : n) :
    ∑ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
        _root_.GlobalTheory.RootEx.colE c (ρ + 1) β)⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl r) (Sum.inl s) *
      (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
        _root_.GlobalTheory.RootEx.colE c (ρ + 1) β) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩) = β r := by
  obtain ⟨hll, hlr, -⟩ := unipotent_block_entries_eq_one_zero u.2
  obtain ⟨hll', -, hrl'⟩ := unipotent_block_entries_eq_one_zero (inv_mem u.2)
  have h1 : ∀ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
      _root_.GlobalTheory.RootEx.colE c (ρ + 1) β) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩) = ((x : Matrix n n k) *ᵥ β) s := by
    intro s
    rw [Units.val_mul, Units.val_mul, _root_.GlobalTheory.RootEx.Radical.embX_val,
      _root_.GlobalTheory.RootEx.ExchangeSupport.colE_val]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hll, hlr, _root_.GlobalTheory.RootEx.ExchangeSupport.colM,
      Matrix.mulVec, dotProduct, Matrix.one_apply]
  have h2 : ∀ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
      _root_.GlobalTheory.RootEx.colE c (ρ + 1) β)⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl r) (Sum.inl s) = (↑x⁻¹ : Matrix n n k) r s := by
    intro s
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← map_inv,
      _root_.GlobalTheory.RootEx.Radical.embX_val, _root_.GlobalTheory.RootEx.ExchangeSupport.colE_inv_val]
    simp only [Matrix.coe_units_inv] at hll' hrl' ⊢
    have hz : ∀ i : Fin c, (i : ℕ) = ρ →
        ∑ a, ((u : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)⁻¹ (Sum.inr i) (Sum.inl a) *
          (↑x : Matrix n n k)⁻¹ a s = 0 :=
      fun i hi => Finset.sum_eq_zero fun a _ => by rw [hrl' a i (by omega), zero_mul]
    simp +contextual [Matrix.mul_apply, Fintype.sum_sum_type, hll', _root_.GlobalTheory.RootEx.ExchangeSupport.colM,
      Matrix.one_apply, hz]
  simp_rw [h1, h2]
  change ((↑x⁻¹ : Matrix n n k) *ᵥ ((x : Matrix n n k) *ᵥ β)) r = β r
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]


open MeasureTheory ValuativeRel Matrix in
theorem _root_.GlobalTheory.RootEx.ProperTriple.proper_triple : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ)
    (_ : ρ < c) (C : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact C),
    ∃ D : Set (GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1) × (n → k)), IsCompact D ∧
      ∀ z : GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1) × (n → k),
        _root_.GlobalTheory.RootEx.embX c z.1 * (z.2.1 : GL (n ⊕ Fin c) k) *
          _root_.GlobalTheory.RootEx.colE c (ρ + 1) z.2.2 ∈ C → z ∈ D := by
  intro k _ _ _ _ n _ _ c ρ _ hρc C hC
  let F : GL (n ⊕ Fin c) k → (n → k) := fun g r =>
    ∑ s, (↑g⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl r) (Sum.inl s) *
      (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩)
  have hF : Continuous F := by
    refine continuous_pi fun r => continuous_finsetSum _ fun s _ => ?_
    exact (Units.continuous_coe_inv.matrix_elem _ _).mul (Units.continuous_val.matrix_elem _ _)
  have hK : IsCompact (F '' C) := hC.image hF
  have hC' : IsCompact ((fun q : GL (n ⊕ Fin c) k × (n → k) =>
      q.1 * (_root_.GlobalTheory.RootEx.colE c (ρ + 1) q.2)⁻¹) '' (C ×ˢ (F '' C))) :=
    (hC.prod hK).image (continuous_fst.mul
      (_root_.GlobalTheory.RootEx.ExchangeSupport.continuous_colE.comp continuous_snd).inv)
  obtain ⟨D₀, hD₀, hD₀C⟩ := _root_.GlobalTheory.QuotInt.compact_preimage
    (_root_.GlobalTheory.RootEx.VolN.isClosed_N (k := k) (n := n) (c := c) (ρ + 1)) hC'
  refine ⟨(fun q : (GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1)) × (n → k) =>
    (q.1.1, q.1.2, q.2)) '' (D₀ ×ˢ (F '' C)), (hD₀.prod hK).image (by fun_prop), ?_⟩
  intro z hz
  have hβ : z.2.2 ∈ F '' C := ⟨_, hz, funext (recover_colE_vec_from_embX_product hρc z.1 z.2.1 z.2.2)⟩
  have hz' : (z.1, z.2.1) ∈ D₀ := hD₀C _ ⟨(_, z.2.2), ⟨hz, hβ⟩, by simp⟩
  exact ⟨((z.1, z.2.1), z.2.2), ⟨hz', hβ⟩, rfl⟩

end GlobalTheory.RootEx.ProperTriple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralWhittakerTwist
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.RootEx

private theorem exists_open_translations {M : Type*} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] {Φ : M → ℂ} (hΦ : Φ ∈ SB M) :
    ∃ Λ : AddSubgroup M, IsOpen (Λ : Set M) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  obtain ⟨K, hKo, hK⟩ := GlobalTheory.QuotInt.exists_open_stab (G := Multiplicative M)
    (F := fun x => Φ (Multiplicative.toAdd x)) hΦ
  refine ⟨{ carrier := {y | Multiplicative.ofAdd y ∈ K}
            add_mem' := fun hy hz => K.mul_mem hy hz
            zero_mem' := K.one_mem
            neg_mem' := fun hy => K.inv_mem hy }, hKo, ?_⟩
  intro x y hy
  exact hK (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) hy

theorem exists_isQuotInt_unfolding : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (P P' : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P'] (π : Representation ℂ (GL n k) P) (π' : Representation ℂ (GL n' k) P') (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P) (_ : ∀ g h φ Ψ Ψ', Ψ'.1 = om μ g h Ψ.1 → θ (π' g φ) Ψ' = π h (θ φ Ψ)) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : IsPos ψ p π σ b) (φ : P') (F : A) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (f : GL (n ⊕ Fin c) k → ℂ) (_ : ∀ h Ψ, Ψ.1 = opE ψ ν p (om μ 1 h Φ.1) → f h = b (θ φ Ψ) (σ h F)), ∃ z, IsQuotInt ν μX μG p f z := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ hψc hψ1 ν _ μ hμ μX _ μG _ A _ _ σ hσ P P' _ _ _ _
    π π' θ hθ b hb φ F Φ f hf
  have hom := om_isSmoothRepresentation k (n' ⊕ Fin (c + 1)) (n ⊕ Fin c) μ hμ
  have hom' := om_isSmoothRepresentation k n' n μ hμ
  have hE := opE_SB_and_linear k n n' c p ψ hψc ν
  have hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  have hmemΨ : ∀ h : GL (n ⊕ Fin c) k, opE ψ ν p (om μ 1 h Φ.1) ∈ SB (Matrix n n' k) :=
    fun h => hE.1 _ (hom.2.2.2.1 1 h Φ.1 Φ.2)
  have om_smul : ∀ {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      (g : GL a k) (h : GL b k) (z : ℂ) (G : Matrix b a k → ℂ), om μ g h (z • G) = z • om μ g h G := by
    intro a b _ _ _ _ g h z G
    funext y
    simp only [om, Pi.smul_apply, smul_eq_mul]
    ring
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hU : {y : GL (n ⊕ Fin c) k | σ y F = F ∧ om μ 1 y Φ.1 = Φ.1} ∈ 𝓝 (1 : GL (n ⊕ Fin c) k) := by
      have hσU : {y : GL (n ⊕ Fin c) k | σ y F = F} ∈ 𝓝 (1 : GL (n ⊕ Fin c) k) :=
        (hσ F).mem_nhds (by simp)
      have ho : IsOpen {y : GL (n ⊕ Fin c) k | om μ 1 y Φ.1 = Φ.1} :=
        (hom.2.2.2.2 Φ.1 Φ.2).preimage (continuous_const.prodMk continuous_id)
      filter_upwards [hσU, ho.mem_nhds (hom.1 Φ.1)] with y hy hz
      exact ⟨hy, hz⟩
    have hx : {y | x⁻¹ * y ∈ {y : GL (n ⊕ Fin c) k | σ y F = F ∧ om μ 1 y Φ.1 = Φ.1}} ∈ 𝓝 x := by
      have hc : Continuous fun y : GL (n ⊕ Fin c) k => x⁻¹ * y := continuous_const.mul continuous_id
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hU)
    filter_upwards [hx] with y hy
    obtain ⟨z, rfl⟩ : ∃ z, y = x * z := ⟨x⁻¹ * y, by group⟩
    simp only [inv_mul_cancel_left] at hy
    obtain ⟨h1, h2⟩ := hy
    have e1 : om μ 1 (x * z) Φ.1 = om μ 1 x Φ.1 := by
      have := hom.2.1 1 1 x z Φ.1
      rw [mul_one] at this
      rw [this, h2]
    have hσz : σ (x * z) F = σ x F := by
      rw [map_mul, Module.End.mul_apply, h1]
    rw [hf (x * z) ⟨_, hmemΨ x⟩ (by rw [e1]), hf x ⟨_, hmemΨ x⟩ rfl, hσz]
  obtain ⟨Λ, hΛo, hΛ⟩ := exists_open_translations (M := Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) Φ.2
  obtain ⟨Ω, hΩ, hΩR⟩ := opE_support_compact_mod_R k n n' c p hp1 hpc ψ hψc hψ1 ν (tsupport Φ.1) hΦ.2
    Λ hΛo
  have hsupp : ∀ h, f h ≠ 0 → ∃ r ∈ R k n c p, ∃ w ∈ Ω, h = r * w := by
    intro h hfh
    have hne : opE ψ ν p (om μ 1 h Φ.1) ≠ 0 := by
      intro h0
      apply hfh
      rw [hf h 0 (by rw [h0]; rfl)]
      simp
    obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hne
    exact hΩR μ Φ.1 (subset_tsupport _) hΛ (fun _ => 1) (IsLocallyConstant.const 1) h x₀
      (by simpa using hx₀)
  have hequiv : ∀ (x : GL n k), ∀ u ∈ N k n c p, ∀ h, f (embX c x * u * h) =
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) * f h := by
    intro x u hu h
    let Ψ'' : SB (Matrix n n' k) := ⟨om μ 1 x (opE ψ ν p (om μ 1 h Φ.1)), hom'.2.2.2.1 1 x _ (hmemΨ h)⟩
    have m1 : om μ 1 (embX c x * u * h) Φ.1 = om μ 1 (embX c x) (om μ 1 u (om μ 1 h Φ.1)) := by
      have e1 := hom.2.1 1 1 (embX c x * u) h Φ.1
      have e2 := hom.2.1 1 1 (embX c x) u (om μ 1 h Φ.1)
      rw [mul_one] at e1 e2
      rw [e1, e2]
    have hkey : (((((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) *
        (ψ (-simpleSum u) : ℂ)) • Ψ'' : SB (Matrix n n' k)) : Matrix n n' k → ℂ) =
        opE ψ ν p (om μ 1 (embX c x * u * h) Φ.1) := by
      rw [m1, (opE_om_embX k n n' c p hp1 hpc ψ ν μ _).1 x,
        opE_om_target_unipotent k n n' c p hp1 hpc ψ ν μ _ u hu, om_smul, Submodule.coe_smul, smul_smul]
    have hθΨ : θ φ Ψ'' = π x (θ φ ⟨_, hmemΨ h⟩) := by
      have := hθ 1 x φ ⟨_, hmemΨ h⟩ Ψ'' rfl
      simpa using this
    rw [hf _ _ hkey, hf h ⟨_, hmemΨ h⟩ rfl, map_smul, hθΨ, map_smul, LinearMap.smul_apply, map_mul,
      map_mul, Module.End.mul_apply, Module.End.mul_apply, hb.2 x, hb.1 _ u hu, smul_eq_mul]
    have hN : 0 < nabs k (Matrix.GeneralLinearGroup.det x) := GlobalTheory.RootEx.OpELevi.nabs_pos _
    have hpow : (nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) =
        nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) *
          nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) := by
      rw [← Real.rpow_add hN]
      ring_nf
    have hψ : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
        Circle.coe_one]
    rw [hpow, Complex.ofReal_mul]
    linear_combination
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) *
      b (θ φ ⟨_, hmemΨ h⟩) (σ h F) * hψ
  exact (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp1 hpc ν μX μG f).2 hloc ⟨Ω, hΩ, hsupp⟩ hequiv

end GlobalTheory.RootEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatFunDifferentiableOn
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.DoublingSeries

def ratFun (q N : ℕ) (α : Fin N → ℂˣ) (X : ℂ) : ℂ :=
  (∏ i, (1 - (α i : ℂ) * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X)⁻¹) *
    (∏ i, (1 - (((α i)⁻¹ : ℂˣ) : ℂ) * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X)⁻¹) *
      ∏ i ∈ Finset.Icc 1 N, (1 - (q : ℂ) ^ (-(i : ℂ)) * X ^ 2)

theorem ratFun_cpow {q : ℕ} (hq : 1 < q) (N : ℕ) (α : Fin N → ℂˣ) (s : ℂ) :
    lFactor q α (s + 1 / 2) * lFactor q α⁻¹ (s + 1 / 2) * invNormFactor q N s =
      ratFun q N α ((q : ℂ) ^ (-s)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have h1 : (q : ℂ) ^ (-(s + 1 / 2)) = (q : ℂ) ^ (-(1 / 2 : ℂ)) * (q : ℂ) ^ (-s) := by
    rw [← Complex.cpow_add _ _ hq0]; ring_nf
  have h2 : ∀ i : ℕ, (q : ℂ) ^ (-(2 * s + i)) = (q : ℂ) ^ (-(i : ℂ)) * ((q : ℂ) ^ (-s)) ^ 2 := fun i => by
    rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq0]; push_cast; ring_nf
  simp only [lFactor, invNormFactor, ratFun, h1, h2, Pi.inv_apply, mul_assoc]

theorem ratFun_differentiableOn {q : ℕ} (hq : 1 < q) (N : ℕ) (α : Fin N → ℂˣ) (ρ : ℝ)
    (hα : ∀ x, ‖(α x : ℂ)‖ ≤ (q : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (q : ℝ) ^ ρ) :
    DifferentiableOn ℂ (ratFun q N α) (Metric.ball 0 ((q : ℝ) ^ (1 / 2 - ρ))) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have key : ∀ a : ℂ, ‖a‖ ≤ (q : ℝ) ^ ρ → ∀ X ∈ Metric.ball (0 : ℂ) ((q : ℝ) ^ (1 / 2 - ρ)),
      1 - a * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X ≠ 0 := by
    intro a ha X hX
    rw [mem_ball_zero_iff] at hX
    have hn : ‖a * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X‖ < 1 := by
      rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
      have hre : (-(1 / 2 : ℂ)).re = -(1 / 2) := by norm_num
      rw [hre]
      calc ‖a‖ * (q : ℝ) ^ (-(1 / 2 : ℝ)) * ‖X‖ ≤ (q : ℝ) ^ ρ * (q : ℝ) ^ (-(1 / 2 : ℝ)) * ‖X‖ := by gcongr
        _ < (q : ℝ) ^ ρ * (q : ℝ) ^ (-(1 / 2 : ℝ)) * (q : ℝ) ^ (1 / 2 - ρ) := by gcongr
        _ = 1 := by rw [← Real.rpow_add hq0, ← Real.rpow_add hq0, show ρ + -(1 / 2 : ℝ) + (1 / 2 - ρ) = 0 by ring, Real.rpow_zero]
    intro h
    have e : a * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X = 1 := by linear_combination -h
    rw [e, norm_one] at hn
    exact lt_irrefl _ hn
  unfold ratFun
  refine DifferentiableOn.mul (DifferentiableOn.mul ?_ ?_) ?_
  · exact DifferentiableOn.fun_finsetProd fun i _ =>
      ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).inv
        fun X hX => key _ (hα i).1 X hX
  · exact DifferentiableOn.fun_finsetProd fun i _ =>
      ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).inv
        fun X hX => key (((α i)⁻¹ : ℂˣ) : ℂ) (by rw [Units.val_inv_eq_inv_val, norm_inv]; exact (hα i).2) X hX
  · exact DifferentiableOn.fun_finsetProd fun i _ =>
      (differentiableOn_const (𝕜 := ℂ) (1 : ℂ)).sub ((differentiableOn_const (𝕜 := ℂ) ((q : ℂ) ^ (-(i : ℂ)))).mul (differentiableOn_id (𝕜 := ℂ).pow 2))

theorem exists_cpow_neg_eq {q : ℕ} (hq : 1 < q) (s₀ : ℝ) {z : ℂ} (hz : z ≠ 0) (hzs : ‖z‖ < (q : ℝ) ^ (-s₀)) :
    ∃ s : ℂ, s₀ < s.re ∧ (q : ℂ) ^ (-s) = z := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hl : 0 < Real.log q := Real.log_pos hq1
  refine ⟨-Complex.log z / (Real.log q : ℂ), ?_, ?_⟩
  · have e : (-Complex.log z / (Real.log q : ℂ)).re = -Real.log ‖z‖ / Real.log q := by
      rw [Complex.div_ofReal_re, Complex.neg_re, Complex.log_re]
    rw [e, lt_div_iff₀ hl]
    have := Real.log_lt_log (norm_pos_iff.2 hz) hzs
    rw [Real.log_rpow (by linarith)] at this
    linarith
  · have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
    have hl' : (Real.log q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl.ne'
    rw [show (Real.log q : ℂ) * -(-Complex.log z / (Real.log q : ℂ)) = Complex.log z by field_simp]
    exact Complex.exp_log hz

theorem cpow_split {q : ℕ} (hq : 1 < q) (N : ℕ) (s : ℂ) {m : ℤ} (hm : 0 ≤ m) :
    (q : ℂ) ^ (-((N : ℂ) / 2 + s) * (m : ℂ)) =
      (((q : ℝ) ^ (-((N : ℝ) / 2) * (m : ℝ)) : ℝ) : ℂ) * ((q : ℂ) ^ (-s)) ^ m.toNat := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq0]
  congr 1
  have : ((m.toNat : ℕ) : ℂ) = (m : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hm
  push_cast
  rw [this]
  ring

theorem sumAbs_nonneg {D : Type} [Fintype D] (e : D → ℤ) : 0 ≤ sumAbs e :=
  Finset.sum_nonneg fun i _ => abs_nonneg (e i)

end GlobalTheory.DoublingSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexConjUniformizerPowerDiagonalGLReindex
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section
namespace GlobalTheory.ReindexTorus

def reindexGL (k : Type) [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (σ : n ≃ n') : GL n k ≃* GL n' k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k σ).toMulEquiv

theorem val_reindexGL (k : Type) [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (σ : n ≃ n') (g : GL n k) : (reindexGL k σ g).val = Matrix.reindex σ σ g.val := rfl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem map_reindexGL_KO (σ : n ≃ n') : (KO k n).map (reindexGL k σ).toMonoidHom = KO k n' := by
  ext x
  rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap, GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.SplitFlip.mem_KO_iff]
  have h1 : ∀ i j, ((reindexGL k σ).symm x).val i j = x.val (σ i) (σ j) := fun i j => rfl
  have h2 : ∀ i j, (((reindexGL k σ).symm x)⁻¹).val i j = (x⁻¹).val (σ i) (σ j) := fun i j => by
    rw [← map_inv]; rfl
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, h1, h2]
  exact and_congr ⟨fun h i j => by simpa using h (σ.symm i) (σ.symm j), fun h i j => h _ _⟩
    ⟨fun h i j => by simpa using h (σ.symm i) (σ.symm j), fun h i j => h _ _⟩

theorem reindexGL_torusElt (σ : n ≃ n') (ϖ : kˣ) (e : n → ℤ) :
    reindexGL k σ (torusElt k n ϖ e) = torusElt k n' ϖ (e ∘ σ.symm) := by
  refine Units.ext ?_
  rw [val_reindexGL, val_torusElt, val_torusElt, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  rfl

theorem relIndex_conj_torusElt_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (σ : n ≃ n') (e : n → ℤ),
    ((KO k n').map (MulAut.conj (torusElt k n' ϖ (e ∘ σ.symm))).toMonoidHom).relIndex (KO k n') =
      ((KO k n).map (MulAut.conj (torusElt k n ϖ e)).toMonoidHom).relIndex (KO k n) := by
  intro k _ _ _ _ ϖ n n' _ _ _ _ σ e
  set φ := reindexGL k σ
  have hconj : ∀ g : GL n k, ∀ H : Subgroup (GL n k),
      (H.map (MulAut.conj g).toMonoidHom).map φ.toMonoidHom =
        (H.map φ.toMonoidHom).map (MulAut.conj (φ g)).toMonoidHom := by
    intro g H
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x : 1
    simp [φ, map_mul, map_inv]
  have hK := map_reindexGL_KO k σ
  rw [← reindexGL_torusElt k σ ϖ e, ← hK, ← hconj]
  have key : ∀ A B : Subgroup (GL n k), (A.map φ.toMonoidHom).relIndex (B.map φ.toMonoidHom) = A.relIndex B := by
    intro A B
    rw [Subgroup.map_equiv_eq_comap_symm' φ A, Subgroup.relIndex_comap, Subgroup.map_map]
    have : (φ.symm.toMonoidHom.comp φ.toMonoidHom) = MonoidHom.id _ := by ext x : 1; simp
    rw [this, Subgroup.map_id]
  exact key _ _

end GlobalTheory.ReindexTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMulMatrixVolumeOpenSubgroupIntegralGL
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
open scoped Pointwise

namespace GlobalTheory.IndexVolume

theorem relIndex_mul_measure_subgroup {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by
  obtain ⟨s, hs, -⟩ := (H.subgroupOf L).exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  have hU : (⋃ a : s, (a.val : L) • (H : Set G)) = (L : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, SetLike.mem_coe]
    constructor
    · rintro ⟨a, h, hh, rfl⟩
      exact L.mul_mem a.val.2 (hHL hh)
    · intro hx
      obtain ⟨⟨b, h⟩, hbh, -⟩ := hs.existsUnique ⟨x, hx⟩
      refine ⟨b, (h.val : G), Subgroup.mem_subgroupOf.mp h.2, ?_⟩
      have := congrArg Subtype.val hbh
      exact this
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => (a.val : L) • (H : Set G)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, hh1, rfl⟩ ⟨h2, hh2, he⟩
    apply hab
    have hh1' : (⟨h1, hHL hh1⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh1
    have hh2' : (⟨h2, hHL hh2⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh2
    have e : (a.val : L) * ⟨h1, hHL hh1⟩ = (b.val : L) * ⟨h2, hHL hh2⟩ := Subtype.ext he.symm
    have := (hs.existsUnique ((a.val : L) * ⟨h1, hHL hh1⟩)).unique
      (y₁ := (a, ⟨_, hh1'⟩)) (y₂ := (b, ⟨_, hh2'⟩)) rfl e.symm
    exact congrArg Prod.fst this
  calc (H.relIndex L : ENNReal) * μ H = ∑' a : s, μ ((a.val : L) • (H : Set G)) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ (⋃ a : s, (a.val : L) • (H : Set G)) :=
        (measure_iUnion hdisj fun a => hH.const_smul _).symm
    _ = μ L := by rw [hU]

theorem volGL_of_subset_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
    (ν : Measure k) (s : Set (GL n k)) (hs : MeasurableSet s) (hK : s ⊆ KO k n) :
    volGL ν n s = volM ν n n (Units.val '' s) := by
  have hE := Model.measurableEmbedding_val (k := k) n
  unfold volGL
  rw [withDensity_apply _ hs, setLIntegral_congr_fun hs (g := fun _ => 1), setLIntegral_one, hE.comap_apply]
  intro g hg
  obtain ⟨u, rfl⟩ := hK hg
  have h1 : nabs k (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u)) = 1 := by
    rw [nabs_eq_one_iff]
    have : ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) : kˣ) : k) = algebraMap 𝒪[k] k u.val.det :=
      ((algebraMap 𝒪[k] k).map_det u.val).symm
    rw [this]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)
  simp only [h1, Real.one_rpow, ENNReal.ofReal_one]

theorem relIndex_mul_volM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (n : Type) [Fintype n] [DecidableEq n] (H L : Subgroup (GL n k)),
    H ≤ L → L ≤ KO k n → IsOpen (H : Set (GL n k)) →
    0 < (volM ν n n (Units.val '' (H : Set (GL n k)))).toReal ∧
    (H.relIndex L : ℝ) * (volM ν n n (Units.val '' (H : Set (GL n k)))).toReal =
      (volM ν n n (Units.val '' (L : Set (GL n k)))).toReal := by
  intro k _ _ _ _ _ _ ν _ n _ _ H L hHL hLK hH
  obtain ⟨hB, hlc, hsc, hc, -, -, hhaar, -⟩ := volGL_haar k n ν
  have hL : IsOpen (L : Set (GL n k)) := Subgroup.isOpen_mono hHL hH
  have hLc : IsCompact (L : Set (GL n k)) := hc.of_isClosed_subset (L.isClosed_of_isOpen hL) hLK
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hLc
  haveI : Finite (L ⧸ H.subgroupOf L) :=
    Subgroup.quotient_finite_of_isOpen _ (hH.preimage continuous_subtype_val)
  haveI : (H.subgroupOf L).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have key := relIndex_mul_measure_subgroup H L hHL hH.measurableSet (volGL ν n)
  have h0 : volGL ν n H ≠ 0 := (hH.measure_pos _ ⟨1, one_mem _⟩).ne'
  have ht : volGL ν n H ≠ ⊤ := ((measure_mono (hHL.trans hLK)).trans_lt hc.measure_lt_top).ne
  rw [← volGL_of_subset_KO ν _ hH.measurableSet (hHL.trans hLK),
    ← volGL_of_subset_KO ν _ hL.measurableSet hLK, ← key]
  refine ⟨ENNReal.toReal_pos h0 ht, ?_⟩
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

end GlobalTheory.IndexVolume
end

