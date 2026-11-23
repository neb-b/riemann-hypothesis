module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRankOneCornerPrincipalSeriesCongruence
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem corner_val_le_one {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (i j : Fin n) : valuation k (g.val i j) ≤ 1 := by
  obtain ⟨g, rfl⟩ := hg
  exact (g.val i j).2

theorem corner_mem_KO {g : GL (Fin n) k} (hM : ∀ i j, valuation k (g.val i j) ≤ 1) (hd : valuation k g.val.det = 1) :
    g ∈ KO k (Fin n) := by
  let N : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, hM i j⟩
  have e : (algebraMap 𝒪[k] k).mapMatrix N = g.val := rfl
  have hu : IsUnit N.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
    rw [RingHom.map_det, e, hd]
  obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det N).2 hu
  refine ⟨u, Units.ext ?_⟩
  change (algebraMap 𝒪[k] k).mapMatrix u.val = g.val
  rw [hu', e]

end

theorem corner_rankOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ x ∈ KO k (Fin n), ∀ a b : Fin n, a < b → ¬ Triv (ψ a / ψ b) (x.val a b) → (∀ j, b < j → Triv (ψ a / ψ j) (x.val a j)) → ∃ j ∈ grp ψ, ∃ (u : kˣ) (s : k), valuation k (u : k) = 1 ∧ valuation k s ≤ 1 ∧ s * x.val a b = (u : k) - 1 ∧ ψ a u ≠ ψ b u ∧ theta ψ j = (ψ b u : ℂ) ∧ x * j * x⁻¹ ∈ KO k (Fin n) ∧ (x * j * x⁻¹).val = 1 + Matrix.vecMulVec (fun i => s * x.val i b) (Pi.single a 1) := by
  intro k _ _ _ _ n ψ hord x hx a b hab hnt htr
  have hnt' := hnt
  unfold Triv at hnt'
  push_neg at hnt'
  obtain ⟨u, hu, hle, hne⟩ := hnt'
  have hx0 : x.val a b ≠ 0 := fun h0 => hnt (h0 ▸ triv_zero _)
  set s : k := ((u : k) - 1) / x.val a b with hs
  have hsx : s * x.val a b = (u : k) - 1 := div_mul_cancel₀ _ hx0
  have hs1 : valuation k s ≤ 1 := by
    rw [hs, map_div₀]
    exact div_le_one_of_le₀ hle zero_le'
  have hsm : ∀ i j, valuation k (s * x.val i j) ≤ valuation k (x.val i j) := fun i j => by
    rw [map_mul]
    exact mul_le_of_le_one_left' hs1
  let M : Matrix (Fin n) (Fin n) k := 1 + Matrix.vecMulVec (Pi.single b s) (x.val a)
  have hdet : M.det = (u : k) := by
    simp only [M]
    rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_single, mul_comm, hsx]
    ring
  let j : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact u.ne_zero)
  have hj : j.val = 1 + Matrix.vecMulVec (Pi.single b s) (x.val a) := rfl
  have hjK : j ∈ KO k (Fin n) := by
    refine corner_mem_KO (fun i l => ?_) (by rw [show j.val.det = (u : k) from hdet]; exact hu)
    rw [hj, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [Matrix.one_apply]; split_ifs <;> simp
    · rw [Matrix.vecMulVec_apply, Pi.single_apply]
      split_ifs
      · exact (hsm _ _).trans (corner_val_le_one hx _ _)
      · simp
  refine ⟨j, ⟨hjK, fun i l hil => ?_⟩, u, s, hu, hs1, hsx, ?_, ?_, ?_, ?_⟩
  · rw [hj, Matrix.add_apply, Matrix.one_apply_ne hil.ne, zero_add, Matrix.vecMulVec_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      exact triv_mono _ _ _ (hsm _ _) (hord a i l l hab.le hil.le le_rfl _ (htr l hil))
    · rw [zero_mul]; exact triv_zero _
  · intro h
    apply hne
    simp [h]
  · refine theta_rankOne k n ψ j _ _ b u hu hj fun i => ?_
    rw [Pi.single_apply]
    split_ifs with h
    · rw [h, hsx]
    · simp
  · exact mul_mem (mul_mem hx hjK) (inv_mem hx)
  · have hxx : x.val * (x⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Units.val_mul, Units.val_mul, hj, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hxx, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul]
    congr 2
    · ext i
      simp [Matrix.mulVec_single, mul_comm]
    · ext l
      have := congrFun (congrFun hxx a) l
      rw [Matrix.mul_apply] at this
      rw [Matrix.vecMul, dotProduct]
      rw [Pi.single_apply, this, Matrix.one_apply]
      simp [eq_comm]

end GlobalTheory.PsType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSlTwoPermutedModularFamilyOfLevel
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FamOfLevel

theorem redGL_mul (N : ℕ) (γ δ : SL(2, ℤ)) : redGL N (γ * δ) = redGL N γ * redGL N δ := by
  simp [redGL]

theorem redGL_eq_one_iff (N : ℕ) (γ : SL(2, ℤ)) : redGL N γ = 1 ↔ γ ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem', redGL]
  constructor
  · intro h
    apply Matrix.SpecialLinearGroup.toGL_injective
    simpa using h
  · intro h
    rw [h]; simp

theorem slash_eq_of_redGL_eq (N : ℕ) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[k] γ = f) {γ δ : SL(2, ℤ)}
    (h : redGL N γ = redGL N δ) : f ∣[k] γ = f ∣[k] δ := by
  have hη : γ * δ⁻¹ ∈ CongruenceSubgroup.Gamma N := by
    rw [← redGL_eq_one_iff, redGL_mul, h, ← redGL_mul, mul_inv_cancel]
    simp [redGL]
  have : γ = (γ * δ⁻¹) * δ := by group
  rw [this, SlashAction.slash_mul, hf _ hη]

theorem exists_family (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[k] γ = f) :
    ∃ F : GL (Fin 2) (ZMod N) → ℍ → ℂ, IsFam (gact N 1) k F ∧
      (∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ) ∧
      ∀ α, (∃ γ : SL(2, ℤ), α = redGL N γ) ∨ F α = 0 := by
  classical
  let F : GL (Fin 2) (ZMod N) → ℍ → ℂ := fun α =>
    if h : ∃ γ : SL(2, ℤ), α = redGL N γ then f ∣[k] h.choose else 0
  have hF : ∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ := by
    intro γ
    have h : ∃ δ : SL(2, ℤ), redGL N γ = redGL N δ := ⟨γ, rfl⟩
    simp only [F, dif_pos h]
    exact slash_eq_of_redGL_eq N k f hf h.choose_spec.symm
  refine ⟨F, ?_, hF, ?_⟩
  · intro α γ
    rw [gact_one]
    by_cases h : ∃ δ : SL(2, ℤ), α = redGL N δ
    · obtain ⟨δ, rfl⟩ := h
      rw [hF, ← redGL_mul, hF, SlashAction.slash_mul]
    · have h' : ¬ ∃ δ : SL(2, ℤ), α * redGL N γ = redGL N δ := by
        rintro ⟨δ, hδ⟩
        apply h
        refine ⟨δ * γ⁻¹, ?_⟩
        rw [redGL_mul, ← hδ, mul_assoc, ← redGL_mul, mul_inv_cancel]
        simp [redGL]
      simp only [F, dif_neg h, dif_neg h']
      exact SlashAction.zero_slash _ _
  · intro α
    by_cases h : ∃ γ : SL(2, ℤ), α = redGL N γ
    · exact Or.inl h
    · right; simp only [F, dif_neg h]

end GlobalTheory.FamOfLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitEvalEqKummerClass
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem exists_un_eval_eq_cls : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l n : ℕ) [Fact l.Prime], ∀ a ∈ X.A l, ∃ f ∈ X.Un (l ^ n), AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f := by
  intro Ω _ _ _ ε X hj l n _ a ha
  obtain ⟨-, -, hmul, hone, hsmul, -, -⟩ := GlobalTheory.KZ.H3.cls_props Ω ε X l n
  obtain ⟨u1, umul, -, -, -, upow, -⟩ := GlobalTheory.KZ.UnClosure.un_closure ε X ε.injective hj (l ^ n)
  unfold Tower.A at ha
  induction ha using Submodule.span_induction with
  | mem x hx => exact hx n
  | zero => exact ⟨1, u1, by rw [map_zero, hone]⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, ef⟩ := hx
    obtain ⟨g, hg, eg⟩ := hy
    exact ⟨f * g, umul f g hf hg, by rw [map_add (f := _), ef, eg, hmul]⟩
  | smul c x _ hx =>
    obtain ⟨f, hf, ef⟩ := hx
    exact ⟨_, upow _ f hf, by rw [map_smul, ef, hsmul]⟩

end GlobalTheory.KZ.ES
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationSubringPullbackIntegralElements
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.K5

theorem exists_valuationSubring_isInt_comap :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (Ωl : Type)
      [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl,
      ∃ B : ValuationSubring Ω, ((p : ℕ) : Ω) ∈ B.nonunits ∧ ∀ x, x ∈ B ↔ IsInt (p := p) (j x) := by
  intro Ω _ _ _ p _ Ωl _ _ hC j
  have hvaluation : ∃ v : Valuation Ωl NNReal,
      (∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) ∧ v (p : Ωl) < 1 := by
    obtain ⟨_, hdvr, hirr⟩ := _root_.GlobalTheory.K5.completed_laurent_isDVR p
    have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
      hirr.maximalIdeal_eq
    have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
      rw [hmax]
      exact _root_.GlobalTheory.K5.o0_isAdicComplete_span_p p
    have := hC.alg
    obtain ⟨v, hv⟩ :=
      _root_.GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr (O0 p) Ωl hC.inj
    have : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hC
    have hp0 : (p : Ωl) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hle : v (p : Ωl) ≤ 1 := (hv _).2 (by
      simpa [IsInt] using GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ωl) (p : ℤ))
    refine ⟨v, hv, lt_of_le_of_ne hle ?_⟩
    intro heq
    have hi : v (p : Ωl)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
    have hint : IsInt (p := p) ((p : Ωl)⁻¹) := (hv _).1 hi
    exact GlobalTheory.K5.Basic.not_cong_one_zero hC 1 one_ne_zero
      ⟨(p : Ωl)⁻¹, hint, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩
  obtain ⟨v, hv, hp1⟩ := hvaluation
  let w : Valuation Ω NNReal := v.comap j
  refine ⟨w.valuationSubring, ?_, fun x => ?_⟩
  · rw [ValuationSubring.mem_nonunits_iff, ← map_one w.valuationSubring.valuation,
      ← w.isEquiv_valuation_valuationSubring.lt_iff_lt, map_one]
    show v (j ((p : ℕ) : Ω)) < 1
    rw [map_natCast]
    exact hp1
  · rw [Valuation.mem_valuationSubring_iff]
    exact hv (j x)

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpTwoPiIRatInFieldRootsOfUnityProperties
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNRoots

theorem alg_mem_range (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (z : ℂ) (hz : IsAlgebraic ℚ z) : z ∈ ε.range := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hi : IsIntegral ℚ z := hz.isIntegral
  set p := minpoly ℚ z with hp
  have hm : p.Monic := minpoly.monic hi
  have hqm : (p.map (algebraMap ℚ Ω)).Monic := hm.map _
  have hroots := hqm.roots_map_of_card_eq_natDegree ε IsAlgClosed.card_roots_eq_natDegree
  have hcomp : ε.comp (algebraMap ℚ Ω) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  rw [Polynomial.map_map, hcomp] at hroots
  have hne : p.map (algebraMap ℚ ℂ) ≠ 0 := (hm.map _).ne_zero
  have hzr : z ∈ (p.map (algebraMap ℚ ℂ)).roots := by
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
    exact minpoly.aeval ℚ z
  rw [← hroots] at hzr
  obtain ⟨w, -, hw⟩ := Multiset.mem_map.1 hzr
  exact ⟨w, hw⟩

theorem exp_isAlgebraic (x : ℚ) : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) := by
  have hpow : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I) := by
      have hx : (x : ℂ) = (x.num : ℂ) / (x.den : ℂ) := by
        exact_mod_cast (Rat.num_div_den x).symm
      have hd : (x.den : ℂ) ≠ 0 := by exact_mod_cast x.den_nz
      rw [hx]; field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  refine ⟨Polynomial.X ^ x.den - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero x.pos 1, ?_⟩
  simp [hpow]

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ ε.range) ∧ (∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ∧ eOm ε 0 = 1 ∧ (∀ x y : ℚ, eOm ε (x + y) = eOm ε x * eOm ε y) ∧ (∀ N : ℕ, 0 < N → IsPrimitiveRoot (eOm ε (1 / N)) N) ∧ ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ ε.range := by
  intro Ω _ _ _ ε
  have hr : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ ε.range :=
    fun x => alg_mem_range Ω ε _ (exp_isAlgebraic x)
  have he : ∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
    intro x
    obtain ⟨w, hw⟩ := hr x
    exact Function.invFun_eq ⟨w, hw⟩
  have hinj : Function.Injective ε := ε.injective
  refine ⟨hr, he, ?_, ?_, ?_, fun z hz => alg_mem_range Ω ε z hz⟩
  · apply hinj; rw [he, map_one]; simp
  · intro x y; apply hinj
    rw [map_mul, he, he, he, ← Complex.exp_add]; congr 1; push_cast; ring
  · intro N hN
    apply IsPrimitiveRoot.of_map_of_injective (f := ε) _ hinj
    rw [he]
    have h := Complex.isPrimitiveRoot_exp N hN.ne'
    convert h using 2
    push_cast; ring

end GlobalTheory.FNRoots
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHasSumReindexNat
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_hasSum_reindex_nat : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (h : HahnSeries ℚ Ω) (N : ℕ) (n₀ : ℤ) (a : ℕ → Ω) (z v : ℂ), 0 < N → (∀ k : ℕ, h.coeff (((n₀ + k : ℤ) : ℚ) / N) = a k) → (∀ r : ℚ, (∀ k : ℕ, r ≠ ((n₀ + k : ℤ) : ℚ) / N) → h.coeff r = 0) → (HasSum (fun r : ℚ => ε (h.coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) v ↔ HasSum (fun k : ℕ => ε (a k) * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) (v * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N)))) := by
  intro Ω _ ε h N n₀ a z v hN ha h0
  set g : ℕ → ℚ := fun k => (((n₀ + k : ℤ) : ℚ) / N) with hg
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hinj : Function.Injective g := by
    intro k l hkl
    simp only [hg] at hkl
    have := (div_left_inj' hNq).mp hkl
    have h2 : ((n₀ + k : ℤ)) = n₀ + l := by exact_mod_cast this
    omega
  set f : ℚ → ℂ := fun r => ε (h.coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z) with hf
  have hzero : ∀ r, r ∉ Set.range g → f r = 0 := by
    intro r hr
    have : ∀ k : ℕ, r ≠ ((n₀ + k : ℤ) : ℚ) / N := by
      intro k hk; exact hr ⟨k, hk.symm⟩
    simp [hf, h0 r this]
  set c : ℂ := Complex.exp (2 * Real.pi * Complex.I * n₀ * z / N) with hc
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have hcomp : f ∘ g = fun k : ℕ => (ε (a k) * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) * c := by
    funext k
    simp only [Function.comp, hf, hg, ha k, hc]
    rw [← Complex.exp_nat_mul, mul_assoc (ε (a k)), ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [← hinj.hasSum_iff hzero, hcomp]
  have hv : v = (v * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N))) * c := by
    rw [hc, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  conv_lhs => rw [hv]
  exact hasSum_mul_right_iff hc0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1CapGamma0LevelActsFreelyUpperHalfPlane
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.FreeAct

theorem ent_ofSL (γ : SL(2, ℤ)) (i j : Fin 2) :
    ent (ofSL γ) i j = ((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := by
  simp [ent, ofSL]

theorem key (a b c d x y : ℝ) (h1 : a - d = 2 * c * x) (h2 : c * (x ^ 2 - y ^ 2) + (d - a) * x - b = 0)
    (hdet : a * d - b * c = 1) : 4 * c ^ 2 * y ^ 2 = 4 - (a + d) ^ 2 := by
  linear_combination (-4 * c) * h2 + 4 * hdet + (a - d - 2 * c * x) * h1

theorem no_small (N : ℕ) (hN : 4 ≤ N) (t k : ℤ) (hk : t - 2 = (N : ℤ) * k) (ht : t ^ 2 < 4) : False := by
  have h1 : -1 ≤ t := by nlinarith
  have h2 : t ≤ 1 := by nlinarith
  have hN' : (4 : ℤ) ≤ N := by exact_mod_cast hN
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · nlinarith
  · subst hk0; omega
  · nlinarith

end GlobalTheory.KZ.FreeAct

namespace GlobalTheory.KZ


open FreeAct in
theorem gam_free : ∀ (N l : ℕ), 4 ≤ N → ∀ γ ∈ Gam N l, ∀ z ∈ Hs, mob (ofSL γ) z = z → γ = 1 := by
  intro N l hN γ hγ z hz hfix
  have hγ1 : γ ∈ CongruenceSubgroup.Gamma1 N := hγ.1
  rw [CongruenceSubgroup.Gamma1_mem] at hγ1
  obtain ⟨ha1, hd1, -⟩ := hγ1
  set A := (γ : Matrix (Fin 2) (Fin 2) ℤ) with hA
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hden := GlobalTheory.KZ.MobLaws.den_ne (ofSL γ) hz
  simp only [ent_ofSL] at hden
  unfold mob at hfix
  simp only [ent_ofSL] at hfix
  rw [div_eq_iff hden] at hfix
  have hy : 0 < z.im := hz
  have hre := congrArg Complex.re hfix
  have him := congrArg Complex.im hfix
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, Complex.ratCast_re, Complex.ratCast_im] at hre him
  push_cast at hre him
  simp at hre him
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (A 0 0) N).1 (by simpa using ha1.symm)
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (A 1 1) N).1 (by simpa using hd1.symm)
  have hN' : (4 : ℤ) ≤ N := by exact_mod_cast hN
  simp only [← hA] at hre him
  generalize e00 : A 0 0 = a at *
  generalize e01 : A 0 1 = b at *
  generalize e10 : A 1 0 = c at *
  generalize e11 : A 1 1 = d at *
  have h1 : (a : ℝ) - d = 2 * c * z.re := by
    have : ((a : ℝ) - d - 2 * c * z.re) * z.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have h2 : (c : ℝ) * (z.re ^ 2 - z.im ^ 2) + (d - a) * z.re - b = 0 := by linarith
  have hdetR : (a : ℝ) * d - b * c = 1 := by exact_mod_cast hdet
  have hk4 := key a b c d z.re z.im h1 h2 hdetR
  by_cases hc : c = 0
  · subst hc
    have had : a = d := by
      have : (a : ℝ) = d := by simp at h1; linarith
      exact_mod_cast this
    subst had
    have hb : b = 0 := by
      have : (b : ℝ) = 0 := by simpa using h2
      exact_mod_cast this
    subst hb
    have haa : a * a = 1 := by simpa using hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' haa with ⟨ha, -⟩ | ⟨ha, -⟩
    · subst ha
      ext i j
      fin_cases i <;> fin_cases j <;> simp [← hA, e00, e01, e10, e11]
    · exfalso
      subst ha
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · nlinarith
      · subst hk0; omega
      · nlinarith
  · exfalso
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    have hpos : 0 < 4 * (c : ℝ) ^ 2 * z.im ^ 2 := by positivity
    have ht : (a + d) ^ 2 < 4 := by
      have : ((a : ℝ) + d) ^ 2 < 4 := by linarith
      exact_mod_cast this
    exact no_small N hN (a + d) (k + m) (by linear_combination hk + hm) ht

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixActionMemHomogeneousPolyFunctionsStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ), (∀ a ∈ X.A l, X.kmap l (X.sl (toGQ m)).toRingEquiv a ∈ X.A l) → ∀ b ∈ X.Pol l w, X.act l m b ∈ X.Pol l w := by
  first | exact @GlobalTheory.KZ.PolAct.act_mem_pol | exact GlobalTheory.KZ.PolAct.act_mem_pol | (intros; apply GlobalTheory.KZ.PolAct.act_mem_pol <;> assumption)
end

