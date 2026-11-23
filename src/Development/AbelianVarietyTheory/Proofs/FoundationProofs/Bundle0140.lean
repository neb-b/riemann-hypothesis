module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0138
public import Formalism.FormalDegreeBessel.StatementRP
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0123
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelAddZeroCongr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSpanPrincipalCongruenceLevelFunction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EllipticPointsStabilizer
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.EllipticZero

lemma denom_mul_SL (g h : SL(2, ℤ)) (z : ℍ) :
    denom ((g * h : SL(2, ℤ)) : GL (Fin 2) ℝ) z
      = denom (g : GL (Fin 2) ℝ) ((h • z : ℍ) : ℂ) * denom (h : GL (Fin 2) ℝ) z := by
  have hd : 0 < ((h : GL (Fin 2) ℝ)).det.val := by simp
  have := denom_cocycle (g : GL (Fin 2) ℝ) (h : GL (Fin 2) ℝ) z.im_ne_zero
  rw [← coe_smul_of_det_pos hd, ← ModularGroup.sl_moeb] at this
  rw [← this, map_mul, map_mul]

lemma conj_fix (γ u : SL(2, ℤ)) (σ : ℍ) (hu : u • σ = σ) :
    (γ * u * γ⁻¹) • (γ • σ) = γ • σ ∧
      denom ((γ * u * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) ((γ • σ : ℍ) : ℂ)
        = denom (u : GL (Fin 2) ℝ) σ := by
  refine ⟨by rw [mul_smul, mul_smul, inv_smul_smul, hu], ?_⟩
  have h1 := denom_mul_SL (γ * u * γ⁻¹) γ σ
  have h2 := denom_mul_SL γ u σ
  rw [inv_mul_cancel_right, h2, hu, mul_comm] at h1
  exact (mul_right_cancel₀ (denom_ne_zero _ _) h1).symm

lemma eq_zero_of_fix {k : ℤ} (f : ModularForm 𝒮ℒ k) (u : SL(2, ℤ)) (σ : ℍ) (hu : u • σ = σ)
    (hk : denom (u : GL (Fin 2) ℝ) σ ^ k ≠ 1) : f σ = 0 := by
  have h : f (u • σ) = denom u σ ^ k * f σ :=
    SlashInvariantForm.slash_action_eqn'' f (by simp) σ
  rw [hu] at h
  have : (denom (u : GL (Fin 2) ℝ) σ ^ k - 1) * f σ = 0 := by linear_combination -h
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hk)

lemma exists_four : ∃ (σ : ℍ) (u : SL(2, ℤ)), u • σ = σ ∧
    IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) σ) 4 := by
  refine ⟨UpperHalfPlane.I, ModularGroup.S, ?_, ?_⟩
  · rw [modular_S_smul]; ext1; simp
  · rw [ModularGroup.denom_S]; exact Complex.isPrimitiveRoot_I

lemma exists_six : ∃ (σ : ℍ) (u : SL(2, ℤ)), u • σ = σ ∧
    IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) σ) 6 := by
  have hp := Complex.isPrimitiveRoot_exp 6 (by norm_num)
  set μ := Complex.exp (2 * Real.pi * Complex.I / (6 : ℕ)) with hμ
  have him : 0 < μ.im := by
    have : μ = Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
      rw [hμ]; congr 1; push_cast; ring
    rw [this, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]
    positivity
  have h6 : μ ^ 6 = 1 := hp.pow_eq_one
  have h3 : μ ^ 3 - 1 ≠ 0 := sub_ne_zero.2 (hp.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
  have h1 : μ + 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    exact him.ne' this
  have hq : μ ^ 2 - μ + 1 = 0 := by
    have : (μ ^ 3 - 1) * ((μ + 1) * (μ ^ 2 - μ + 1)) = 0 := by linear_combination h6
    exact (mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h3)).resolve_left h1
  have h0 : μ ≠ 0 := hp.ne_zero (by norm_num)
  refine ⟨⟨μ, him⟩, ModularGroup.T * ModularGroup.S, ?_, ?_⟩
  · rw [mul_smul, modular_S_smul, modular_T_smul]
    ext1
    simp only [coe_vadd]
    push_cast
    field_simp
    linear_combination -hq
  · rw [denom_mul_SL, ModularGroup.denom_S]
    have : ∀ z : ℍ, denom ((ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) z = 1 := fun z => by
      rw [ModularGroup.denom_apply]; simp [ModularGroup.T]
    rw [this, one_mul]
    exact hp

theorem elliptic_of_zero : ∀ τ₀ : ℍ,
    (E₆ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 4) ∧
    (E₄ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧
      IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 6) := by
  intro τ₀
  constructor
  · intro h
    obtain ⟨σ, u, hu, hp⟩ := exists_four
    have h0 : E₆ σ = 0 := eq_zero_of_fix E₆ u σ hu (by
      rw [Ne, hp.zpow_eq_one_iff_dvd]; norm_num)
    obtain ⟨γ, rfl⟩ := _root_.GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ τ₀ σ (by rw [h, h0]; ring)
    obtain ⟨h1, h2⟩ := conj_fix γ u σ hu
    exact ⟨_, h1, h2 ▸ hp⟩
  · intro h
    obtain ⟨σ, u, hu, hp⟩ := exists_six
    have h0 : E₄ σ = 0 := eq_zero_of_fix E₄ u σ hu (by
      rw [Ne, hp.zpow_eq_one_iff_dvd]; norm_num)
    obtain ⟨γ, rfl⟩ := _root_.GlobalTheory.JOrbit.exists_smul_of_E₄_E₆ τ₀ σ (by rw [h, h0]; ring)
    obtain ⟨h1, h2⟩ := conj_fix γ u σ hu
    exact ⟨_, h1, h2 ▸ hp⟩

end GlobalTheory.EllipticZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EquivariantSubspace
section
open Formalism.QuantumDeterminants

namespace GlobalTheory.EquivariantSubspace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smoothOnH_zero (H : Matrix (Fin n) (Fin n) ℂ) :
    SmoothOnH H (0 : Matrix (Fin n) (Fin n) ℂ → E) :=
  fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem smoothOnH_add {H : Matrix (Fin n) (Fin n) ℂ} {f f' : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : SmoothOnH H f) (hf' : SmoothOnH H f') : SmoothOnH H (f + f') := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), ?_⟩
  intro g hg hH
  rw [Pi.add_apply, hfF g hg.1 hH, hfF' g hg.2 hH]

theorem smoothOnH_smul {H : Matrix (Fin n) (Fin n) ℂ} {f : Matrix (Fin n) (Fin n) ℂ → E} (a : ℂ)
    (hf : SmoothOnH H f) : SmoothOnH H (a • f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun g => a • F g, hU, hgU, hF.const_smul a, ?_⟩
  intro g hg hH
  rw [Pi.smul_apply, hfF g hg hH]

end GlobalTheory.EquivariantSubspace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostDualTraceDataTowerUnionAdjoin
section
noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt.TrTower

section Sep

variable {L : Type*} [Field L] {G : Type*} [Group G] [MulSemiringAction G L]

theorem isSep_mul_right {v : Valuation L ℝ≥0} {N : Subgroup G} {n : ℕ} {a b : Fin n → L} {c : L}
    (h : IsSep v N a b c) {d : L} (hd : d ∈ Fix L N) (hdv : v d ≤ 1) (hcd : v (c * d) ≤ 1) :
    IsSep v N (fun i => a i * d) b (c * d) := by
  refine
    { a_mem := fun i => mul_mem (h.a_mem i) hd
      b_mem := h.b_mem
      c_mem := mul_mem h.c_mem hd
      a_le := ?_
      b_le := h.b_le
      c_le := hcd
      sum_in := ?_
      sum_out := ?_ }
  · intro i
    rw [map_mul]
    exact mul_le_one' (h.a_le i) hdv
  · intro σ hσ
    simp_rw [mul_right_comm _ d]; rw [← Finset.sum_mul, h.sum_in σ hσ]
  · intro σ hσ
    simp_rw [mul_right_comm _ d]; rw [← Finset.sum_mul, h.sum_out σ hσ, zero_mul]

theorem isSep_swap {v : Valuation L ℝ≥0} {N : Subgroup G} {n : ℕ} {a b : Fin n → L} {c : L}
    (h : IsSep v N a b c) : IsSep v N b a c := by
  refine
    { a_mem := h.b_mem
      b_mem := h.a_mem
      c_mem := h.c_mem
      a_le := h.b_le
      b_le := h.a_le
      c_le := h.c_le
      sum_in := ?_
      sum_out := ?_ }
  · intro σ hσ
    have h1 := congrArg (σ • ·) (h.sum_in σ⁻¹ (inv_mem hσ))
    have hc : σ • c = c := h.c_mem ⟨σ, hσ⟩
    simp only [Finset.smul_sum, smul_mul', smul_inv_smul, hc] at h1
    simpa [mul_comm] using h1
  · intro σ hσ
    have h1 := congrArg (σ • ·) (h.sum_out σ⁻¹ (fun h' => hσ (by simpa using inv_mem h')))
    simp only [Finset.smul_sum, smul_mul', smul_inv_smul, smul_zero] at h1
    simpa [mul_comm] using h1

end Sep

section Tower

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def fixInt {H : Subgroup (Gal p Ω)} (V : Subgroup H) :
    Subalgebra (O0 p) (integralClosure (O0 p) Ω) where
  carrier := {s | ∀ g : V, g • (s : Ω) = s}
  mul_mem' {x y} hx hy g := by
    simp only [Set.mem_setOf_eq, Subalgebra.coe_mul] at *
    rw [smul_mul', hx g, hy g]
  add_mem' {x y} hx hy g := by
    simp only [Set.mem_setOf_eq, Subalgebra.coe_add] at *
    rw [smul_add, hx g, hy g]
  algebraMap_mem' r g := by
    show g • (algebraMap (O0 p) Ω r) = _
    exact ((g : H) : Gal p Ω).commutes r

theorem towerAlg_fixed (T : Tower p Ω) {s : integralClosure (O0 p) Ω} (hs : s ∈ towerAlg T)
    (g : ↥(⨅ n, Gn T n)) : g • (s : Ω) = s := by
  have hle : towerAlg T ≤ fixInt (⊤ : Subgroup ↥(⨅ n, Gn T n)) := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨m, rfl⟩ | ⟨m, rfl⟩) g
    · exact ((GlobalTheory.K5.Basic.mem_gn T m _).1 (Subgroup.mem_iInf.1 (g : ↥(⨅ n, Gn T n)).2 m)).1
    · exact ((GlobalTheory.K5.Basic.mem_gn T m _).1 (Subgroup.mem_iInf.1 (g : ↥(⨅ n, Gn T n)).2 m)).2
  exact hle hs ⟨g, trivial⟩

end Tower

end GlobalTheory.AlmostEt.TrTower

namespace GlobalTheory.AlmostEt.TrTower

theorem exists_trData_towerAlg : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (F : Finset (integralClosure (O0 p) Ω)),
    ∃ (C : Subalgebra (O0 p) (integralClosure (O0 p) Ω))
      (tr : (integralClosure (O0 p) Ω) → (integralClosure (O0 p) Ω)) (n : ℕ)
      (a b : Fin n → (integralClosure (O0 p) Ω)),
      (↑F : Set (integralClosure (O0 p) Ω)) ⊆ C ∧
        IsTrData (towerAlg T) C tr a b (p : (integralClosure (O0 p) Ω)) := by
  intro p _ Ω _ _ hp2 hclo T F
  classical
  have hpcoe : ((p : integralClosure (O0 p) Ω) : Ω) = p := map_natCast (integralClosure (O0 p) Ω).val p
  obtain ⟨v, hvint, hvinv, hp0, hp1, hS⟩ := GlobalTheory.T.exists_valuation_almostEtale_towerFixer p Ω hp2 hclo T
  obtain ⟨U, -, hUfin, hUfix, hUsep⟩ := hS (F.image Subtype.val)
  obtain ⟨n, a, b, c, hsep, hc⟩ := hUsep (v p) hp1
  haveI := hUfin
  haveI : Fintype (↥(⨅ n, Gn T n) ⧸ U) := Fintype.ofFinite _
  have hvinv' : ∀ (g : ↥(⨅ n, Gn T n)) (x : Ω), v (g • x) = v x := fun g x => hvinv g x
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [map_zero] at hc; exact (not_lt_zero' hc)
  have hvc : 0 < v c := lt_of_le_of_lt (by positivity) hc

  have hpfix : ∀ (g : ↥(⨅ n, Gn T n)), g • (p : Ω) = p := fun g => by
    change ((g : Gal p Ω)) (p : Ω) = p
    exact map_natCast _ p
  have hd : (p : Ω) / c ∈ Fix Ω U := div_mem (fun g => hpfix g) hsep.c_mem
  have hdv : v ((p : Ω) / c) ≤ 1 := by
    rw [map_div₀]; exact div_le_one_of_le₀ hc.le (by positivity)
  have hsep' : IsSep v U (fun i => a i * ((p : Ω) / c)) b (p : Ω) := by
    have := isSep_mul_right hsep hd hdv (by rw [mul_div_cancel₀ _ hc0]; exact hp1.le)
    rwa [mul_div_cancel₀ _ hc0] at this
  have hsw := isSep_swap hsep'
  have hint : ∀ x : Ω, v x ≤ 1 → x ∈ integralClosure (O0 p) Ω := fun x hx => (hvint x).1 hx
  let a' : Fin n → integralClosure (O0 p) Ω := fun i => ⟨_, hint _ (hsep'.a_le i)⟩
  let b' : Fin n → integralClosure (O0 p) Ω := fun i => ⟨_, hint _ (hsep'.b_le i)⟩
  have htrint : ∀ s : integralClosure (O0 p) Ω, cosetTrace U (s : Ω) ∈ integralClosure (O0 p) Ω :=
    fun s => Subalgebra.sum_mem _ fun q _ => GlobalTheory.K5.Basic.isInt_gal _ s.2
  let tr : integralClosure (O0 p) Ω → integralClosure (O0 p) Ω := fun s => ⟨_, htrint s⟩
  have htr : ∀ s, (tr s : Ω) = cosetTrace U (s : Ω) := fun s => rfl
  have hle : towerAlg T ≤ fixInt U := fun s hs g => towerAlg_fixed T hs (g : ↥(⨅ n, Gn T n))
  refine ⟨fixInt U, tr, n, a', b', ?_, ?_⟩
  · intro s hs
    exact hUfix _ (Finset.mem_image_of_mem _ hs)
  refine
    { le := hle
      e_mem := Subalgebra.natCast_mem _ p
      a_mem := fun i => hsep'.a_mem i
      b_mem := fun i => hsep'.b_mem i
      tr_mem := ?_
      tr_add := ?_
      tr_mul := ?_
      left := ?_
      right := ?_
      sum := ?_ }
  · intro x hx
    apply _root_.GlobalTheory.K5.mem_towerAlg_of_fixed p Ω hclo T
    intro g hg
    exact (cosetTrace_fixed_props Ω v _ hvinv' U _ hx).1 ⟨g, hg⟩
  · intro x _ y _
    apply Subtype.ext
    simp only [htr, Subalgebra.coe_add, cosetTrace, smul_add, Finset.sum_add_distrib]
  · intro β hβ x hx
    apply Subtype.ext
    simp only [htr, Subalgebra.coe_mul]
    exact (cosetTrace_fixed_props Ω v _ hvinv' U _ hx).2.2 _ (towerAlg_fixed T hβ)
  · intro x hx
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, hpcoe, AddSubmonoidClass.coe_finsetSum, htr]
    exact GlobalTheory.T.sum_mul_cosetRepresentativeTrace_eq Ω v _ U n _ _ _ hsep' _ hx
  · intro x hx
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, hpcoe, AddSubmonoidClass.coe_finsetSum, htr]
    exact GlobalTheory.T.sum_mul_cosetRepresentativeTrace_eq Ω v _ U n _ _ _ hsw _ hx
  · apply Subtype.ext
    simp only [Subalgebra.coe_mul, hpcoe, AddSubmonoidClass.coe_finsetSum]
    simpa using hsep'.sum_in 1 (one_mem _)

end GlobalTheory.AlmostEt.TrTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBettiCocycleKummerRelation
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiEx

theorem kum_sum {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    {ι : Type} (s : Finset ι) (r : ι → ℤ_[l]) (x : ι → X.Khat l) (χ : ι → SL(2, ℤ) → ZMod (l ^ n))
    (h : ∀ i, H3.Kum X l n (x i) (χ i)) :
    H3.Kum X l n (∑ i ∈ s, r i • x i) (fun δ => ∑ i ∈ s, PadicInt.toZModPow n (r i) * χ i δ) := by
  classical
  obtain ⟨hadd, hzero, -⟩ := _root_.GlobalTheory.KZ.H3.KumAdd.kum_add_zero_near Ω ε X l n
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact hzero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact hadd _ _ _ _ (GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n (r a) (x a) (χ a) (h a)) ih

theorem exists_betti_cocycle {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (_hε : Function.Injective ε) (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero))
    (N l w : ℕ) [Fact l.Prime] (hl : l ≠ 2) (hN : 5 ≤ N) (hc : Nat.Coprime N l) (hw : Odd w) :
    ∀ b ∈ X.BSet N l w, ∃ c ∈ Z1 N l w, BtZ X N l b c := by
  rintro b ⟨⟨c, hcA, hb⟩, hinv⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hJ : H3.JHol X := by
    obtain ⟨φ, h1, h2⟩ := hj
    exact ⟨φ, h2, h1⟩
  have hlN : ¬ l ∣ N := (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).1 hc.symm
  obtain ⟨Φ, hΦ, hK⟩ := _root_.GlobalTheory.KZ.H3.kum_family Ω ε X l hJ N w c hcA
    (fun γ hγ => _root_.GlobalTheory.KZ.H3.coef_of_inv Ω ε X l N w b c hb γ hγ (hinv γ hγ))
  obtain ⟨z, hz, hnear⟩ := _root_.GlobalTheory.KZ.H3.cocycle_lift_of_fam N l w (by omega) hl hlN hw Φ hΦ
  refine ⟨fun δ => z δ, ⟨fun γ => hz.1 γ γ.2, fun γ δ => hz.2 γ γ.2 δ δ.2⟩, fun n u => ?_⟩
  obtain ⟨M, hM, hMn⟩ := hnear n
  have hk := kum_sum X l n Finset.univ (fun i : Fin (w + 1) => u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) c _ (hK n)
  rw [← hb u] at hk
  refine ⟨_, hk, M, hM, fun δ hδ => ?_⟩
  obtain ⟨-, hexp, -, hev, -⟩ := GlobalTheory.KZ.H3.mon_expand (ZMod (l ^ n)) w
  have e := hMn δ hδ
  simp only at e ⊢
  rw [e]
  conv_lhs => rw [hexp (Φ n δ) (hΦ.1 n δ)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, MvPolynomial.eval_C, hev]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.KZ.BettiEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSpanPrincipalCongruenceLevelFunctionStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_span_principalCongruenceLevel_functions : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ M : ℕ, 0 < M → ∃ T : Finset X.K, (∀ x ∈ T, Lev X M x) ∧ ∀ f : X.K, Lev X M f → f ∈ Submodule.span (IntermediateField.adjoin Ω {X.jK}) (T : Set X.K) := by
  first | exact @GlobalTheory.KZ.ES.LevFin.exists_finset_span | exact GlobalTheory.KZ.ES.LevFin.exists_finset_span | (intros; apply GlobalTheory.KZ.ES.LevFin.exists_finset_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInjectiveCuspExpansionRingHom
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

variable {Ω : Type} [Field Ω] (ε : Ω →+* ℂ)

theorem exists_isExp_of_mem_ring (a : ring ε.range) : ∃ h : HahnSeries ℚ Ω, IsExp ε a h :=
  _root_.GlobalTheory.FN.exists_isExp Ω ε a (((_root_.GlobalTheory.FN.mem_ring_iff_inR ε.range).1 a).1 a.2)

def expan (a : ring ε.range) : HahnSeries ℚ Ω := Classical.choose (exists_isExp_of_mem_ring ε a)

theorem isExp_expan (a : ring ε.range) : IsExp ε a (expan ε a) :=
  Classical.choose_spec (exists_isExp_of_mem_ring ε a)

theorem expan_eq_of_isExp {a : ring ε.range} {h : HahnSeries ℚ Ω} (ha : IsExp ε a h) : expan ε a = h :=
  (_root_.GlobalTheory.FNExp.exp_props Ω ε).2.1 _ _ _ (isExp_expan ε a) ha

def expanHom : ring ε.range →+* HahnSeries ℚ Ω where
  toFun := expan ε
  map_one' := by
    apply expan_eq_of_isExp
    have h := (_root_.GlobalTheory.FNExp.exp_props Ω ε).2.2.1 1
    have e1 : ((1 : ring ε.range) : ℍ → ℂ) = fun _ => ε 1 := by ext; simp
    rw [e1]; simpa using h
  map_mul' a b := by
    apply expan_eq_of_isExp
    have h := ((_root_.GlobalTheory.FNExp.exp_props Ω ε).1 _ _ _ _ (isExp_expan ε a) (isExp_expan ε b)).2.2
    simpa using h
  map_zero' := by
    apply expan_eq_of_isExp
    have h := (_root_.GlobalTheory.FNExp.exp_props Ω ε).2.2.1 0
    have e0 : ((0 : ring ε.range) : ℍ → ℂ) = fun _ => ε 0 := by ext; simp
    rw [e0]; simpa using h
  map_add' a b := by
    apply expan_eq_of_isExp
    have h := ((_root_.GlobalTheory.FNExp.exp_props Ω ε).1 _ _ _ _ (isExp_expan ε a) (isExp_expan ε b)).1
    simpa using h

theorem expanHom_injective : Function.Injective (expanHom ε) := by
  intro a b hab
  have hsub := ((_root_.GlobalTheory.FNExp.exp_props Ω ε).1 _ _ _ _ (isExp_expan ε a) (isExp_expan ε b)).2.1
  have h0 : expan ε a - expan ε b = 0 := sub_eq_zero.mpr hab
  rw [h0] at hsub
  have hmem : ((a - b : ring ε.range) : ℍ → ℂ) ∈ ring ε.range := (a - b).2
  have hin : InR ε.range ((a - b : ring ε.range) : ℍ → ℂ) := ((_root_.GlobalTheory.FN.mem_ring_iff_inR ε.range).1 _).1 hmem
  have hhol := _root_.GlobalTheory.FN.inR_mdifferentiable ε.range _ hin
  push_cast at hhol
  have := (_root_.GlobalTheory.FNExp.exp_props Ω ε).2.2.2.1 _ hhol hsub
  exact Subtype.ext (sub_eq_zero.mp this)

theorem expansion_injective_ringHom :
    ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ e : GlobalTheory.FN.ring ε.range →+* HahnSeries ℚ Ω,
      Function.Injective e ∧ ∀ a : GlobalTheory.FN.ring ε.range, IsExp ε a (e a) :=
  fun _ _ ε => ⟨expanHom ε, expanHom_injective ε, isExp_expan ε⟩

end GlobalTheory.FN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOfExpansionSumEqPrimePowMulIsEvalStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_expansionSum_eq_primePow_mul_isEval : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p), (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp p (e t)) → ∀ (v : ℕ) (o : Ω), IsInt (p := p) o → ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) = (p : Ω) ^ v * o → ∃ (c : ℤ → Ω) (x' : Ω), Ev ψ c o x' := by
  first | exact @GlobalTheory.GeoFix.Divide.divide_ev | exact GlobalTheory.GeoFix.Divide.divide_ev | (intros; apply GlobalTheory.GeoFix.Divide.divide_ev <;> assumption)
end

