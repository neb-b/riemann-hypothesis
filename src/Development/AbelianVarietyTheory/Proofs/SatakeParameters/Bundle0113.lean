module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalRingCardinality.DataKerI
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DepthZeroJacquetInjectiveOfAdmissible
section
namespace GlobalTheory

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

theorem depthZeroJacquetInjective_of_admissible :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.MoyPrasadJacquetIso →
      GlobalTheory.Published.DepthZeroJacquetInjective := by
  intro hBZ hMP k _ _ _ _ n s d e π v hv h0
  have hadm := (hBZ k).1 (Fin n) π.V π.π π.smooth π.irr
  have hb := hMP k n s d e π.V π.π hadm
  have h00 : (0 : π.V) ∈ fixed π.π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))) := by
    first
      | exact Submodule.zero_mem _
      | exact fun _ => map_zero _
      | simp [fixed]
  exact hb.injOn hv h00 (by simpa using h0)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHyperspecialDoubleCosetOfElementaryDivisor
section
namespace GlobalTheory.SplitLabel

open Matrix

section Alg

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem smul_mulVec_congr (ε : R) (M : Matrix n n R) {x y : n → R} (h : ε • x = ε • y) :
    ε • M *ᵥ x = ε • M *ᵥ y := by
  rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, h]

omit [DecidableEq n] in
theorem smul_mulVec_mat (ε : R) {A B B' : Matrix n n R} (h : ε • (A * B) = ε • B') (x : n → R) :
    ε • A *ᵥ (B *ᵥ x) = ε • B' *ᵥ x := by
  rw [Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, h, Matrix.smul_mulVec]


omit [DecidableEq n] in
theorem stab_of_bases (ε : R) (hε : ε * ε = ε) (Λ Z : Set (n → R)) {A B B' : Matrix n n R}
    (h : ε • (A * B) = ε • B')
    (h1 : ∀ z ∈ Z, ε • B *ᵥ z ∈ Λ) (h2 : ∀ y ∈ Λ, ∃ z ∈ Z, ε • y = ε • B *ᵥ z)
    (h1' : ∀ z ∈ Z, ε • B' *ᵥ z ∈ Λ) (h2' : ∀ y ∈ Λ, ∃ z ∈ Z, ε • y = ε • B' *ᵥ z) :
    (∀ y ∈ Λ, ε • A *ᵥ y ∈ Λ) ∧ ∀ y ∈ Λ, ∃ z ∈ Λ, ε • y = ε • A *ᵥ z := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, e⟩ := h2 y hy
    rw [smul_mulVec_congr ε A e, smul_mulVec_mat ε h]
    exact h1' z hz
  · obtain ⟨z, hz, e⟩ := h2' y hy
    refine ⟨_, h1 z hz, ?_⟩
    rw [e, ← smul_mulVec_mat ε h]
    apply smul_mulVec_congr
    rw [smul_smul, hε]

theorem stab_of_div (ε : R) (Λ Z : Set (n → R)) {A B B' M M' N b : Matrix n n R}
    (t t' : n → R) (h : ε • (A * B) = ε • B') (hN : N * (A * M) = 1) (hb : b = N * M')
    (hΛ : ∀ y ∈ Λ, ε • y ∈ Λ)
    (hu : ∀ z ∈ Z, ∃ w ∈ Z, ε • (fun i => t' i * z i) = ε • fun i => t i * w i)
    (hu' : ∀ z ∈ Z, ∃ w ∈ Z, ε • (fun i => t i * z i) = ε • fun i => t' i * w i)
    (h3 : ∀ y ∈ Λ, ∃ z ∈ Z, ε • M *ᵥ y = ε • B *ᵥ fun i => t i * z i)
    (h4 : ∀ z ∈ Z, ∃ y ∈ Λ, ε • M *ᵥ y = ε • B *ᵥ fun i => t i * z i)
    (h3' : ∀ y ∈ Λ, ∃ z ∈ Z, ε • M' *ᵥ y = ε • B' *ᵥ fun i => t' i * z i)
    (h4' : ∀ z ∈ Z, ∃ y ∈ Λ, ε • M' *ᵥ y = ε • B' *ᵥ fun i => t' i * z i) :
    (∀ y ∈ Λ, ε • b *ᵥ y ∈ Λ) ∧ ∀ y ∈ Λ, ∃ z ∈ Λ, ε • y = ε • b *ᵥ z := by
  have key : ∀ y y' : n → R, ε • M' *ᵥ y' = ε • A *ᵥ (M *ᵥ y) → ε • b *ᵥ y' = ε • y := by
    intro y y' e
    rw [hb, ← Matrix.mulVec_mulVec, smul_mulVec_congr ε N e, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, hN, Matrix.one_mulVec]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, e⟩ := h3' y hy
    obtain ⟨w, hw, ew⟩ := hu z hz
    obtain ⟨y', hy', e'⟩ := h4 w hw
    rw [key y' y]
    · exact hΛ y' hy'
    · rw [e, smul_mulVec_congr ε B' ew, smul_mulVec_congr ε A e', smul_mulVec_mat ε h]
  · obtain ⟨z, hz, e⟩ := h3 y hy
    obtain ⟨w, hw, ew⟩ := hu' z hz
    obtain ⟨y', hy', e'⟩ := h4' w hw
    refine ⟨y', hy', (key y y' ?_).symm⟩
    rw [e', smul_mulVec_congr ε A e, smul_mulVec_mat ε h, smul_mulVec_congr ε B' ew]

omit [DecidableEq n] in
theorem smul_mul_congr_left (ε : R) {X Y : Matrix n n R} (h : ε • X = ε • Y) (Z : Matrix n n R) :
    ε • (X * Z) = ε • (Y * Z) := by
  rw [← Matrix.smul_mul, h, Matrix.smul_mul]

omit [DecidableEq n] in
theorem smul_mul_congr_right (ε : R) {X Y : Matrix n n R} (h : ε • X = ε • Y) (Z : Matrix n n R) :
    ε • (Z * X) = ε • (Z * Y) := by
  rw [← Matrix.mul_smul, h, Matrix.mul_smul]

end Alg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem change_unif {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D)
    (ϖ ϖ' : 𝓞 D.host.E) (k : Fin V.rank → ℤ) (he : IsIdemAt e P) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (h1' : ϖ' ∈ P.asIdeal) (h2' : ϖ' ∉ P.asIdeal ^ 2)
    (z : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (hz : IntVec z) :
    ∃ w, IntVec w ∧ finPart D e • (fun i => finPart D (incA D ((ϖ' : D.host.E) ^ k i)) * z i) =
      finPart D e • fun i => finPart D (incA D ((ϖ : D.host.E) ^ k i)) * w i := by
  have hε : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1.1]
  have h0 : (ϖ : D.host.E) ≠ 0 := by
    intro h
    have : ϖ = 0 := by exact_mod_cast h
    exact h2 (this ▸ zero_mem _)
  refine ⟨fun i => finPart D e * finPart D (incA D ((ϖ' : D.host.E) ^ k i / (ϖ : D.host.E) ^ k i)) * z i,
    fun i => GlobalTheory.SplitLatBasis.mul_mem_intAE D ((_root_.GlobalTheory.LatIntFacts.int_facts V).2.1 P e ϖ ϖ' he h1 h2 h1' h2' (k i)) (hz i), ?_⟩
  funext i
  have e1 : finPart D (incA D ((ϖ' : D.host.E) ^ k i)) = finPart D (incA D ((ϖ : D.host.E) ^ k i)) *
      finPart D (incA D ((ϖ' : D.host.E) ^ k i / (ϖ : D.host.E) ^ k i)) := by
    rw [← map_mul, ← map_mul, mul_div_cancel₀ _ (zpow_ne_zero _ h0)]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [e1]
  linear_combination (-(finPart D (incA D ((ϖ : D.host.E) ^ k i)) *
      finPart D (incA D ((ϖ' : D.host.E) ^ k i / (ϖ : D.host.E) ^ k i)) * z i)) * hε

theorem split_label : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ ϖ' : 𝓞 D.host.E) (d : List ℤ) (α α' : GA D V), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → Formalism.L2.Theta.SuppAt e V α → Formalism.L2.Theta.SuppAt e V α' → DivAt V e (ϖ : D.host.E) d α → DivAt V e (ϖ' : D.host.E) d α' → ∃ a ∈ locPart V (KsphC V ∅) e, ∃ b ∈ locPart V (KsphC V ∅) e, α' = a * α * b := by
  intro D V P e ϖ ϖ' d α α' he h1 h2 h1' h2' hα hα' hd hd'
  obtain ⟨-, B, hB1, hB2, hB3, hB4⟩ := hd
  obtain ⟨-, B', hB1', hB2', hB3', hB4'⟩ := hd'
  have hε : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1.1]
  obtain ⟨C, hBC, hCB⟩ := (_root_.GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hε fun y hy => (hB2 y hy).imp fun _ h => h.2
  obtain ⟨C', hBC', hCB'⟩ := (_root_.GlobalTheory.LatIntFacts.int_facts V).2.2 _ B' hε fun y hy => (hB2' y hy).imp fun _ h => h.2
  have hinv : finPart D e • ((B' * C) * (B * C')) = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) := by
    have := smul_mul_congr_right _ (smul_mul_congr_left _ hCB C') B'
    rw [Matrix.one_mul, hBC'] at this
    rw [← this]
    simp only [Matrix.mul_assoc]
  obtain ⟨a, haS, ha⟩ := _root_.GlobalTheory.SplitLift.split_lift V e he.1 _ _ hinv
  have hAB : finPart D e • (finMat D.sp.cm.sig V.gram a * B) = finPart D e • B' := by
    rw [smul_mul_congr_left _ ha B, Matrix.mul_assoc, smul_mul_congr_right _ hCB B', Matrix.mul_one]
  have hs := stab_of_bases (finPart D e) hε {y | y ∈ LamHat V} {z | IntVec z} hAB
    (fun z hz => hB1 z hz) (fun y hy => hB2 y hy) (fun z hz => hB1' z hz) (fun y hy => hB2' y hy)
  have haK : a ∈ KsphC V ∅ := _root_.GlobalTheory.SplitStab.mem_ksph_of_split V e a he.1 haS hs.1 hs.2
  obtain ⟨hf1, hf2, -⟩ := (_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e (e + cA D e) (Or.inl ⟨he, rfl⟩)
  obtain ⟨L, hL⟩ := ((_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).1 _ hf1 hf2).1
  have hbS : Formalism.L2.Theta.SuppAt e V ((a * α)⁻¹ * α') :=
    (hL _).1 (L.mul_mem (L.inv_mem (L.mul_mem ((hL _).2 haS) ((hL _).2 hα))) ((hL _).2 hα'))
  have hN : finMat D.sp.cm.sig V.gram (a * α)⁻¹ *
      (finMat D.sp.cm.sig V.gram a * finMat D.sp.cm.sig V.gram α) = 1 := by
    rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, ← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, inv_mul_cancel,
      Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one]
  have ht := stab_of_div (finPart D e) {y | y ∈ LamHat V} {z | IntVec z}
    (fun i => finPart D (incA D ((ϖ : D.host.E) ^ d.getD i.1 0)))
    (fun i => finPart D (incA D ((ϖ' : D.host.E) ^ d.getD i.1 0))) hAB hN
    (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul _ _ (a * α)⁻¹ α')
    (fun y hy => (_root_.GlobalTheory.LatIntFacts.int_facts V).1 _ (GlobalTheory.AdIdem.idempotent_mem_intAE D _ hε) y hy)
    (fun z hz => change_unif V P e ϖ ϖ' _ he h1 h2 h1' h2' z hz)
    (fun z hz => change_unif V P e ϖ' ϖ _ he h1' h2' h1 h2 z hz)
    (fun y hy => hB3 y hy) (fun z hz => hB4 z hz) (fun y hy => hB3' y hy) (fun z hz => hB4' z hz)
  have hbK : (a * α)⁻¹ * α' ∈ KsphC V ∅ := _root_.GlobalTheory.SplitStab.mem_ksph_of_split V e _ he.1 hbS ht.1 ht.2
  exact ⟨a, ⟨haK, haS⟩, _, ⟨hbK, hbS⟩, by rw [mul_inv_cancel_left]⟩

end GlobalTheory.SplitLabel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowEqSpanNormOne
section
noncomputable section

namespace GlobalTheory.KernelScalarUnit

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts GlobalTheory.UnUnitCmp
open scoped nonZeroDivisors

section Ideals

variable {K : Type} [Field K] [NumberField K]

theorem exists_pow_eq_span {𝔞 𝔟 : Submodule (𝓞 K) K} (h : 𝔞 * 𝔟 = 1) :
    ∃ (n : ℕ) (a : K), 0 < n ∧ 𝔞 ^ n = Submodule.span (𝓞 K) {a} := by
  have hu : IsUnit 𝔞 := IsUnit.of_mul_eq_one 𝔟 h
  have hv : IsUnit 𝔟 := IsUnit.of_mul_eq_one 𝔞 (by rw [mul_comm]; exact h)
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨𝔞, FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit hu)⟩
  let J : FractionalIdeal (𝓞 K)⁰ K := ⟨𝔟, FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit hv)⟩
  have hIJ : I * J = 1 := by
    apply FractionalIdeal.coeToSubmodule_injective
    simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one]
    exact h
  let U : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mkOfMulEqOne I J hIJ
  have h1 : ClassGroup.mk K (U ^ Fintype.card (ClassGroup (𝓞 K))) = 1 := by rw [map_pow, pow_card_eq_one]
  obtain ⟨a, ha⟩ := ClassGroup.mk_eq_one_iff.1 h1
  refine ⟨_, a, Fintype.card_pos (α := ClassGroup (𝓞 K)), ?_⟩
  rw [← ha, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
  rfl

omit [NumberField K] in
theorem map_mem_one (c : K →+* K) {x : K} (hx : x ∈ (1 : Submodule (𝓞 K) K)) : c x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨⟨c r, map_isIntegral_int c r.isIntegral_coe⟩, rfl⟩

omit [NumberField K] in
theorem map_mem_pow (c : K →+* K) {𝔞 𝔟 : Submodule (𝓞 K) K} (h : ∀ x ∈ 𝔞, c x ∈ 𝔟) :
    ∀ (n : ℕ), ∀ x ∈ 𝔞 ^ n, c x ∈ 𝔟 ^ n
  | 0, x, hx => by rw [pow_zero] at *; exact map_mem_one c hx
  | n + 1, x, hx => by
    rw [pow_succ] at hx ⊢
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [map_mul c]
      exact Submodule.mul_mem_mul (map_mem_pow c h n a ha) (h b hb)
    · rw [map_add c]
      exact add_mem ha hb

theorem exists_pow_eq_span_normOne (c : K →+* K) (hc : ∀ x, c (c x) = x) {𝔞 𝔟 : Submodule (𝓞 K) K}
    (hb : ∀ x, x ∈ 𝔟 ↔ c x ∈ 𝔞) (h : 𝔞 * 𝔟 = 1) :
    ∃ (n : ℕ) (z : K), 0 < n ∧ c z * z = 1 ∧ 𝔞 ^ n = Submodule.span (𝓞 K) {z} := by
  obtain ⟨n, a, hn, ha⟩ := exists_pow_eq_span h
  have hb' : 𝔟 ^ n = Submodule.span (𝓞 K) {c a} := by
    apply le_antisymm
    · intro y hy
      have h1 := map_mem_pow c (fun x hx => (hb x).1 hx) n y hy
      rw [ha, Submodule.mem_span_singleton] at h1
      obtain ⟨r, hr⟩ := h1
      refine Submodule.mem_span_singleton.2 ⟨⟨c r, map_isIntegral_int c r.isIntegral_coe⟩, ?_⟩
      rw [← hc y, ← hr, Algebra.smul_def r, map_mul]
      rfl
    · rw [Submodule.span_singleton_le_iff_mem]
      exact map_mem_pow c (fun x hx => (hb _).2 (by rwa [hc])) n a (ha ▸ Submodule.mem_span_singleton_self a)
  have h2 : Submodule.span (𝓞 K) {a * c a} = 1 := by
    rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span, ← ha, ← hb', ← mul_pow, h, one_pow]
  have h0 : a * c a ≠ 0 := fun h0 => by
    rw [h0, Submodule.span_singleton_eq_bot.2 rfl] at h2
    have : (1 : K) ∈ (⊥ : Submodule (𝓞 K) K) := h2 ▸ Submodule.mem_one.2 ⟨1, map_one _⟩
    simp at this
  have a0 : a ≠ 0 := left_ne_zero_of_mul h0
  have c0 : c a ≠ 0 := right_ne_zero_of_mul h0
  refine ⟨n + n, a / c a, by omega, ?_, ?_⟩
  · rw [map_div₀, hc]; field_simp
  · rw [pow_add, ha, Submodule.span_mul_span, Set.singleton_mul_singleton, ← mul_one (Submodule.span (𝓞 K) {a / c a}), ← h2,
      Submodule.span_mul_span, Set.singleton_mul_singleton]
    congr 2
    field_simp

end Ideals

theorem normOne_pow (D : D7) : NormOnePowerPrincipal D := by
  let := D.host.cmStar
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  rintro 𝔞 ⟨𝔟, hb, h⟩
  obtain ⟨n, z, hn, hz, e⟩ := exists_pow_eq_span_normOne (D.host.conj : D.host.E →+* D.host.E)
    (fun x => by change D.host.conj (D.host.conj x) = x; rw [← hs, ← hs, star_star]) hb h
  have hz' : star z * z = 1 := by rw [hs]; exact hz
  exact ⟨n, ⟨z, hz', by rw [mul_comm]; exact hz'⟩, hn, e⟩

section Local

variable {K : Type} [Field K] [NumberField K] {C : Type} [NormedField C] [IsUltrametricDist C] (ψ : K →+* C)

omit [NumberField K] in
theorem norm_int_le (a : 𝓞 K) : ‖ψ (a : K)‖ ≤ 1 := norm_le_one_of_isIntegral (map_isIntegral_int ψ a.isIntegral_coe)

def ball (r : ℝ) (hr : 0 ≤ r) : Submodule (𝓞 K) K where
  carrier := {x | ‖ψ x‖ ≤ r}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simpa using hr
  smul_mem' := fun c a ha => by
    simp only [Set.mem_ofPred_eq, Algebra.smul_def, map_mul, norm_mul] at *
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le ψ c)).trans ha

end Local

section Det

variable (D : D7) {l : ℕ} [Fact l.Prime] (ψ : D.host.E →+* ℂ_[l]) {N : ℕ}
  {L₀ L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {P : Matrix (Fin N) (Fin N) D.host.E}

end Det

section Power

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

def lamTau (τ : D.what₂.Tau) : D.host.E →+* ℂ_[l] :=
  lam.comp ((embT D τ).codRestrict Qbar (emb_mem (embT D τ)))

theorem tauEmb_eq (τ : D.what₂.Tau) : tauEmb D lam τ = lamTau D lam τ := by
  funext x
  unfold tauEmb lamC
  rw [dite_eq_left (emb_mem (embT D τ) x)]
  rfl

end Power

section Main

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

variable (E : KerEnt D Dx Tw) (O : ∀ u μ, LiftObj D (D.chTw u μ))

end Main

end GlobalTheory.KernelScalarUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalMatrixDoubleCosetOfElementaryDivisorsStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localMatrix_doubleCoset_of_elementaryDivisors : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)) (ϖ : E) (d : Fin V.rank → ℤ) (g : HA (AF F) hc.sig V.gram), IsIdemOf E v e → IsFrameAt V v h → ϖ ≠ 0 → DivG hc V e ϖ d g → ∃ k₁ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, (h⁻¹ * locMat hc V v g * h).1 = k₁.1 * Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i)) * k₂.1 := by
  first | exact @GlobalTheory.PlaceDiv.double_coset_of_divG | exact GlobalTheory.PlaceDiv.double_coset_of_divG | (intros; apply GlobalTheory.PlaceDiv.double_coset_of_divG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
section
noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def intMat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) :
    AddSubgroup (Matrix (Fin a) (Fin b) L) where
  carrier := {u | ∀ i j, u i j ∈ Formalism.UG.intL L}
  zero_mem' := fun _ _ => (Formalism.UG.intL L).zero_mem
  add_mem' := fun ha hb i j => (Formalism.UG.intL L).add_mem (ha i j) (hb i j)
  neg_mem' := fun ha i j => (Formalism.UG.intL L).neg_mem (ha i j)

def intVec (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a : ℕ) : AddSubgroup (Fin a → L) where
  carrier := {u | ∀ i, u i ∈ Formalism.UG.intL L}
  zero_mem' := fun _ => (Formalism.UG.intL L).zero_mem
  add_mem' := fun ha hb i => (Formalism.UG.intL L).add_mem (ha i) (hb i)
  neg_mem' := fun ha i => (Formalism.UG.intL L).neg_mem (ha i)

theorem mem_intMat {a b : ℕ} (u : Matrix (Fin a) (Fin b) L) : u ∈ intMat L a b ↔ ∀ i j, u i j ∈ Formalism.UG.intL L := Iff.rfl

theorem mem_intVec {a : ℕ} (u : Fin a → L) : u ∈ intVec L a ↔ ∀ i, u i ∈ Formalism.UG.intL L := Iff.rfl

def latIdx {a b : ℕ} (x : Matrix (Fin a) (Fin b) L) : ℕ :=
  Nat.card (Set.range fun u : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a))

end GlobalTheory.Hk3.HoweDuality

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSelfEqOneIffOfLinearOrderedCommGroupWithZero
section
noncomputable section

open Formalism.UG Matrix

namespace GlobalTheory.Hk3.Inh

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_two {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (hq : Odd q) : Valued.v (2 : L) = 1 := by
  obtain ⟨-, -, -, -, -, h2, hc⟩ := h
  let O := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hc' : Nat.card (IsLocalRing.ResidueField O) = q ^ 2 := hc
  haveI : Finite (IsLocalRing.ResidueField O) := Nat.finite_of_card_ne_zero (by rw [hc']; positivity)
  haveI := Fintype.ofFinite (IsLocalRing.ResidueField O)
  have h0 : ((q ^ 2 : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← hc', Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
  have hle : Valued.v (2 : L) ≤ 1 := (2 : O).2
  by_contra hne
  have hlt : Valued.v (2 : L) < 1 := lt_of_le_of_ne hle hne
  have hm : (2 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [Valuation.mem_maximalIdeal_iff]; exact hlt
  have h2' : (2 : IsLocalRing.ResidueField O) = 0 := by
    have := (IsLocalRing.residue_eq_zero_iff (2 : O)).2 hm
    rwa [map_ofNat] at this
  obtain ⟨k, hk⟩ : Odd (q ^ 2) := hq.pow
  rw [hk] at h0
  push_cast at h0
  rw [h2'] at h0
  simp at h0




section Main

variable {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {ψ : AddChar L ℂ}







end Main

section Laurent

end Laurent

end GlobalTheory.Hk3.Inh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNeAlt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.InertialTypes

theorem not_mem_placesOver_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ placesOver E p) : w ∉ placesOver E q := by
  intro hw'
  have hc : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hw) (w.asIdeal.mul_mem_left b hw')

end GlobalTheory.InertialTypes
end

