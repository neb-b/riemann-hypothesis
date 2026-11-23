module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.DataRRMetric
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MuModelProductValueNeZeroOfDepleted
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMuModelMeasureOfEigenfunctional
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun.IntPtsUnitary

section General
variable {L : Type} [Field L] [TopologicalSpace L] [IsTopologicalRing L] {n : Type} [Fintype n] [DecidableEq n]

omit [TopologicalSpace L] [IsTopologicalRing L] in
theorem coe_GLint (O : Subring L) : (GLint n O : Set (GL n L)) =
    {g : GL n L | ∀ i j, (g : Matrix n n L) i j ∈ O} ∩ {g : GL n L | ∀ i j, ((g⁻¹ : GL n L) : Matrix n n L) i j ∈ O} :=
  Set.ext fun g => ⟨fun h => ⟨P.cartan_entries_of_mem O g h, P.cartan_entries_of_mem O _ (inv_mem h)⟩,
    fun h => P.cartan_mem_of_entries O g h.1 h.2⟩

theorem isOpen_GLint (O : Subring L) (hO : IsOpen (O : Set L)) : IsOpen (GLint n O : Set (GL n L)) := by
  rw [coe_GLint]
  simp only [Set.ofPred_forall]
  refine IsOpen.inter ?_ ?_
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (Units.continuous_val.matrix_elem i j)
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (Units.continuous_coe_inv.matrix_elem i j)

theorem isCompact_GLint [T2Space L] (O : Subring L) (hO : IsCompact (O : Set L)) :
    IsCompact (GLint n O : Set (GL n L)) := by
  have hM : IsCompact {A : Matrix n n L | ∀ i j, A i j ∈ O} := by
    have := isCompact_univ_pi fun _ : n => isCompact_univ_pi fun _ : n => hO
    have e : {A : Matrix n n L | ∀ i j, A i j ∈ O} =
        Set.univ.pi fun _ : n => Set.univ.pi fun _ : n => (O : Set L) :=
      Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    exact e ▸ this
  have := (Units.isClosedEmbedding_embedProduct (α := Matrix n n L)).isCompact_preimage
    (hM.prod (hM.image MulOpposite.continuous_op))
  convert this using 1
  rw [coe_GLint]
  ext g
  exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
    have : A = ((g⁻¹ : GL n L) : Matrix n n L) := MulOpposite.op_injective e
    exact this ▸ hA i j⟩⟩

end General

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isCompact_intL [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    IsCompact (intL L : Set L) := by
  obtain ⟨-, -, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := L)).2 ⟨(Valued.isClosed_integer L).completeSpace_coe,
      (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  exact isCompact_iff_compactSpace.2 hp

theorem coe_KU (σ : L →+* L) (n : ℕ) :
    (KU σ n : Set (GU σ n)) = Subtype.val ⁻¹' (GLint (Fin n) (intL L) : Set (GL (Fin n) L)) := by
  ext g
  exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

theorem isOpen_isCompact_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q →
      IsOpen (KU σ n : Set (GU σ n)) ∧ IsCompact (KU σ n : Set (GU σ n)) := by
  intro L _ _ _ ϖ σ q n h
  rw [coe_KU]
  refine ⟨(isOpen_GLint _ (Valued.isOpen_integer L)).preimage continuous_subtype_val, ?_⟩
  have hc : IsClosed (GU σ n : Set (GL (Fin n) L)) :=
    isClosed_eq (((Units.continuous_val.matrix_map (GlobalTheory.LGrp.continuous_of_unramInv h)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul Units.continuous_val) continuous_const
  exact hc.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_GLint _ (isCompact_intL h))

end GlobalTheory.LFun.IntPtsUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyRingHomComplexOfLeContinuum
section
set_option autoImplicit false

open Formalism.BasicNotions NumberField

namespace GlobalTheory.WittFracComplex


open Cardinal in
theorem nonempty_ringHom_complex_of_le_continuum (K : Type) [Field K] [CharZero K] (hK : #K ≤ 𝔠) :
    Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  have hF : #F = 𝔠 := by
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK,
      max_eq_left Cardinal.aleph0_le_continuum]
  have hL : #L = 𝔠 := by
    refine le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)
    have := Algebra.IsAlgebraic.cardinalMk_le_max F L
    rwa [hF, max_eq_left Cardinal.aleph0_le_continuum] at this
  let j : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  have : CharZero L := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))
  exact ⟨e.toRingHom.comp j⟩

theorem charZero_wittVector (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] [CharP k p] :
    CharZero (WittVector p k) := by
  obtain ⟨q, hq⟩ := CharP.exists (WittVector p k)
  have h1 : ((q : ℕ) : k) = 0 := by
    have := congrArg (WittVector.constantCoeff : WittVector p k →+* k) (CharP.cast_eq_zero (WittVector p k) q)
    rwa [map_natCast, map_zero] at this
  have h2 : p ∣ q := (CharP.cast_eq_zero_iff k p q).1 h1
  rcases CharP.char_is_prime_or_zero (WittVector p k) q with h | h
  · have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hp.out h).1 h2
    subst h3
    exact absurd (CharP.cast_eq_zero (WittVector p k) p) (WittVector.p_nonzero p k)
  · subst h
    exact CharP.charP_to_charZero _


open Cardinal in
theorem mk_wittVector_le (p : ℕ) (k : Type) (hk : #k ≤ ℵ₀) : #(WittVector p k) ≤ 𝔠 := by
  have h : Function.Injective (WittVector.coeff : WittVector p k → ℕ → k) :=
    fun x y h => WittVector.ext (fun n => congrFun h n)
  refine (Cardinal.mk_le_of_injective h).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat, ← Cardinal.aleph0_power_aleph0]
  exact Cardinal.power_le_power_right hk


open Cardinal in
theorem nonempty_ringHom_complex : ∀ (p : ℕ) [Fact p.Prime], Nonempty (DV.KW p →+* ℂ) := by
  intro p _
  have hk : #(AlgebraicClosure (ZMod p)) ≤ ℵ₀ := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max (ZMod p) (AlgebraicClosure (ZMod p))
    rwa [max_eq_right (Cardinal.lt_aleph0_of_finite _).le] at this
  have := charZero_wittVector p (AlgebraicClosure (ZMod p))
  have : CharZero (DV.KW p) :=
    (RingHom.charZero_iff (IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p))).1 this
  refine nonempty_ringHom_complex_of_le_continuum _ ?_
  rw [Cardinal.mk_fractionRing]
  exact mk_wittVector_le p _ hk

end GlobalTheory.WittFracComplex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinaryEisensteinEigenfunctionalExists
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem chapterM_theta : ∀ (N r : ℕ) (χ : DirichletCharacter ℂ N) (sg : ℂ), 0 < N → r.Prime → 7 ≤ r → r ∣ N →
    (sg = 1 ∨ sg = -1) → ∃ θ : DirichletCharacter ℂ N, θ (-1) = sg ∧ θ * χ ≠ 1 ∧ θ * χ⁻¹ ≠ 1 := _root_.GlobalTheory.exists_char_parity_mul_ne_one_mul_inv_ne_one

theorem chapterM_smooth : ∀ (N l e : ℕ) (θ₁ θ₂ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l), 0 < N → l.Prime →
    ¬ l ∣ N → 1 ≤ e → θ₁ ≠ 1 → θ₂ ≠ 1 → ∃ c d : ℕ, 1 < c ∧ 1 < d ∧ c.Coprime (6 * N * l) ∧ d.Coprime (6 * N * l) ∧
      (∀ z : ℂ, ‖z‖ = 1 → (c : ℂ) ^ e ≠ z) ∧ ∀ n₁ n₂ : ℤ, (n₁ = 1 ∨ n₁ = -1) →
        (d : ℂ) ^ 2 ≠ (d : ℂ) ^ (e + 1) * (θ₁ d ^ n₁ * ψ d ^ n₂) ∧ (d : ℂ) ^ 2 ≠ (d : ℂ) ^ (e + 1) * (θ₂ d ^ n₁ * ψ d ^ n₂) := _root_.GlobalTheory.smoothing_integers_two_characters

theorem norm_symm_char_unit {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {N : ℕ} [NeZero N]
    (φ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) : ‖ι.symm (φ u)‖ = 1 := by
  have h : (φ u) ^ Fintype.card (ZMod N)ˣ = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have h2 : ‖ι.symm (φ u)‖ ^ Fintype.card (ZMod N)ˣ = 1 := by
    rw [← norm_pow, ← map_pow, h, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2

theorem chapterM_of_level (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e : ℕ) (he : 1 ≤ e)
    (g : Newform (2 * e + 1)) (hal : ‖ι.symm (g.a l)‖ = 1) (ψ : DirichletCharacter ℂ l)
    (N r : ℕ) (hN : 0 < N) (hr : r.Prime) (hr7 : 7 ≤ r) (hrN : r ∣ N) (hlN : ¬ l ∣ N)
    (χ : DirichletCharacter ℂ N) (g' : ℕ → ℂ) (hprim : Prim (2 * e + 1) N χ g')
    (hg' : ∀ n : ℕ, n.Coprime N → g' n = g.a n) :
    ∃ (θ : DirichletCharacter ℂ N) (α v : ℂ) (B : ℕ) (c : ℕ → ℂ) (c₁ d₁ : ℕ),
      5 ≤ N ∧ ‖ι.symm α‖ = 1 ∧
      α ^ 2 - g.a l * α + χ l * (l : ℂ) ^ (2 * e) = 0 ∧
      EigAll (2 * e + 1) N l χ (fun q => g.a q) α B c ∧ χ (-1) = -1 ∧ θ (-1) = (-1) ^ e * ψ (-1) ∧
      MeasMu ι e ((-1) ^ e * ψ (-1)) (hat θ) (tw2 N ((-1) ^ e * ψ (-1))) ψ α B c v ∧ v ≠ 0 ∧
      1 < c₁ ∧ 1 < d₁ ∧ c₁.Coprime (6 * N * l) ∧ d₁.Coprime (6 * N * l) ∧
      (∀ z : ℂ, ‖z‖ = 1 → (c₁ : ℂ) ^ e ≠ z) ∧ ∀ n₁ n₂ : ℤ, (n₁ = 1 ∨ n₁ = -1) →
        (d₁ : ℂ) ^ 2 ≠ (d₁ : ℂ) ^ (e + 1) * ((θ * χ) d₁ ^ n₁ * ψ d₁ ^ n₂) ∧
        (d₁ : ℂ) ^ 2 ≠ (d₁ : ℂ) ^ (e + 1) * ((θ * χ⁻¹) d₁ ^ n₁ * ψ d₁ ^ n₂) := by
  have hlp : l.Prime := Fact.out
  haveI : NeZero N := ⟨hN.ne'⟩
  have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hlp).2 hlN
  have hgl : g' l = g.a l := hg' l hcop

  have hχm1 : χ (-1) = -1 :=
    (_root_.GlobalTheory.EisM.twisted_lvalue_ne_zero_edge (2 * e + 1) N 1 χ (1 : DirichletCharacter ℂ 1) g' ((((2 * e + 1 : ℕ) : ℝ) + 1) / 2)
      (odd_two_mul_add_one e) hN one_pos hprim le_rfl).1

  have hψ : ψ (-1) = 1 ∨ ψ (-1) = -1 :=
    mul_self_eq_one_iff.mp (by rw [← map_mul, neg_one_mul, neg_neg, map_one])
  have hsg : (-1 : ℂ) ^ e * ψ (-1) = 1 ∨ (-1 : ℂ) ^ e * ψ (-1) = -1 := by
    rcases neg_one_pow_eq_or ℂ e with h | h <;> rcases hψ with h' | h' <;> simp [h, h']
  obtain ⟨θ, hθm1, hθχ, hθχ'⟩ := chapterM_theta N r χ _ hN hr hr7 hrN hsg

  set u : (ZMod N)ˣ := ZMod.unitOfCoprime l hcop with hu
  have hul : ((u : ZMod N)) = (l : ZMod N) := ZMod.coe_unitOfCoprime l hcop
  have hnχ : ‖ι.symm (χ l)‖ = 1 := by rw [← hul]; exact norm_symm_char_unit ι χ u
  have hnχ' : ‖ι.symm (χ⁻¹ l)‖ = 1 := by rw [← hul]; exact norm_symm_char_unit ι χ⁻¹ u
  have hnl : ‖ι.symm (l : ℂ)‖ < 1 := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hlp.one_lt)
  have ht : ‖ι.symm (χ⁻¹ l * g' l)‖ = 1 := by rw [map_mul, norm_mul, hnχ', hgl, hal, one_mul]
  have hD : ‖ι.symm (χ⁻¹ l * (l : ℂ) ^ (2 * e))‖ < 1 := by
    rw [map_mul, norm_mul, hnχ', one_mul, map_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hnl (by omega)
  obtain ⟨α, β, hs, hp, hα, -⟩ := GlobalTheory.unitRoot_split l ι _ _ ht hD

  obtain ⟨B, c, hEig, hval⟩ := _root_.GlobalTheory.EisM.eigF_value_ne_zero l ι e N χ θ ψ g' α β he hN hlN hprim hs hp hα hθm1 hθχ

  obtain ⟨x, y, hxy⟩ : IsCoprime (N : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.2 hcop.symm
  have hbez : (N : ℤ) * x * 1 - l * (-y) * 1 = 1 := by linear_combination hxy
  obtain ⟨B', c', hall, hrel⟩ := _root_.GlobalTheory.EisM.eigAll_of_atkinLehner (2 * e + 1) N l χ g' α B c x (-y) 1 1 hbez (by omega) hN hlp hlN hEig
  have hα0 : α ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hα; exact zero_ne_one hα
  have key := _root_.GlobalTheory.zm_val_ne_zero e N l χ⁻¹ θ ψ (fun n => conj (g' n)) α β x (-y) 1 1 hbez he hN hlp hlN
  simp only [inv_inv, Complex.conj_conj] at key
  have hv := key hprim hs hp hα0 hθm1 hθχ B c hEig hval B' c' hrel (fun a ha => hall.U a ha)
  have hmeas := _root_.GlobalTheory.EisM.measMu_of_eig l ι e N χ θ ψ (χ l * α) B' c' he hN hlN
    (by rw [map_mul, norm_mul, hnχ, hα, one_mul]) hall.kill hall.U hθm1 hχm1
  obtain ⟨c₁, d₁, hc1, hd1, hc1c, hd1c, hc, hd⟩ := chapterM_smooth N l e (θ * χ) (θ * χ⁻¹) ψ hN hlp hlN he hθχ hθχ'
  refine ⟨θ, χ l * α, _, B', c', c₁, d₁, ?_, ?_, ?_, ?_, hχm1, hθm1, hmeas, ?_, hc1, hd1, hc1c, hd1c, hc, hd⟩
  · have := Nat.le_of_dvd hN hrN; omega
  · rw [map_mul, norm_mul, hnχ, hα, one_mul]
  · have hxy1 : χ l * χ⁻¹ l = 1 := by
      rw [← hul, MulChar.inv_apply_eq_inv', mul_inv_cancel₀]
      exact (u.isUnit.map χ).ne_zero
    rw [hgl] at hs
    linear_combination ((χ l) ^ 2 * α) * hs - (χ l) ^ 2 * hp + (χ l * g.a l * α - χ l * (l : ℂ) ^ (2 * e)) * hxy1
  · refine ⟨⟨fun a ha q hq hqN => ?_, hall.U⟩, hall.kill⟩
    have hqc : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hqN (h.trans (dvd_mul_right N l)))
    rw [← hg' q hqc]
    exact hall.T a ha q hq hqN
  · refine mul_ne_zero (div_ne_zero two_ne_zero ?_) hv
    exact_mod_cast (Nat.totient_pos.2 hN).ne'

theorem chapterM_holds : CuspidalUnitaryTwistsClaim := by
  intro l _ hl2 ι e he g hlM hal ψ N₀ hN₀ hlN₀
  have hlp : l.Prime := Fact.out
  obtain ⟨r, hrge, hr⟩ := Nat.exists_infinite_primes (l + 7)
  have hrl : ¬ l ∣ r := by
    intro h
    rcases (Nat.dvd_prime hr).1 h with h1 | h1
    · exact hlp.one_lt.ne' h1
    · omega
  obtain ⟨χ, hprim, hχ⟩ := depleted_newform_prim (2 * e + 1) (N₀ * r) g (by omega) (by nlinarith [hr.two_le])
  have hMpos := g.pos
  have hrpos := hr.pos
  have hN : 0 < g.M * (g.M * (N₀ * r)) ^ 2 := by positivity
  have hL : g.M * (N₀ * r) ∣ g.M * (g.M * (N₀ * r)) ^ 2 := (dvd_pow_self _ two_ne_zero).mul_left g.M
  have hrN : r ∣ g.M * (g.M * (N₀ * r)) ^ 2 := (dvd_mul_of_dvd_right (dvd_mul_left r N₀) g.M).trans hL
  have hN₀N : N₀ ∣ g.M * (g.M * (N₀ * r)) ^ 2 := (dvd_mul_of_dvd_right (dvd_mul_right N₀ r) g.M).trans hL
  have hMN : g.M ∣ g.M * (g.M * (N₀ * r)) ^ 2 := dvd_mul_right _ _
  have hlN : ¬ l ∣ g.M * (g.M * (N₀ * r)) ^ 2 := by
    intro h
    rcases hlp.dvd_mul.1 h with h | h
    · exact hlM h
    · rcases hlp.dvd_mul.1 (hlp.dvd_of_dvd_pow h) with h | h
      · exact hlM h
      · rcases hlp.dvd_mul.1 h with h | h
        · exact hlN₀ h
        · exact hrl h
  have hg' : ∀ n : ℕ, n.Coprime (g.M * (g.M * (N₀ * r)) ^ 2) →
      (fun n => if n.Coprime (g.M * (N₀ * r)) then g.a n else 0) n = g.a n := by
    intro n hn
    simp only [if_pos (hn.coprime_dvd_right hL)]
  obtain ⟨θ, α, v, B, c, c₁, d₁, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    chapterM_of_level l ι e he g hal ψ _ r hN hr (by omega) hrN hlN χ _ hprim hg'
  exact ⟨_, χ, θ, α, v, B, c, c₁, d₁, h1, hMN, hN₀N, hlN, hχ, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

end GlobalTheory.EisM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PointGlobalSectionsNeBot
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped NNReal

namespace GlobalTheory.PointGeometry

variable (F : Type) [Field F] [NumberField F]

structure AdelicLine where

  inf : InfinitePlace F → ℝ

  fin : HeightOneSpectrum (𝓞 F) → ℝ
  fin_finite : (Function.mulSupport fin).Finite

variable {F}


open Classical in
def AdelicLine.of (a : InfinitePlace F → ℝ) (b : HeightOneSpectrum (𝓞 F) → ℝ) : AdelicLine F :=
  if h : (Function.mulSupport b).Finite then ⟨a, b, h⟩ else ⟨a, 1, by simp⟩

@[simp] theorem AdelicLine.of_inf (a : InfinitePlace F → ℝ) (b : HeightOneSpectrum (𝓞 F) → ℝ) :
    (AdelicLine.of a b).inf = a := by
  unfold AdelicLine.of; split_ifs <;> rfl

theorem AdelicLine.of_fin (a : InfinitePlace F → ℝ) {b : HeightOneSpectrum (𝓞 F) → ℝ}
    (h : (Function.mulSupport b).Finite) : (AdelicLine.of a b).fin = b := by
  unfold AdelicLine.of; rw [dite_eq_left h]

def AdelicLine.deg (L : AdelicLine F) : ℝ :=
  -((∑ v : InfinitePlace F, (v.mult : ℝ) * Real.log (L.inf v)) + ∑ᶠ w, Real.log (L.fin w)) /
    (Module.finrank ℚ F : ℝ)

def AdelicLine.twist (L : AdelicLine F) (ci : InfinitePlace F → ℝ)
    (cf : HeightOneSpectrum (𝓞 F) → ℝ) : AdelicLine F :=
  AdelicLine.of (fun v => Real.exp (-ci v) * L.inf v) (fun w => Real.exp (-cf w) * L.fin w)

theorem AdelicLine.twist_fin (L : AdelicLine F) (ci : InfinitePlace F → ℝ)
    {cf : HeightOneSpectrum (𝓞 F) → ℝ} (h : (Function.support cf).Finite) :
    (L.twist ci cf).fin = fun w => Real.exp (-cf w) * L.fin w := by
  refine AdelicLine.of_fin _ ((h.union L.fin_finite).subset fun w hw => ?_)
  by_contra hn
  simp only [Set.mem_union, Function.mem_support, Function.mem_mulSupport, not_or, not_not] at hn
  exact hw (by simp [hn.1, hn.2])

variable [StarRing F]

def latticeNorm (W : HLat F) (ι : W.V →ₗ[F] F) (w : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (⨆ x : W.L, FinitePlace.mk w (ι x))⁻¹

def frameSq (W : HLat F) (ι : W.V →ₗ[F] F) (v : InfinitePlace F) : ℝ≥0 :=
  ∑ k : W.ι, ‖∑ i, (W.X v) i k • v.embedding (ι (W.b i))‖₊ ^ 2

def ofLattice (W : HLat F) (ι : W.V →ₗ[F] F) : AdelicLine F :=
  AdelicLine.of (fun v => (Real.sqrt (frameSq W ι v))⁻¹) (latticeNorm W ι)

variable (F)

def pointGeo : DV.Geo F where
  Var := Unit
  dim _ := 0
  Fn _ := F
  Dv _ := PUnit
  Eff _ _ := True
  eff_zero _ := trivial
  eff_add _ _ _ _ _ := trivial
  H0 _ _ := ⊤
  degreeZeroCohomology_finiteDimensional _ _ := inferInstance
  mul_mem_riemannRochSpace_add _ _ _ _ _ _ _ := Submodule.mem_top
  riemannRoch_mono _ _ _ _ := le_rfl
  KY _ := 0
  Cl _ := Set Unit
  properCl _ Z := Z ≠ Set.univ
  subCl _ Z Z' := Z ⊆ Z'
  supp _ _ := ∅
  inter _ _ := 1
  nef _ _ := True
  big _ _ := True
  bpf _ _ V := ∃ f ∈ V, f ≠ 0
  phiBir _ _ V := ∃ f ∈ V, f ≠ 0
  phiNoContr _ _ _ _ := True
  vanishOn _ _ f Z := Z.Nonempty → f = 0
  hdim _ i _ := if i = 0 then 1 else 0
  pts _ _ := Unit
  ptsMeas _ _ := ⊤
  vol _ _ := @MeasureTheory.Measure.dirac Unit ⊤ ()
  FnC _ _ := ℂ
  cx _ σ := σ
  cx_smul _ σ a f := by simp
  Met _ _ _ := ℝ≥0
  mAdd _ _ _ _ h h' := h * h'
  mPow _ _ _ k h := h ^ k
  fsMet _ _ _ _ _ e := ∑ k, ‖e k‖₊ ^ 2
  pn _ _ _ h f _ := ‖f‖ ^ 2 / (h : ℝ)
  pnK _ _ _ h f _ := ‖f‖ ^ 2 / (h : ℝ)
  mSmooth _ _ _ h := h ≠ 0
  mPsh _ _ _ _ _ := True
  redZero _ _ _ _ S := S = Set.univ
  agreeOn _ _ _ f g S := S.Nonempty → f = g
  resNorm _ _ _ h _ _ _ g _ := ‖g‖ ^ 2 / (h : ℝ)
  Adl _ := AdelicLine F
  ofW _ _ W ι := ofLattice W ι
  twist _ L ci cf := L.twist ci cf
  arTop _ L := L.deg
  arVol _ L := max L.deg 0
  nefA _ L := 0 ≤ L.deg
  supInf _ L v τ f := v f * L.inf v ^ τ
  supFin _ L w τ f := FinitePlace.mk w f * L.fin w ^ τ
  cutGood _ bd _ _ _ _ _ _ _ := bd = ∅
  cutHt _ L _ _ _ _ _ _ _ := L.deg
  cutOrd _ _ _ _ _ _ _ _ _ _ := 0
  resFull _ _ _ _ _ _ _ _ M ι _ :=
    (M.L.map (ι.restrictScalars (𝓞 F))).FG ∧ M.L.map (ι.restrictScalars (𝓞 F)) ≠ ⊥
  resDeg _ _ _ _ _ _ _ _ M ι L := (AdelicLine.of L.inf (latticeNorm M ι)).deg
  supInf_ofW _ _ W ι v τ f := by
    rw [ciSup_unique]
    change v f * (ofLattice W ι).inf v ^ τ =
      Real.sqrt (‖v.embedding f‖ ^ 2 / ((frameSq W ι v ^ τ : ℝ≥0) : ℝ))
    rw [ofLattice, AdelicLine.of_inf, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
      InfinitePlace.norm_embedding_eq, inv_pow, div_eq_mul_inv]
    congr 2
    rw [NNReal.coe_pow, eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity),
      ← mul_pow, Real.mul_self_sqrt (NNReal.coe_nonneg _)]
  supInf_twist _ L ci cf _ v τ f := by
    rw [AdelicLine.twist, AdelicLine.of_inf, mul_pow, ← Real.exp_nat_mul, mul_neg]
    ring
  supFin_twist _ L ci cf h w τ f := by
    rw [AdelicLine.twist_fin L ci h, mul_pow, ← Real.exp_nat_mul, mul_neg]
    ring
  regOn _ _ _ _ _ := True

theorem point_global_sections_ne_bot (Y : (pointGeo F).Var) : (pointGeo F).H0 Y 0 ≠ ⊥ :=
  (top_ne_bot : (⊤ : Submodule F F) ≠ ⊥)

theorem exists_geo : ∀ (F : Type) [Field F] [NumberField F] [StarRing F],
    ∃ G : DV.Geo F, ∃ Y : G.Var, G.H0 Y 0 ≠ ⊥ :=
  fun F _ _ _ => ⟨pointGeo F, (), point_global_sections_ne_bot F _⟩

end GlobalTheory.PointGeometry
end
end

