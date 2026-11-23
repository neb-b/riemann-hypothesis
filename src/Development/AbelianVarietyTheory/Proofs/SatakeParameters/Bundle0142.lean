module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0034
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import ReciprocityTheory.DualLattices.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0136
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalSubgroupContainingHyperspecialEqTopUnramif
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormalHyp

theorem unip_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ N : Subgroup (Formalism.UG.GU σ n), N.Normal → Formalism.UG.KU σ n ≤ N → ∀ u : Formalism.UG.GU σ n, Formalism.UG.IsUnipU u → u ∈ N := by
  intro L _ _ ϖ σ q n hU N hN hK u hu
  obtain ⟨hσσ, hσv, hσϖ, hϖ, -, -, -⟩ := hU
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  set U := (((u : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hUdef
  obtain ⟨M, hM⟩ := GlobalTheory.UnitarySwap.exists_pow_mem hϖ' U
  let b : Fin n → ℤ := fun i => (M : ℤ) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))
  have hb : ∀ i : Fin n, b i.rev = -b i := by
    intro i
    have := i.isLt
    simp only [b, Fin.val_rev]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  obtain ⟨s, hs, hs'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ b i) (fun i => by
    rw [map_zpow₀, hσϖ, hb, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])
  have hpow : ∀ k : ℤ, 0 ≤ k → Valued.v (ϖ ^ k) ≤ 1 := by
    intro k hk
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, map_pow]
    exact pow_le_one₀ zero_le hϖ1
  set k := s * u * s⁻¹ with hkdef
  have hkm : (((k : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ϖ ^ b i) * U * Matrix.diagonal (fun i => (ϖ ^ b i)⁻¹) := by
    rw [hkdef, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hs, hs']
  have hI : Formalism.UG.P.fIwasawaInt (((k : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    intro i j
    rw [hkm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases lt_trichotomy i j with hij | rfl | hij
    · have hle : (M : ℤ) ≤ b i - b j := by
        have : (i.val : ℤ) + 1 ≤ j.val := by exact_mod_cast hij
        simp only [b]
        nlinarith
      have e : ϖ ^ b i * U i j * (ϖ ^ b j)⁻¹ = ϖ ^ (b i - b j - M) * (ϖ ^ M * U i j) := by
        rw [zpow_sub₀ h0, zpow_sub₀ h0, zpow_natCast]
        field_simp
      rw [e, map_mul]
      exact mul_le_one' (hpow _ (by omega)) (hM i j)
    · have e1 : U i i = 1 := hu.2 i
      rw [e1, mul_one, mul_inv_cancel₀ (zpow_ne_zero _ h0), map_one]
    · have e1 : U i j = 0 := hu.1 i j hij
      rw [e1, mul_zero, zero_mul, map_zero]; exact zero_le
  have hkK : k ∈ Formalism.UG.KU σ n := by
    have := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ k) hI
    have e : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ k) = k := Subtype.ext (Units.ext rfl)
    rwa [e] at this
  have := hN.conj_mem k (hK hkK) s⁻¹
  have e : s⁻¹ * k * s⁻¹⁻¹ = u := by rw [hkdef]; group
  rwa [e] at this

theorem diag_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ N : Subgroup (Formalism.UG.GU σ n), N.Normal → Formalism.UG.KU σ n ≤ N → (∀ u : Formalism.UG.GU σ n, Formalism.UG.IsUnipU u → u ∈ N) → ∀ t : Formalism.UG.GU σ n, (∀ i j : Fin n, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) → t ∈ N := by
  intro L _ _ ϖ σ q n hU N hN hK hu t ht
  have hU' := hU
  obtain ⟨hσσ, hσv, hσϖ, hϖ, -, -, -⟩ := hU'
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  set T := (((t : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTdef
  have hTd : T = Matrix.diagonal (fun i => T i i) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · rw [Matrix.diagonal_apply_ne _ h]; exact ht i j h
  have hunit : ∀ i : Fin n, σ (T i i) * T i.rev i.rev = 1 := by
    intro i
    have := congrFun (congrFun (Formalism.UG.P.fIwasawa_mem_un σ t) i) i.rev
    rw [Formalism.UG.P.fIwasawa_gram, Formalism.UG.P.fIwasawa_antiJ, if_pos rfl] at this
    unfold Formalism.UG.P.fIwasawaH at this
    rw [Finset.sum_eq_single i.rev] at this
    · rw [Fin.rev_rev] at this; exact this
    · intro j _ hj
      show σ (T j.rev i) * T j i.rev = 0
      rw [ht j i.rev (fun h => hj h), mul_zero]
    · simp
  have hne : ∀ i, T i i ≠ 0 := by
    intro i h; have := hunit i; rw [h, map_zero, zero_mul] at this; exact zero_ne_one this
  have hv0 : ∀ i, Valued.v (T i i) ≠ 0 := fun i => by simpa using hne i
  let c : Fin n → ℤ := fun i => - WithZero.log (Valued.v (T i i))
  have hvrev : ∀ i, Valued.v (T i.rev i.rev) = (Valued.v (T i i))⁻¹ := by
    intro i
    have := congrArg Valued.v (hunit i)
    rw [map_mul, map_one, hσv] at this
    exact (eq_inv_of_mul_eq_one_right this)
  have hc : ∀ i : Fin n, c i.rev = -c i := by
    intro i
    simp only [c]
    rw [hvrev, WithZero.log_inv]
  obtain ⟨s, hs, hs'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ c i) (fun i => by
    rw [map_zpow₀, hσϖ, hc, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])
  have hsN : s ∈ N := _root_.GlobalTheory.torus_mem_normal L ϖ σ q n hU N hN hK hu c hc s hs
  have hvpow : ∀ i, Valued.v (ϖ ^ c i) = Valued.v (T i i) := by
    intro i
    rw [map_zpow₀, hϖ', ← WithZero.exp_zsmul, ← WithZero.exp_log (hv0 i)]
    simp [c]
  have hε : (((s⁻¹ * t : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => (ϖ ^ c i)⁻¹ * T i i) := by
    rw [Subgroup.coe_mul, Units.val_mul, hs', ← hTdef, hTd, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; simp
  have hI : Formalism.UG.P.fIwasawaInt (((s⁻¹ * t : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    intro i j
    rw [hε]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, map_mul, map_inv₀, hvpow, inv_mul_cancel₀ (hv0 i)]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero]; exact zero_le
  have hkK : s⁻¹ * t ∈ Formalism.UG.KU σ n := by
    have := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ (s⁻¹ * t)) hI
    have e : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ (s⁻¹ * t)) = s⁻¹ * t := Subtype.ext (Units.ext rfl)
    rwa [e] at this
  have e : t = s * (s⁻¹ * t) := by group
  rw [e]
  exact N.mul_mem hsN (hK hkK)

theorem borel_eq_diag_mul_unip : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (b : Formalism.UG.GU σ n), Formalism.UG.IsBorelU b → ∃ d u : Formalism.UG.GU σ n, (∀ i j : Fin n, i ≠ j → ((d : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) ∧ Formalism.UG.IsUnipU u ∧ b = d * u := by
  intro L _ _ σ n b hb
  obtain ⟨d, hd, hd'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ)
    (fun i => (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)
    (Formalism.UG.P.fSatake_unit_diag hb)
  have hne : ∀ i, (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
    intro i h0; have := Formalism.UG.P.fSatake_unit_diag hb i; rw [h0, map_zero, zero_mul] at this; exact zero_ne_one this
  have hu : (((d⁻¹ * b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ((((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)⁻¹) *
        (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [Subgroup.coe_mul, Units.val_mul, hd']
  refine ⟨d, d⁻¹ * b, fun i j hij => by rw [hd, Matrix.diagonal_apply_ne _ hij], ⟨fun i j hji => ?_, fun i => ?_⟩, by group⟩
  · rw [hu, Matrix.diagonal_mul, hb i j hji, mul_zero]
  · rw [hu, Matrix.diagonal_mul, inv_mul_cancel₀ (hne i)]

open Formalism.UG in
theorem frame {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q n : ℕ}
    (hU : IsUnramInv ϖ σ q) {J : GL (Fin n) L} (hJ : J ∈ GLint (Fin n) (intL L))
    (hh : ∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) :
    ∃ P ∈ GLint (Fin n) (intL L), cT σ (P : Matrix (Fin n) (Fin n) L) * (J : Matrix (Fin n) (Fin n) L) * P = antiJ L n := by
  obtain ⟨U, rfl⟩ := hJ
  let c := GlobalTheory.UnramDoubleCoset.intConj hU.2.1
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hU.1 x)
  let ι := (intL L).subtype
  let B : Matrix (Fin n) (Fin n) (intL L) := U
  have hB : cT c B = B := by
    ext i j
    show σ ((B j i : intL L) : L) = (B i j : L)
    exact hh j i
  obtain ⟨p, hp⟩ := GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hc (GlobalTheory.UnramDoubleCoset.exists_dvd_norm_sub_X hU) hB U.isUnit
  have hu : IsUnit B := U.isUnit
  have h2 : IsUnit (Polynomial.aeval B p) := isUnit_of_mul_isUnit_right (by rw [hp]; exact hu)
  obtain ⟨h, hh', eh⟩ := GlobalTheory.UnramDoubleCoset.exists_antiJ_frame hU n
  set K : GL (Fin n) L := bc ι h2.unit with hKdef
  have hK : (K : Matrix (Fin n) (Fin n) L) = (Polynomial.aeval B p).map ι := rfl
  have hJ : ((bc ι U : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = cT σ (K : Matrix (Fin n) (Fin n) L) * K := by
    rw [hK, GlobalTheory.UnitaryDoubleCoset.cT_map ι (c := c) (fun _ => rfl), ← Matrix.map_mul, hp]; rfl
  refine ⟨K⁻¹ * h, mul_mem (inv_mem ⟨_, rfl⟩) hh', ?_⟩
  rw [hJ, Units.val_mul, cT_mul, ← eh, Matrix.mul_one]
  have e1 : cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * cT σ (K : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  have e2 : (K : Matrix (Fin n) (Fin n) L) * ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv K
  calc cT σ (h : Matrix (Fin n) (Fin n) L) * cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (cT σ (K : Matrix (Fin n) (Fin n) L) * K) * (((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * h)
      = cT σ (h : Matrix (Fin n) (Fin n) L) * (cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * cT σ (K : Matrix (Fin n) (Fin n) L)) * ((K : Matrix (Fin n) (Fin n) L) * ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) * h := by
        simp only [Matrix.mul_assoc]
    _ = cT σ (h : Matrix (Fin n) (Fin n) L) * h := by rw [e1, e2, Matrix.mul_one, Matrix.mul_one]

open Formalism.UG in
theorem antiJ_case {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q n : ℕ}
    (hU : IsUnramInv ϖ σ q) (N : Subgroup (GU σ n)) (hN : N.Normal) (hK : KU σ n ≤ N) : N = ⊤ := by
  have h2 := unip_mem L ϖ σ q n hU N hN hK
  have h3 := diag_mem L ϖ σ q n hU N hN hK h2
  rw [eq_top_iff]
  intro g _
  obtain ⟨b, k, hb, hk, rfl⟩ := Formalism.UG.P.fIwasawa_iwasawa σ hU.1 hU.2.1 g
  obtain ⟨d, u, hd, hu, rfl⟩ := borel_eq_diag_mul_unip L σ n b hb
  exact N.mul_mem (N.mul_mem (h3 d hd) (h2 u hu)) (hK hk)

theorem normal_closure_hyp : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (J : GL (Fin n) L), Formalism.UG.IsUnramInv ϖ σ q → Odd q → J ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) → ∀ N : Subgroup (Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L)), N.Normal → (∀ g : Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L), (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → g ∈ N) → N = ⊤ := by
  intro L _ _ _ ϖ σ q n J hU hq hJ hh N hN hK
  obtain ⟨P, hP, eP⟩ := frame hU hJ hh
  have memφ : ∀ g : Formalism.UG.GU σ n, P * (g : GL (Fin n) L) * P⁻¹ ∈ Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L) := by
    intro g
    simpa using GlobalTheory.InertDoubleCoset.conj_mem_UJ σ (GlobalTheory.InertDoubleCoset.inv_frame σ eP) g.2
  have memψ : ∀ g : Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L), P⁻¹ * (g : GL (Fin n) L) * P ∈ Formalism.UG.GU σ n :=
    fun g => GlobalTheory.InertDoubleCoset.conj_mem_UJ σ eP g.2
  let φ : Formalism.UG.GU σ n →* Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L) :=
    { toFun := fun g => ⟨P * (g : GL (Fin n) L) * P⁻¹, memφ g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hK' : Formalism.UG.KU σ n ≤ N.comap φ := by
    intro k hk
    show φ k ∈ N
    apply hK
    show P * (k : GL (Fin n) L) * P⁻¹ ∈ _
    exact mul_mem (mul_mem hP (Subgroup.mem_subgroupOf.1 hk).2) (inv_mem hP)
  have htop := antiJ_case hU (N.comap φ) (hN.comap φ) hK'
  rw [eq_top_iff]
  intro g _
  have hm : (⟨P⁻¹ * (g : GL (Fin n) L) * P, memψ g⟩ : Formalism.UG.GU σ n) ∈ N.comap φ := by rw [htop]; trivial
  have e : φ ⟨P⁻¹ * (g : GL (Fin n) L) * P, memψ g⟩ = g := Subtype.ext (by
    show P * (P⁻¹ * (g : GL (Fin n) L) * P) * P⁻¹ = g
    group)
  rw [← e]
  exact hm

end GlobalTheory.NormalHyp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormDiscreteValuationField
section
open Matrix

namespace GlobalTheory.SmithValued

variable (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]

noncomputable def vNN : Valuation L NNReal :=
  (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).map
    { toMonoidWithZeroHom := WithZeroMulInt.toNNReal (e := 2) (by norm_num)
      monotone' := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num)).monotone }

theorem vNN_le_one_iff (x : L) : vNN L x ≤ 1 ↔ x ∈ Formalism.UG.intL L := by
  have h := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num)).le_iff_le
    (a := (Valued.v x : WithZero (Multiplicative ℤ))) (b := 1)
  rw [map_one] at h
  exact h

theorem vNN_integers : (vNN L).Integers ↥(Formalism.UG.intL L) := by
  refine ⟨Subtype.val_injective, ?_, ?_⟩
  · intro x
    exact (vNN_le_one_iff L _).2 x.2
  · intro r hr
    exact ⟨⟨r, (vNN_le_one_iff L _).1 hr⟩, rfl⟩

theorem exists_clear {ι : Type} (s : Finset ι) (f : ι → L) :
    ∃ c : L, c ≠ 0 ∧ c ∈ Formalism.UG.intL L ∧ ∀ i ∈ s, c * f i ∈ Formalism.UG.intL L := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, one_mem _, by simp⟩
  | insert a s _ ih =>
    obtain ⟨c, hc0, hc, hs⟩ := ih
    by_cases ha : f a ∈ Formalism.UG.intL L
    · refine ⟨c, hc0, hc, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact mul_mem hc ha
      · exact hs i hi
    · have h0 : f a ≠ 0 := by
        intro h; exact ha (h ▸ zero_mem _)
      have hinv : (f a)⁻¹ ∈ Formalism.UG.intL L := by
        rw [← vNN_le_one_iff] at ha ⊢
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ (not_le.1 ha).le
      refine ⟨(f a)⁻¹ * c, mul_ne_zero (inv_ne_zero h0) hc0, mul_mem hinv hc, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · have : (f i)⁻¹ * c * f i = c := by field_simp
        rw [this]; exact hc
      · rw [mul_assoc]; exact mul_mem hinv (hs i hi)

theorem smith_valued : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) (M : Matrix (Fin m) (Fin n) L),
    ∃ (P P' : Matrix (Fin m) (Fin m) L) (Q Q' : Matrix (Fin n) (Fin n) L) (d : Fin m → L),
      (∀ i j, P i j ∈ Formalism.UG.intL L) ∧ (∀ i j, P' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, Q i j ∈ Formalism.UG.intL L) ∧ (∀ i j, Q' i j ∈ Formalism.UG.intL L) ∧ P * P' = 1 ∧ Q * Q' = 1 ∧
      M = P * Matrix.of (fun (j : Fin m) (k : Fin n) => if (k : ℕ) = (j : ℕ) then d j else 0) * Q := by
  intro L _ _ m n M
  classical
  obtain ⟨c, hc0, -, hc⟩ := exists_clear L (Finset.univ : Finset (Fin m × Fin n))
    (fun p => M p.1 p.2)
  let A : Matrix (Fin m) (Fin n) ↥(Formalism.UG.intL L) :=
    Matrix.of fun i j => ⟨c * M i j, hc (i, j) (Finset.mem_univ _)⟩
  have diagonalize : ∀ (d n : ℕ) (X : Matrix (Fin d) (Fin n) ↥(Formalism.UG.intL L)),
      ∃ (P : Matrix (Fin d) (Fin d) ↥(Formalism.UG.intL L))
        (Q : Matrix (Fin n) (Fin n) ↥(Formalism.UG.intL L)) (a : Fin d → ↥(Formalism.UG.intL L)),
        IsUnit P.det ∧ IsUnit Q.det ∧
          ∀ j k, (P * X * Q) j k = if (k : ℕ) = (j : ℕ) then a j else 0 := by
    open ReciprocityTheory.PGsh.Up.Smith in
    intro d
    induction d with
    | zero =>
      intro n X
      exact ⟨1, 1, Fin.elim0, by simp, by simp, fun j => j.elim0⟩
    | succ d ih =>
      intro n X
      cases n with
      | zero => exact ⟨1, 1, 0, by simp, by simp, fun j k => k.elim0⟩
      | succ n =>
        let g : Fin (n + 1) → Fin (d + 1) → ↥(Formalism.UG.intL L) := fun j i => X i j
        obtain ⟨i₀, a, u, s, hu, -, hs, hz, hnz⟩ := exists_pivot (vNN_integers L) g
        by_cases ha : a = 0
        · have hX : X = 0 := by
            apply Matrix.ext
            intro i j
            exact congrFun (hz ha j) i
          exact ⟨1, 1, 0, by simp, by simp, fun j k => by simp [hX]⟩
        obtain ⟨j₀, hj₀, hs₀⟩ := hnz ha
        have hcol : ∀ i, X i j₀ = a * u i := fun i => congrFun hj₀ i
        have hrow : ∀ j, X i₀ j = a * s j := hs
        let B := (Vm i₀ u)ᵀ * X * Vm j₀ s
        have hB (i j) : B i j = if i = i₀ then (if j = j₀ then a else 0) else
            if j = j₀ then 0 else X i j - s j * (a * u i) := by
          dsimp only [B]
          rw [Matrix.mul_assoc, VmT_mul, mul_Vm, mul_Vm]
          by_cases hi : i = i₀ <;> by_cases hj : j = j₀
          · subst i
            subst j
            simp [hcol, hu]
          · subst i
            simp [hj, hrow, hs₀]
            ring
          · subst j
            simp [hi, hcol, hu]
            ring
          · simp only [hi, hj, ite_false, hcol, hrow, hu]
            ring
        let C := B.submatrix (piv i₀) (piv j₀)
        let Y := Matrix.of fun (i : Fin d) (j : Fin n) => C i.succ j.succ
        obtain ⟨P, Q, b, hP, hQ, hY⟩ := ih n Y
        let U : Matrix (Fin (d + 1)) (Fin (d + 1)) ↥(Formalism.UG.intL L) :=
          (piv i₀).toPEquiv.toMatrix
        let V : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥(Formalism.UG.intL L) :=
          (piv j₀).symm.toPEquiv.toMatrix
        have hC : U * B * V = C := by
          dsimp only [U, V, C]
          rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
          rfl
        have hrow₀ (j : Fin n) : C 0 j.succ = 0 := by
          simp [C, piv_zero, piv_succ, hB, Fin.succAbove_ne]
        have hcol₀ (i : Fin d) : C i.succ 0 = 0 := by
          simp [C, piv_zero, piv_succ, hB, Fin.succAbove_ne]
        obtain ⟨h00, h0j, hi0, hij⟩ := blockOne_mul_mul_blockOne P C Q hrow₀ hcol₀
        refine ⟨bd1 P * U * (Vm i₀ u)ᵀ, Vm j₀ s * V * bd1 Q, Fin.cons a b, ?_, ?_, ?_⟩
        · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, Matrix.det_transpose, det_Vm, mul_one]
          exact hP.mul (isUnit_det_perm _)
        · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, det_Vm, one_mul]
          exact (isUnit_det_perm _).mul hQ
        · have hfull : bd1 P * U * (Vm i₀ u)ᵀ * X * (Vm j₀ s * V * bd1 Q) =
              bd1 P * C * bd1 Q := by
            rw [← hC]
            simp only [B, Matrix.mul_assoc]
          intro i j
          rw [hfull]
          refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
          · rw [h00]
            simp [C, piv_zero, hB]
          · rw [h0j]
            simp
          · rw [hi0]
            simp
          · rw [hij, hY]
            simp [Fin.val_succ]
  obtain ⟨P, Q, a, hP, hQ, hD⟩ := diagonalize m n A
  let φ : ↥(Formalism.UG.intL L) →+* L := (Formalism.UG.intL L).subtype
  have hP1 : P⁻¹.map φ * P.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hP, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hQ1 : Q⁻¹.map φ * Q.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hQ, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hQ2 : Q.map φ * Q⁻¹.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hQ, Matrix.map_one _ (map_zero φ) (map_one φ)]
  refine ⟨P⁻¹.map φ, P.map φ, Q⁻¹.map φ, Q.map φ, fun j => c⁻¹ * (a j : L),
    fun i j => (P⁻¹ i j).2, fun i j => (P i j).2, fun i j => (Q⁻¹ i j).2, fun i j => (Q i j).2,
    hP1, hQ1, ?_⟩
  have hA : A.map φ = c • M := by
    ext i j; simp [A, φ]
  have hD' : Matrix.of (fun (j : Fin m) (k : Fin n) =>
      if (k : ℕ) = (j : ℕ) then c⁻¹ * (a j : L) else 0) = P.map φ * M * Q.map φ := by
    have h1 : (P * A * Q).map φ = c • (P.map φ * M * Q.map φ) := by
      rw [Matrix.map_mul, Matrix.map_mul, hA, Matrix.mul_smul, Matrix.smul_mul]
    have h2 : P.map φ * M * Q.map φ = c⁻¹ • (P * A * Q).map φ := by
      rw [h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h2]
    ext j k
    rw [Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, hD, smul_eq_mul]
    split_ifs
    · rfl
    · simp
  rw [hD', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP1, Matrix.one_mul, Matrix.mul_assoc, hQ2,
    Matrix.mul_one]

end GlobalTheory.SmithValued
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriEigenvectorJacquetQuotientNeZero
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

namespace GlobalTheory.TameIwahori.JacquetNonzero

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem jacquet_mk_ne_zero (hp : GlobalTheory.Published.DepthZeroJacquetInjective)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (π : Irr k n) (v : π.V) (θ : Fin n → kˣ →* ℂˣ) (hv : v ≠ 0) (hI : IsIwVec θ π.π v) :
    (Submodule.Quotient.mk v : Jacquet π.π (unipB k (Fin n))) ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.PointStabilizer.mk_ne_zero
  | exact _root_.GlobalTheory.PointStabilizer.mk_ne_zero
  | (apply _root_.GlobalTheory.PointStabilizer.mk_ne_zero <;> assumption)
  | (intros; apply _root_.GlobalTheory.PointStabilizer.mk_ne_zero <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PointStabilizer.mk_ne_zero <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PointStabilizer.mk_ne_zero ..)

end GlobalTheory.TameIwahori.JacquetNonzero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedSpecialOfUnitEigenStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_special_of_unit_eigen : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), x.mono0 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ‖α‖ = 1) → ∀ l : ℕ, (x.lpChar (WD.lpSp (h := h) l)).tempered := by
  first | exact @GlobalTheory.WeilDeligne.WD.tempered_lpChar_lpSp_of_mono0 | exact GlobalTheory.WeilDeligne.WD.tempered_lpChar_lpSp_of_mono0 | (intros; apply GlobalTheory.WeilDeligne.WD.tempered_lpChar_lpSp_of_mono0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → conjPl P ≠ P → UnrPl P χS → UnrPl P χT → VacFix ψ om P ∧ ∀ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ) (t : ℕ), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → (T.rank = S.rank + t → ∀ k, k ≤ T.rank → Match ψ om P (dualC (splitC S.rank fun j => if j ≤ k then (Ideal.absNorm P.asIdeal : ℂ) ^ ((S.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank)⁻¹ ^ k * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank) ^ j else 0)) (Finsupp.single (splitLab T.rank k) 1)) ∧ (S.rank = T.rank + t → ∀ k, k ≤ S.rank → Match ψ om P (dualC (Finsupp.single (splitLab S.rank k) 1)) (splitC T.rank fun j => if j ≤ k then (Ideal.absNorm P.asIdeal : ℂ) ^ ((T.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank)⁻¹ ^ k * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank) ^ j else 0)) := by
  first | exact @GlobalTheory.Hk3.SplitMatch.match_split | exact GlobalTheory.Hk3.SplitMatch.match_split | (intros; apply GlobalTheory.Hk3.SplitMatch.match_split <;> assumption)
end

