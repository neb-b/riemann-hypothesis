module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0562
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0849
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameUniformizerPower
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DepthZeroRankOneLabel

open ValuativeRel

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]

theorem val_lt_iff (y : w.adicCompletion E) : valuation (w.adicCompletion E) y < 1 ↔ ‖y‖ < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.lt_one_iff_lt_one, Valued.toNormedField.norm_lt_one_iff]

theorem val_le_iff (y : w.adicCompletion E) : valuation (w.adicCompletion E) y ≤ 1 ↔ ‖y‖ ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.le_one_iff_le_one, Valued.toNormedField.norm_le_one_iff]

theorem val_lt_of_mem {x : 𝓞 E} (hx : x ∈ w.asIdeal) :
    valuation (w.adicCompletion E) (algebraMap E (w.adicCompletion E) (x : E)) < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.lt_one_iff_lt_one]
  rw [adic_valued_algebraMap, RingOfIntegers.coe_eq_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_mem]
  exact hx

variable (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi in
theorem val_int_le (z : ℤ_[g]) : valuation (w.adicCompletion E) (i (z : ℚ_[g])) ≤ 1 :=
  (val_le_iff _).2 (GlobalTheory.TypeRec.Model.emb_le w g i.toRingHom hi _ z.2)

include hi in
theorem val_int_lt (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (z : ℤ_[g]) (hz : PadicInt.toZMod z = 0) :
    valuation (w.adicCompletion E) (i (z : ℚ_[g])) < 1 := by
  have h1 : z ∈ RingHom.ker (PadicInt.toZMod (p := g)) := hz
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h1
  obtain ⟨c, rfl⟩ := h1
  rw [PadicInt.coe_mul, map_mul, map_mul, PadicInt.coe_natCast, map_natCast]
  exact mul_lt_one_of_nonneg_of_lt_one_right (val_int_le i hi c) zero_le
    ((val_lt_iff _).2 (Formalism.BasicNotions.Examples₂.LocF.norm_l_lt w g hw))

include hi in
theorem exists_red (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hT : GlobalTheory.SplitWeil.IsTame μ) :
    ∃ θ : (ZMod g)ˣ →* ℂˣ, ∀ z : ℤ_[g]ˣ, θ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom z) =
      μ (Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom z)) := by
  have hs := IsLocalRing.surjective_units_map_of_local_ringHom (PadicInt.toZMod (p := g))
    (ZMod.ringHom_surjective _) (IsLocalHom.of_surjective _ (ZMod.ringHom_surjective _))
  let f : ℤ_[g]ˣ →* (ZMod g)ˣ := Units.map (PadicInt.toZMod (p := g)).toMonoidHom
  let φ : ℤ_[g]ˣ →* ℂˣ :=
    μ.comp ((Units.map i.toRingHom.toMonoidHom).comp (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom))
  have hker : f.ker ≤ φ.ker := fun z hz => by
    rw [MonoidHom.mem_ker] at hz ⊢
    apply hT
    have h1 : PadicInt.toZMod ((z : ℤ_[g]) - 1) = 0 := by
      have e := congrArg Units.val hz
      rw [map_sub, map_one, sub_eq_zero]
      exact e
    have := val_int_lt i hi hw ((z : ℤ_[g]) - 1) h1
    simpa [φ] using this
  exact ⟨f.liftOfSurjective hs ⟨φ, hker⟩, fun z => MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ, hker⟩ z⟩

end GlobalTheory.DepthZeroRankOneLabel

namespace GlobalTheory.DepthZeroRankOneLabel

open ValuativeRel GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem inflates_units (i : ℚ_[g] ≃+* w.adicCompletion E) (θ : (ZMod g)ˣ →* ℂˣ) (χ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hχ : GlobalTheory.SmGL.IsSmoothChar χ)
    (hθ : ∀ z : ℤ_[g]ˣ, θ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom z) =
      χ (Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom z))) :
    GlobalTheory.SerSys.TameGen.Inflates ((GlobalTheory.SmGL.IrrRep.det (Fin 1) χ hχ).ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom))
      (GlobalTheory.Published.DepthZeroModel.tauOne θ) := by
  refine ⟨LinearMap.id, fun e => (one_ne_zero : (1 : ℂ) ≠ 0) (LinearMap.congr_fun e (1 : ℂ)), fun k (v : ℂ) => ?_⟩
  have h1 : Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.inc g 1 k) =
      Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
    ext; simp [GlobalTheory.GLp.inc, RingHom.map_det]
  have h2 : Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 k) =
      Units.map (PadicInt.toZMod (p := g)).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
    ext; simp [GlobalTheory.GLp.red, RingHom.map_det]
  have e2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k)) =
      Units.map i.toRingHom.toMonoidHom (Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.inc g 1 k)) := by
    ext; simp
  change ((θ (Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 k)) : ℂˣ) : ℂ) • v =
    ((χ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k))) : ℂˣ) : ℂ) • v
  rw [e2, h1, h2, hθ]

end GlobalTheory.DepthZeroRankOneLabel

namespace GlobalTheory.DepthZeroRankOneLabel

open GlobalTheory.TameRes

theorem residue_of_cong {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime] (hAP : IsPlaceOver (F := E) A P)
    (hN : normV P = g) (hgP : ((g : ℕ) : 𝓞 E) ∈ P.asIdeal) (hgP2 : ((g : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (σ : G E Ω) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g)
    (hσ : σ ∈ Ine (F := E) A) (hζ : IsGenSys ζ) (hT : TameCoupled A κ σ ζ) (u ϖ : 𝓞 E) (π : Ω)
    (hϖ : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2) (hπ : π ^ (normV P - 1) = algebraMap E Ω (ϖ : E))
    (hv : A.valuation (σ π / π - algebraMap E Ω (u : E)) < 1) :
    ∃ a : ℕ, a.Coprime g ∧ u - (a : 𝓞 E) ∈ P.asIdeal ∧
      algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (a : ZMod g) = ζ 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hgp : g.Prime := Fact.out
  have hg2 : 2 ≤ g := hgp.two_le
  have hgΩ : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hgp.ne_zero
  rw [hN] at hπ

  have hg1 : 0 < g - 1 := by omega
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((g : ℕ) : Ω) hg1
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_pow hg1.ne'] at hy; exact hgΩ hy.symm
  have hTy : redThrough A κ (σ y / y) = ζ 1 := hT 1 one_pos y (by rw [pow_one]; exact hy)
  have hϖ0 : algebraMap E Ω (ϖ : E) ≠ 0 := by
    rw [ne_eq, map_eq_zero, RingOfIntegers.coe_eq_zero_iff]
    rintro rfl; exact hϖ2 (zero_mem _)
  have hπ0 : π ≠ 0 := by rintro rfl; rw [zero_pow hg1.ne'] at hπ; exact hϖ0 hπ.symm
  have hϖg : A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation ((g : ℕ) : Ω) := by
    have e : ((g : ℕ) : Ω) = algebraMap E Ω (((g : ℕ) : 𝓞 E) : E) := by simp
    rw [e]
    exact le_antisymm (val_le_of_unif hAP hϖ hgP hgP2) (val_le_of_unif hAP hgP hϖ hϖ2)
  have hπy : A.valuation π = A.valuation y := by
    have h1 : A.valuation π ^ (g - 1) = A.valuation y ^ (g - 1) := by
      rw [← map_pow, ← map_pow, hπ, hy, hϖg]
    exact (pow_left_inj₀ zero_le zero_le hg1.ne').mp h1
  have hvy0 : A.valuation y ≠ 0 := by simpa using hy0
  have hw1 : A.valuation (π / y) = 1 := by rw [map_div₀, hπy, div_self hvy0]
  have hwσ : A.valuation (σ (π / y) - π / y) < 1 := hσ.2 _ hw1.le
  have hσy0 : σ y ≠ 0 := fun h => hy0 (σ.injective (by rw [h, map_zero]))
  have key : σ π / π - σ y / y = (σ y / y) * ((σ (π / y) - π / y) / (π / y)) := by
    rw [map_div₀]
    field_simp
  have hq : A.valuation (σ y / y) ≤ 1 := (A.valuation_le_one_iff _).2 (tameQuot_mem A σ hg1 hgΩ hy)
  have h1 : A.valuation (σ π / π - σ y / y) < 1 := by
    rw [key, map_mul, map_div₀ A.valuation (σ (π / y) - π / y), hw1, div_one]
    calc A.valuation (σ y / y) * A.valuation (σ (π / y) - π / y)
        ≤ 1 * A.valuation (σ (π / y) - π / y) := by gcongr
      _ < 1 := by rw [one_mul]; exact hwσ

  obtain ⟨a, -, hua⟩ := exists_nat_sub_mem P g hN hgP u
  have hua' : A.valuation (algebraMap E Ω (u : E) - (a : Ω)) < 1 := by
    have := (hAP (u - (a : 𝓞 E))).2 hua
    simpa using this
  have h3 : A.valuation (σ y / y - (a : Ω)) < 1 := by
    have e : σ y / y - (a : Ω) = -(σ π / π - σ y / y) + (σ π / π - algebraMap E Ω (u : E)) +
        (algebraMap E Ω (u : E) - (a : Ω)) := by ring
    rw [e]
    refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ?_ hv) hua'
    rw [Valuation.map_neg]; exact h1
  have haA : (a : Ω) ∈ A := by exact_mod_cast (natCast_mem A a)
  have hred : redThrough A κ (σ y / y) = (a : Formalism.CyclotomicNorms.Fbar g) := by
    rw [redThrough_eq_of_val_sub κ (tameQuot_mem A σ hg1 hgΩ hy) haA h3]
    unfold redThrough
    rw [dite_eq_left haA]
    have : (⟨(a : Ω), haA⟩ : A) = (a : A) := Subtype.ext (by simp)
    rw [this, map_natCast, map_natCast]
  have hz : ζ 1 = (a : Formalism.CyclotomicNorms.Fbar g) := by rw [← hTy, hred]
  refine ⟨a, ?_, hua, by rw [map_natCast, hz]⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hgp]
  intro hd
  have h0 : (a : Formalism.CyclotomicNorms.Fbar g) = 0 := (CharP.cast_eq_zero_iff (Formalism.CyclotomicNorms.Fbar g) g a).2 hd
  have ho := (hζ 1 one_pos).1
  rw [hz, h0, pow_one] at ho
  have hz0 : orderOf (0 : Formalism.CyclotomicNorms.Fbar g) = 0 := by
    rw [orderOf_eq_zero_iff']
    intro n hn
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hn)]
    exact zero_ne_one
  omega

end GlobalTheory.DepthZeroRankOneLabel

namespace GlobalTheory.DepthZeroRankOneLabel

def labDatum {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ) : GlobalTheory.GLq.LabelDatum g where
  teich := t
  teich_inj := ht
  gen := ζ
  gen_order d hd := (hζ d hd).1
  gen_norm d e hd he := (hζ d hd).2 (d * e) (dvd_mul_right d e) (Nat.mul_pos hd he)

end GlobalTheory.DepthZeroRankOneLabel

end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLabelRootOfHarishChandraConstituent
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GLq.DetSplit

open GlobalTheory.GLq Polynomial
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem ip_hc_mono_left (m k n : ℕ) (hn : n = m + k) (ψ : Gn g n → ℂ) (hψ : IsIrr ψ)
    (α A : Gn g m → ℂ) (hα : IsIrr α) (hA : IsChar A) (hαA : ip α A ≠ 0)
    (β : Gn g k → ℂ) (hβ : IsChar β) (h : ip ψ (hc m k α β n) ≠ 0) : ip ψ (hc m k A β n) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hα hA hαA
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_left]
  have hc := (_root_.GlobalTheory.GLq.HCChar.hc_isChar_and_res_decomp g m k n hn).1
  exact GlobalTheory.GLq.DetRoot.ip_add_ne_zero hψ (hc α β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hα) hβ) (hc R β hR hβ) h

theorem ip_hc_mono_right (m k n : ℕ) (hn : n = m + k) (ψ : Gn g n → ℂ) (hψ : IsIrr ψ)
    (α : Gn g m → ℂ) (hα : IsChar α) (β B : Gn g k → ℂ) (hβ : IsIrr β) (hB : IsChar B) (hβB : ip β B ≠ 0)
    (h : ip ψ (hc m k α β n) ≠ 0) : ip ψ (hc m k α B n) ≠ 0 := by
  obtain ⟨R, hR, he⟩ := GlobalTheory.GLq.LabelMul.exists_add_of_ip_ne_zero hβ hB hβB
  rw [he, GlobalTheory.GLq.LabelMul.hc_add_right]
  have hc := (_root_.GlobalTheory.GLq.HCChar.hc_isChar_and_res_decomp g m k n hn).1
  exact GlobalTheory.GLq.DetRoot.ip_add_ne_zero hψ (hc α β hα (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβ)) (hc α R hα hR) h

theorem hcL_append_of (K₁ K₂ : List (Pc g)) (h₁ : ∀ q ∈ K₁, IsCusp q.2) (h₂ : ∀ q ∈ K₂, IsCusp q.2)
    (m₁ m₂ n : ℕ) (e₁ : degL K₁ = m₁) (e₂ : degL K₂ = m₂) (hn : n = m₁ + m₂) :
    hcL (K₁ ++ K₂) n = hc m₁ m₂ (hcL K₁ m₁) (hcL K₂ m₂) n := by
  subst e₁ e₂
  exact GlobalTheory.GLq.LabelMul.hcL_append K₁ K₂ (fun q hq => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (h₁ q hq))
    (fun q hq => GlobalTheory.GLq.IpCuspProd.isChar_of_isCusp (h₂ q hq)) n hn

theorem root_of_constituent : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r a c : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (u : ZMod p) (f : Polynomial (ZMod p)) (ψ : GlobalTheory.GLq.Gn p r → ℂ) (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ) (β : GlobalTheory.GLq.Gn p c → ℂ) (σ : GlobalTheory.GLq.Gn p a → ℂ), r = a + 1 + c → GlobalTheory.GLq.IsIrr ψ → GlobalTheory.GLq.IsIrr α → GlobalTheory.GLq.IsIrr β → GlobalTheory.GLq.IsIrr σ → GlobalTheory.GLq.HasLabel L ψ f → GlobalTheory.GLp.IsCharLab L θ u → GlobalTheory.GLq.ip ψ (GlobalTheory.GLq.hc (a + 1) c α β r) ≠ 0 → GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 → f.IsRoot u := by
  intro p _ L r a c θ u f ψ α β σ hr hψ hα hβ hσ hL hlab hψαβ hασ
  obtain ⟨Q, hQ, hQd, rfl, hQi⟩ := hL
  obtain ⟨Kσ, hKσ, hKσd, hKσi⟩ := GlobalTheory.GLq.SuppCusp.exists_cusp_list p a σ hσ
  obtain ⟨Kβ, hKβ, hKβd, hKβi⟩ := GlobalTheory.GLq.SuppCusp.exists_cusp_list p c β hβ
  have hθI : IsIrr (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    GlobalTheory.GLq.LabelDet.isIrr_hom (θ.comp Matrix.GeneralLinearGroup.det)
  have hθC := GlobalTheory.GLq.LabelMul.isChar_of_isIrr hθI
  have hθcusp : IsCusp (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) :=
    ⟨one_pos, hθI, fun a h1 h2 => by omega⟩
  have hQc : ∀ q ∈ Q.map Prod.snd, IsCusp q.2 := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    exact (hQ q' hq').2.1
  have hA := GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hQc _ hQd
  have fin : ∀ K' : List (Pc p), (Q.map Prod.snd).Perm K' →
      (⟨1, fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)⟩ : Pc p) ∈ K' →
      ((Q.map Prod.fst).prod).IsRoot u := by
    intro K' hp hm
    obtain ⟨⟨P, s⟩, hq, hs⟩ := List.mem_map.1 (hp.mem_iff.2 hm)
    dsimp only at hs
    subst hs
    have hP := GlobalTheory.GLq.DetRoot.eq_of_isCuspOf_det L θ u hlab P (hQ _ hq)
    have hdvd : P ∣ (Q.map Prod.fst).prod := List.dvd_prod (List.mem_map.2 ⟨_, hq, rfl⟩)
    exact Polynomial.IsRoot.dvd (by rw [hP]; exact root_X_sub_C.2 rfl) hdvd
  generalize (fun y : Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) = θd at hθI hθC hθcusp hασ fin
  have h1 := GlobalTheory.GLq.DetRoot.ip_hc_left a α hα σ hσ θd hθC Kσ hKσ hKσd hKσi hασ
  have hT : ∀ q ∈ [(⟨1, θd⟩ : Pc p)], IsCusp q.2 := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hθcusp
  have hTd : degL [(⟨1, θd⟩ : Pc p)] = 1 := by simp [degL]
  have eα : hcL (Kσ ++ [(⟨1, θd⟩ : Pc p)]) (a + 1) = hc a 1 (hcL Kσ a) θd (a + 1) := by
    rw [hcL_append_of Kσ _ hKσ hT a 1 (a + 1) hKσd hTd rfl,
      GlobalTheory.GLq.IpCuspProd.hcL_single 1 θd (GlobalTheory.GLq.IpCuspProd.isClass_of_isChar hθC)]
  rw [← eα] at h1
  have hKα : ∀ q ∈ Kσ ++ [(⟨1, θd⟩ : Pc p)], IsCusp q.2 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hKσ q hq
    · exact hT q hq
  have hKαd : degL (Kσ ++ [(⟨1, θd⟩ : Pc p)]) = a + 1 := by
    rw [GlobalTheory.GLq.LabelMul.degL_append, hKσd, hTd]
  have hAα := GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKα _ hKαd
  have h2 := ip_hc_mono_left (a + 1) c r hr ψ hψ α _ hα hAα h1 β (GlobalTheory.GLq.LabelMul.isChar_of_isIrr hβ) hψαβ
  have h3 := ip_hc_mono_right (a + 1) c r hr ψ hψ _ hAα β (hcL Kβ c) hβ
    (GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKβ _ hKβd) hKβi h2
  rw [← hcL_append_of _ Kβ hKα hKβ (a + 1) c r hKαd hKβd hr] at h3
  have hKall : ∀ q ∈ (Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ, IsCusp q.2 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hKα q hq
    · exact hKβ q hq
  have hKd : degL ((Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ) = r := by
    rw [GlobalTheory.GLq.LabelMul.degL_append, hKαd, hKβd, hr]
  have hB := GlobalTheory.GLq.DetRoot.isChar_hcL_cusp _ hKall _ hKd
  have hAB := GlobalTheory.GLq.DetRoot.ip_ne_zero_of_common hψ hA hB hQi h3
  refine fin ((Kσ ++ [(⟨1, θd⟩ : Pc p)]) ++ Kβ) ?_ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))))
  by_contra hn
  exact hAB ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp p _ _ _ hQd hKd hQc hKall).1 hn)

end GlobalTheory.GLq.DetSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneDualTransportMonodromyDimWild
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne.ConjDual

theorem valuation_lt_one_iff {Ω : Type} [Field Ω] {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω)
    (hA : ∀ y, y ∈ A ↔ c y ∈ A') (y : Ω) : A.valuation y < 1 ↔ A'.valuation (c y) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, hA, map_inv₀,
    EmbeddingLike.map_eq_zero_iff]

theorem tame_dual {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {a : WDRep h V}
    (ha : a.Tame) : a.dual.Tame := by
  intro σ hσ
  have h1 : a.ρ σ⁻¹ = 1 := ha σ⁻¹ ((Wild E A).inv_mem hσ)
  rw [WDRep.dual_ρ, h1]
  ext
  simp

theorem transport_dual {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)}
    {h : IsPlaceOver A w} {h' : IsPlaceOver A' w'} (s : E → E) (c : Ω ≃+* Ω)
    (hc : ∀ x : E, c (algebraMap E Ω x) = algebraMap E Ω (s x))
    (hA : ∀ y, y ∈ A ↔ c y ∈ A') (x : WD h) (x' : WD h') (n : ℕ)
    (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ))
    (hb : WD.mk b = x.lpDual) (hb' : WD.mk b' = x') (hN : b.N = b'.N)
    (hρ : ∀ (τ : Weil h) (τ' : Weil h'),
      (∀ z, c ((τ : G E Ω) z) = (τ' : G E Ω) (c z)) → b.ρ τ = b'.ρ τ') :
    (x.mono0 → x'.mono0) ∧ x'.lpDim = x.lpDim ∧ (x.tame → x'.tame) := by
  subst hb'
  induction x using WD.ind with
  | hP m a =>
    rw [WD.lpDual_mk] at hb
    refine ⟨fun h0 => ?_, ?_, fun h0 => ?_⟩
    · rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0 ⊢
      rw [← hN, ← WD.monodromyZero_ofWeilDeligneRepClass_iff, hb, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.dual_N, h0]
      ext
      simp
    · have h1 := congrArg WD.lpDim hb
      rw [WD.lpDim_mk, WD.lpDim_mk, Subspace.dual_finrank_eq] at h1
      rw [WD.lpDim_mk, WD.lpDim_mk, h1]
    · rw [WD.tame_mk] at h0 ⊢
      have h1 : b.Tame := by
        rw [← WD.tame_mk, hb, WD.tame_mk]
        exact tame_dual h0
      intro τ' hτ'
      let σ : G E Ω :=
        { (c.trans ((τ' : G E Ω) : Ω ≃+* Ω)).trans c.symm with
          commutes' := fun r => by
            show c.symm ((τ' : G E Ω) (c (algebraMap E Ω r))) = _
            rw [hc, AlgEquiv.commutes, ← hc, RingEquiv.symm_apply_apply] }
      have hσ : ∀ z, c (σ z) = (τ' : G E Ω) (c z) := fun z => c.apply_symm_apply _
      have hw : σ ∈ Wild E A := fun y hy => by
        rw [valuation_lt_one_iff c hA, map_sub, map_div₀, map_one, hσ]
        exact hτ' _ ((_root_.map_ne_zero c).2 hy)
      rw [← hρ ⟨σ, Ine_le_Weil h (Wild_le_Ine hw)⟩ τ' hσ]
      exact h1 _ hw

theorem mono_dim_wild : ∀ (D : D7) (w w' : PlE D.host) (c : D.nd.Om ≃+* D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) →
    (∀ y, y ∈ D.nd.plOm.1 w ↔ c y ∈ D.nd.plOm.1 w') →
    ∀ (x : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w)) (x' : GlobalTheory.WeilDeligne.WD (D.nd.plOm.2 w')) (n : ℕ)
      (b : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w) (Fin n → ℂ)) (b' : GlobalTheory.WeilDeligne.WDRep (D.nd.plOm.2 w') (Fin n → ℂ)),
    GlobalTheory.WeilDeligne.WD.mk b = x.lpDual → GlobalTheory.WeilDeligne.WD.mk b' = x' → b.N = b'.N →
    (∀ (τ : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w)) (τ' : GlobalTheory.WeilDeligne.Weil (D.nd.plOm.2 w')),
        (∀ z, c ((τ : GE D.nd) z) = (τ' : GE D.nd) (c z)) → b.ρ τ = b'.ρ τ') →
    (x.mono0 → x'.mono0) ∧ x'.lpDim = x.lpDim ∧
    ((∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), σ ∈ wildSet D.nd (D.nd.plOm.1 w) → x.inePol σ = (X - 1) ^ x.lpDim) →
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w'), σ ∈ wildSet D.nd (D.nd.plOm.1 w') → x'.inePol σ = (X - 1) ^ x'.lpDim) := by
  intro D w w' c hc hA x x' n b b' hb hb' hN hρ
  obtain ⟨h1, h2, h3⟩ := transport_dual (fun y => D.host.conj y) c hc hA x x' n b b' hb hb' hN hρ
  refine ⟨h1, h2, fun H σ _ hσ => ?_⟩
  exact (WD.tame_iff_inePol x').mp (h3 ((WD.tame_iff_inePol x).mpr
    fun τ hτ => H τ (Wild_le_Ine hτ) hτ)) σ hσ

end GlobalTheory.WeilDeligne.ConjDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDiagonalUniformizerEqZeroOfNotAntitoneStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_diagonalUniformizer_eq_zero_of_not_antitone : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (w : HeightOneSpectrum (𝓞 E)), w ∉ S →
    (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), IsUnifV E w (ϖ w : w.adicCompletion E) →
    ∀ (W : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, W (g * finGL E (m + 1) κ) = W g) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ)), ¬ Antitone (l w) →
    ∀ p : GA E (m + 1), Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = 1 →
    W (p * GlobalTheory.CellDec.tl (m + 1) ϖ l) = 0 := by
  first | exact @GlobalTheory.CellVanish.eq_zero_of_not_antitone | exact GlobalTheory.CellVanish.eq_zero_of_not_antitone | (intros; apply GlobalTheory.CellVanish.eq_zero_of_not_antitone <;> assumption)
end

