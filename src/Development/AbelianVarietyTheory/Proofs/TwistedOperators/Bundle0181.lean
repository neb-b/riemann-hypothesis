module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterFiniteOrderValuesInField
section
namespace HeckeCharacterValueBounds
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.CompanionTheory.CharValues

open Formalism.L2.Host

section General

variable {E : Type} [Field E] [NumberField E]

theorem exp_lt_one (m : ℕ) : (WithZero.exp (-((m : ℤ) + 1)) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private theorem valued_v_algebraMap_adicCompletion' (v : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (v.adicCompletion E) a) = v.valuation E a := by
  first
    | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
    | (rw [HeightOneSpectrum.algebraMap_adicCompletion]; exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a)

theorem locK_eq_of_level (χ : HChar E) {v : HeightOneSpectrum (𝓞 E)} {m : ℕ} (h : χ.LevelLe v m) (x y : Eˣ)
    (hxy : v.valuation E ((y : E) - x) ≤ WithZero.exp (-((m : ℤ) + 1)) * v.valuation E (x : E)) :
    χ.locK v y = χ.locK v x := by
  have hx0 : (x : E) ≠ 0 := x.ne_zero
  have hv0 : v.valuation E (x : E) ≠ 0 := ((v.valuation E).ne_zero_iff).mpr hx0

  have hd : ((y * x⁻¹ : Eˣ) : E) - 1 = ((y : E) - x) * (x : E)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ hx0]
  have hle : v.valuation E (((y * x⁻¹ : Eˣ) : E) - 1) ≤ WithZero.exp (-((m : ℤ) + 1)) := by
    rw [hd, map_mul, map_inv₀]
    calc v.valuation E ((y : E) - x) * (v.valuation E (x : E))⁻¹
        ≤ WithZero.exp (-((m : ℤ) + 1)) * v.valuation E (x : E) * (v.valuation E (x : E))⁻¹ := by
          first | gcongr | exact mul_le_mul_right' hxy _
      _ = WithZero.exp (-((m : ℤ) + 1)) := by rw [mul_assoc, mul_inv_cancel₀ hv0, mul_one]
  have hlt : v.valuation E (((y * x⁻¹ : Eˣ) : E) - 1) < v.valuation E 1 := by
    rw [map_one]
    exact lt_of_le_of_lt hle (exp_lt_one m)
  have hu : v.valuation E ((y * x⁻¹ : Eˣ) : E) = 1 := ((v.valuation E).map_eq_of_sub_lt hlt).trans (map_one _)

  have hA : IsUnitAt v (atFin v (y * x⁻¹)) := by
    show Valued.v (algebraMap E (v.adicCompletion E) ((y * x⁻¹ : Eˣ) : E)) = 1
    rw [valued_v_algebraMap_adicCompletion']
    exact hu
  have hB : Valued.v (((atFin v (y * x⁻¹) : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1) ≤
      WithZero.exp (-(m : ℤ)) := by
    show Valued.v (algebraMap E (v.adicCompletion E) ((y * x⁻¹ : Eˣ) : E) - 1) ≤ _
    rw [← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, valued_v_algebraMap_adicCompletion']
    exact le_trans hle (WithZero.exp_le_exp.mpr (by omega))
  have h1 : χ.locK v (y * x⁻¹) = 1 := h _ hA hB
  calc χ.locK v y = χ.locK v (y * x⁻¹ * x) := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = χ.locK v x := by rw [map_mul, h1, one_mul]

theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 E))) (t : HeightOneSpectrum (𝓞 E) → 𝓞 E) (m : HeightOneSpectrum (𝓞 E) → ℕ)
    (ht : ∀ v, t v ≠ 0) : ∃ y : 𝓞 E, ∀ v ∈ S,
      v.valuation E ((y : E) - (t v : E)) ≤ WithZero.exp (-((m v : ℤ) + 1)) * v.valuation E (t v : E) := by
  classical

  have hk : ∀ v : HeightOneSpectrum (𝓞 E),
      WithZero.exp (WithZero.log (v.intValuation (t v))) = v.intValuation (t v) :=
    fun v => WithZero.exp_log (v.intValuation_ne_zero _ (ht v))
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => ((m v : ℤ) + 1 - WithZero.log (v.intValuation (t v))).toNat)
    (fun v _ => Ideal.prime_of_isPrime v.ne_bot v.isPrime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))
    (fun v => t v.1)
  refine ⟨y, fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem (y - t v) _).mpr (hy v hv)
  have h2 : v.valuation E ((y : E) - (t v : E)) = v.intValuation (y - t v) := by
    have h := v.valuation_of_algebraMap (K := E) (y - t v)
    first
      | (push_cast at h; exact h)
      | exact h
      | simpa using h
  have h3 : v.valuation E (t v : E) = v.intValuation (t v) := v.valuation_of_algebraMap (K := E) (t v)
  rw [h2, h3, ← hk v, ← WithZero.exp_add]
  refine le_trans h1 (WithZero.exp_le_exp.mpr ?_)
  have := Int.self_le_toNat ((m v : ℤ) + 1 - WithZero.log (v.intValuation (t v)))
  omega

private theorem exp_neg_succ_mul_lt_self (m : ℕ) {b : WithZero (Multiplicative ℤ)} (hb : b ≠ 0) :
    WithZero.exp (-((m : ℤ) + 1)) * b < b := by
  rw [← WithZero.exp_log hb, ← WithZero.exp_add, WithZero.exp_lt_exp]
  omega

theorem locK_mem (χ : HChar E) (G : Subgroup ℂˣ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (hunr : ∀ v, v ∉ T → χ.UnrAt v) (hval : ∀ v, v ∉ T → χ.val v ∈ G)
    (hinf : ∀ k, χ.inf k ∈ G) (P : HeightOneSpectrum (𝓞 E)) (x : Eˣ) : χ.locK P x ∈ G := by
  classical
  choose m hm using GlobalTheory.Mem.UnrAe.exists_levelLe χ

  have key : ∀ a : 𝓞 E, a ≠ 0 → ∀ k : Eˣ, (k : E) = (a : E) → χ.locK P k ∈ G := by
    intro a ha k hk

    obtain ⟨y, hy⟩ := exists_approx (insert P T) (fun v => if v = P then a else 1) m
      (fun v => by by_cases h : v = P <;> simp [h, ha])
    have hyP : P.valuation E ((y : E) - (a : E)) ≤ WithZero.exp (-((m P : ℤ) + 1)) * P.valuation E (a : E) := by
      simpa using hy P (Finset.mem_insert_self P T)
    have hva : P.valuation E (a : E) ≠ 0 := by
      rw [(P.valuation E).ne_zero_iff]
      intro h0
      exact ha (RingOfIntegers.ext (by rw [h0]; rfl))
    have hy0 : (y : E) ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg] at hyP
      exact absurd hyP (not_le.mpr (exp_neg_succ_mul_lt_self (m P) hva))
    set ky : Eˣ := Units.mk0 (y : E) hy0 with hky
    have hone : ∀ v ∈ insert P T, v ≠ P → χ.locK v ky = 1 := by
      intro v hv hvP
      have h1 : v.valuation E ((ky : E) - ((1 : Eˣ) : E)) ≤
          WithZero.exp (-((m v : ℤ) + 1)) * v.valuation E ((1 : Eˣ) : E) := by
        simpa [hvP, hky] using hy v hv
      rw [locK_eq_of_level χ (hm v) 1 ky h1, map_one]
    have hPk : χ.locK P ky = χ.locK P k := by
      apply locK_eq_of_level χ (hm P) k ky
      simpa [hky, hk] using hyP

    have hS : ∀ v, v ∉ insert P T → χ.UnrAt v := fun v hv => hunr v (fun h => hv (Finset.mem_insert_of_mem h))
    have hPR := GlobalTheory.TypeValues.productRule χ (insert P T) hS ky
    rw [Finset.prod_eq_single_of_mem P (Finset.mem_insert_self P T) hone] at hPR
    have hF : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ insert P T), χ.val v ^ ordF v ky) ∈ G :=
      finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun v =>
        finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun hv =>
          G.zpow_mem (hval v fun h => hv (Finset.mem_insert_of_mem h)) _
    have h1 := G.one_mem
    rw [← hPR] at h1
    rw [← hPk]
    exact (G.mul_mem_cancel_left (hinf ky)).mp ((G.mul_mem_cancel_right hF).mp h1)

  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 E) (x : E)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective (𝓞 E) E
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact x.ne_zero hab.symm
  have haE : algebraMap (𝓞 E) E a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha0
  have hbE : algebraMap (𝓞 E) E b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
  have hx : x = Units.mk0 _ haE * (Units.mk0 _ hbE)⁻¹ := by
    ext
    rw [← hab, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, div_eq_mul_inv]
  rw [hx, map_mul, map_inv]
  exact G.mul_mem (key a ha0 _ rfl) (G.inv_mem (key b hb0 _ rfl))

end General

theorem main : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (L : Type) [Field L] (σ : L →+* ℂ), ChrEq c χ → 0 < n → χ.OrderDvd n → χ.ValuesIn 0 σ → ∀ x : (AE D)ˣ, ∃ y : Lˣ, σ y = (c x : ℂ) := by
  intro D c χ n L _ σ hc hn ho hv x
  classical
  have hfin := GlobalTheory.Mem.UnrAe.finite_ramified χ
  have hunr : ∀ v, v ∉ hfin.toFinset → χ.UnrAt v := fun v hv => by
    by_contra h
    exact hv (hfin.mem_toFinset.mpr h)
  have hval : ∀ v, v ∉ hfin.toFinset → χ.val v ∈ GlobalTheory.TameVal.unitsIn σ.fieldRange := by
    intro v hv'
    obtain ⟨y, hy⟩ := hv v (hunr v hv')
    have hw : χ.valTw 0 v = ((χ.val v : ℂˣ) : ℂ) := by simp [HChar.valTw]
    exact RingHom.mem_fieldRange.mpr ⟨y, hy.trans hw⟩
  have hinf : ∀ k, χ.inf k ∈ GlobalTheory.TameVal.unitsIn σ.fieldRange := fun k => by
    rw [GlobalTheory.TypeValues.inf_eq_one χ hn ho k]
    exact Subgroup.one_mem _
  have hM : ∀ P k, ((χ.locK P k : ℂˣ) : ℂ) ∈ σ.fieldRange := fun P k =>
    locK_mem χ (GlobalTheory.TameVal.unitsIn σ.fieldRange) hfin.toFinset hunr hval hinf P k
  obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp (GlobalTheory.TwistValues.char_mem c χ hc hn ho σ.fieldRange hM x)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact Circle.coe_ne_zero _ hy.symm
  exact ⟨Units.mk0 y hy0, hy⟩

end GlobalTheory.CompanionTheory.CharValues

end

end

end HeckeCharacterValueBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
theorem _root_.GlobalTheory.Adopt.heckeCharacter_finiteOrder_values_in_field : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (n : ℕ) (L : Type) [Field L] (σ : L →+* ℂ), ChrEq c χ → 0 < n → χ.OrderDvd n → χ.ValuesIn 0 σ → ∀ x : (AE D)ˣ, ∃ y : Lˣ, σ y = (c x : ℂ) := by
  intro D c χ n L _ σ h₁ h₂ h₃ h₄ x
  exact HeckeCharacterValueBounds.GlobalTheory.CompanionTheory.CharValues.main D c χ n L σ h₁ h₂ h₃ h₄ x

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.Grow GlobalTheory.Size

namespace GlobalTheory.Chain.LiftConv

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}

theorem thetaKO_left (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (g : GA D V) :
    ∀ γ ∈ GQ W, ∀ h, thetaKO ω g (γ * h) f = thetaKO ω g h f := by
  intro γ hγ h

  have hsplit : ((g, γ * h) : GA D V × GA D W) = (1, γ) * (g, h) := by
    ext <;> simp
  have hpres : IsThetaFunO ψ V W (ω (g, h) f) := hω.om_pres _ _ hf
  unfold thetaKO
  rw [hsplit, map_mul, Module.End.mul_apply]
  exact hω.om_aut 1 (one_mem _) γ hγ _ hpres

theorem thetaKO_continuous (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (g : GA D V) :
    Continuous fun h => thetaKO ω g h f := by

  have hpair : Continuous fun h : GA D W => ((g, h) : GA D V × GA D W) := by fun_prop
  unfold thetaKO
  exact (hω.om_cont f hf 0).comp hpair

theorem thetaKO_modGrowth (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D) (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (hf : IsThetaFunO ψ V W f) (g : GA D V) : ModGrowth W fun h => thetaKO ω g h f := by
  obtain ⟨A, d, hAd⟩ := hG V.rank W.rank
  obtain ⟨U, hUo, hfU⟩ := GlobalTheory.Size.isTheta_iff_level.mp hf
  obtain ⟨μ, 𝓕, hcov⟩ := GlobalTheory.Size.exists_isCovolOne V W
  obtain ⟨C, -, hC⟩ := (hAd V W rfl rfl).real ψ hθ hUo
  obtain ⟨-, hbd⟩ := hC χS χT ω hω μ 𝓕 hcov f hfU

  refine ⟨C * (sobO ψ θ μ 𝓕 d f).toReal * height V g ^ A, A, fun h => ?_⟩
  have key := hbd g h
  unfold thetaKO
  calc ‖ω (g, h) f 0‖ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (height V g * height W h) ^ A := key
    _ = C * (sobO ψ θ μ 𝓕 d f).toReal * height V g ^ A * height W h ^ A := by
      rw [mul_pow]; ring

theorem integrableOn_of_rapidDec (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D) (hθ : IsInfFam θ)
    (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν) {F : GA D W → ℂ} (hF : RapidDec W F) (g : GA D V) :
    IntegrableOn (fun h => thetaKO ω g h f * F h) 𝓕 ν := by
  have hcont := thetaKO_continuous hω hf g
  exact hF.integrableOn_modGrowth_mul hν h𝓕 (thetaKO_modGrowth hG hθ hω hf g)
    (thetaKO_left hω hf g) hcont.aestronglyMeasurable

theorem liftInteg_of_growth (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D) :
    LiftInteg D := by
  intro V W θ ψ χS χT ω hθ hω ν 𝓕 hν h𝓕 f F hf hFs hFc g

  have hdec : RapidDec W F := rapidDec_of_cuspForm hP hθ hFs hFc
  exact integrableOn_of_rapidDec hG hθ hω hf hν h𝓕 hdec g

end GlobalTheory.Chain.LiftConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareComm

variable {D : D7} {M X V : HSp D} (ω : WRep M X) (j : GA D V → GA D X) (G : GA D V → ℂ)
  (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) (μ : Measure (GA D V)) (𝓔 : Set (GA D V))

variable {ω j G ν 𝓕 μ 𝓔}

theorem ofSgn_symm_mem_GQ (ε : Bool) {γ : GA D M} (hγ : γ ∈ GQ M) : (ofSgn ε M).symm γ ∈ GQ (sgn ε M) := by
  have hγ' : γ.1 ∈ HFin (AF D.host.F) D.sp.cm.sig M.gram := hγ
  cases ε
  · exact hγ'
  · have hm : γ.1 ∈ HFin (AF D.host.F) D.sp.cm.sig (-M.gram) := by
      unfold HFin at hγ' ⊢
      rw [UJ_neg]
      exact hγ'
    rw [← neg_gram] at hm
    exact hm

theorem integral_rightTranslate (h : IsHaarFD M ν 𝓕) {f : GA D M → ℂ} (hf : ∀ γ ∈ GQ M, ∀ w, f (γ * w) = f w) (u : GA D M) :
    (IntegrableOn (fun w => f (w * u)) 𝓕 ν ↔ IntegrableOn f 𝓕 ν) ∧ ∫ w in 𝓕, f (w * u) ∂ν = ∫ w in 𝓕, f w ∂ν := by
  obtain ⟨hH, hFD⟩ := h
  obtain ⟨_, _, _, hB, hTG, _, hC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D M
  have : ν.IsMulRightInvariant :=
    (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D M ν hH).1
  have hpres : MeasurePreserving (fun w => w * u) ν ν := measurePreserving_mul_right ν u
  have hemb : MeasurableEmbedding (fun w : GA D M => w * u) := (MeasurableEquiv.mulRight u).measurableEmbedding
  set S : Set (GA D M) := (fun w => w * u⁻¹) ⁻¹' 𝓕 with hSdef
  have hS : IsFundamentalDomain (GQ M) S ν :=
    hFD.preimage_of_equiv (measurePreserving_mul_right ν u⁻¹).quasiMeasurePreserving Function.bijective_id
      (fun g x => by simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc])
  have hset : (fun w => w * u) ⁻¹' S = 𝓕 := by
    ext w
    simp [hSdef]
  have hinv : ∀ (g : GQ M) (x : GA D M), f (g • x) = f x := fun g x => hf g g.2 x
  refine ⟨?_, ?_⟩
  · have h1 := hpres.integrableOn_comp_preimage hemb (f := f) (s := S)
    rw [hset] at h1
    exact h1.trans (hS.integrableOn_iff hFD hinv)
  · have h2 := hpres.setIntegral_preimage_emb hemb f S
    rw [hset] at h2
    exact h2.trans (hS.setIntegral_eq hFD hinv)

end GlobalTheory.SquareComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetWordMultiplicityAdditiveJordanHolder
section
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.SmGL.Exponents.Additive

section General

variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem exists_mem_twKer {ρ : Representation F G V} {σ : Representation F G W}
    (p : ρ.IntertwiningMap σ) (hp : Function.Surjective p) (N : Subgroup G) {w : W}
    (hw : w ∈ twKer σ N 1) : ∃ v ∈ twKer ρ N 1, p v = w := by
  have : twKer σ N 1 ≤ (twKer ρ N 1).map p.toLinearMap := Submodule.span_le.2 (by
    rintro _ ⟨n, w, rfl⟩
    obtain ⟨v, rfl⟩ := hp w
    refine ⟨_, Submodule.subset_span ⟨n, v, rfl⟩, ?_⟩
    simp [p.isIntertwining])
  exact this hw

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem wordMult_exact {π : Representation ℂ (GL (Fin n) k) V}
    {π₁ : Representation ℂ (GL (Fin n) k) W} {π₂ : Representation ℂ (GL (Fin n) k) U}
    (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂) (hπ : IsSmooth π)
    (hι : Function.Injective ι) (hp : Function.Surjective p) (he : Function.Exact ι p)
    (w : List ℂˣ) : wordMult π w = wordMult π₁ w + wordMult π₂ w := by
  unfold wordMult
  split_ifs
  swap
  · simp
  refine jhMult_exact (compMap (jacMap (points _) ι) _) (compMap (jacMap (points _) p) _)
    (isIrreducible_ofChar _) (GlobalTheory.T.jacquetModule_map_injective_of_injective k _ _ _ (points _) W V π₁ π ι hπ hι) (fun x => ?_)
    (fun x => ?_) (fun x hx => ?_)
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨v, rfl⟩ := hp u
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (p (ι u)) = 0
    rw [he.apply_apply_eq_zero]
    rfl
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : p v ∈ twKer π₂ (unipRad k (points (Fin n))) 1 :=
      (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨v', hv', h2⟩ := exists_mem_twKer p hp _ h1
    obtain ⟨u, hu⟩ := (he (v - v')).1 (by rw [map_sub, h2, sub_self])
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v
    rw [hu]
    exact (Submodule.Quotient.eq _).2 (by simpa using hv')

theorem wordMult_of_subsingleton [Subsingleton V] (π : Representation ℂ (GL (Fin n) k) V)
    (w : List ℂˣ) : wordMult π w = 0 := by
  unfold wordMult
  split_ifs
  · have : Subsingleton (Jacquet π (unipB k (Fin n))) :=
      (Submodule.Quotient.mk_surjective _).subsingleton
    exact jhMult_of_subsingleton (isIrreducible_ofChar _) _
  · rfl

theorem sum_add {I : Type 1} (f : I → ℕ∞) (x y : I →₀ ℤ) (hx : ∀ c, 0 ≤ x c) (hy : ∀ c, 0 ≤ y c) :
    ((x + y).sum fun c a => (a.toNat : ℕ∞) * f c) =
      (x.sum fun c a => (a.toNat : ℕ∞) * f c) + y.sum fun c a => (a.toNat : ℕ∞) * f c := by
  classical
  rw [Finsupp.sum_of_support_subset (x + y) Finsupp.support_add _ (by simp),
    Finsupp.sum_of_support_subset x Finset.subset_union_left _ (by simp),
    Finsupp.sum_of_support_subset y Finset.subset_union_right _ (by simp),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finsupp.add_apply, Int.toNat_add (hx c) (hy c), Nat.cast_add, add_mul]

theorem wordMult_eq_sum (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π)
    (hπ : IsSmooth π) (w : List ℂˣ) :
    wordMult π w = (cls π h).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  have hfl : ∀ S : Subrepresentation π, HasFiniteLength S.toRepresentation := fun S =>
    IsFiniteLength.of_injective h
      (f := Representation.IntertwiningMap.equivLinearMapAsModule S.toRepresentation π
        ⟨S.toSubmodule.subtype, fun _ => rfl⟩) Subtype.val_injective
  have hsm : ∀ S : Subrepresentation π, IsSmooth S.toRepresentation := fun S =>
    (IsSubquotient.of_injective (σ := S.toRepresentation) (ρ := π)
      ⟨S.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective).isSmooth hπ
  have key : ∀ S : Subrepresentation π, wordMult S.toRepresentation w =
      (cls S.toRepresentation (hfl S)).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    rcases eq_or_ne S ⊥ with rfl | hS
    · have : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
      have h0 : cls (⊥ : Subrepresentation π).toRepresentation (hfl ⊥) = 0 := by
        ext c
        simp [cls_apply, jhMult_of_subsingleton (IrrRep.irr _)]
      rw [h0, wordMult_of_subsingleton, Finsupp.sum_zero_index]
    obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hS)
    let ι : T.toRepresentation.IntertwiningMap S.toRepresentation :=
      ⟨Submodule.inclusion hT.le, fun _ => rfl⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have hι : Function.Injective ι := Submodule.inclusion_injective hT.le
    have hps : Function.Surjective p := Submodule.Quotient.mk_surjective _
    have he : Function.Exact ι p := fun v =>
      ⟨fun hv => ⟨⟨v.1, (hp v).1 hv⟩, rfl⟩, by
        rintro ⟨u, rfl⟩
        exact (hp _).2 u.2⟩
    let σ : IrrRep (GL (Fin n) k) :=
      ⟨_, subQuot S T, (IsSubquotient.of_surjective p hps).isSmooth (hsm S),
        isIrreducible_subQuot hT⟩
    have hσ : cls (subQuot S T) σ.hasFiniteLength = Finsupp.single σ.cl 1 := cls_irr σ _
    obtain ⟨ψ⟩ := σ.nonempty_equiv_rep
    rw [wordMult_exact ι p (hsm S) hι hps he, cls_exact ι p hι hps he _ (hfl T) σ.hasFiniteLength,
      sum_add _ _ _ (fun c => by simp [cls_apply]) (fun c => by simp [cls_apply]), ih T hT.lt, hσ,
      Finsupp.sum_single_index (by simp), wordMult_congr ψ]
    simp [σ]
  rw [← wordMult_congr (topEquiv π), key ⊤, cls_congr (topEquiv π) _ h]

theorem wordMult_additive : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π), IsSmooth π → ∀ w : List ℂˣ, wordMult π w = (cls π h).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w :=
  fun _ _ _ _ _ _ _ _ _ π h hπ w => wordMult_eq_sum π h hπ w

end GlobalTheory.SmGL.Exponents.Additive
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionsSquareIntegrableHeisenbergUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSquare

theorem thetaFunctions_squareIntegrable_heisenbergUnitary : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.ThetaSquareIntegrable D :=
  GlobalTheory.ThetaSquare.theta_square_integrable

end GlobalTheory.ThetaSquare
end

