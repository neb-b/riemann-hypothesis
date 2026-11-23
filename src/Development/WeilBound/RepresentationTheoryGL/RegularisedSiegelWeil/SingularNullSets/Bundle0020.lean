module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0019
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0016
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.MemIntROfFinPart
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.NormDetLeFactorialMulProd

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Kdata
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT boxA fouA intF)

variable {F : Type} [Field F] [NumberField F]

theorem memH {ε : AF F} (h : fixE ε) : ε * h.1 = h.1 := h.2

theorem memY {ε : AF F} (y : (AddMonoidHom.mulLeft ε).ker) : ε * y.1 = 0 := y.2

theorem kdata (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS : S ⊆ S')
    {ε : AF F} (hε : IsIdF S ε) (db : Measure (AF F)) (ν : Measure (fixE ε)) [SFinite ν]
    (νY : Measure (AddMonoidHom.mulLeft ε).ker) [SFinite νY] (c : ℝ≥0) (hc : 0 < c)
    (hdec : ∀ f : AF F → ℂ,
      (Integrable f db ↔ Integrable (fun z : fixE ε × (AddMonoidHom.mulLeft ε).ker => f (z.1.1 + z.2.1)) (ν.prod νY)) ∧
      ∫ x, f x ∂db = (c : ℂ) * ∫ z : fixE ε × (AddMonoidHom.mulLeft ε).ker, f (z.1.1 + z.2.1) ∂(ν.prod νY))
    (ρ : Ainf F → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU0 : ∀ v, (0 : Fv F v) ∈ U v)
    (hI : Integrable (fouA ψ db (testT ρ S' U)) db)
    (hinv : ∀ z, ∫ b, fouA ψ db (testT ρ S' U) b * ψ (b * z) ∂db = testT ρ S' U (-z))
    (hne : ∫ y, testT ρ S' U y ∂db ≠ 0) :
    ∃ (g : fixE ε → ℂ) (Gc : ℝ), 0 ≤ Gc ∧ Integrable g ν ∧ (∀ h, ‖g h‖ ≤ 1) ∧
      (∀ s, ∫ h, g h * ψ (h.1 * s) ∂ν = ((Gc * tR ρ S' U (-(ε * s)) : ℝ) : ℂ)) ∧
      ∀ h : fixE ε, g h = fouA ψ db (testT ρ S' U) h.1 / ∫ y, testT ρ S' U y ∂db := by
  classical
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  have hεε := idF_mul hε
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set τH : fixE ε → ℂ := fun h => ((tR ρ S' U h.1 : ℝ) : ℂ) with hτH
  set τY : (AddMonoidHom.mulLeft ε).ker → ℂ := fun y => ((bR S' U y.1 : ℝ) : ℂ) with hτY
  set A : AF F → ℂ := fun s => ∫ h, τH h * ψ (h.1 * s) ∂ν with hA
  set Bf : AF F → ℂ := fun s => ∫ y, τY y * ψ (y.1 * s) ∂νY with hBf
  have hsplit : ∀ (h : fixE ε) (y : (AddMonoidHom.mulLeft ε).ker), testT ρ S' U (h.1 + y.1) = τH h * τY y := by
    intro h y
    rw [testT_eq, tR_split hSS hε ρ U hU0 (memH h) (memY y)]
    push_cast
    rfl
  have hpm : ∀ (h h0 : fixE ε) (y y0 : (AddMonoidHom.mulLeft ε).ker),
      (h.1 + y.1) * (h0.1 + y0.1) = h.1 * h0.1 + y.1 * y0.1 := by
    intro h h0 y y0
    have h1 : h.1 * y0.1 = 0 := fix_mul_ker hεε (memH h) (memY y0)
    have h2 : y.1 * h0.1 = 0 := by rw [mul_comm]; exact fix_mul_ker hεε (memH h0) (memY y)
    rw [add_mul, mul_add, mul_add, h1, h2, add_zero, zero_add]
  have hfou : ∀ (h0 : fixE ε) (y0 : (AddMonoidHom.mulLeft ε).ker),
      fouA ψ db (testT ρ S' U) (h0.1 + y0.1) = (c : ℂ) * (A h0.1 * Bf y0.1) := by
    intro h0 y0
    simp only [fouA]
    rw [(hdec _).2]
    congr 1
    rw [← integral_prod_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hsplit, hpm, AddChar.map_add_eq_mul]
    ring
  have hint : ∫ y, testT ρ S' U y ∂db = (c : ℂ) * ((∫ h, τH h ∂ν) * ∫ y, τY y ∂νY) := by
    rw [(hdec _).2, ← integral_prod_mul]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => hsplit z.1 z.2)
  set IH := ∫ h, τH h ∂ν with hIH
  set IY := ∫ y, τY y ∂νY with hIY
  have hIH0 : IH ≠ 0 := fun h0 => hne (by rw [hint, h0, zero_mul, mul_zero])
  have hIY0 : IY ≠ 0 := fun h0 => hne (by rw [hint, h0, mul_zero, mul_zero])
  have hτHI : Integrable τH ν := by
    by_contra hn
    exact hIH0 (integral_undef hn)
  have hτR : Integrable (fun h : fixE ε => tR ρ S' U h.1) ν := by
    have := hτHI.norm
    refine this.congr (Filter.Eventually.of_forall fun h => ?_)
    simp only [hτH, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (tR_nonneg hρ0 S' U _)
  set IHr := ∫ h, tR ρ S' U h.1 ∂ν with hIHr
  have hIHc : IH = (IHr : ℂ) := integral_ofReal
  have hIHr0 : 0 < IHr := by
    refine lt_of_le_of_ne (integral_nonneg fun h => tR_nonneg hρ0 S' U _) fun h0 => hIH0 ?_
    rw [hIHc, ← h0, Complex.ofReal_zero]
  have hA0 : A 0 = IH := by
    simp only [hA, mul_zero, AddChar.map_zero_eq_one, mul_one]
    exact hIH.symm
  have hB0 : Bf 0 = IY := by
    simp only [hBf, mul_zero, AddChar.map_zero_eq_one, mul_one]
    exact hIY.symm
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.2.1

  have hAc : Continuous A := by
    refine continuous_of_dominated (bound := fun h => ‖τH h‖) (fun s => ?_) (fun s => ?_) hτHI.norm ?_
    · exact hτHI.aestronglyMeasurable.mul
        (hψ.1.comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun h => by rw [norm_mul, hψn, mul_one]
    · exact Filter.Eventually.of_forall fun h => continuous_const.mul (hψ.1.comp (continuous_const.mul continuous_id))

  set IB := ∫ y, Bf y.1 ∂νY with hIB
  have hinvH : ∀ s, ε * s = s →
      ((tR ρ S' U (-s) : ℝ) : ℂ) = (c : ℂ) ^ 2 * IB * ∫ h, A h.1 * ψ (h.1 * s) ∂ν := by
    intro s hs
    have h1 := hinv s
    rw [(hdec _).2, testT_eq] at h1
    have h2 : ∀ z : fixE ε × (AddMonoidHom.mulLeft ε).ker,
        fouA ψ db (testT ρ S' U) (z.1.1 + z.2.1) * ψ ((z.1.1 + z.2.1) * s) =
          ((c : ℂ) * (A z.1.1 * ψ (z.1.1 * s))) * Bf z.2.1 := by
      intro z
      have hz : z.2.1 * s = 0 := by rw [mul_comm]; exact fix_mul_ker hεε hs (memY z.2)
      rw [hfou, add_mul, hz, add_zero]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall h2),
      integral_prod_mul (fun h : fixE ε => (c : ℂ) * (A h.1 * ψ (h.1 * s))) (fun y : (AddMonoidHom.mulLeft ε).ker => Bf y.1),
      integral_const_mul] at h1
    rw [← h1]
    ring

  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : fixE ε, tR ρ S' U h₀.1 ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hIHr0.ne'
    rw [hIHr]
    simp [hn]
  have hIB0 : IB ≠ 0 := by
    intro h0
    have h1 := hinvH (-h₀.1) (by rw [mul_neg, memH h₀])
    rw [neg_neg, h0, mul_zero, zero_mul] at h1
    exact hh₀ (by exact_mod_cast h1)
  set κ : ℂ := ((c : ℂ) ^ 2 * IB)⁻¹ with hκ
  have hcB : (c : ℂ) ^ 2 * IB ≠ 0 := mul_ne_zero (pow_ne_zero _ hc0) hIB0
  have hinvG : ∀ s, ∫ h, A h.1 * ψ (h.1 * s) ∂ν = κ * ((tR ρ S' U (-(ε * s)) : ℝ) : ℂ) := by
    intro s
    have hes : ε * (ε * s) = ε * s := by rw [← mul_assoc, hεε]
    have h1 : ∀ h : fixE ε, h.1 * s = h.1 * (ε * s) := fun h => by
      conv_lhs => rw [← memH h]
      ring
    simp only [h1]
    rw [hinvH _ hes, hκ, ← mul_assoc, inv_mul_cancel₀ hcB, one_mul]

  have hAI : Integrable (fun h : fixE ε => A h.1) ν := by
    have h1 := (hdec (fouA ψ db (testT ρ S' U))).1.1 hI
    have h2 : (fun z : fixE ε × (AddMonoidHom.mulLeft ε).ker => fouA ψ db (testT ρ S' U) (z.1.1 + z.2.1)) =
        fun z => (c : ℂ) * (A z.1.1 * Bf z.2.1) := funext fun z => hfou z.1 z.2
    rw [h2] at h1
    have hBI : Integrable (fun y : (AddMonoidHom.mulLeft ε).ker => Bf y.1) νY := by
      by_contra hn
      exact hIB0 (integral_undef hn)
    have hK : 0 < ∫ y, ‖Bf y.1‖ ∂νY :=
      lt_of_lt_of_le (norm_pos_iff.2 hIB0) (norm_integral_le_integral_norm _)
    have h3 := ((integrable_prod_iff h1.aestronglyMeasurable).1 h1).2
    have h4 : ∀ h : fixE ε, ∫ y, ‖(c : ℂ) * (A h.1 * Bf y.1)‖ ∂νY =
        (‖(c : ℂ)‖ * ∫ y, ‖Bf y.1‖ ∂νY) * ‖A h.1‖ := by
      intro h
      simp_rw [norm_mul]
      rw [integral_const_mul, integral_const_mul]
      ring
    simp only [h4] at h3
    have hcK : ‖(c : ℂ)‖ * ∫ y, ‖Bf y.1‖ ∂νY ≠ 0 := mul_ne_zero (norm_ne_zero_iff.2 hc0) hK.ne'
    have h5 : Integrable (fun h : fixE ε => ‖A h.1‖) ν := by
      refine (h3.const_mul (‖(c : ℂ)‖ * ∫ y, ‖Bf y.1‖ ∂νY)⁻¹).congr (Filter.Eventually.of_forall fun h => ?_)
      simp only
      rw [← mul_assoc, inv_mul_cancel₀ hcK, one_mul]
    exact (integrable_norm_iff (hAc.comp continuous_subtype_val).aestronglyMeasurable).1 h5

  obtain ⟨M, hM⟩ := hρc.bddAbove_range_of_hasCompactSupport hρs
  have hτM : ∀ h : fixE ε, tR ρ S' U h.1 ≤ M := by
    intro h
    have hρM : ρ (fstA F h.1) ≤ M := hM ⟨_, rfl⟩
    unfold tR
    by_cases hb : sndA F h.1 ∈ boxA S' U
    · rw [Set.indicator_of_mem hb, mul_one]; exact hρM
    · rw [Set.indicator_of_notMem hb, mul_zero]; exact (hρ0 _).trans hρM
  have hk := kappa_real ψ hψ ν (fun h => tR ρ S' U h.1) (fun h => tR_nonneg hρ0 S' U _) hτR hIHr0 M hτM
    (fun h => A h.1) (fun s => rfl) hAI κ (fun s => by
      have := hinvG s.1
      rw [memH s] at this
      exact this)
  have hAb : ∀ s, ‖A s‖ ≤ IHr := by
    intro s
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [hIHr]
    congr 1
    funext h
    rw [norm_mul, hψn, mul_one, Complex.norm_real, Real.norm_of_nonneg (tR_nonneg hρ0 S' U _)]
  have hκr : κ = (κ.re : ℂ) := Complex.ext (by simp) (by simp [hk.1])
  have hIHr0' : (IHr : ℂ) ≠ 0 := by exact_mod_cast hIHr0.ne'
  refine ⟨fun h => A h.1 / IH, κ.re / IHr, div_nonneg hk.2 hIHr0.le, hAI.div_const _, fun h => ?_, fun s => ?_,
    fun h => ?_⟩
  · rw [norm_div, hIHc, Complex.norm_real, Real.norm_of_nonneg hIHr0.le]
    exact (div_le_one hIHr0).2 (hAb _)
  · simp_rw [div_mul_eq_mul_div]
    rw [integral_div, hinvG, hIHc, hκr]
    push_cast
    field_simp
    rw [Complex.ofReal_re]
    ring
  · have h1 := hfou h 0
    rw [ZeroMemClass.coe_zero, add_zero, hB0] at h1
    simp only
    rw [h1, hint]
    field_simp

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutId
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

set_option maxHeartbeats 1600000 in
theorem cutId : Polar → CfFJ → CoefId → ThCoef → FourierPt → WeakApproximationFinitePlace → CfInv → ThBdd → CutLow → IkSch → IkEq → WMaj → CutId := by
  intro hPolar hCfFJ hCoefId hThCoef hFP hWA1 hCfInv hThBdd hCutLow _ hIkEq hWMaj
  intro D n t B W d hn ψ χ θ μB μW ωB ωW hS I H hH Φ U dd E σ hcont ε hrad nb hnb v C hK hKv 𝓕 h𝓕 Ψ Ψ' hΨ hΨ'
  obtain ⟨nb₀, lam, 𝓖, hCD⟩ := _root_.GlobalTheory.CompanionTheory.SWCoef.coefDataExists D n
  have hC : CoefData (D := D) (n := n) nb lam 𝓖 := ⟨hnb, hCD.2⟩
  obtain ⟨κ, hκ⟩ := hCoefId D n t B W d hn ψ χ θ μB μW ωB ωW hS I H hH Φ U dd E σ hcont ε hrad nb lam 𝓖 hC
  refine ⟨κ, ?_⟩

  have hBr : B.rank = W.rank + 2 * t := d.rank_add.symm
  have hlaw : IsLaw χ ((t : ℂ) / 2) (fun g => (ωB g Φ).1 0) :=
    LCutId.law0 hS.hB Φ _ (by rw [hBr, ← hn]; push_cast; ring)
  have hηB : ResEta D χ B.rank := by rw [hBr]; exact LCutId.resEta_add hS.hη t
  have hφc : Continuous (fun g => (ωB g Φ).1 0) :=
    (hWMaj D n B ψ hS.hψ χ hS.hχ hηB θ hS.hθ μB hS.hμB ωB hS.hB Φ).1.comp (continuous_id.prodMk continuous_const)
  have hpol := hPolar D n W.rank t hn hS.big ψ hS.hψ χ hS.hχ hS.hη
    (fun h0 => absurd h0 (by have := hS.pos; omega)) θ hS.hθ H hH _ hφc hlaw U dd E σ hcont ε hrad
  have hRk := hpol.1 1 le_rfl

  obtain ⟨hcf, -, -⟩ := hCfFJ D n H _ _ U dd E σ hcont ε hrad
  have hcf1c := (hcf 1).1
  have hcf1i := (hcf 1).2
  have hcfK : ∀ k ∈ KAt D n v, ∀ g, cf dd E ((t : ℂ) / 2) ε 1 (g * k) = cf dd E ((t : ℂ) / 2) ε 1 g := by
    intro k hk g
    exact hCfInv D n H _ _ U dd E σ hcont ε hrad k (fun g => (hKv k hk).2 g) (fun g => by
      show (ωB (g * k) Φ).1 0 = (ωB g Φ).1 0
      rw [map_mul, Module.End.mul_apply, (hKv k hk).1]) 1 g
  obtain ⟨-, ⟨U₁, hU₁, hU₁i⟩, hlow⟩ := hCutLow D n W.rank ψ hS.hψ nb hnb v C hK _ hcf1c hcf1i hcfK

  have hΨK : ∀ k ∈ KAt D n v, ωW k Ψ = Ψ := fun k hk => Subtype.ext (by
    rw [hIkEq D n t B W d hn ψ χ θ μB μW ωB ωW hS I Φ Ψ hΨ k, (hKv k hk).1, ← hΨ])
  obtain ⟨-, hthL, ⟨U₂, hU₂, hU₂i⟩, -, hthF⟩ :=
    hThBdd D n W ψ hS.hψ χ hS.hχ hS.hη θ hS.hθ μW hS.hμW ωW hS.hW nb hnb v C hK Ψ Ψ' hΨK hΨ'
  obtain ⟨F₂, hF₂⟩ : ∃ F₂ : G D n → ℂ, F₂ = fun g => ∫ h in 𝓕, theta ωW Ψ' g h ∂I.m := ⟨_, rfl⟩
  have hF₁L : ∀ γ ∈ GF D n, ∀ g, cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (γ * g) = cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) g := by
    intro γ hγ g
    unfold cutR
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, hcf1i γ hγ]
  have hF₁c : Continuous (cutR nb C (cf dd E ((t : ℂ) / 2) ε 1)) := by
    unfold cutR
    exact continuous_finsetSum _ fun x _ => continuous_const.mul (hcf1c.comp (continuous_mul_const _))
  have hF₂L : ∀ γ ∈ GF D n, ∀ g, F₂ (γ * g) = F₂ g := by
    intro γ hγ g
    rw [hF₂]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    exact hthL γ hγ g h
  have hF₂R : ∀ k ∈ U₂, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ g, F₂ (g * k) = F₂ g := by
    intro k hk hk' g
    rw [hF₂]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    show ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E, (ωW (g * k) Ψ').1 _ = ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E, (ωW g Ψ').1 _
    rw [map_mul, Module.End.mul_apply, hU₂i k hk hk']

  have key : ∀ g, proj D.sp.cm.sig (Jst D n) v g = 1 → cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) g = κ * F₂ g := by
    intro g hg
    obtain ⟨-, hTc, hTβ⟩ := hThCoef D n W ψ hS.hψ θ hS.hθ I.m 𝓕 I.haar h𝓕 lam 𝓖 hCD.2 (ωW g Ψ').1 (ωW g Ψ').2
    have hthS : ∀ x : hermA D n, F₂ (nb x * g) = thS W I.m 𝓕 (fun X => pch ψ x.1 (ip W X X) * (ωW g Ψ').1 X) := by
      intro x
      rw [hF₂]
      refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      exact (hthF x g hg).2 h
    have hF₂c : Continuous fun x : hermA D n => F₂ (nb x * g) := by
      simp only [hthS]; exact hTc
    have hF₁c' : Continuous fun x : hermA D n => cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) :=
      hF₁c.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_nb hnb).mul continuous_const)
    have hper : ∀ {F : G D n → ℂ}, (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
        ∀ γ ∈ ratHerm D n, ∀ x, F (nb (γ + x) * g) = F (nb x * g) := by
      intro F hF γ hγ x
      rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
      exact hF _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _
    have hcoef : ∀ β : HermE D n, fc ψ lam 𝓖 nb (cutR nb C (cf dd E ((t : ℂ) / 2) ε 1)) β g =
        κ * ∫ x in 𝓖, F₂ (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam := by
      intro β
      simp only [hthS]
      have hlowβ := hlow lam 𝓖 hC β g hg
      have horb : ∀ x₀ : Matrix (Fin W.rank) (Fin n) D.host.E, gramQ W x₀ = β.1 →
          orb W I.m (ωW g Ψ').1 x₀ = cutF ψ C (rat β.1) * orb W I.m (ωW g Ψ).1 x₀ := by
        intro x₀ hx₀
        unfold orb
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun h => ?_)
        show (ωW g Ψ').1 _ = _ * (ωW g Ψ).1 _
        rw [(hthF 0 g hg).1, LCutId.ip_orbit, hx₀]
      rcases lt_trichotomy β.1.rank W.rank with hlt | heq | hgt
      · rw [hlowβ.2 hlt]
        by_cases hx : ∃ x, x.rank = W.rank ∧ gramQ W x = β.1
        · obtain ⟨x₀, hx₀r, hx₀⟩ := hx
          rw [(hTβ β).2 x₀ hx₀r hx₀]
          unfold orb
          rw [show (∫ h, (ωW g Ψ').1 (mm (Formalism.L2.Theta.mt W h⁻¹) (rat x₀)) ∂I.m) = ∫ _h, (0 : ℂ) ∂I.m from
            integral_congr_ae (Eventually.of_forall fun h => ?_), integral_zero, mul_zero]
          show (ωW g Ψ').1 _ = 0
          rw [(hthF 0 g hg).1, LCutId.ip_orbit, hx₀]
          by_cases hdual : ∀ y : hermA D n, IntAt v y → pch ψ y.1 (rat β.1) = 1
          · rw [hK β hlt hdual, zero_mul]
          · push Not at hdual
            obtain ⟨y, hy, hne⟩ := hdual
            have hfix := LCutId.omega_fix hS.hW hnb Ψ hΨK hg hy (mm (Formalism.L2.Theta.mt W h⁻¹) (rat x₀))
            rw [LCutId.ip_orbit, hx₀] at hfix
            have h2 : (1 - pch ψ y.1 (rat β.1)) * (ωW g Ψ).1 (mm (Formalism.L2.Theta.mt W h⁻¹) (rat x₀)) = 0 := by
              rw [sub_mul, one_mul, ← hfix, sub_self]
            rw [(mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hne)), mul_zero]
        · rw [(hTβ β).1 hx, mul_zero]
      · rw [hlowβ.1]
        by_cases hx : ∃ x, gramQ W x = β.1
        · obtain ⟨x₀, hx₀⟩ := hx
          have hx₀r : x₀.rank = W.rank := by
            have h1 := LCutId.rank_gram_le W x₀
            rw [hx₀, heq] at h1
            exact le_antisymm (Matrix.rank_le_height x₀) h1
          rw [((hκ β heq g).2 x₀ hx₀), (hTβ β).2 x₀ hx₀r hx₀, horb x₀ hx₀,
            hIkEq D n t B W d hn ψ χ θ μB μW ωB ωW hS I Φ Ψ hΨ g]
          ring
        · rw [(hκ β heq g).1 hx, (hTβ β).1 fun ⟨x, _, hx'⟩ => hx ⟨x, hx'⟩, mul_zero, mul_zero]
      · rw [hlowβ.1, hRk nb lam 𝓖 hC β (Nat.succ_le_of_lt hgt) g, mul_zero]
        rw [(hTβ β).1 fun ⟨x, hxr, hx'⟩ => by
          have h1 := LCutId.rank_gram_le W x
          rw [hx', hxr] at h1
          omega, mul_zero]
    have hf0 := hFP D n ψ hS.hψ lam 𝓖 hCD.2
      (fun x => cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) - κ * F₂ (nb x * g))
      (hF₁c'.sub (continuous_const.mul hF₂c))
      (fun γ hγ x => by simp only [hper hF₁L γ hγ x, hper hF₂L γ hγ x])
      (fun β => by
        have i1 := LCutId.intOn hCD.2 hF₁c' (hper hF₁L) (LCutId.cont_conj_pch hS.hψ β) (LCutId.norm_conj_pch hS.hψ · β)
        have i2 := LCutId.intOn hCD.2 hF₂c (hper hF₂L) (LCutId.cont_conj_pch hS.hψ β) (LCutId.norm_conj_pch hS.hψ · β)
        have e : (fun x : hermA D n => (cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) - κ * F₂ (nb x * g)) *
            conj (pch ψ x.1 (rat β.1))) = fun x => cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) * conj (pch ψ x.1 (rat β.1)) -
              κ * (F₂ (nb x * g) * conj (pch ψ x.1 (rat β.1))) := funext fun x => by ring
        rw [e, integral_sub i1 (i2.const_mul κ), integral_const_mul, ← LCutId.fc_eq hS.hψ, hcoef β, sub_self])
    have h0 := congrFun hf0 0
    simp only [GlobalTheory.CompanionTheory.FourierN.nb_zero hnb, one_mul, Pi.zero_apply] at h0
    exact sub_eq_zero.1 h0

  intro g
  obtain ⟨γ, hγ, g', hg', k, hkU, hkv, hgeq⟩ := hWA1 D n v (U₁ ⊓ U₂) (by rw [Subgroup.coe_inf]; exact hU₁.inter hU₂) g
  have e1 : cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (γ * g' * k) = cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) g' := by
    rw [hU₁i k (Subgroup.mem_inf.1 hkU).1 hkv, hF₁L γ hγ]
  have e2 : F₂ (γ * g' * k) = F₂ g' := by
    rw [hF₂R k (Subgroup.mem_inf.1 hkU).2 hkv, hF₂L γ hγ]
  rw [hgeq, e1, key g' hg', ← e2, hF₂]

end PositivityTheory.Rg.Rsw.L

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LLatBoundA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

theorem fullRank_col (D : D7) (a n n₀ : ℕ) (hn₀ : 0 < n₀) (f : SchwartzMap (D.what₂.Tau → Fin a → Fin n → ℂ) ℂ) :
    ∃ C : ℝ, ∀ B : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ, (∀ τ, ‖(B τ).det‖ = 1) →
      ∑' ξ : {ξ : Matrix (Fin a) (Fin n) D.host.E // ξ.rank = a ∧ ∀ i j, (n₀ : D.host.E) * ξ i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D},
        ‖f (fun τ => B τ * ξ.1.map (tauE D τ))‖ₑ ≤ ENNReal.ofReal C := by
  haveI := GlobalTheory.CompanionTheory.Ipf.Bdd.nonempty_tau D
  obtain ⟨e, he⟩ : ∃ e : (D.what₂.Tau → Fin n → Fin a → ℂ) ≃ₗ[ℝ] (D.what₂.Tau → Fin a → Fin n → ℂ),
      ∀ x τ i j, e x τ i j = x τ j i :=
    ⟨{ toFun := fun x τ i j => x τ j i
       invFun := fun y τ j i => y τ i j
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl }, fun _ _ _ _ => rfl⟩
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.Twist.FullRank.tsum_schwartz_fullRank_le D.host.E (GlobalTheory.CompanionTheory.Ipf.Bdd.intR D)
    D.what₂.Tau (tauE D) (fun z hz h0 => GlobalTheory.CompanionTheory.Ipf.Bdd.one_le_prod_tauE z hz h0) a n n₀ hn₀
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e.toContinuousLinearEquiv f)
  refine ⟨C, fun B hB => ?_⟩
  have hBt : ∀ τ, ‖(B τ)ᵀ.det‖ = 1 := fun τ => by
    rw [Matrix.det_transpose]
    exact hB τ
  obtain ⟨T, hT⟩ : ∃ T : {γ : Matrix (Fin n) (Fin a) D.host.E //
        γ.rank = a ∧ ∀ i j, (n₀ : D.host.E) * γ i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D} ≃
      {ξ : Matrix (Fin a) (Fin n) D.host.E //
        ξ.rank = a ∧ ∀ i j, (n₀ : D.host.E) * ξ i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D},
      ∀ γ, (T γ).1 = γ.1ᵀ :=
    ⟨{ toFun := fun γ => ⟨γ.1ᵀ, by rw [Matrix.rank_transpose]; exact γ.2.1, fun i j => γ.2.2 j i⟩
       invFun := fun ξ => ⟨ξ.1ᵀ, by rw [Matrix.rank_transpose]; exact ξ.2.1, fun i j => ξ.2.2 j i⟩
       left_inv := fun γ => Subtype.ext (Matrix.transpose_transpose _)
       right_inv := fun ξ => Subtype.ext (Matrix.transpose_transpose _) }, fun _ => rfl⟩
  rw [← T.tsum_eq]
  refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) (hC (fun τ => (B τ)ᵀ) hBt)
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  congr 2
  funext τ i j
  rw [LinearEquiv.coe_toContinuousLinearEquiv']
  refine Eq.trans ?_ (he _ τ i j).symm
  rw [hT]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, mul_comm]

end PositivityTheory.Rg.Rsw.L.LLatBound

end
end

