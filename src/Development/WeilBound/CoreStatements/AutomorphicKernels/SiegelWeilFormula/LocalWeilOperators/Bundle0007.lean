module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0004
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0006
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0009
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0005
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OppositeUnipotentWeylConj

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Assemble
section
noncomputable section

open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace RD

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

theorem ok_of_conj (hT : TAll) {y y' : GR d.n} {x₁ x₂ : d.G} {A₁ A₂ A' : d.LF → d.LF} {B₁ B₂ : d.MF → d.MF}
    (h₁ : R.StepOK w x₁ A₁ B₁) (h₂ : R.StepOK w x₂ A₂ B₂) (h' : R.StepOK w (R.ι w y') A' id)
    (hy : R.ι w y = x₁ * R.ι w y' * x₂) (h1 : x₁ * x₂ = 1) : R.OkY w y := by
  have hsch := d.om_sch
  have hc := R.step_comp w hsch (R.step_comp w hsch h₁ h') h₂
  have h0 := R.step_comp w hsch h₁ h₂
  intro f hf
  by_cases hf0 : ∀ u, f u = 0
  · refine ⟨0, ⟨0, by ext; simp⟩, fun Ψ hΨ Φ hΦ hTΦ => ?_⟩
    have : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hTΦ]; funext X; simp [RD.tens, hf0])
    subst this
    rw [map_zero, d.T_zero]
    funext X
    simp [RD.tens]
  · push Not at hf0
    obtain ⟨u₀, hu₀⟩ := hf0
    by_cases hex : ∃ κ : ℂ, κ ≠ 0 ∧ A₁ (A₂ f) = κ • f
    · obtain ⟨κ, hκ, hA⟩ := hex
      refine ⟨κ⁻¹ • A₁ (A' (A₂ f)), ?_, fun Ψ hΨ Φ hΦ hTΦ => ?_⟩
      · obtain ⟨φ, hφ⟩ := hc.1 f hf
        refine ⟨κ⁻¹ • φ, ?_⟩
        funext u
        have := congrFun hφ u
        simp only [Function.comp_apply] at this
        simp [this]
      · have e := (hc.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
        have e0 := (h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
        rw [h1, map_one, Module.End.one_apply, hTΦ] at e0
        have hBaway := (h0.2 Ψ hΨ).1
        have hB : ∀ X, B₁ (B₂ Ψ) X = κ⁻¹ * Ψ X := by
          intro X
          obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u₀
          have h2 := congrFun e0 (X + Z)
          have h3 := hΨ X Z hZ1 hZ2
          have h4 := hBaway X Z hZ1 hZ2
          simp only [RD.tens, Function.comp_apply, hZ3, hA, Pi.smul_apply, smul_eq_mul] at h2 h4
          rw [h3, h4] at h2
          rw [eq_inv_mul_iff_mul_eq₀ hκ]
          apply mul_left_cancel₀ hu₀
          linear_combination -h2
        rw [hy, e]
        funext X
        simp only [RD.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hB]
        ring
    · refine ⟨0, ⟨0, by ext; simp⟩, fun Ψ hΨ Φ hΦ hTΦ => ?_⟩
      have hΨ0 : ∀ X, Ψ X = 0 := by
        by_contra hne
        push Not at hne
        obtain ⟨X₀, hX₀⟩ := hne
        have e0 := (h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
        rw [h1, map_one, Module.End.one_apply, hTΦ] at e0
        have hBaway := (h0.2 Ψ hΨ).1
        have key : ∀ u, f u * Ψ X₀ = A₁ (A₂ f) u * B₁ (B₂ Ψ) X₀ := by
          intro u
          obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
          have h2 := congrFun e0 (X₀ + Z)
          have h3 := hΨ X₀ Z hZ1 hZ2
          have h4 := hBaway X₀ Z hZ1 hZ2
          simp only [RD.tens, Function.comp_apply, hZ3] at h2 h4
          rw [h3, h4] at h2
          exact h2
        have hB0 : B₁ (B₂ Ψ) X₀ ≠ 0 := by
          intro h0'
          have := key u₀
          rw [h0', mul_zero] at this
          exact mul_ne_zero hu₀ hX₀ this
        apply hex
        refine ⟨Ψ X₀ / B₁ (B₂ Ψ) X₀, div_ne_zero hX₀ hB0, ?_⟩
        funext u
        have := key u
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [div_mul_eq_mul_div, eq_div_iff hB0]
        linear_combination -this
      have : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hTΦ]; funext X; simp [RD.tens, hΨ0])
      subst this
      rw [map_zero, d.T_zero]
      funext X
      simp [RD.tens, hΨ0]

end RD

theorem herm_smul_one' {n : ℕ} (t : ℝ) :
    ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

theorem locOpEx_of (hT : TAll) (hA : AuxiliaryPrimeFunction) : LocOpEx := by
  intro F E _ _ _ _ _ σ d R w
  refine ⟨_, R.isLocOp_of_ok w fun y => ?_⟩
  have hsch := d.om_sch
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  obtain ⟨C, s, B, -, hW⟩ := R.stepW w hT hA ε w₀ hw₀
  have okN : ∀ (y : GR d.n) (b : Matrix (Fin d.n) (Fin d.n) ℂ), bᴴ = b → mR y = nU b → R.OkY w y :=
    fun y b hb hy => R.ok_of_step w (R.stepN w hT y b hb hy)
  have okM : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = Glob.mM a → R.OkY w y := by
    intro y a ha hy
    obtain ⟨c, -, hc⟩ := R.stepM w hT y a ha hy
    exact R.ok_of_step w hc
  have okB : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = Glob.nbar c → R.OkY w y := by
    intro y c hc hy
    obtain ⟨y', x, hx, hy', hrel⟩ := R.nbar_conj' w hw₀ y c hc hy
    have hW3 := R.step_comp w hsch (R.step_comp w hsch hW hW) hW
    exact R.ok_of_conj w hT hW3 hW (R.stepN w hT y' x hx hy') hrel (RD.w_four hw₀)
  obtain ⟨y1, y2, y3, y4, hy, ⟨t, ht⟩, ⟨c, hc, hc2⟩, ⟨a, ha, ha2⟩, ⟨b, hb, hb2⟩⟩ := PositivityTheory.Rg.Sw.Glob.decomp d.n y
  rw [hy]
  exact R.ok_mul w hsch (R.ok_mul w hsch (R.ok_mul w hsch (okN y1 _ (herm_smul_one' t) ht) (okB y2 c hc hc2))
    (okM y3 a ha ha2)) (okN y4 b hb hb2)

end PositivityTheory.SiegelWeilFormula

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocNbar
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

def locFT {m n : ℕ} (C s : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) : (Fin m → Fin n → ℂ) → ℂ :=
  fun u => C * ∫ v : Fin m → Fin n → ℂ,
    Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v

def chirp {m n : ℕ} (k : ℂ) (x : Matrix (Fin n) (Fin n) ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) :
    (Fin m → Fin n → ℂ) → ℂ :=
  fun u => Complex.exp (2 * Real.pi * Complex.I * k * Matrix.trace (x * ((Matrix.of u)ᴴ * Matrix.of u))) * g u

theorem locFT_zero {m n : ℕ} (C s : ℂ) : locFT (m := m) (n := n) C s 0 = 0 := by
  funext u
  simp [locFT]

theorem chirp_zero {m n : ℕ} (k : ℂ) (x : Matrix (Fin n) (Fin n) ℂ) : chirp (m := m) k x 0 = 0 := by
  funext u
  simp [chirp]

theorem locFT_smul {m n : ℕ} (C s a : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) :
    locFT C s (a • g) = a • locFT C s g := by
  funext u
  simp only [locFT, Pi.smul_apply, smul_eq_mul]
  rw [show (fun v : Fin m → Fin n → ℂ => Complex.exp (2 * Real.pi * Complex.I *
      ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * (a * g v)) = fun v => a * (Complex.exp
      (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) from
    funext fun v => by ring, integral_const_mul]
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace RD

variable {d : SD σ} (R : RD d) {w : InfinitePlace F}
  {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}

theorem locOp_zero (hT : TAll) (hG : GoodAwayEx) (hL : R.IsLocOp w L) (y : GR d.n) : L y 0 = 0 := by
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  have h0 : IsSw (0 : d.LF) := ⟨0, by ext; simp⟩
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ h0
  have hΦ0 : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hT']; funext X; simp [RD.tens])
  have e := (hL y 0 h0).2 Ψ hΨ.1 Φ hΦ hT'
  rw [hΦ0, map_zero, d.T_zero] at e
  apply R.tens_cancel hΨ.1 hΨ.2.1
  rw [← e]
  funext X
  simp [RD.tens]

theorem locOp_nbar (hT : TAll) (hA : AuxiliaryPrimeFunction) (hG : GoodAwayEx) (hL : R.IsLocOp w L) :
    ∃ (C s κ : ℂ) (ε : ℤˣ), s ≠ 0 ∧ κ ≠ 0 ∧
      (∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f) ∧
      (∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f))))) ∧
      (∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        locFT C s (L y f) = chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)) ∧
      ‖s‖ = 2 ∧ ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ = -1 := by
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  obtain ⟨C, B, -, hW⟩ := R.stepW_exp w hT hA ε w₀ hw₀
  set s : ℂ := -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ with hs_def
  have hW' : R.StepOK w w₀ (locFT C s) B := hW
  have hζn : ‖R.ζ‖ = 1 := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩ <;> rw [hz] <;> simp
  have hunit : ∀ u : ℤˣ, ‖((u : ℤ) : ℂ)‖ = 1 := fun u => by
    rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> simp
  have hsn : ‖s‖ = 2 := by
    rw [hs_def, norm_div, norm_mul, norm_mul, hunit, hunit, hζn]
    norm_num
  have hs : s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hsn
    norm_num at hsn
  have hη : ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ = -1 := by
    rw [R.isW_eps w hw₀]
    rcases R.hζ with ⟨he, hz⟩ | ⟨he, hz⟩
    · rw [he, hz]; simp
    · rw [he, hz]; simp [Complex.inv_I]
  have hsch := d.om_sch
  have h4 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hW'
  rw [RD.w_four hw₀] at h4
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, Ψ X₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hΨ.2.1 (funext hc)
  have hB4 : d.IsAwayW w (B (B (B (B Ψ)))) := (h4.2 Ψ hΨ.1).1
  have key : ∀ f : d.LF, IsSw f → ∀ X, f (R.loc w X) * Ψ X =
      locFT C s (locFT C s (locFT C s (locFT C s f))) (R.loc w X) * B (B (B (B Ψ))) X := by
    intro f hf X
    obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
    have e := (h4.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
    rw [map_one, Module.End.one_apply, hT'] at e
    exact congrFun e X
  have key0 : ∀ f : d.LF, IsSw f → ∀ u, f u * Ψ X₀ =
      locFT C s (locFT C s (locFT C s (locFT C s f))) u * B (B (B (B Ψ))) X₀ := by
    intro f hf u
    obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
    have := key f hf (X₀ + Z)
    rwa [hZ3, hΨ.1 X₀ Z hZ1 hZ2, hB4 X₀ Z hZ1 hZ2] at this
  by_cases hb : B (B (B (B Ψ))) X₀ = 0
  · have hz : ∀ f : d.LF, IsSw f → f = 0 := by
      intro f hf
      funext u
      have := key0 f hf u
      rw [hb, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hX₀
    refine ⟨C, s, 1, ε, hs, one_ne_zero, fun f hf => ?_, fun y c hc hy f hf => ?_, fun y c hc hy f hf => ?_, hsn, hη⟩
    · rw [hz f hf]
      simp [locFT_zero]
    · rw [hz f hf, R.locOp_zero hT hG hL y]
      simp [locFT_zero, chirp_zero]
    · rw [hz f hf, R.locOp_zero hT hG hL y]
      simp [locFT_zero, chirp_zero]
  · set κ := Ψ X₀ / B (B (B (B Ψ))) X₀ with hκ
    have hκ0 : κ ≠ 0 := div_ne_zero hX₀ hb
    have h4f : ∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f := by
      intro f hf
      funext u
      have := key0 f hf u
      simp only [Pi.smul_apply, smul_eq_mul, hκ]
      field_simp
      linear_combination -this
    have hmain : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        IsSw (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)) ∧
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)))) := by
      intro y c hc hy f hf
      obtain ⟨y', hy', hrel⟩ := R.oppositeUnipotent_weylConj w hw₀ y c hc hy
      have hx : ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)ᴴ = (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c := by
        have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
          rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
          · rw [hz]; simp
          · rw [hz]; simp [Complex.inv_I]
        rw [Matrix.conjTranspose_smul, hc, hs]
      have hN : R.StepOK w (R.ι w y') (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)) id :=
        R.stepN w hT y' _ hx hy'
      refine ⟨hN.1 _ (hW'.1 f hf), ?_⟩
      by_cases hf0 : ∀ u, f u = 0
      · have : f = 0 := funext hf0
        rw [this, R.locOp_zero hT hG hL y]
        simp [locFT_zero, chirp_zero]
      push Not at hf0
      obtain ⟨u₀, hu₀⟩ := hf0
      have hBΨ : ∀ X, B (B (B (B Ψ))) X = κ⁻¹ * Ψ X := by
        intro X
        obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u₀
        have := key f hf (X + Z)
        rw [hZ3, hΨ.1 X Z hZ1 hZ2, hB4 X Z hZ1 hZ2, h4f f hf] at this
        simp only [Pi.smul_apply, smul_eq_mul] at this
        rw [eq_inv_mul_iff_mul_eq₀ hκ0]
        apply mul_left_cancel₀ hu₀
        linear_combination -this
      have hc3 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hN) hW'
      obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
      have e := (hc3.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
      have e1 := (hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'
      rw [hrel] at e1
      apply R.tens_cancel hΨ.1 hΨ.2.1
      rw [← e1, e]
      funext X
      simp only [RD.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hBΨ]
      ring
    refine ⟨C, s, κ, ε, hs, hκ0, h4f, fun y c hc hy f hf => (hmain y c hc hy f hf).2,
      fun y c hc hy f hf => ?_, hsn, hη⟩
    obtain ⟨hsw, heq⟩ := hmain y c hc hy f hf
    rw [heq, locFT_smul, h4f _ hsw, smul_smul, inv_mul_cancel₀ hκ0, one_smul]

end RD

end PositivityTheory.SiegelWeilFormula

end
end

