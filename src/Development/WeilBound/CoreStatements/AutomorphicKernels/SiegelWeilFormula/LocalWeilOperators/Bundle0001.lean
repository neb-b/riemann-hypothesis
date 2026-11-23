module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.GoodAwayEx

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.ExistsInsW
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace SD

variable (d : SD σ)

theorem ae_ext (z z' : AE F E) (h : ∀ w, piInf (d.B.emb w) z = piInf (d.B.emb w) z') (hf : finOne F • z = finOne F • z') :
    z = z' :=
  Place.ad_ext d.cm d.B.emb h hf

theorem exists_insW (w : InfinitePlace F) : ∃ ins : ℂ →+ AE F E, (∀ z, piInf (d.B.emb w) (ins z) = z) ∧
    (∀ w', w' ≠ w → ∀ z, piInf (d.B.emb w') (ins z) = 0) ∧ ∀ z, finOne F • ins z = 0 := by
  obtain ⟨s, -, h1, h2, h3, -⟩ := Place.exists_sec d.cm d.B.emb
  refine ⟨AddMonoidHom.mk' (fun z => s (Pi.single w z)) (fun a b => by rw [Pi.single_add, h3]), fun z => ?_,
    fun w' hw' z => ?_, fun z => h2 _⟩
  · simp [h1]
  · simp [h1, Pi.single_eq_of_ne hw']

end SD

end PositivityTheory.SiegelWeilFormula

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.IsLocOpOfOk
section
noncomputable section

open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

abbrev SD.LF (d : SD σ) : Type := (Fin d.m → Fin d.n → ℂ) → ℂ

abbrev SD.MF (d : SD σ) : Type := Mx F E d.m d.n → ℂ

namespace RD

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

def StepOK (x : d.G) (A : d.LF → d.LF) (B : d.MF → d.MF) : Prop :=
  (∀ f, IsSw f → IsSw (A f)) ∧ ∀ Ψ, d.IsAwayW w Ψ → d.IsAwayW w (B Ψ) ∧
    ∀ f, IsSw f → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om x Φ) = R.tens w (A f) (B Ψ)

def Good (y : GR d.n) (g f : d.LF) : Prop :=
  ∀ Ψ, d.IsAwayW w Ψ → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om (R.ι w y) Φ) = R.tens w g Ψ

def OkY (y : GR d.n) : Prop := ∀ f, IsSw f → ∃ g, IsSw g ∧ R.Good w y g f

def Lc (y : GR d.n) (f : d.LF) : d.LF := if h : ∃ g, IsSw g ∧ R.Good w y g f then h.choose else 0

theorem isLocOp_of_ok (h : ∀ y, R.OkY w y) : R.IsLocOp w (R.Lc w) := by
  intro y f hf
  have hx := h y f hf
  have e : R.Lc w y f = hx.choose := by simp only [Lc, dif_pos hx]
  rw [e]
  exact ⟨hx.choose_spec.1, fun Ψ hΨ Φ hΦ hT => hx.choose_spec.2 Ψ hΨ Φ hΦ hT⟩

theorem ok_of_step {y : GR d.n} {A : d.LF → d.LF} (h : R.StepOK w (R.ι w y) A id) : R.OkY w y := by
  intro f hf
  exact ⟨A f, h.1 f hf, fun Ψ hΨ Φ hΦ hT => (h.2 Ψ hΨ).2 f hf Φ hΦ hT⟩

theorem step_comp (hsch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch) {x x' : d.G} {A A' : d.LF → d.LF}
    {B B' : d.MF → d.MF} (h : R.StepOK w x A B) (h' : R.StepOK w x' A' B') :
    R.StepOK w (x * x') (A ∘ A') (B ∘ B') := by
  refine ⟨fun f hf => h.1 _ (h'.1 f hf), fun Ψ hΨ => ⟨(h.2 _ (h'.2 Ψ hΨ).1).1, fun f hf Φ hΦ hT => ?_⟩⟩
  have e1 := (h'.2 Ψ hΨ).2 f hf Φ hΦ hT
  have e2 := (h.2 (B' Ψ) (h'.2 Ψ hΨ).1).2 (A' f) (h'.1 f hf) (d.om x' Φ) (hsch x' Φ hΦ) e1
  rw [map_mul, Module.End.mul_apply]
  exact e2

theorem ok_mul (hsch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch) {y y' : GR d.n} (h : R.OkY w y)
    (h' : R.OkY w y') : R.OkY w (y * y') := by
  intro f hf
  obtain ⟨g', hg', hG'⟩ := h' f hf
  obtain ⟨g, hg, hG⟩ := h g' hg'
  refine ⟨g, hg, fun Ψ hΨ Φ hΦ hT => ?_⟩
  rw [map_mul, map_mul, Module.End.mul_apply]
  exact hG Ψ hΨ _ (hsch _ Φ hΦ) (hG' Ψ hΨ Φ hΦ hT)

end RD

end PositivityTheory.SiegelWeilFormula

end
end

