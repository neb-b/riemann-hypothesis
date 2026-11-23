module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.CharCrysModel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

theorem isUnram_iff (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) : IsUnram (χ.loc w) ↔ χ.UnrAt w := by
  refine forall_congr' fun x => imp_congr_left ?_
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  rw [← ord_eq_zero_iff, SphCompletion.ord_completion, neg_eq_zero, IsUnitAt]
  constructor
  · intro hl
    rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]
  · intro hv
    rw [hv, WithZero.log_one]

theorem of_classicalTheorems (hD : HeckeLAdicCharacterDeRham) (hB : DeRhamPotSemistable) (hW : AlgebraicCharacterWD)
    (hL : LocalLanglandsGL) : HeckeLAdicCharacterCrystalline := by
  intro E Ω _ _ _ _ _ l _ P AI hT ι art ha χ n μ h1 h2 h3 w A h O _ _ _ Bw hj hu
  obtain ⟨rc, ⟨a, ha', -⟩, -⟩ := hL.1 E Ω A w h
  have hξ := ParamAboveModel.isComp_loc (w := w) χ
  have hc : Continuous fun g : ↥(Dec (F := E) A) =>
      (((rk1 μ).comp (Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) := by
    refine continuous_matrix fun i j => ?_
    have e : (fun g : ↥(Dec (F := E) A) =>
      (((rk1 μ).comp (Dec (F := E) A).subtype g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) i j) =
      fun g : ↥(Dec (F := E) A) => ((μ g : (Om l)ˣ) : Om l) := by
      funext g
      rw [Subsingleton.elim i j]
      simp [rk1]
    rw [e]
    exact Units.continuous_val.comp (h2.comp continuous_subtype_val)
  have hr := hB.isPstAt hT.some Bw _ hc (hD E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj).1
  rw [← GlobalTheory.PstLaws.unr_wdAt_iff Bw h hj P ι _ hr,
    hW E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj _ hξ a ha',
    GlobalTheory.LocLanglands.Test.unr_lpOfChar_iff ha' hξ.1]
  exact (isUnram_iff χ w).2 hu

end GlobalTheory.Published.CharCrysModel

end
