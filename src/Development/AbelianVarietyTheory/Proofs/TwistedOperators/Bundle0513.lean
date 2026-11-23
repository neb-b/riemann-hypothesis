module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormFiniteDimCompactStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0485
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceIsoReadingComponentsCharacters
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch

open GlobalTheory.LFun GlobalTheory.LFun.SplitTie

section Place

variable {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem complMap_apply_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl F} {w : Pl E} (h : w.under (𝓞 F) = v) (b : Af F) :
    complMap h (b v) = GlobalTheory.AdeleBaseChange.locMap F w (b (w.under (𝓞 F))) := by
  subst h; rfl

theorem piW_tmul (b : AF D.host.F) (x : D.host.E) : piW τ (b ⊗ₜ[D.host.F] x) = evFin D.host.F v b * τ x := by
  show splitProj τ (compFin D.host.F D.host.E v (b ⊗ₜ[D.host.F] x)) = _
  rw [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  rfl

theorem cpt_tmul (w : Pl D.host.E) (b : AF D.host.F) (x : D.host.E) :
    cpt (D := D) w (toEAf D (b ⊗ₜ[D.host.F] x)) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.locMap D.host.F w (b.2 (w.under (𝓞 D.host.F))) := by
  have e : toEAf D (b ⊗ₜ[D.host.F] x) = x ⊗ₜ[D.host.F] b.2 := rfl
  rw [e]
  show (toAd D (x ⊗ₜ[D.host.F] b.2)) w = _
  rw [toAd_spec]
  rfl

theorem isPlaceIso_complEquiv : IsPlaceIso τ (splitPrime τ) (complEquiv τ (splitPrime_under τ)) := by
  intro a
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul b x =>
    rw [piW_tmul, cpt_tmul, complEquiv_apply, map_mul, complMap_apply_emb, mul_comm]
    congr 1
    exact complMap_apply_under (splitPrime_under τ) b.2
  | add x y hx hy =>
    rw [RingHom.map_add (piW τ), RingEquiv.map_add (e := _), RingHom.map_add (toEAf D), RingHom.map_add (cpt _), hx, hy]

theorem isEquiv_Fv {F : Type} [Field F] [NumberField F] (v : Pl F) :
    (ValuativeRel.valuation (Fv F v)).IsEquiv (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))) :=
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  ValuativeRel.isEquiv _ _

theorem valued_complEquiv_symm (y : Kw (D := D) (splitPrime τ)) :
    Valued.v ((complEquiv τ (splitPrime_under τ)).symm y) = Valued.v y := by
  conv_rhs => rw [← (complEquiv τ (splitPrime_under τ)).apply_symm_apply y]
  rw [complEquiv_apply, SplitTie.valued_complMap]

theorem continuous_complEquiv_symm : Continuous (complEquiv τ (splitPrime_under τ)).symm := by
  refine continuous_of_continuousAt_zero (complEquiv τ (splitPrime_under τ)).symm ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have h0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp k :=
    ⟨_, (WithZero.exp_log h0).symm⟩
  filter_upwards [(GlobalTheory.Idele.isOpen_valued_le (K := D.host.E) (splitPrime τ) (-((k.natAbs + 1 : ℕ) : ℤ))).mem_nhds
    (by simp)] with a ha
  rw [Valuation.restrict_lt_iff_lt_embedding, hk, valued_complEquiv_symm]
  exact ha.trans_lt (WithZero.exp_lt_exp.2 (by omega))

theorem isLocIso_complEquiv : IsLocIso (complEquiv τ (splitPrime_under τ)) := by
  refine ⟨SplitChart.continuous_complMap _, continuous_complEquiv_symm τ, fun x => ?_⟩
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, (Good.isEquiv_Kw (D := D) _).le_one_iff_le_one,
    (isEquiv_Fv v).le_one_iff_le_one, complEquiv_apply, SplitTie.valued_complMap]

end Place

section Chars

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem chrW_nu {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (hα : X.α = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (hβ : X.β = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j)
    {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : (Fv D.host.F v)ˣ) :
    chrW X.ν τ x = (locGrid G t (splitPrime τ)).nu i j
      (Units.map ((complEquiv τ (splitPrime_under τ) : Fv D.host.F v →* Kw (splitPrime τ))) x) := by
  have e1 : X.ν = G.nu t i (j + 1) := by
    show X.α / X.β = _
    rw [hα, hβ]
    exact mul_div_mul_right_eq_div _ _ _
  have e2 : chrW X.ν τ x = locChar X.ν (splitPrime τ)
      (Units.map ((complEquiv τ (splitPrime_under τ) : Fv D.host.F v →* Kw (splitPrime τ))) x) := rfl
  rw [e2, e1, locChar_eq_of_chrEq (SqNum.chrEq_nu G t i j hL)]
  have hj : (j : ℕ) < D.R.m := j.2
  simp only [SqNum.nuH, Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, div_eq_mul_inv]
  rfl

end Chars

section Psi

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem at_atPl {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (y : Kw (D := D) (splitPrime τ)) :
    At (evFin D.host.F v) (atPl (splitPrime τ) y) := by
  classical
  intro u hu
  refine ae_ext ?_ fun Q => ?_
  · rw [Algebra.smul_def, RingHom.map_mul, (atPl_spec _ y).1, mul_zero, map_zero]
  · rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, (atPl_spec _ y).2, map_zero, map_zero]
    by_cases h : Q = splitPrime τ
    · subst h
      have h1 : cpt (D := D) (splitPrime τ) (toEAf D (algebraMap (AF D.host.F) (AE D) u)) =
          GlobalTheory.AdeleBaseChange.locMap D.host.F (splitPrime τ) (u.2 ((splitPrime τ).under (𝓞 D.host.F))) :=
        (comp_toAd D).base u (splitPrime τ)
      rw [h1, ← complMap_apply_under (splitPrime_under τ)]
      have h2 : u.2 v = 0 := hu
      rw [h2, map_zero, zero_mul]
    · rw [Pi.single_eq_of_ne h, mul_zero]

theorem psiLoc_eq_psiAt (W : G.Weil) {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : Fv D.host.F v) :
    psiLoc W.ψ v x = psiAt W (splitPrime τ) ((xiAt (splitPrime τ))⁻¹ * complEquiv τ (splitPrime_under τ) x) := by
  classical
  set w := splitPrime τ with hw
  set jj := complEquiv τ (splitPrime_under τ) with hjj
  have hξ : xiAt (D := D) w ≠ 0 := (map_ne_zero _).2 cmHost_imaginaryGenerator_ne_zero
  have hz : incA D D.host.xi0 * atPl w ((xiAt w)⁻¹ * jj x) = atPl w (jj x) := by
    rw [← Good.atPl_mul]
    congr 1
    rw [← mul_assoc]
    change xiAt w * (xiAt w)⁻¹ * jj x = jj x
    rw [mul_inv_cancel₀ hξ, one_mul]
  have hcm := isCMExt_host D
  have hp1 : piW τ (atPl w (jj x)) = x :=
    jj.injective (by rw [isPlaceIso_complEquiv τ, (atPl_spec w _).2, Pi.single_eq_same])
  have hp2 : piW (τ.comp D.sp.cm.sig) (atPl w (jj x)) = 0 :=
    (complEquiv (τ.comp D.sp.cm.sig) (splitPrime_under _)).injective (by
      rw [isPlaceIso_complEquiv (τ.comp D.sp.cm.sig), (atPl_spec w _).2, Pi.single_eq_of_ne (splitPrime_comp_ne hcm τ),
        map_zero])
  show psiLoc W.ψ v x = W.ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * atPl w ((xiAt w)⁻¹ * jj x)))
  rw [hz, GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v τ _ (at_atPl τ _), hp1, hp2, add_zero]
  rfl

end Psi

theorem exists_placeIso_chars : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (t : T) (i j : Fin D.R.m) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), X.α = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j → X.β = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j →
    ∀ {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E), splitPrime τ = w →
    ∃ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso τ w jj ∧ IsLocIso jj ∧
      (∀ x, chrW X.ν τ x = (locGrid G t w).nu i j (Units.map (jj : Fv D.host.F v →* Kw w) x)) ∧
      ∀ x, psiLoc W.ψ v x = psiAt W w ((xiAt w)⁻¹ * jj x) := by
  intro D T L sc G μ₀ hL W t i j X hα hβ v τ w hw
  subst hw
  exact ⟨complEquiv τ (splitPrime_under τ), isPlaceIso_complEquiv τ, isLocIso_complEquiv τ,
    fun x => chrW_nu hL t i j X hα hβ τ x, fun x => psiLoc_eq_psiAt W τ x⟩

end GlobalTheory.FlipMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKSubmoduleInfimumAndIrreducibleSupremum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.CuspGK

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

theorem isGKSub_sInf (s : Set (Submodule ℂ (GA D V → ℂ))) (h : ∀ A ∈ s, IsGKSub θ M A) : IsGKSub θ M (sInf s) := by
  constructor
  · intro τ g hg f hf
    exact Submodule.mem_sInf.2 fun A hA => (h A hA).k τ g hg f (Submodule.mem_sInf.1 hf A hA)
  · intro τ X hX f hf
    exact Submodule.mem_sInf.2 fun A hA => (h A hA).lie τ X hX f (Submodule.mem_sInf.1 hf A hA)


open scoped Matrix in
variable {M} in
theorem InK.inv {τ : D.what₂.Tau} {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (h : InK M τ g) : InK M τ g⁻¹ := by
  obtain ⟨hU, hk⟩ := h
  have hfd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  set k := M.fr τ * g * (M.fr τ)⁻¹ with hkdef
  have hku : k ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := hk.1
  have hsk : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hku
  have hks : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hku
  have hkdet : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det _).1 ⟨⟨k, star k, hks, hsk⟩, rfl⟩
  have hdet : k.det = g.det := by
    rw [hkdef, Matrix.det_mul, Matrix.det_mul, mul_comm (M.fr τ).det, mul_assoc, ← Matrix.det_mul,
      Matrix.mul_nonsing_inv _ hfd, Matrix.det_one, mul_one]
  have hgd : IsUnit g.det := hdet ▸ hkdet
  have hg1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgd
  have hU' : gᴴ * gramAt D V τ * g = gramAt D V τ := hU
  refine ⟨?_, ?_⟩
  · show (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = gramAt D V τ
    calc (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * gramAt D V τ * g) * g⁻¹ := by rw [hU']
      _ = (g * g⁻¹)ᴴ * gramAt D V τ * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [hg1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · have e1 : M.fr τ * g⁻¹ * (M.fr τ)⁻¹ = k⁻¹ := by
      rw [hkdef, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hfd]
      simp only [Matrix.mul_assoc]
    have hinv : k⁻¹ = star k := Matrix.inv_eq_left_inv hsk
    rw [e1, hinv]
    refine ⟨Matrix.mem_unitaryGroup_iff.2 (by rw [star_star]; exact hsk), ?_⟩
    have hJ : star (Formalism.REAL.Jm (M.ε τ)) = Formalism.REAL.Jm (M.ε τ) := Formalism.REAL.Jm_conjTranspose _
    have hcomm : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ, m * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * m →
        star m * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * star m := fun m hm => by
      have h2 : star (m * Formalism.REAL.Jm (M.ε τ)) = star (Formalism.REAL.Jm (M.ε τ) * m) := congrArg star hm
      rw [star_mul, star_mul, hJ] at h2
      exact h2.symm
    exact hcomm k hk.2

end GlobalTheory.CuspGK

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergLineDerivativeFiniteSpan
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ArchUniq
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.HeisDerivSpan

open GlobalTheory.HeisDeriv

variable {F : Type} [Field F] [NumberField F]

def trPairL {κ : Type} [Fintype κ] (z : κ → mixedEmbedding.mixedSpace F) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).comp
    (∑ i, (LinearMap.mulLeft ℝ (z i)).comp (LinearMap.proj i))

theorem trPairL_apply {κ : Type} [Fintype κ] (z w : κ → mixedEmbedding.mixedSpace F) :
    trPairL z w = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, z i * w i) := by
  simp [trPairL, LinearMap.sum_apply]

theorem fderiv_basis {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (f : SInf F κ)
    (z v : κ → mixedEmbedding.mixedSpace F) :
    fderiv ℝ (⇑f) z v = ∑ j, (b.repr v j : ℂ) * fderiv ℝ (⇑f) z (b j) := by
  calc fderiv ℝ (⇑f) z v = fderiv ℝ (⇑f) z (∑ j, b.repr v j • b j) := by rw [b.sum_repr]
    _ = _ := by rw [map_sum]; simp only [map_smul, Complex.real_smul]

theorem mult_basis {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (y : κ → AF F)
    (z : κ → mixedEmbedding.mixedSpace F) :
    mult F y z = ∑ j, (b.repr (fun i => evI F (y i)) j : ℂ) * mult F (liftV (b j)) z := by
  have h1 : ∀ w : κ → AF F, trForm F w z = trPairL z (fun i => evI F (w i)) := by
    intro w
    rw [trForm_apply, trPairL_apply]
  have h2 : trPairL z (fun i => evI F (y i)) =
      ∑ j, b.repr (fun i => evI F (y i)) j * trPairL z (b j) := by
    calc trPairL z (fun i => evI F (y i))
        = trPairL z (∑ j, b.repr (fun i => evI F (y i)) j • b j) := by rw [b.sum_repr]
      _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul]
  have h3 : ∀ j, (fun i => evI F (liftV (F := F) (b j) i)) = b j := fun j => Coord.loc_lift (b j)
  simp only [mult_apply, h1, h3, h2]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.HeisDerivSpan

namespace GlobalTheory.HeisDerivSpan

open GlobalTheory.HeisDeriv GlobalTheory.HeisDerivArch

variable {F : Type} [Field F] [NumberField F]

theorem actsD_heisLine_eq {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (f g : SInf F (Fin n × Fin d))
    (hg : ActsD (evI F) (M.heisLine ψ u) f g) :
    g = heisD F (fun i => evI F ((M.co.e u).1 i)) (M.co.e u).2 f := by
  ext y
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hr := hR f
  set x : Fin n × Fin d → AF F := liftV y with hx
  have hd1 := hg R hr x
  have hd2 := actsD_heisLine_heisD M ψ hψ u f R hr x
  have huniq := hd1.unique hd2
  have hRx : R x = R 0 := by
    have := hr.1 0 x (at_liftV y)
    rwa [zero_add] at this
  have hlx : (fun i => evI F (x i)) = y := Coord.loc_lift y
  simp only [tens, hlx, hRx] at huniq
  exact mul_right_cancel₀ hR0 huniq

theorem heisLine_deriv_finite_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∃ (m : ℕ) (L : Fin m → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)),
      ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = D f) ∧
        ∀ f, D f ∈ Submodule.span ℂ (Set.range fun i => L i f) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ
  let b := Module.finBasis ℝ (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  set N := Module.finrank ℝ (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  let A : Fin N → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun j =>
    (LineDeriv.lineDerivOpCLM ℂ (SInf F (Fin n × Fin d)) (b j)).toLinearMap
  let B : Fin N → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun j =>
    (SchwartzMap.smulLeftCLM ℂ (⇑(mult F (liftV (b j))))).toLinearMap
  refine ⟨N + N, fun i => Sum.elim A B (finSumFinEquiv.symm i), fun u _ => ?_⟩
  refine ⟨heisD F (fun i => evI F ((M.co.e u).1 i)) (M.co.e u).2, fun f f₁ =>
    ⟨actsD_heisLine_eq M ψ hψ u f f₁, fun h => by subst h; exact actsD_heisLine_heisD M ψ hψ u f⟩, fun f => ?_⟩
  set S := Submodule.span ℂ (Set.range fun i => Sum.elim A B (finSumFinEquiv.symm i) f) with hS
  have hA : ∀ j, A j f ∈ S := fun j => Submodule.subset_span ⟨finSumFinEquiv (Sum.inl j), by simp only [Equiv.symm_apply_apply, Sum.elim_inl]⟩
  have hB : ∀ j, B j f ∈ S := fun j => Submodule.subset_span ⟨finSumFinEquiv (Sum.inr j), by simp only [Equiv.symm_apply_apply, Sum.elim_inr]⟩
  set v : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).1 i) with hv
  set y := (M.co.e u).2 with hy
  have key : heisD F v y f = ∑ j, (b.repr v j : ℂ) • A j f +
      ∑ j, (b.repr (fun i => evI F (y i)) j : ℂ) • B j f := by
    ext z
    rw [heisD_apply, fderiv_basis b f z v, mult_basis b y z, Finset.sum_mul]
    simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul, A, B,
      ContinuousLinearMap.coe_coe, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [SchwartzMap.smulLeftCLM_apply_apply (mult F (liftV (F := F) (b j))).hasTemperateGrowth]
    simp only [smul_eq_mul]
    ring
  rw [key]
  exact add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hA j))
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hB j))

end GlobalTheory.HeisDerivSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentPartFinitePointMemShiftedTensorLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LiftLevel

theorem partAt_finW_mem_hatA_sh : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ y ∈ tens (stdL D.host.E S.rank) (conjI Lv.𝔪 • C.X.Λ), GlobalTheory.LiftLevel.partAt e (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) := by
  intro D S T C Pg Q e he Lv hLv y hy

  have hm : Lv.𝔪 ⊔ conjI Lv.𝔪 = ⊤ := Ideal.isCoprime_iff_sup_eq.1 Lv.cop
  have h1 : (1 : 𝓞 D.host.E) ∈ Lv.𝔪 ⊔ conjI Lv.𝔪 := by rw [hm]; exact Submodule.mem_top
  obtain ⟨t, ht, c, hc, htc⟩ := Submodule.mem_sup.1 h1
  have hcP : ∀ PP ∈ Pg ∪ Q, conjI Lv.𝔪 ≤ PP.asIdeal := by
    intro PP hPP x hx
    have h2 := mem_of_mem_conjI hx
    rw [hLv, liftI] at h2
    have h3 : stO x ∈ conjI PP.asIdeal := Finset.inf_le (f := fun PP : Formalism.L2.DIV.Pl D.host.E => conjI PP.asIdeal)
      hPP (Ideal.prod_le_inf h2)
    have h4 := mem_of_mem_conjI h3
    have h5 : stO (stO x) = x := RingOfIntegers.ext (star_star _)
    rwa [h5] at h4
  have htP : ∀ PP ∈ Pg ∪ Q, t ∉ PP.asIdeal := by
    intro PP hPP htm
    have h6 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal := htc ▸ add_mem htm (hcP PP hPP hc)
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h6)
  have hPQ : (Pg ∪ Q).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply Lv.proper
    rw [hLv, liftI, hne, Finset.prod_empty, Ideal.one_eq_top]
  have ht0 : (t : D.host.E) ≠ 0 := by
    obtain ⟨PP, hPP⟩ := hPQ
    intro h
    apply htP PP hPP
    have : t = 0 := RingOfIntegers.ext (h.trans rfl)
    rw [this]; exact zero_mem _

  have hsub : conjI Lv.𝔪 • C.X.Λ ≤ C.X.Λ := Submodule.smul_le_right
  have htL : ∀ v ∈ conjI Lv.𝔪 • C.X.Λ, t • v ∈ Lv.sh C.X.Λ := by
    intro v hv s hs
    have hv' : t • v ∈ Lv.𝔪 • C.X.Λ := Submodule.smul_mem_smul ht (hsub hv)
    exact Submodule.smul_mem _ s hv'
  have hty : (t : D.host.E) • y ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ) := smul_mem_tens t htL hy
  have h0 : finW S T ((t : D.host.E) • y) ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) := by
    rw [GlobalTheory.Ker.SignVac.finW_eq]
    exact GlobalTheory.Ker.SignVac.finTens_mem (GlobalTheory.LatVac.one_mem_intAf _) hty

  have hz1 : finPart D (e * incA D ((t : D.host.E))⁻¹) ∈ intAE D :=
    GlobalTheory.IdemSumInt.finPart_idemSum_mul_inv_mem D e (Pg ∪ Q) he t htP
  have hA' : ∀ o : 𝓞 D.host.E, ∀ z ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ),
      (o : D.host.E) • z ∈ tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ) :=
    fun o z hz => smul_mem_tens o (fun u hu => Submodule.smul_mem _ o hu) hz
  have e1 : partAt e (finW S T y) = (e * incA D ((t : D.host.E))⁻¹) • finW S T ((t : D.host.E) • y) := by
    have e2 : finW S T ((t : D.host.E) • y) =
        (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) • finW S T y := by
      rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul,
        Matrix.transpose_smul]
    have e3 : finW S T y = (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • finW S T y := by
      rw [GlobalTheory.Ker.SignVac.finW_eq, GlobalTheory.LatVac.tmul_smul_finTens, one_mul, one_smul]
    rw [e2, smul_smul, mul_assoc]
    have e4 : incA D ((t : D.host.E))⁻¹ * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t : D.host.E) : AE D) =
        pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E) := by
      change ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((t : D.host.E))⁻¹) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ ht0]
    rw [e4, mul_smul, ← e3, partAt_eq_smul]
  rw [e1]
  exact smul_mem_hatA_of_int hA' hz1 h0

end GlobalTheory.LiftLevel

end
end

