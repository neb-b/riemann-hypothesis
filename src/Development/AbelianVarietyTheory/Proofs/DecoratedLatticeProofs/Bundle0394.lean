module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TypeChainPrincipalEntryNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelBoxProductOrthogonalSumTarget
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceUpWittExtendByZeroRankZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.RankZeroSrc

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ι_mul_incA (p : Place D k) (x : k) (a : D.host.E) : p.ι x * (incA D a : AE D) = p.ι (x * p.pr a) := by
  have h : x * p.pr a = p.π (p.ι x * (incA D a : AE D)) := by rw [map_mul, p.π_ι]; rfl
  rw [h, p.ι_π, ← mul_assoc, Witness.e_ι]

theorem map_ι_mul_rat (p : Place D k) {l m : ℕ} {Y : Type} [Fintype Y] (N : Matrix Y (Fin l) k)
    (M : Matrix (Fin l) (Fin m) D.host.E) :
    (N.map p.ι) * (rat M : Matrix (Fin l) (Fin m) (AE D)) = (N * M.map p.pr).map p.ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rat, Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul_incA]

theorem fromCols_toCols₁ {Z n : Type} (x : Matrix Z (n ⊕ Fin 0) k) : fromCols x.toCols₁ 0 = x := by
  conv_rhs => rw [← Matrix.fromCols_toCols x]
  congr 1
  ext i j
  exact j.elim0

theorem splitLocalPlace_up_wittExtendByZero_rankZero (p : Place D k) {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z] (J : JacLev D 0)
    (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin 0)) (hF : p.IsJacFrame J s hh F₀ F) (T : HSp D)
    (FT : Frame k T.rank Z) (x : Matrix Z n k) :
    J.d.ext0 T (p.up F₀ FT x) = p.up F FT (fromCols x 0) := by
  have hq : J.d.q0 * J.d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact J.d.p0_j0)
  have hq' : J.d.q0.map p.pr * J.d.i₀.map p.pr = 1 := by
    rw [← show (J.d.q0 * J.d.i₀).map p.pr = J.d.q0.map p.pr * J.d.i₀.map p.pr from Matrix.map_mul (f := Witness.prH p), hq]
    exact Matrix.map_one _ (map_zero (Witness.prH p)) (map_one (Witness.prH p))
  have hβ : F.β.toCols₁ = J.d.i₀.map p.pr * F₀.β := by ext r a; exact hF.2.1 r a
  have h1 : F.β * F.γ = 1 := F.βγ
  have h0 : F.β.toCols₂ * F.γ.toRows₂ = 0 := by ext i j; simp [Matrix.mul_apply]
  rw [← Matrix.fromCols_toCols F.β, ← Matrix.fromRows_toRows F.γ, Matrix.fromCols_mul_fromRows, h0, add_zero, hβ] at h1
  have hγ : F.γ.toRows₁ = F₀.γ * J.d.q0.map p.pr := by
    have e : F₀.γ * J.d.q0.map p.pr * (J.d.i₀.map p.pr * F₀.β * F.γ.toRows₁) = F.γ.toRows₁ := by
      rw [show F₀.γ * J.d.q0.map p.pr * (J.d.i₀.map p.pr * F₀.β * F.γ.toRows₁) =
          F₀.γ * (J.d.q0.map p.pr * J.d.i₀.map p.pr) * F₀.β * F.γ.toRows₁ by simp only [Matrix.mul_assoc],
        hq', Matrix.mul_one, F₀.γβ, Matrix.one_mul]
    rw [← e, h1, Matrix.mul_one]
  rw [HypDec.matrixExtendByZero_apply]
  unfold Place.up
  rw [HypDec.p0, map_ι_mul_rat]
  congr 1
  conv_rhs => rw [← Matrix.fromRows_toRows F.γ, Matrix.mul_assoc, Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero, hγ]
  simp only [Matrix.mul_assoc]

theorem wittExtensionByZero_symplectic_form_eq {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (w w' : WO S₀ T) :
    symplO S T (d.ext0 T w) (d.ext0 T w') = symplO S₀ T w w' := by
  have h := d.hO_ext T 0 0 0 0 w w'
  simp only [map_zero, zero_add, add_zero, pairS, Matrix.mul_zero, trace_zero] at h
  unfold symplO
  rw [h]

theorem wittExtensionByZero_preserves_isHalf {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) {e : AE D} {y : WO S₀ T} (hy : IsHalf e y) :
    IsHalf e (d.ext0 T y) := fun i j => by
  rw [HypDec.matrixExtendByZero_apply, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, hy i l]

end GlobalTheory.LocMod.RankZeroSrc

namespace GlobalTheory.LocMod.RankZeroSrc

theorem localModel_rankZeroWitt_source_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (J : JacLev D 0) (s hh : k) (n Z : Type) [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z] (F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n) (F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin 0)), p.IsJacFrame J s hh F₀ F → ∀ (T : HSp D) (FT : GlobalTheory.LocMod.Frame k T.rank Z) (Tm : SB (Matrix Z (n ⊕ Fin 0) k) →ₗ[ℂ] (WO J.W T → ℂ)), p.IsModel ψ F FT Tm → ∃ T₂ : SB (Matrix Z n k) →ₗ[ℂ] (WO J.W₀ T → ℂ), p.IsModel ψ F₀ FT T₂ ∧ ∀ (Ψ : SB (Matrix Z n k)) (Φ : SB (Matrix Z (n ⊕ Fin 0) k)), (∀ x, Ψ.1 x = Φ.1 (fromCols x 0)) → ∀ w, T₂ Ψ w = Tm Φ (J.d.ext0 T w) := by
  intro D k _ _ _ _ p ψ hψ J s hh n Z _ _ _ _ F₀ F hF T FT Tm hM
  have hT := _root_.GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D ψ J.W J.W₀ T J.d hψ
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := Z) (n' := n ⊕ Fin 0)
  have hc1 : Continuous fun x : Matrix Z (n ⊕ Fin 0) k => x.toCols₁ :=
    continuous_pi fun i => continuous_pi fun j => by
      show Continuous fun a : Matrix Z (n ⊕ Fin 0) k => a i (Sum.inl j)
      exact (continuous_apply (Sum.inl j)).comp (continuous_apply i)
  have hc2 : Continuous fun x : Matrix Z n k => (fromCols x 0 : Matrix Z (n ⊕ Fin 0) k) :=
    continuous_pi fun i => continuous_pi fun j => by
      rcases j with j | j
      · show Continuous fun a : Matrix Z n k => a i j
        exact (continuous_apply j).comp (continuous_apply i)
      · exact j.elim0
  let R : SB (Matrix Z n k) → SB (Matrix Z (n ⊕ Fin 0) k) := fun Ψ =>
    ⟨fun x => Ψ.1 x.toCols₁, GlobalTheory.FinPl.Comm.comp_mem_SB Ψ.2 hc1 hc2 fromCols_toCols₁⟩
  have hR : ∀ Ψ x, (R Ψ).1 x = Ψ.1 x.toCols₁ := fun _ _ => rfl
  let T₂ : SB (Matrix Z n k) →ₗ[ℂ] (WO J.W₀ T → ℂ) :=
    { toFun := fun Ψ w => Tm (R Ψ) (J.d.ext0 T w)
      map_add' := fun Ψ Ψ' => by
        funext w
        rw [show R (Ψ + Ψ') = R Ψ + R Ψ' from Subtype.ext rfl, map_add (f := _)]
        rfl
      map_smul' := fun c Ψ => by
        funext w
        rw [show R (c • Ψ) = c • R Ψ from Subtype.ext rfl, map_smul]
        rfl }
  have hT₂ : ∀ Ψ w, T₂ Ψ w = Tm (R Ψ) (J.d.ext0 T w) := fun _ _ => rfl
  have hup : ∀ x, p.up F FT x = J.d.ext0 T (p.up F₀ FT x.toCols₁) := fun x => by
    rw [splitLocalPlace_up_wittExtendByZero_rankZero p J s hh F₀ F hF T FT, fromCols_toCols₁]
  refine ⟨T₂, ⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩, fun Ψ Φ h w => ?_⟩
  · exact (hT.2.2.1 (Tm (R Ψ))).2 (hM.theta _)
  · have e1 : Tm (R Ψ') = heisO ψ J.W T (p.up F FT (fromCols x 0)) (Tm (R Ψ)) := hM.trans _ _ _ fun t => by
      rw [hR, hR, h]
      congr 1
    funext w
    rw [hT₂, e1, ← splitLocalPlace_up_wittExtendByZero_rankZero p J s hh F₀ F hF T FT]
    simp only [heisO, hT₂]
    rw [J.d.wittDecomp_sympl_extAnisotropic_extAnisotropic, map_add (f := _)]
  · have e1 : Tm (R Ψ') = heisO ψ J.W T (J.d.ext0 T y) (Tm (R Ψ)) := hM.modul _ (wittExtensionByZero_preserves_isHalf J.d T hy) _ _ fun t => by
      rw [hR, hR, h, hup, wittExtensionByZero_symplectic_form_eq]
    funext w
    rw [hT₂, e1]
    simp only [heisO, hT₂]
    rw [J.d.wittDecomp_sympl_extAnisotropic_extAnisotropic, map_add (f := _)]
  · rw [hT₂, show R Ψ = Φ from Subtype.ext (funext fun x => by rw [hR, h, fromCols_toCols₁])]

end GlobalTheory.LocMod.RankZeroSrc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepKernelLocalModels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastKerLoc


open GlobalTheory.LocFlat.CFac in
theorem lastLoc : ∀ (D : D7), LastLoc D := by
  intro D k _ _ _ _ _ _ p ν hν ψ hψ ψk hχ ρ B S X T L'' o'' τ hL hτ s z₀ hs hz n n' Z _ _ _ _ _ _ FA F₀ FS FT FX hcore hFX T₁ T₂ hT₁ hT₂
  classical
  obtain ⟨-, hck, -⟩ := _root_.GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hψc, hψ1⟩ := hck ψk hχ
  let κ : WO S L'' → WO B.L S := fun w => GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.L S ((rat τ : Mx D B.L.rank L''.rank) * w)
  let Bl : SB (Matrix Z n k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.A S → WO S X → ℂ) :=
    LinearMap.mk₂ ℂ (fun Ψ₂ Ψ₁ u => o''.boxT S (T₂ Ψ₂) fun w => T₁ Ψ₁ ((B.o.resS S).symm (u, κ w)))
      (by intros; funext u v; simp only [OrthDec.boxT, map_add (f := _), Pi.add_apply, add_mul])
      (by intros; funext u v; simp only [OrthDec.boxT, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc])
      (by intros; funext u v; simp only [OrthDec.boxT, map_add (f := _), Pi.add_apply, mul_add])
      (by intros; funext u v; simp only [OrthDec.boxT, map_smul, Pi.smul_apply, smul_eq_mul]; ring)
  obtain ⟨Λ, hΛ1, hΛ2⟩ := _root_.GlobalTheory.LocFlat.CQLast.exists_pair_map k ν hν ψk hψc hψ1 n n' Z _ Bl
  obtain ⟨hXi, hPsi⟩ := _root_.GlobalTheory.LocFlat.LastColumn.lastColumn_datum_mem_SB k ν hν ψk hψc hψ1 n n' Z
  obtain ⟨hHat, hDec⟩ := _root_.GlobalTheory.LocMod.LastRow.transform_onto_and_span_lastRow k ν hν ψk hψc hψ1 n Z
  have hBl : ∀ a Ψ u v, Bl a Ψ u v = T₂ a (o''.resT S v).1 * T₁ Ψ ((B.o.resS S).symm (u, κ (o''.resT S v).2)) :=
    fun _ _ _ _ => rfl
  refine ⟨Λ, ⟨?_, ?_⟩, ?_⟩
  · intro Ξ₂ v
    obtain ⟨N, a, c, g, hg, hsum⟩ := hDec Ξ₂
    have hsl := fun i => _root_.GlobalTheory.SliceLeft.slice_left D k p ψ ρ B S s n n' FA F₀ FS hcore T₁ hT₁ (c i) (κ (o''.resT S v).2)
    choose T' hT' hT'eq using hsl
    obtain ⟨hz0, hlin⟩ := _root_.GlobalTheory.LocMod.Place.isModel_linear D k p ψ n n' B.A S FA FS
    refine ⟨∑ i, (T₂ (a i) (o''.resT S v).1) • T' i, ?_, ?_⟩
    · refine Finset.sum_induction _ (fun T => p.IsModel ψ FA FS T) (fun _ _ h1 h2 => (hlin _ _ h1 h2).1) hz0 ?_
      intro i _
      exact (hlin _ _ (hT' i) (hT' i)).2 _
    · intro Ξ₁ Ξ hΞ u
      have hΞs : Ξ = ∑ i, prodSB Ξ₁ (g i) := by
        apply Subtype.ext
        funext q
        rw [hΞ, Submodule.coe_sum, Finset.sum_apply, hsum, Submodule.coe_sum, Finset.sum_apply, Finset.mul_sum]
        rfl
      have hPi : ∀ i, ∃ Ψ₁ : SB (Matrix n (n' ⊕ Unit) k), ∀ x, Ψ₁.1 x = Ξ₁.1 x.toCols₁ * (c i).1 (Matrix.of fun r _ => x r (Sum.inr ())) :=
        fun i => hPsi Ξ₁ (c i)
      choose Ψ hΨ using hPi
      have hterm : ∀ i, Λ (prodSB Ξ₁ (g i)) = Bl (a i) (Ψ i) := fun i =>
        hΛ2 Ξ₁ (a i) (c i) (Ψ i) (prodSB Ξ₁ (g i)) (hΨ i) (fun q => by rw [prodSB_apply, hg])
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hΞs, map_sum, Finset.sum_apply, Finset.sum_apply, LinearMap.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hterm, hBl, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hT'eq i Ξ₁ (Ψ i) (hΨ i) u]
  · intro Ξ₁ u
    obtain ⟨FL, hFL, hsl⟩ := _root_.GlobalTheory.SliceLine.slice_line D k p ψ ρ B S s n n' FA F₀ FS hcore T₁ hT₁
    obtain ⟨TLS, hTLS, hTLSeq⟩ := hsl Ξ₁ u
    obtain ⟨FL'', hFL'', TL, hTL, hTLeq⟩ := _root_.GlobalTheory.KappaModel.kappa_model D k p ν hν ψ hψ ψk hχ B.L S L'' B.ζ τ hL hτ s z₀ hs hz n FS FL hFL TLS hTLS
    let P : SB (Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k) :=
      { toFun := fun g => prodSB Ξ₁ g
        map_add' := fun g g' => by apply Subtype.ext; funext q; simp [prodFn, mul_add]
        map_smul' := fun c g => by apply Subtype.ext; funext q; simp [prodFn]; ring }
    let TX : SB (Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] (WO S X → ℂ) := LinearMap.proj u ∘ₗ Λ ∘ₗ P
    have hTXa : ∀ g, TX g = Λ (prodSB Ξ₁ g) u := fun _ => rfl
    refine ⟨TX, _root_.GlobalTheory.LocMod.BoxModel.isModel_boxT D k p ψ S X T L'' o'' n Z FS FT FL'' FX ?_ T₂ TL hT₂ hTL TX ?_, ?_⟩
    · rw [hFX]
      congr 1
      ext r j
      simp [Matrix.mul_apply, hFL'', Matrix.mulVec, dotProduct]
    · intro a b Φ hΦ
      obtain ⟨c, hc⟩ := hHat b
      obtain ⟨Ψ₁, hΨ₁⟩ := hPsi Ξ₁ c
      have h := hΛ2 Ξ₁ a c Ψ₁ (prodSB Ξ₁ Φ) hΨ₁ (fun q => by rw [prodSB_apply, hΦ, hc]; rfl)
      funext v
      rw [hTXa, h, hBl, OrthDec.boxT, hTLeq c b hc, hTLSeq c Ψ₁ hΨ₁]
    · intro Ξ₂ Ξ hΞ v
      have : Ξ = prodSB Ξ₁ Ξ₂ := Subtype.ext (funext hΞ)
      subst this
      rfl
  · intro Ψ₁ Ψ₂
    obtain ⟨Ξ, hΞ⟩ := hXi Ψ₁ Ψ₂
    refine ⟨Ξ, hΞ, fun u => ?_⟩
    rw [hΛ1 Ψ₁ Ψ₂ Ξ hΞ]
    rfl

end GlobalTheory.LastKerLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLevelPrimePhiOneEqOneIffColumns
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section
namespace GlobalTheory.PhiOneVal

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_last_of_pair {a : ℕ} (Q : Pair k (Fin a)) : ∃ r : Fin a, r.1 + 1 = a := by
  rcases a with _ | a
  · exact absurd (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]) Q.fn_ne
  · exact ⟨Fin.last a, rfl⟩

theorem hasVal_finset_sum {n ι : Type} (Q : Pair k n) (s : Finset ι) (x : ι → n → k) (v : ι → 𝓀[k])
    (h : ∀ i, Q.HasVal (x i) (v i)) : Q.HasVal (∑ i ∈ s, x i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Pair.mem_ker.1 (zero_mem Q.ker)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i).add ih

theorem maps_iff_basis {n n' : Type} [Fintype n] [DecidableEq n] (Q : Pair k n) (Q' : Pair k n') (A A' : Matrix n n k)
    (hA : A' * A = 1) (hQ : ∀ x ∈ Q.lat, ∀ r, (A *ᵥ x) r ∈ 𝒪[k]) (v : n → 𝓀[k])
    (hv : ∀ r, Q.HasVal (A' *ᵥ Pi.single r 1) (v r)) (M : Matrix n' n k) :
    Maps Q Q' M ↔ ∀ r, Q'.HasVal (M *ᵥ (A' *ᵥ Pi.single r 1)) (v r) := by
  rw [maps_iff_hasVal]
  refine ⟨fun h r => h _ _ (hv r), fun h y c hy => ?_⟩
  let w : n → 𝒪[k] := fun r => ⟨_, hQ y hy.mem r⟩
  have e : y = ∑ r, w r • (A' *ᵥ Pi.single r 1) := by
    have e1 : A *ᵥ y = ∑ r, w r • (Pi.single r 1 : n → k) := by
      ext i
      simp [w, Pi.single_apply, Finset.sum_apply, Subring.smul_def]
    calc y = A' *ᵥ (A *ᵥ y) := by rw [mulVec_mulVec, hA, one_mulVec]
      _ = _ := by
        rw [e1, mulVec_sum]
        exact Finset.sum_congr rfl fun r _ => mulVec_smul _ _ _
  have h1 := hasVal_finset_sum Q Finset.univ _ _ fun r => (hv r).smul (w r)
  have h2 := hasVal_finset_sum Q' Finset.univ _ _ fun r => (h r).smul (w r)
  rw [← e] at h1
  rw [hy.unique h1]
  convert h2 using 1
  conv_lhs => rw [e, mulVec_sum]
  exact Finset.sum_congr rfl fun r _ => mulVec_smul _ _ _

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (φ : E →+* k) (ψ : 𝓞 E →+* 𝒪[k])

theorem hasVal_col_iff (hψ : ∀ c, (ψ c : k) = φ (algebraMap (𝓞 E) E c))
    (hres : ∀ c, residue 𝒪[k] (ψ c) = 0 ↔ c ∈ P.asIdeal)
    (hint : ∀ x : E, φ x ∈ 𝒪[k] → ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E s * x)
    {b : ℕ} (Q : Pair k (Fin b)) (B B' : Matrix (Fin b) (Fin b) k) (hB : B * B' = 1)
    (hQ : ∀ x ∈ Q.lat, ∀ r, (B *ᵥ x) r ∈ 𝒪[k]) (t : 𝓞 E)
    (hv : ∀ w : Fin b → 𝓞 E, ∀ r : Fin b, r.1 + 1 = b →
      Q.HasVal (B' *ᵥ fun r' => φ (algebraMap (𝓞 E) E (w r'))) (residue 𝒪[k] (ψ (t * w r))))
    (u : Fin b → E) (ε : 𝓞 E) :
    Q.HasVal (B' *ᵥ fun q => φ (u q)) (residue 𝒪[k] (ψ (t * ε))) ↔
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ c : Fin b → 𝓞 E, (∀ q, algebraMap (𝓞 E) E (c q) = algebraMap (𝓞 E) E s * u q) ∧
        ∀ q : Fin b, q.1 + 1 = b → t * (c q - s * ε) ∈ P.asIdeal := by
  have key : ∀ (s : 𝓞 E) (c : Fin b → 𝓞 E), (∀ q, algebraMap (𝓞 E) E (c q) = algebraMap (𝓞 E) E s * u q) →
      (B' *ᵥ fun r' => φ (algebraMap (𝓞 E) E (c r'))) = ψ s • (B' *ᵥ fun q => φ (u q)) := by
    intro s c hc
    rw [← mulVec_smul]
    congr 1
    ext q
    rw [hc, map_mul, ← hψ]
    rfl
  have key2 : ∀ s c : 𝓞 E, t * (c - s * ε) ∈ P.asIdeal ↔
      residue 𝒪[k] (ψ (t * c)) = residue 𝒪[k] (ψ s) * residue 𝒪[k] (ψ (t * ε)) := by
    intro s c
    rw [← hres, ← map_mul, ← map_mul, show t * (c - s * ε) = t * c - s * (t * ε) by ring, map_sub, map_sub, sub_eq_zero]
  constructor
  · intro h
    have h1 := hQ _ h.mem
    rw [mulVec_mulVec, hB, one_mulVec] at h1
    choose s hs c hc using fun q => hint _ (h1 q)
    have hc' : ∀ q, algebraMap (𝓞 E) E (c q * ∏ q' ∈ Finset.univ.erase q, s q') =
        algebraMap (𝓞 E) E (∏ q', s q') * u q := by
      intro q
      rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ q), map_mul, map_mul, hc]
      ring
    refine ⟨∏ q, s q, ?_, fun q => c q * ∏ q' ∈ Finset.univ.erase q, s q', hc', fun q hq => ?_⟩
    · haveI := P.isPrime
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨q, -, hq⟩
      exact hs q hq
    · rw [key2]
      have h2 := hv (fun q => c q * ∏ q' ∈ Finset.univ.erase q, s q') q hq
      rw [key _ _ hc'] at h2
      exact h2.unique (h.smul _)
  · rintro ⟨s, hs, c, hc, hP⟩
    obtain ⟨q, hq⟩ := exists_last_of_pair Q
    have h2 := hv c q hq
    rw [key _ _ hc, (key2 _ _).1 (hP q hq)] at h2
    obtain ⟨v, hv'⟩ : IsUnit (ψ s) := by
      by_contra hn
      exact hs ((hres s).1 ((residue_eq_zero_iff _).2 hn))
    have h3 := h2.smul (↑v⁻¹ : 𝒪[k])
    rwa [← hv', smul_smul, Units.inv_mul, one_smul, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at h3

end Local

theorem maps_rd_iff_colCond : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P →
    ∀ {S T : HSp D} {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (α : Frame p S (Fin S.rank)) (β : Frame p T (Fin T.rank))
    (Q : Pair k (Fin S.rank)) (Q' : Pair k (Fin T.rank)) (LS : Lat S) (LT : Lat T) (t : 𝓞 D.host.E),
    (∀ z, z ∈ LS ↔ z ∈ intVec D _) → (∀ z, z ∈ LT ↔ z ∈ intVec D _) → α.IsLat LS Q.lat → β.IsLat LT Q'.lat →
    (∀ w ∈ LS, ∀ r : Fin S.rank, r.1 + 1 = S.rank → ∃ s : 𝒪[k],
      (s : k) = p.pr (incA D ((t : D.host.E) * w r)) ∧ Q.HasVal (α.b' *ᵥ fun r' => p.pr (incA D (w r'))) (residue 𝒪[k] s)) →
    (∀ w ∈ LT, ∀ r : Fin T.rank, r.1 + 1 = T.rank → ∃ s : 𝒪[k],
      (s : k) = p.pr (incA D ((t : D.host.E) * w r)) ∧ Q'.HasVal (β.b' *ᵥ fun r' => p.pr (incA D (w r'))) (residue 𝒪[k] s)) →
    ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (Maps Q Q' (GlobalTheory.FinPl.rd α β (z.map (incA D))) ↔ ColCond P t (toHom S T hS hT z)) := by
  intro D k _ _ _ _ p P hP S T a b hS hT α β Q Q' LS LT t hLS hLT hα hβ vS vT z
  subst hS hT
  let φ : D.host.E →+* k := p.pr.comp (incA D)
  have hres := _root_.GlobalTheory.PhiOneVal.residue_pr_int_eq_zero_iff p P hP
  let ψ : 𝓞 D.host.E →+* 𝒪[k] := (φ.comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict _ fun c => (hres c).1
  have hψ : ∀ c, (ψ c : k) = φ (algebraMap (𝓞 D.host.E) D.host.E c) := fun c => rfl
  have hres' : ∀ c, residue 𝒪[k] (ψ c) = 0 ↔ c ∈ P.asIdeal := fun c => (hres c).2
  have hS : ∀ w : Fin S.rank → 𝓞 D.host.E, ∀ r : Fin S.rank, r.1 + 1 = S.rank →
      Q.HasVal (α.b' *ᵥ fun r' => φ (algebraMap (𝓞 D.host.E) D.host.E (w r'))) (residue 𝒪[k] (ψ (t * w r))) := by
    intro w r hr
    obtain ⟨s, hs, h⟩ := vS (fun r' => algebraMap (𝓞 D.host.E) D.host.E (w r')) ((hLS _).2 fun i => (w i).isIntegral_coe) r hr
    have : s = ψ (t * w r) := Subtype.ext (by rw [hs, hψ, map_mul (algebraMap (𝓞 D.host.E) D.host.E)]; rfl)
    exact this ▸ h
  have hT : ∀ w : Fin T.rank → 𝓞 D.host.E, ∀ r : Fin T.rank, r.1 + 1 = T.rank →
      Q'.HasVal (β.b' *ᵥ fun r' => φ (algebraMap (𝓞 D.host.E) D.host.E (w r'))) (residue 𝒪[k] (ψ (t * w r))) := by
    intro w r hr
    obtain ⟨s, hs, h⟩ := vT (fun r' => algebraMap (𝓞 D.host.E) D.host.E (w r')) ((hLT _).2 fun i => (w i).isIntegral_coe) r hr
    have : s = ψ (t * w r) := Subtype.ext (by rw [hs, hψ, map_mul (algebraMap (𝓞 D.host.E) D.host.E)]; rfl)
    exact this ▸ h
  obtain ⟨l, hl⟩ := exists_last_of_pair Q
  have hy : ∀ r : Fin S.rank, Q.HasVal (α.b' *ᵥ Pi.single r 1)
      (residue 𝒪[k] (ψ (t * if r.1 + 1 = S.rank then 1 else 0))) := by
    intro r
    have h := hS (Pi.single r 1) l hl
    have e1 : (fun r' => φ (algebraMap (𝓞 D.host.E) D.host.E ((Pi.single r 1 : Fin S.rank → 𝓞 D.host.E) r'))) =
        Pi.single r 1 := by
      ext r'
      by_cases h' : r' = r <;> simp [Pi.single_apply, h']
    have e2 : (Pi.single r 1 : Fin S.rank → 𝓞 D.host.E) l = if r.1 + 1 = S.rank then 1 else 0 := by
      rw [Pi.single_apply]
      exact if_congr ⟨fun h => h ▸ hl, fun h => Fin.ext (by omega)⟩ rfl rfl
    rwa [e1, e2] at h
  rw [maps_iff_basis Q Q' α.b α.b' α.b'b (fun x hx => (_root_.GlobalTheory.PhiOneVal.LatChar.lat_iff α LS Q.lat hα hLS x).1 hx) _ hy]
  refine forall_congr' fun r => ?_
  have e : GlobalTheory.FinPl.rd α β (z.map (incA D)) *ᵥ (α.b' *ᵥ Pi.single r 1) = β.b' *ᵥ fun q => φ (z q r) := by
    rw [GlobalTheory.FinPl.rd, mulVec_mulVec, Matrix.mul_assoc, α.bb', Matrix.mul_one, ← mulVec_mulVec, mulVec_single_one]
    rfl
  rw [e, hasVal_col_iff P φ ψ hψ hres' (GlobalTheory.PhiOneVal.exists_denom_notMem_of_pr_int p P hP) Q' β.b β.b' β.bb'
    (fun x hx => (_root_.GlobalTheory.PhiOneVal.LatChar.lat_iff β LT Q'.lat hβ hLT x).1 hx) t hT]
  have e3 : ∀ q, toHom S T rfl rfl z (Pi.single r 1) q = z q r := by
    intro q
    simp [toHom]
  simp only [e3, mul_ite, mul_one, mul_zero]

end GlobalTheory.PhiOneVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TargetLaw
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

namespace GlobalTheory.SeeSaw.LocTarget

theorem isLoc_one {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {Y : Type} [Fintype Y] [DecidableEq Y] {S : HSp D} (F : GlobalTheory.LocMod.Frame k S.rank Y) : p.IsLoc F 1 1 := by
  have h1 : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  refine ⟨fun i j => by rw [h1, sub_self, Matrix.zero_apply, mul_zero], ?_⟩
  rw [h1, Units.val_one, Matrix.mul_one, F.βγ]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem isComp_inv {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ⁻¹ μ) : p.IsComp χ μ⁻¹ := by
  intro x a ha
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, h x a ha, MonoidHom.inv_apply, Circle.coe_inv, inv_inv]

theorem om_phi {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ}
    (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hu : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) (j b : ℕ) (H : j + b = s) (hb : j + 1 + b = s + 1)
    (x : ((S.T t).lev (j + 1) b hb).J) :
    GlobalTheory.SplitWeil.om (μ (j + 1)) 1 x.1 ((S.T t).Phi j b H) =
      ((((S.T t).lev (j + 1) b hb).lam x : ℂ))⁻¹ • (S.T t).Phi j b H := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SeeSaw.MuUnits.withMu_eq k s κ S t μ hμ hu
  have hL : ((withMu S μ hμ).T t).Laws := Chain.ofType_laws _ _ _ _ _
  obtain ⟨hJ, hl⟩ := h2 (j + 1) b hb
  have hx : x.1 ∈ (((withMu S μ hμ).T t).lev (j + 1) b hb).J := by rw [hJ]; exact x.2
  have := (hL.1 j b H).2 ⟨x.1, hx⟩
  rw [h1, hl x.1 hx x.2, Units.val_inv_eq_inv_val] at this
  exact this

end GlobalTheory.SeeSaw.LocTarget
end

