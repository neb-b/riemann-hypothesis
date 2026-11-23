module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumLocalSphericalZetaUnramified
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocZeta

theorem hasSum_quot_of_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H}
    (hK : ∀ g, g ∈ K ↔ e g ∈ K') {f : G → ℂ} (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g) {s : ℂ}
    (h : HasSum (fun b : H ⧸ K' => f (e.symm b.out)) s) : HasSum (fun a : G ⧸ K => f a.out) s :=
  _root_.GlobalTheory.hasSum_quotient_transport G H e K K' hK f hf s h

theorem kerGL_mul_right {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r N : ℕ} {z : ℂˣ}
    {φ : GL (Fin r) (w.adicCompletion E) → ℂ} (hφ : KerGL w N z φ) (g k : GL (Fin r) (w.adicCompletion E))
    (hk : k ∈ KGL w (n := r)) : φ (g * k) = φ g :=
  GlobalTheory.T.sphericalZetaKernelGL_right_invariant_integral E w r N z φ hφ g k hk

theorem kerU_mul_right {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
    {σ : w.adicCompletion E →+* w.adicCompletion E} {ϖ : w.adicCompletion E} {q r N : ℕ} (hU : IsUnramInv ϖ σ q)
    {z : ℂˣ} {φ : GU σ r → ℂ} (hφ : KerU ϖ q N z φ) (g k : GU σ r) (hk : k ∈ KU σ r) : φ (g * k) = φ g := by
  obtain ⟨d, t, -, ht, k₁, h₁, k₂, h₂, rfl⟩ := cartanU hU g
  rw [mul_assoc (k₁ * t), hφ d t ht k₁ h₁ _ (mul_mem h₂ hk), hφ d t ht k₁ h₁ k₂ h₂]

theorem conj_qpow (q : ℕ) (x : ℝ) : starRingEnd ℂ ((q : ℂ) ^ (x : ℂ)) = (q : ℂ) ^ (x : ℂ) := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.conj_ofReal]

theorem kerGL_conj {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r N : ℕ} {z : ℂˣ}
    {φ : GL (Fin r) (w.adicCompletion E) → ℂ} (hφ : KerGL w N z φ) :
    KerGL w N (star z) (fun g => starRingEnd ℂ (φ g)) := by
  intro ϖ hϖ d t ht k₁ h₁ k₂ h₂
  show starRingEnd ℂ (φ (k₁ * t * k₂)) = _
  rw [hφ ϖ hϖ d t ht k₁ h₁ k₂ h₂, map_mul, map_zpow₀]
  have := conj_qpow (qV E w) (-((N : ℝ) / 2) * ((∑ i, |d i| : ℤ) : ℝ))
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_intCast, Complex.ofReal_ofNat] at this
  rw [this]
  rfl

theorem kerU_conj {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ} {ϖ : L}
    {q N : ℕ} {z : ℂˣ} {φ : GU σ r → ℂ} (hφ : KerU ϖ q N z φ) :
    KerU ϖ q N (star z) (fun g => starRingEnd ℂ (φ g)) := by
  intro d t ht k₁ h₁ k₂ h₂
  show starRingEnd ℂ (φ (k₁ * t * k₂)) = _
  rw [hφ d t ht k₁ h₁ k₂ h₂]
  simp [map_zpow₀]

theorem quadSign_eq (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (∀ w w' : HeightOneSpectrum (𝓞 D.host.E), w ≠ w' → (∀ u, u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') →
      quadSign D v = 1) ∧
    (∀ w : HeightOneSpectrum (𝓞 D.host.E), (∀ u, u.under (𝓞 D.host.F) = v ↔ u = w) → quadSign D v = -1) :=
  _root_.GlobalTheory.QuadSignLocal.quadSign_split_inert D v

theorem value_split (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hne : w ≠ w')
    (hall : ∀ u, u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') (hN : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal)
    (hN' : Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal) (hB' : B w' = (B w).map (·⁻¹))
    (hs : (B w).map star = (B w).map (·⁻¹)) (hm : m w * m w' = 1) (hm1 : ‖(m w : ℂ)‖ = 1) (hq : quadSign D v = 1) :
    starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) =
      eulerFac ((B w).map (star (m w) * ·)) (npow w (-((1 + (D.R.t : ℂ)) / 2))) *
        eulerFac ((B w).map fun β => (star (m w) * β)⁻¹) (npow w (-((1 + (D.R.t : ℂ)) / 2))) *
        ∏ i ∈ Finset.Ioc D.R.t (D.R.r + D.R.t), (1 - ((qV D.host.E w : ℂ) ^ i)⁻¹) :=
  _root_.GlobalTheory.LocZetaSplit.conj_LvTw_div_dLoc D B m v w w' hne hall hN hN' hB' hs hm hm1 hq

theorem value_inert (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hall : ∀ u, u.under (𝓞 D.host.F) = v ↔ u = w) (hN : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2)
    (hs : (B w).map star = B w) (hm : (m w : ℂ) = (-1) ^ D.R.nV) (hq : quadSign D v = -1) :
    starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) =
      eulerFac (B w) (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.t + 1))⁻¹) *
        ∏ j ∈ Finset.range D.R.r,
          (1 - (-(qV D.host.F v : ℂ)) ^ j * (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.r + D.R.t))⁻¹)) :=
  _root_.GlobalTheory.FinZeta.conj_LvTw_div_dLoc_inert D B m v w hall hN hs hm hq


set_option maxHeartbeats 1000000 in
theorem hasSum_localZeta : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (D : D7) (V : HSp D), V.rank = D.R.r → ∀ (χ : (AE D)ˣ →* Circle), Formalism.L2.Theta.ResEta D χ D.R.nV → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χ w) → ∀ φ : Gv V v → ℂ, IsLocKer V D.R.nV (val χ) v φ → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gv V v) X), IsUnitarisable ρ → ∀ (x : X) (B : Fam D.host.E), (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsParamVec D.sp.cm.sig V.gram (frameLat V) h ρ x (B w) ∧ ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)) → ∀ ℓ : X →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : Gv V v ⧸ Kv V v => φ a.out * starRingEnd ℂ (ℓ (ρ a.out x))) (LvTw B (val χ) v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ) * starRingEnd ℂ (ℓ x)) := by
  intro hG D V hr χ hχ v hU φ hφ X _ _ ρ hρu x B hB ℓ hℓ
  classical
  have hc := isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hc.2.2.1
  have hχ' := (resEta_iff χ _).1 hχ
  have hJ := GlobalTheory.Mem.VolExists.isHermND D.sp.cm V
  have hd := SelfDual.isSelfDualAt_frameLat D V v
  have hrt : V.rank ≤ D.R.t := by
    have := D.R.rank_add_five_le
    rw [hr]
    unfold Ranks.r
    omega
  have hnV : D.R.nV = V.rank + D.R.t := by rw [hr]; rfl
  obtain ⟨w, h⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  obtain ⟨C, hC⟩ := hℓ
  have hfix : ∀ k ∈ Kv V v, ρ k x = x := GlobalTheory.LGrp.mem_fixed.1 (hB w h).1.mem_fixed
  have hnz : ‖(((star (val χ w) : ℂˣ)) : ℂ)‖ = 1 := by
    rw [Units.coe_star]
    simpa using norm_val χ w
  suffices H : HasSum (fun a : Gv V v ⧸ Kv V v => starRingEnd ℂ (φ a.out) * ℓ (ρ a.out x))
      (starRingEnd ℂ (LvTw B (val χ) v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) * ℓ x) by
    have := H.map (starRingEnd ℂ) Complex.continuous_conj
    simpa [Function.comp_def] using this
  rcases (hB w h).1 with ⟨hv, e, he, hsat⟩ | ⟨hw, c, ϖ, e, α, hUI, he, hsat, hBw⟩
  · obtain ⟨w', hne, hall, hN, hN', -⟩ := SplitChart.exists_conj_place hc h hv
    have h' : w'.under (𝓞 D.host.F) = v := (hall w').2 (Or.inr rfl)
    have hB' : B w' = (B w).map (·⁻¹) :=
      ConjPlace.eq_map_inv_of_isParamVec hc hJ hd hne (hB w h).1 (hB w' h').1
    have hm : val χ w * val χ w' = 1 := ResEta.val_mul_val h2 hχ' hne h h' (hU w h) (hU w' h')
    have hs : (B w).map star = (B w).map (·⁻¹) :=
      GlobalTheory.T.satakeParameterGL_star_eq_inv_of_unitarisable _ w _ _ _ x (B w) (hρu.imp fun _ hb => ⟨hb.1, hb.2.1, fun g => hb.2.2 (e.symm g)⟩) hsat
    have hk := kerGL_conj ((hφ w h).1 hv e he)
    rw [hnV] at hk
    have hbd : ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ (((V.rank : ℝ) - 1) / 2) ∧
        ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ (((V.rank : ℝ) - 1) / 2) := by
      intro β hβ
      rw [hr]
      refine ⟨(hB w h).2 β hβ, ?_⟩
      have := (hB w' h').2 β⁻¹ (hB' ▸ Multiset.mem_map_of_mem _ hβ)
      have e2 : (qV D.host.E w : ℝ) = ((Ideal.absNorm w'.asIdeal : ℕ) : ℝ) := by
        rw [hN', ← hN]; rfl
      rw [e2]
      exact this
    have hsum := GlobalTheory.T.unramified_zeta_sum_GL_cosets hG D.host.E w V.rank D.R.t hrt (star (val χ w)) _ hnz hk X
      (ρ.comp e.symm.toMonoidHom) x (B w) hsat hbd ℓ ⟨C, fun g => hC _⟩
    rw [value_split D B (val χ) v w w' hne hall hN hN' hB' hs hm (norm_val χ w) ((quadSign_eq D v).1 w w' hne hall),
      ← hr]
    refine hasSum_quot_of_equiv e he.2 (f := fun g => starRingEnd ℂ (φ g) * ℓ (ρ g x)) ?_ hsum
    intro g k hk'
    have e1 : φ (g * k) = φ g := by
      have := kerGL_mul_right ((hφ w h).1 hv e he) (e g) (e k) ((he.2 k).1 hk')
      simpa using this
    show starRingEnd ℂ (φ (g * k)) * ℓ (ρ (g * k) x) = starRingEnd ℂ (φ g) * ℓ (ρ g x)
    rw [e1, map_mul, Module.End.mul_apply, hfix k hk']
  · have hall := InertChart.under_eq_iff hw
    have hNw := InertChart.absNorm_eq h2 hw
    have hval : val χ w = (-1) ^ D.R.nV := ResEta.val_of_isInertAt h2 hχ' hw (hU w h)
    have hk := kerU_conj ((hφ w h).2 hw c ϖ e hUI he)
    rw [hnV] at hk
    have hstarB : (B w).map star = B w := by
      rw [hBw]
      have := bcParam_eq_of_satU_eq (α := fun i => star (α i)) hUI
        (_root_.GlobalTheory.LFun.ConjParam.satU_star_eq _ ϖ c _ _ hUI _ _ x α (hρu.imp fun _ hb => ⟨hb.1, hb.2.1, fun g => hb.2.2 (e.symm g)⟩) hsat)
      conv_rhs => rw [← this]
      simp [bcParam, star_inv, Function.comp_def]
    have htb : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound (qV D.host.F v) V.rank α := by
      have hq : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) = (qV D.host.F v : ℝ) ^ 2 := by
        rw [hNw]; push_cast; rfl
      have hQ : (0 : ℝ) < (qV D.host.F v : ℝ) ^ 2 := by
        have := one_lt_absNorm v
        have : (0 : ℝ) < (qV D.host.F v : ℝ) := by
          show (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)
          exact_mod_cast (by omega : 0 < Ideal.absNorm v.asIdeal)
        positivity
      intro i
      have h1 := (hB w h).2 (α i) (by rw [hBw]; simp [bcParam])
      have h3 := (hB w h).2 (α i)⁻¹ (by rw [hBw]; simp [bcParam])
      rw [hq, ← hr] at h1 h3
      refine ⟨?_, h1⟩
      rw [Real.rpow_neg hQ.le]
      rw [Units.val_inv_eq_inv_val, norm_inv] at h3
      exact inv_le_of_inv_le₀ (norm_pos_iff.2 (α i).ne_zero) h3
    have hsum := _root_.GlobalTheory.ZetaSumU.hasSum_zetaSum_inert _ ϖ c (qV D.host.F v) V.rank D.R.t hUI hrt (star (val χ w)) _ hnz hk X
      (ρ.comp e.symm.toMonoidHom) x α hsat htb ℓ ⟨C, fun g => hC _⟩
    rw [value_inert D B (val χ) v w hall hNw hstarB (by rw [hval]; push_cast; rfl) ((quadSign_eq D v).2 w hall), hBw, ← hr]
    refine hasSum_quot_of_equiv e he.2.2 (f := fun g => starRingEnd ℂ (φ g) * ℓ (ρ g x)) ?_ hsum
    intro g k hk'
    have e1 : φ (g * k) = φ g := by
      have := kerU_mul_right hUI ((hφ w h).2 hw c ϖ e hUI he) (e g) (e k) ((he.2.2 k).1 hk')
      simpa using this
    show starRingEnd ℂ (φ (g * k)) * ℓ (ρ (g * k) x) = starRingEnd ℂ (φ g) * ℓ (ρ g x)
    rw [e1, map_mul, Module.End.mul_apply, hfix k hk']

end GlobalTheory.LocZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisAvgInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

theorem heisAvg_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (m : ℕ)
    (lam : WO S T → ℂ), (∀ x ∈ Λ, ∀ y ∈ Λ, lam (x + y) = lam x * lam y * ψ (symplOH S T x y)) →
    ∀ [Fintype (Qm m Λ)] (g : WO S T → ℂ), (∀ l ∈ Λ, lam (m • l) • heisO ψ S T (m • l) g = g) →
    ∀ b ∈ Λ, lam b • heisO ψ S T b (∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g) =
      ∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g := by
  intro D ψ S T Λ m lam hlam _ g hg b hb
  have hsm : ∀ (x : WO S T) (c : ℂ) (f : WO S T → ℂ), heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
    intro x c f; funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  have hsumlin : ∀ (x : WO S T) (F : Qm m Λ → WO S T → ℂ),
      heisO ψ S T x (∑ q, F q) = ∑ q, heisO ψ S T x (F q) := by
    intro x F; funext w; simp only [heisO, Finset.sum_apply, Finset.mul_sum]
  have hmul : ∀ x ∈ Λ, ∀ y ∈ Λ, lam x • heisO ψ S T x (lam y • heisO ψ S T y g) =
      lam (x + y) • heisO ψ S T (x + y) g := by
    intro x hx y hy
    rw [hsm, GlobalTheory.FinTranslate.heisO_heisO, smul_smul, smul_smul, hlam x hx y hy]
  have key : ∀ q : Qm m Λ, lam b • heisO ψ S T b (lam (repm q) • heisO ψ S T (repm q) g) =
      lam (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) •
        heisO ψ S T (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) g := by
    intro q
    have hbq : b + repm q ∈ Λ := Λ.add_mem hb (repm_mem q)
    rw [hmul b hb _ (repm_mem q)]
    have hmk : (QuotientAddGroup.mk (⟨b + repm q, hbq⟩ : Λ) : Qm m Λ) =
        (QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q := by
      conv_rhs => rw [← mk_repm q]
      rfl
    have h1 := repm_mk_sub (m := m) hbq
    rw [hmk] at h1
    obtain ⟨l, hl, hl'⟩ := mem_mLat.1 h1
    have he : repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q) = (b + repm q) + m • l := by
      rw [hl']; abel
    rw [he, ← hmul _ hbq _ (Λ.nsmul_mem hl m), hg l hl]
  calc lam b • heisO ψ S T b (∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g)
      = ∑ q : Qm m Λ, lam (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) •
          heisO ψ S T (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) g := by
        rw [hsumlin, Finset.smul_sum]
        exact Finset.sum_congr rfl fun q _ => key q
    _ = _ := Equiv.sum_comp (Equiv.addLeft (QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ))
          (fun q => lam (repm q) • heisO ψ S T (repm q) g)

end GlobalTheory.FinDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergArchimedeanDiffOperatorHasDerivAtFamil
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

noncomputable section

namespace GlobalTheory.HeisOrbit.DOpDeriv

theorem hasDerivAt_fderiv_family {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℝ × E → ℂ) (hH : ContDiff ℝ 2 H) (g : E → ℂ)
    (hg : ∀ y, HasDerivAt (fun t => H (t, y)) (g y) 0) (P : ℝ → E) (P' : E) (hP : HasDerivAt P P' 0) (y : E) :
    HasDerivAt (fun t => fderiv ℝ (fun z => H (t, z)) y (P t))
      (fderiv ℝ g y (P 0) + fderiv ℝ (fun z => H (0, z)) y P') 0 := by
  have hd : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (fderiv ℝ H) :=
    (hH.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : ∀ (t : ℝ) (v : E), fderiv ℝ (fun z => H (t, z)) y v = fderiv ℝ H (t, y) (0, v) := by
    intro t v
    have := ((hd (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)).fderiv
    have e : (fun z => H (t, z)) = H ∘ (fun z => (t, z)) := rfl
    rw [e, this]
    simp
  have h2 : g = fun z => fderiv ℝ H (0, z) (1, 0) := by
    funext z
    have hc : HasDerivAt (fun t : ℝ => (t, z)) ((1 : ℝ), (0 : E)) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) z)
    have := (hd (0, z)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
    exact (hg z).unique this
  have h3 : ∀ v : E, fderiv ℝ g y v = fderiv ℝ (fderiv ℝ H) (0, y) (0, v) (1, 0) := by
    intro v
    have a := (hd1 (0, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right (0 : ℝ) y)
    have b := (a.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : E)) y)).fderiv
    have e : g = fun z => ((fderiv ℝ H) ∘ (fun z => ((0 : ℝ), z))) z (1, 0) := h2
    rw [e, b]
    simp
  have hs : IsSymmSndFDerivAt ℝ H (0, y) :=
    hH.contDiffAt.isSymmSndFDerivAt (by simp)
  have hc : HasDerivAt (fun t : ℝ => (t, y)) ((1 : ℝ), (0 : E)) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) y)
  have a := (hd1 (0, y)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have hQ : HasDerivAt (fun t : ℝ => ((0 : ℝ), P t)) ((0 : ℝ), P') 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk hP
  have b := a.clm_apply hQ
  simp only [h1, h3]
  rw [hs.eq (0, P 0) (1, 0)]
  exact b

theorem dOp_hasDerivAt : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (P Q : ℝ → (κ → mixedEmbedding.mixedSpace F))
    (g' : SInf F κ) (P' Q' : κ → mixedEmbedding.mixedSpace F),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    (∀ y, HasDerivAt (fun t => G t y) (g' y) 0) → HasDerivAt P P' 0 → HasDerivAt Q Q' 0 → ∀ y,
    HasDerivAt (fun t => GlobalTheory.HeisOrbit.dOp (P t) (Q t) (G t) y) (GlobalTheory.HeisOrbit.dOp (P 0) (Q 0) g' y + GlobalTheory.HeisOrbit.dOp P' Q' (G 0) y) 0 := by
  intro F _ _ κ _ G P Q g' P' Q' hG hg hP hQ y
  have h1 := hasDerivAt_fderiv_family (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2)
    (hG.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))) g' hg P P' hP y
  let L : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
    { toFun := fun q => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * q i)
      map_add' := by
        intro a b
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
      map_smul' := by
        intro c a
        simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, RingHom.id_apply] }
  have h2 : HasDerivAt (fun t => L (Q t)) (L Q') 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hQ
  have h3 := ((h2.ofReal_comp.const_mul (2 * Real.pi * Complex.I : ℂ)).mul (hg y))
  have h4 := h1.sub h3
  refine HasDerivAt.congr_deriv (f := fun t => GlobalTheory.HeisOrbit.dOp (P t) (Q t) (G t) y) h4 ?_
  symm
  simp only [GlobalTheory.HeisOrbit.dOp]
  change _ = fderiv ℝ g' y (P 0) + fderiv ℝ (G 0) y P' - (2 * Real.pi * Complex.I *
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * Q' i) : ℝ) : ℂ) * G 0 y + 2 * Real.pi * Complex.I *
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * Q 0 i) : ℝ) : ℂ) * g' y)
  ring

end GlobalTheory.HeisOrbit.DOpDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartEqZeroOfIsHalfIdempotentSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.IdemHalf

theorem infPart_eq_zero_of_isSplitIdem {D : D7} {e : AE D} (h : IsSplitIdem D e) :
    infPart D e = 0 ∧ infPart D (cA D e) = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -, -⟩, hε⟩ := h
  have hz : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    show infPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  have hs : infPart D e + infPart D (cA D e) = 0 := by rw [← (infPart D).map_add, hε, hz]
  have hm : infPart D e * infPart D (cA D e) = 0 := by rw [← (infPart D).map_mul, h2, (infPart D).map_zero]
  have hi : infPart D e * infPart D e = infPart D e := by rw [← (infPart D).map_mul, h1]
  have hb : infPart D (cA D e) = - infPart D e := eq_neg_of_add_eq_zero_right hs
  rw [hb, mul_neg, hi] at hm
  have ha : infPart D e = 0 := neg_eq_zero.mp hm
  exact ⟨ha, by rw [hb, ha, neg_zero]⟩

theorem halfFin : ∀ {D : D7} (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ {m n : ℕ} (y : Mx D m n), (IsHalf e y ∨ IsHalf (cA D e) y) → y.map (infPart D) = 0 := by
  intro D P e he m n y hy
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have h0 : infPart D (∑ PP ∈ P, es PP) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum (infPart D)]
    exact Finset.sum_eq_zero fun PP hPP => (infPart_eq_zero_of_isSplitIdem (hes PP hPP).1).1
  have h1 : infPart D (cA D (∑ PP ∈ P, es PP)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum (cA D), map_sum (infPart D)]
    exact Finset.sum_eq_zero fun PP hPP => (infPart_eq_zero_of_isSplitIdem (hes PP hPP).1).2
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  rcases hy with hy | hy
  · rw [← hy i j, (infPart D).map_mul, h0, zero_mul]
  · rw [← hy i j, (infPart D).map_mul, h1, zero_mul]

end GlobalTheory.IdemHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeVacuumSumHeisenbergTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVacComb

theorem isLatVac_sum_heisO : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (g : WO S T → ℂ), IsLatVac (heisO ψ S T) Λ g → ∀ {ι : Type} (R : Finset ι) (c : ι → ℂ) (t : ι → WO S T), (∀ z ∈ R, ∀ u ∈ Λ, ψ (symplO S T u (t z)) = 1) → IsLatVac (heisO ψ S T) Λ (∑ z ∈ R, c z • heisO ψ S T (t z) g) := by
  intro D ψ S T Λ g hg ι R c t ht
  have key : ∀ w : WO S T, heisO ψ S T w g = g → (∀ z ∈ R, ψ (symplO S T w (t z)) = 1) →
      heisO ψ S T w (∑ z ∈ R, c z • heisO ψ S T (t z) g) = ∑ z ∈ R, c z • heisO ψ S T (t z) g := by
    intro w hw hwt
    rw [GlobalTheory.SplitScalar.heisO_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [GlobalTheory.SplitScalar.heisO_smul, GlobalTheory.SplitScalar.heisO_comm, hw, hwt z hz, one_smul]
  refine ⟨fun u hu => key (2 • u) (hg.1 u hu) fun z hz => ht z hz _ (AddSubgroup.nsmul_mem Λ hu 2),
    fun e he u hu hue => key u (hg.2 e he u hu hue) fun z hz => ht z hz u hu⟩

end GlobalTheory.LatVacComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelTowerRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepRows.RowRapidPf

theorem multT_le_empty {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) :
    MultT θ M J χ ≤ MultT θ M ∅ 1 :=
  Submodule.map_mono (Submodule.span_mono fun _ h =>
    ⟨h.aut, h.cusp, fun _ _ hk => absurd hk (Set.notMem_empty _), h.equiv, h.cont⟩)

end GlobalTheory.SepRows.RowRapidPf

end
end

