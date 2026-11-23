module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0254
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumDependsOnlyAtBadPlacesFirstCoupledSte
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

noncomputable section
namespace GlobalTheory.TwV.AwayCpl
theorem frames_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : SB t μ, ∃ k : GLint t.X.E (D.R.N j) P.1, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 ∧
      ∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ ((t.cst μ).D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp t.X.E (D.R.N j)) l))) := GlobalTheory.T.chartPoints_frames_congr_away_from_badPrimes

theorem levAt_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.Ok → Pr.Ok → ChIdx.Ok Ch sel mu cst L G m2 → ∀ j (b : L.β j) (P : rowSG Pr sel mu) (k : GLint X.E (R.N j) P.1), j ≤ m2 + 1 →
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E (R.N j)) l))) →
    GlobalTheory.TopLaw.LevAt (L.levG j b) (L.levQ j b) P k 1 := _root_.GlobalTheory.LevOneAt.levAt_one

theorem rhoS_det_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok → ∀ (i n : ℕ) (P : rowSG Pr sel mu) (k : GLint X.E n P.1),
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E n) l))) →
    rhoS Ch sel mu i P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1 := _root_.GlobalTheory.TwV.AwayCpl.RhoOne.rhoS_det_one

theorem exists_approx : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E))) (f : SB → (Sp E n ≃ₗ[E] Sp E n)) (y0 : SB → Sp E n) (e : SB → ℕ),
    ∃ y : Sp E n, ∀ P l, IntAt P.1 ((((qOf P.1 : ℕ) : E) ^ (e P))⁻¹ * ((f P).symm y - y0 P) l) := _root_.GlobalTheory.CRTFrame.approx_frames_target

theorem psiAt_coset : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    ChIdx.Ok Ch sel mu cst L G m2 → ∀ (al : L.β m2) (P : rowSG Pr sel mu) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (k : GLint X.E (R.N (m2 + 1)) P.1)
    (w w₁ : Sp X.E (R.N (m2 + 1))),
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E (R.N (m2 + 1))) l))) →
    SameCoset sel mu cst P (k.1.symm w₁) w →
    PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ w₁ = PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ w := _root_.GlobalTheory.PsiCosetInv.psiAt_coset

theorem lat_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1) := GlobalTheory.T.adelicPoints_same_badComponents_same_localization

theorem fnl_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1 → ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := GlobalTheory.T.chartFunctional_eq_of_agree_badPlaces_allSteps

theorem intAt_sub {E : Type} [Field E] {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := by
  obtain ⟨r₁, s₁, hs₁, e₁⟩ := ha
  obtain ⟨r₂, s₂, hs₂, e₂⟩ := hb
  refine ⟨s₂ * r₁ - s₁ * r₂, s₁ * s₂, fun hm => (P.isPrime.mem_or_mem hm).elim hs₁ hs₂, ?_⟩
  rw [map_sub, map_mul, map_mul, map_mul, ← e₁, ← e₂]
  ring

theorem phiT_data_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1 ∧ ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTi j hj β x x₁ p p₁ h h₁ hag P
  have e := lat_away A dtU a hP hTi j hj β x x₁ p p₁ h h₁ hag P
  exact ⟨e, fnl_away A dtU a hP hTi j hj β x x₁ p p₁ h h₁ hag P e⟩


open Classical in
theorem ptAway_cpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i hi, i = t.m2 → PtAway A a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTi i hi hi2
  subst hi2
  intro β β' x x' x₁ x₁' p p' p₁ p₁' h h' h₁ h₁' hag
  have hX := hP.fields.ok
  have hPr := t.pr_ok
  have hL := t.idx_ok μ
  funext z
  unfold xiPt
  simp only [dif_neg (lt_irrefl _), if_pos rfl]
  unfold XiCpl1
  refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun P _ => ?_)

  · have H := phiT_data_away A dtU a hP hTi t.m2 _ β x x₁ p p₁ h h₁ (fun v hv => (hag v hv).1)
    have H' := phiT_data_away A dtU a hP hTi (t.m2 + 1) hi β' x' x₁' p' p₁' h' h₁' (fun v hv => (hag v hv).2)
    have e : ∀ P : t.Pr.vT (t.word u), (∀ y ∈ (p₁.deco.1).at P.1, z y ∈ (p₁'.deco.1).at P.1 ∧ p₁'.deco.1.f P (z y) = p₁.deco.1.f P y) ↔
        (∀ y ∈ (p.deco.1).at P.1, z y ∈ (p'.deco.1).at P.1 ∧ p'.deco.1.f P (z y) = p.deco.1.f P y) := by
      intro P
      rw [(H P).1, (H' P).1]
      refine forall₂_congr fun y hy => and_congr_right fun hz => ?_
      rw [(H P).2 y hy, (H' P).2 _ hz]
    unfold phiT
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ((forall_congr' e).1 h1) h2
    · exact absurd ((forall_congr' e).2 h2) h1
    · rfl

  · obtain ⟨k, hk, hkc⟩ := frames_away A dtU a hP hTi t.m2 _ β x x₁ p p₁ h h₁ (fun v hv => (hag v hv).1) P
    obtain ⟨k', hk', hkc'⟩ := frames_away A dtU a hP hTi (t.m2 + 1) hi β' x' x₁' p' p₁' h' h₁' (fun v hv => (hag v hv).2) P
    have hne : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1),
        repY (cosetOf A (t.m2 + 1) hi β' q) ∈ cosetOf A (t.m2 + 1) hi β' q := by
      intro q
      obtain ⟨y, hy⟩ := exists_approx t.X.E (D.R.N (t.m2 + 1)) (SB t μ) (frsF t.sel (t.tup μ) q) (y0At A (t.m2 + 1) hi β')
        (fun P => if P.1 ∈ t.Pr.vGs then 0 else (t.cst μ).M)
      exact Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) hi β' q) ⟨y, fun P l => hy P l⟩
    obtain ⟨bL, -⟩ := hL.last_uniq
    have hc1 := hne p₁' P
    have hc0 := hne p' P
    rw [hk'] at hc1
    rw [hk, hk']
    generalize repY (cosetOf A (t.m2 + 1) hi β' p₁') = Y₁ at hc1 ⊢
    generalize repY (cosetOf A (t.m2 + 1) hi β' p') = Y₀ at hc0 ⊢
    generalize frsF t.sel (t.tup μ) p P = f at ⊢
    generalize frsF t.sel (t.tup μ) p' P = f' at hc0 hc1 ⊢
    rw [show (f' * k'.1).symm Y₁ = k'.1.symm (f'.symm Y₁) from rfl] at hc1
    have lawS := GlobalTheory.CoupledLaw.psiAt_source hX hPr hL (al := A.ib t.m2 hi β) (P := P) (κ := k) (a := 1)
      (levAt_one _ _ _ _ _ _ _ _ _ _ _ hX hPr hL t.m2 (A.ib t.m2 hi β) P k (Nat.le_succ _) hkc) (inFr f f' z) (f'.symm Y₁)
    have lawT := GlobalTheory.CoupledLaw.psiAt_target hX hPr hL (b := bL) (P := P) (κ := k') (a := 1)
      (levAt_one _ _ _ _ _ _ _ _ _ _ _ hX hPr hL (t.m2 + 1) bL P k' le_rfl hkc') ((t.idx μ).h t.m2 (A.ib t.m2 hi β) P)
      (k'.1.symm.toLinearMap ∘ₗ (inFr f f' z ∘ₗ k.1.toLinearMap)) (k'.1.symm (f'.symm Y₁))
    have hrS := rhoS_det_one t.X t.Pr D.R t.Ch t.sel t.S (t.tup μ) (t.cst μ) hL.cst_ok t.m2 _ P k hkc
    have hrT := rhoS_det_one t.X t.Pr D.R t.Ch t.sel t.S (t.tup μ) (t.cst μ) hL.cst_ok t.m2 _ P k' hkc'
    have hsc : SameCoset t.sel (t.tup μ) (t.cst μ) P (k'.1.symm (f'.symm Y₁)) (f'.symm Y₀) := fun l => by
      have := intAt_sub (hc1 l) (hc0 l)
      convert this using 1
      simp only [Pi.sub_apply]
      ring
    have hpsi := psiAt_coset _ _ _ _ _ _ _ _ _ _ _ hL (A.ib t.m2 hi β) P (inFr f f' z) k' (f'.symm Y₀) (f'.symm Y₁) hkc' hsc
    have e1 : inFr (f * k.1) (f' * k'.1) z = k'.1.symm.toLinearMap ∘ₗ (inFr f f' z ∘ₗ k.1.toLinearMap) := LinearMap.ext fun v => rfl
    have e2 : (f' * k'.1).symm Y₁ = k'.1.symm (f'.symm Y₁) := rfl
    have e3 : k'.1.toLinearMap ∘ₗ (k'.1.symm.toLinearMap ∘ₗ (inFr f f' z ∘ₗ k.1.toLinearMap)) = inFr f f' z ∘ₗ k.1.toLinearMap :=
      LinearMap.ext fun v => LinearEquiv.apply_symm_apply _ _
    have e4 : k'.1 (k'.1.symm (f'.symm Y₁)) = f'.symm Y₁ := LinearEquiv.apply_symm_apply _ _
    rw [e3, e4, hrT, mul_one, Units.val_one, one_mul] at lawT
    rw [hrS, mul_one, Units.val_one, one_mul] at lawS
    rw [e1, e2, ← lawT, lawS, hpsi]

end GlobalTheory.TwV.AwayCpl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceNotBadBelow
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GoodOffBad

theorem conj_eq_complexConj (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem isConjPl_conjPlE_left {D : D7} (P : PlE D.host) : IsConjPl D.host (GlobalTheory.SplitConjPlace.conjPlE P) P := by
  intro x y hxy
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
  have : IsCMField.ringOfIntegersComplexConj D.host.E x = y := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, hxy, conj_eq_complexConj]
  rw [this]

theorem conjPlE_mem_placesOver {D : D7} (P : PlE D.host) (p : ℕ) :
    GlobalTheory.SplitConjPlace.conjPlE P ∈ placesOver D.host.E p ↔ P ∈ placesOver D.host.E p := by
  show ((p : ℕ) : 𝓞 D.host.E) ∈ (GlobalTheory.SplitConjPlace.conjPlE P).asIdeal ↔ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE, map_natCast]

end GlobalTheory.GoodOffBad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceSplitCondition
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ValInert

theorem conjSelf (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hI : Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w) : IsConjPl D.host w w := by
  intro x y hxy
  have hw : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (w.under (𝓞 D.host.F)).asIdeal = w.asIdeal := hI
  let σ : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)
  have hσ : ∀ z : 𝓞 D.host.E, ((σ z : 𝓞 D.host.E) : D.host.E) = D.host.conj (z : D.host.E) := fun z => rfl
  have key : w.asIdeal ≤ Ideal.comap σ w.asIdeal := by
    conv_lhs => rw [← hw]
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : σ (algebraMap _ _ s) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s := by
      apply RingOfIntegers.ext
      rw [hσ]
      have hm : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s : 𝓞 D.host.E) : D.host.E) ∈ D.host.F := by
        show ((s : D.host.F) : D.host.E) ∈ D.host.F
        exact (s : D.host.F).2
      exact (GlobalTheory.DesignBC.mem_F_iff D _).1 hm
    rw [e, ← hw]
    exact Ideal.mem_map_of_mem _ hs
  have hy : y = σ x := RingOfIntegers.ext (hxy.trans (hσ x).symm)
  have hx : x = σ y := RingOfIntegers.ext (by rw [hσ, hxy, GlobalTheory.DesignBC.conj_conj])
  exact ⟨fun h => hy ▸ key h, fun h => hx ▸ key h⟩

theorem notSplit (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : IsConjPl D.host w w) : ¬ IsSplitPl D.host w := by
  rintro ⟨x, hx, hy⟩
  obtain ⟨y, hy'⟩ : ∃ y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) :=
    ⟨RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x, rfl⟩
  exact hy y hy' ((h x y hy').1 hx)

theorem xi_eq {D : D7} {nch : NChoice D} {C C' : CharFrame D} (h : C = C') (T : TupTied D C nch) (T' : TupTied D C' nch)
    (h' : HEq T T') : T.xi = T'.xi := by
  subst h
  cases h'
  rfl

end GlobalTheory.ValInert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixedVectorMemLocalModelImage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel

namespace GlobalTheory.LocMod.Place

theorem heisO_mem_iSup_range_of_fixed : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ (c : k), c ≠ 0 → ∀ g, Formalism.IndefR.Datum.IsThetaFunO ψ S T g → (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → Formalism.IndefR.Datum.heisO ψ S T (p.up FS FT (c • x)) g = g) → (∀ y : Formalism.IndefR.Datum.WO S T, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y → (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → ψ (Formalism.IndefR.Datum.symplO S T (p.up FS FT (c • x)) y) = 1) → Formalism.IndefR.Datum.heisO ψ S T y g = g) → ∀ r : Formalism.IndefR.Datum.WO S T, Formalism.IndefR.Datum.IsHalf p.e r → Formalism.IndefR.Datum.heisO ψ S T r g ∈ ⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) →ₗ[ℂ] (Formalism.IndefR.Datum.WO S T → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ c hc g hg hfix hhalf r hr
  classical
  obtain ⟨FT', hFT'⟩ := GlobalTheory.LocMod.Witness.exists_scaled FT (Equiv.refl Y) (fun _ => c) (fun _ => hc)
  have hβ : FT'.β = c • FT.β := by
    ext i j
    simp [hFT']
  have hup : ∀ x, p.up FS FT' x = p.up FS FT (c • x) := by
    intro x
    unfold GlobalTheory.LocMod.Place.up
    rw [hβ, Matrix.smul_mul, Matrix.mul_smul]
  obtain ⟨T₁, hT₁, hT₁Φ⟩ := (GlobalTheory.LocModU.localModel_uniq_transport_exist D k p Y Y' S T FS FT' ψ hψ).2.2 g hg
    (fun x hx => by rw [hup]; exact hfix x hx)
    (fun y hy h => hhalf y hy (fun x hx => by rw [← hup]; exact h x hx))
  let Φ : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) := ⟨_, GlobalTheory.LocMod.Place.intInd_mem_SB k Y Y'⟩
  have hΦ : T₁ Φ = g := hT₁Φ Φ rfl
  have hr' : p.up FS FT' (p.down FS FT' r) = r := GlobalTheory.LocMod.Witness.up_down p FS FT' hr
  let Φ₁ : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) := ⟨fun t => Φ.1 (t + p.down FS FT' r),
    Φ.2.1.comp_continuous (continuous_add_const _), Φ.2.2.comp_homeomorph (Homeomorph.addRight _)⟩
  have h1 : T₁ Φ₁ = heisO ψ S T r g := by
    rw [hT₁.trans (p.down FS FT' r) Φ Φ₁ (fun t => rfl), hr', hΦ]
  obtain ⟨Tm', hTm', hchg⟩ := GlobalTheory.LocMod.Place.exists_isModel_chg D k p Y Y' S T FS FT' Y Y' FS FT ψ T₁ hT₁
  let e : Matrix Y Y' k ≃ₜ Matrix Y Y' k := Homeomorph.smulOfNeZero c⁻¹ (inv_ne_zero hc)
  let Φ' : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) := ⟨fun t => Φ₁.1 (c⁻¹ • t), Φ₁.2.1.comp_continuous e.continuous, Φ₁.2.2.comp_homeomorph e⟩
  have h2 : Tm' Φ' = T₁ Φ₁ := hchg Φ₁ Φ' (fun x => by
    show Φ₁.1 x = Φ₁.1 (c⁻¹ • (FT.γ * FT'.β * x * (FS.γ * FS.β)))
    rw [hβ, FS.γβ, Matrix.mul_one, Matrix.mul_smul, FT.γβ, Matrix.smul_mul, Matrix.one_mul,
      smul_smul, inv_mul_cancel₀ hc, one_smul])
  rw [← h1, ← h2]
  exact Submodule.mem_iSup_of_mem Tm' (Submodule.mem_iSup_of_mem hTm' (LinearMap.mem_range_self Tm' Φ'))

end GlobalTheory.LocMod.Place
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicFixedVectorIsSatakeEigenInertPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EigIsoInert

def stabRt {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (f : GAf L n → W) : Subgroup (GAf L n) where
  carrier := {κ | NG.rt L n κ f = f}
  one_mem' := funext fun y => by
    show f (y * 1) = f y
    rw [mul_one]
  mul_mem' := by
    intro a b ha hb
    have ha' : NG.rt L n a f = f := ha
    have hb' : NG.rt L n b f = f := hb
    show NG.rt L n (a * b) f = f
    have e : NG.rt L n (a * b) f = NG.rt L n a (NG.rt L n b f) := funext fun y => by
      show f (y * (a * b)) = f (y * a * b)
      rw [mul_assoc]
    rw [e, hb', ha']
  inv_mem' := by
    intro a ha
    have ha' : NG.rt L n a f = f := ha
    show NG.rt L n a⁻¹ f = f
    calc NG.rt L n a⁻¹ f = NG.rt L n a⁻¹ (NG.rt L n a f) := by rw [ha']
      _ = f := funext fun y => by
        show f (y * a⁻¹ * a) = f y
        rw [inv_mul_cancel_right]

theorem eig_of_irr (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n)
    (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (w : HeightOneSpectrum (𝓞 L)) (hw : NG.OverPl w v) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ)
    (hsat : NG.SatAt { a with S := S, irrS := hS } Dv α) (f : GAf L n → a.W) (hfS : f ∈ S)
    (hfK : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f)
    (h : Formalism.UG.GU Dv.σw n → ℂ) (hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n)) :
    heckeFunI L n (Umax L n) Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f := by
  let U : Subgroup (GAf L n) := Umax L n ⊓ stabRt f
  have hU : ∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n) :=
    fun κ hκ => ⟨fun h1 => h1.1, fun h1 => ⟨h1, hfK κ h1 hκ⟩⟩
  have e1 := GlobalTheory.InertSph.satU_of_fixed L n a S hS v w Dv α hw hsat U hU f hfS (fun κ hκ => hκ.2) h hh
  have hK : ∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
      (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n :=
    fun κ hκ _ => ⟨_root_.GlobalTheory.inertLoc_mem_GU L n v w Dv κ, _root_.GlobalTheory.InertStdLat.loc_mem_KU L n v w Dv κ hκ _⟩
  rw [_root_.GlobalTheory.InertLevel.heckeFunI_level_indep L n v w Dv hK (Umax L n) U (fun _ _ => Iff.rfl) hU a.W h hh.1 f hfK]
  exact e1

theorem eig_of_isoTyp_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → ∀ φ ∈ NG.isoTyp π.ρ π.S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), heckeFunI L n (Umax L n) Dv h φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  intro L _ _ _ n π v w hw Dv α hsat φ hφ hφK h hh
  have hfin : ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) →
      ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
        (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0} :=
    fun U hU h hh => _root_.GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv (fun s => _root_.GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram s)
      (_root_.GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) U hU h hh
  set c := Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α with hc

  have hirr : ∀ S' : Submodule ℂ (GAf L n → π.W), NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S' → ∀ f ∈ S',
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) → heckeFunI L n (Umax L n) Dv h f = c • f := by
    rintro S' ⟨hS', hiso⟩ f hf hfK
    have hsat' : NG.SatAt { π.toAlgWt with S := S', irrS := hS' } Dv α :=
      GlobalTheory.SatIso.satAt_of_iso L n π { π.toAlgWt with S := S', irrS := hS' } ⟨⟨LinearEquiv.refl ℂ _, fun _ _ => rfl⟩, hiso⟩ v w Dv α hfin hsat
    exact eig_of_irr L n π.toAlgWt S' hS' v w hw Dv α hsat' f hf hfK h hh

  obtain ⟨C, cf, xs, hC⟩ := GlobalTheory.SatIso.heckeFunI_eq_sum Dv (Umax L n) h (hfin (Umax L n) (fun _ _ => Iff.rfl) h hh)
  have hadd : ∀ y z : GAf L n → π.W, heckeFunI L n (Umax L n) Dv h (y + z) =
      heckeFunI L n (Umax L n) Dv h y + heckeFunI L n (Umax L n) Dv h z := by
    intro y z
    rw [hC π.W, hC π.W, hC π.W, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_add (f := _), smul_add]
  have hzero : heckeFunI L n (Umax L n) Dv h (0 : GAf L n → π.W) = 0 := by
    rw [hC π.W]
    simp
  have key : ∀ t : Finset (Submodule ℂ (GAf L n → π.W)),
      (↑t ⊆ {S' | NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S'}) → ∀ f ∈ (⨆ i ∈ t, i),
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) → heckeFunI L n (Umax L n) Dv h f = c • f := by
    classical
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _ f hf _
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
      subst hf
      rw [hzero, smul_zero]
    | insert a t ha ih =>
      intro hsub f hf hfix
      have haF : NG.IsIrrRep π.ρ a ∧ NG.IsoRep π.S a := hsub (Finset.mem_insert_self a t)
      have hsF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S'} :=
        fun x hx => hsub (Finset.mem_insert_of_mem hx)
      rw [Finset.iSup_insert] at hf
      have hMst : ∀ g, ∀ y ∈ (⨆ i ∈ t, i), NG.rt L n g y ∈ (⨆ i ∈ t, i) :=
        GlobalTheory.IsoFix.iSup_finset_stable t (fun i hi => (hsF hi).1.1.stable)
      by_cases hd : a ⊓ (⨆ i ∈ t, i) = ⊥
      · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
        have hyz : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ y = y ∧ NG.rt L n κ z = z := by
          intro κ hκ hκt
          have e := hfix κ hκ hκt
          rw [map_add (f := _)] at e
          have h1 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
          have hm : NG.rt L n κ y - y ∈ a ⊓ (⨆ i ∈ t, i) :=
            ⟨a.sub_mem (haF.1.1.stable κ y hy) hy, h1 ▸ Submodule.sub_mem _ hz (hMst κ z hz)⟩
          rw [hd, Submodule.mem_bot] at hm
          refine ⟨sub_eq_zero.1 hm, ?_⟩
          rw [hm] at h1
          exact (sub_eq_zero.1 h1.symm).symm
        rw [hadd, hirr a haF y hy (fun κ hκ hκt => (hyz κ hκ hκt).1),
          ih hsF z hz (fun κ hκ hκt => (hyz κ hκ hκt).2), smul_add]
      · have hsubrep : NG.IsSubrep π.ρ (a ⊓ ⨆ i ∈ t, i) :=
          ⟨inf_le_left.trans haF.1.1.le, fun g y hy => ⟨haF.1.1.stable g y hy.1, hMst g y hy.2⟩⟩
        have heq : a ⊓ (⨆ i ∈ t, i) = a := (haF.1.2.2 _ hsubrep inf_le_left).resolve_left hd
        have hle : a ≤ ⨆ i ∈ t, i := heq ▸ inf_le_right
        exact ih hsF f ((sup_le hle le_rfl) hf) hfix
  unfold NG.isoTyp at hφ
  obtain ⟨s, hs, hfs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hφ
  exact key s hs φ hfs (fun κ hκ hκt => hφK κ hκ hκt)

end GlobalTheory.EigIsoInert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemISupIsLinAtBilin
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThetaLoc

open GlobalTheory.SplitWeil

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ}

theorem isLinAt_comp {Θ Ω : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup Ω] [Module ℂ Ω]
    (ω₁ : GAf E n × GAf E r →* Module.End ℂ Θ) (ω₂ : GAf E n × GAf E r →* Module.End ℂ Ω)
    (P : Θ → Prop) (T : Θ →ₗ[ℂ] Ω) (hT : ∀ p f, P f → T (ω₁ p f) = ω₂ p (T f))
    (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ)
    (ι : SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ) (hP : ∀ Φ, P (ι Φ))
    (h : IsLinAt ω₁ s μ η ι) : IsLinAt ω₂ s μ η (T ∘ₗ ι) := by
  obtain ⟨c, hc, hc', hι⟩ := h
  refine ⟨c, hc, hc', fun h g hh hg Φ Φ' hΦ => ?_⟩
  simp only [LinearMap.comp_apply]
  rw [← hT _ _ (hP Φ), hι h g hh hg Φ Φ' hΦ, map_smul]

end GlobalTheory.ThetaLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeTransformEqOfUnramifiedBaseChangeEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertUbcSatake

theorem satU_eq_of_ubc_eq : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ α β : Fin (n / 2) → ℂ, ubc n (Multiset.map α Finset.univ.val) = ubc n (Multiset.map β Finset.univ.val) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), Formalism.UG.SatU ϖ q h α = Formalism.UG.SatU ϖ q h β :=
  GlobalTheory.SatBcZero.satU_eq_of_ubc_eq

end GlobalTheory.InertUbcSatake
end

