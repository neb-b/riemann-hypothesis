module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0183
public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctOfSsOfAbsIrrOfMapRepDistinct
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct :
    ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ}
      (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → (∀ W, IsIrrSub ρ W → AbsIrrSub ρ W) →
      (∀ W₁ W₂, IsIrrSub (mapRep f ρ) W₁ → IsIrrSub (mapRep f ρ) W₂ → W₁ ⊓ W₂ = ⊥ →
        ¬ IsoSub (mapRep f ρ) W₁ W₂) →
      AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ)) := by
  intro k Γ _ _ L _ f a ρ hss habs hdist
  obtain ⟨n, Vs, hint, hirr⟩ := _root_.GlobalTheory.semisimple_matrix_rep_decomp ρ hss
  have hs : ∀ j, Stable (matRep ((Units.coeHom _).comp ρ)) (Vs j) :=
    fun j g v hv => (hirr j).2.1 g v hv
  have hsp : ∀ j, Submodule.span k (Set.range fun g =>
      (matRep ((Units.coeHom _).comp ρ) g).restrict (hs j g)) = ⊤ :=
    fun j => _root_.GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub ρ (Vs j) (hs j) (habs _ (hirr j))
  refine ⟨Fin n, inferInstance, inferInstance, Vs, hs, hint, fun j => (hirr j).1, hsp, ?_⟩
  intro j j' hjj' e he
  have hiso : IsoSub ρ (Vs j) (Vs j') := by
    refine ⟨e, fun g v h => ?_⟩
    have := congrArg Subtype.val (he g v)
    exact this
  have hdisj : Vs j ⊓ Vs j' = ⊥ :=
    (hint.submodule_iSupIndep.pairwiseDisjoint hjj').eq_bot
  exact hdist _ _
    (GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top f ρ (Vs j) (hs j) (hirr j).1 (hsp j))
    (GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top f ρ (Vs j') (hs j') (hirr j').1 (hsp j'))
    (_root_.GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot f (Vs j) (Vs j') hdisj)
    (_root_.GlobalTheory.isoSub_span_map f ρ (Vs j) (Vs j') (hirr j).2.1 (hirr j').2.1 hiso)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BetaModelCoefficientsInvertL
section
noncomputable section

namespace GlobalTheory.BeCoefficients

open Formalism.MainNotions.FormalGroupSystem
open Formalism.MainNotions.GL3Theta (G1 ModelOverW)
open Formalism.L2.G.Pend (k0ToC)

theorem beCoef : Formalism.L2.KerInert.BeCob.BeCoef := by
  intro l _ g hOk hM hph
  obtain ⟨P0, hP0⟩ := (Formalism.L2.G.Pend.coefWf_iff _).1 hph
  obtain ⟨E0, hE0⟩ := (Formalism.L2.G.Pend.coefWf_iff _).1 (Formalism.L2.G.Pend.exRat_of g hOk hM)
  obtain ⟨L0, hL0⟩ := Formalism.L2.G.Pend.l_mem_ratSub g hOk.2.1 hM
  have hP0' : PowerSeries.map (k0ToC l) P0 = g.ph := hP0
  have hE0' : PowerSeries.map (k0ToC l) E0 = g.ex := hE0
  have hL0' : PowerSeries.map (k0ToC l) L0 = g.l := hL0
  have hE00 : PowerSeries.constantCoeff E0 = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply (map_eq_zero_iff _ (k0ToC l).injective).1
    rw [← PowerSeries.coeff_map, hE0', PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hOk.2.2.1
  have hL00 : PowerSeries.constantCoeff L0 = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply (map_eq_zero_iff _ (k0ToC l).injective).1
    rw [← PowerSeries.coeff_map, hL0', PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Formalism.MainNotions.J.cc_l g
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hs0 : MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) L0 +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) L0) = 0 := by
    rw [map_add (f := _), PowerSeries.constantCoeff_subst_eq_zero (hX 0) _ hL00,
      PowerSeries.constantCoeff_subst_eq_zero (hX 1) _ hL00, add_zero]
  have hs1 : MvPowerSeries.constantCoeff (PowerSeries.subst
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) L0 +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) L0) E0) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hs0 _ hE00
  refine (Formalism.L2.G.Pend.coefWf_iff _).2 ⟨PowerSeries.subst (PowerSeries.subst
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) L0 +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) L0) E0) P0 -
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (K0 l)) P0 -
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (K0 l)) P0, ?_⟩
  rw [map_sub, map_sub, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs1),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 0)),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 1)),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs0), map_add,
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 0)),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hX 1)),
    MvPowerSeries.map_X, MvPowerSeries.map_X, hP0', hE0', hL0']
  rfl

end GlobalTheory.BeCoefficients
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficieStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_weilDeligne_potSemistable_enlarge_coefficients : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥(Dec (F := E) A) →* GL (Fin m) ↥L₁.1), IsPst P (Bw.repE L₁ r₁) → IsPst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) → ∀ σ : ↥(Weil h), WD.charPol (wdPst P ι Bw h hj (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁))) σ = WD.charPol (wdPst P ι Bw h hj (Bw.repE L₁ r₁)) σ := by
  first | exact @GlobalTheory.Pst.EnlargeCoeff.charPol_wdPst_enlarge | exact GlobalTheory.Pst.EnlargeCoeff.charPol_wdPst_enlarge | (intros; apply GlobalTheory.Pst.EnlargeCoeff.charPol_wdPst_enlarge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoboundaryIntegralLawRespectsSimeq
section
noncomputable section

namespace GlobalTheory.CobSimeqProof

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (cob)

theorem simeq_neg {K ι : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {f g : MvPowerSeries ι K}
    (h : Formalism.InvariantFactorPaths.G7.Simeq f g) : Formalism.InvariantFactorPaths.G7.Simeq (-f) (-g) := by
  have h' := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K ι).2.1 f g h
  unfold Formalism.InvariantFactorPaths.G7.Simeq at h' ⊢
  rwa [show -f - -g = g - f by ring]

theorem integral_X {K ι : Type} [NormedField K] (i : ι) : Integral (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem cobSimeq : Formalism.L2.KerInert.BeCob.CobSimeq := by
  intro K _ _ _ F hF0 hFI f f' h
  have R := Formalism.InvariantFactorPaths.G7.Top.simeqRules K Unit
  have hs : ∀ (φ : Unit → MvPowerSeries (Fin 2) K), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) →
      (∀ i, Integral (φ i)) →
      Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.subst φ (f : MvPowerSeries Unit K))
        (MvPowerSeries.subst φ (f' : MvPowerSeries Unit K)) :=
    fun φ h0 hI => R.2.2.2.2 (Fin 2) f f' φ h0 hI h
  have h1 := hs (fun _ => F) (fun _ => hF0) (fun _ => hFI)
  have h2 := simeq_neg (hs (fun _ => MvPowerSeries.X 0) (fun _ => MvPowerSeries.constantCoeff_X _)
    (fun _ => integral_X _))
  have h3 := simeq_neg (hs (fun _ => MvPowerSeries.X 1) (fun _ => MvPowerSeries.constantCoeff_X _)
    (fun _ => integral_X _))
  have R2 := Formalism.InvariantFactorPaths.G7.Top.simeqRules K (Fin 2)
  have H := R2.2.2.2.1 _ _ _ _ (R2.2.2.2.1 _ _ _ _ h1 h2) h3
  have e : ∀ q : PowerSeries K, cob F q = MvPowerSeries.subst (fun _ => F) (q : MvPowerSeries Unit K) +
      -MvPowerSeries.subst (fun _ => (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) (q : MvPowerSeries Unit K) +
      -MvPowerSeries.subst (fun _ => (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) (q : MvPowerSeries Unit K) := by
    intro q
    unfold cob Formalism.InvariantFactorPaths.G7.at1 PowerSeries.subst
    ring
  rw [e f, e f']
  exact H

end GlobalTheory.CobSimeqProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeInterior
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

namespace GlobalTheory

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}


open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} in
theorem _root_.GlobalTheory.phiT_add_smul_homAt (K : Type) [Field K]
    {ST SG SG' S : Finset (HeightOneSpectrum (𝓞 E))}
    (d : _root_.Formalism.L2.Col.Deco E a ST SG) (d' : _root_.Formalism.L2.Col.Deco E b ST SG') (hd' : d'.Ok) (hS : ST ⊆ S) (c : 𝓞 E)
    (hc : ∀ P : ST, c ∈ P.1.asIdeal) (x y₀ : _root_.Formalism.L2.Col.HomE E a b) (hy : y₀ ∈ _root_.Formalism.L2.Col.homAt S d.N d'.N) :
    _root_.Formalism.L2.Col.phiT K d d' (x + c • y₀) = _root_.Formalism.L2.Col.phiT K d d' x := by
  unfold _root_.Formalism.L2.Col.phiT
  have key : ∀ P : ST, ∀ y ∈ d.at P,
      ((x + c • y₀) y ∈ d'.at P ∧ d'.f P ((x + c • y₀) y) = d.f P y) ↔
        (x y ∈ d'.at P ∧ d'.f P (x y) = d.f P y) := by
    intro P y hyP
    have hy0 : y₀ y ∈ d'.at P := hy P.1 (hS P.2) y hyP
    have hcy : c • y₀ y ∈ d'.at P := Submodule.smul_mem _ c hy0
    have hf0 : d'.f P (c • y₀ y) = 0 := by
      rw [hd'.f_smul P c _ hy0, Ideal.Quotient.eq_zero_iff_mem.2 (hc P), zero_mul]
    have happ : (x + c • y₀) y = x y + c • y₀ y := rfl
    rw [happ, Submodule.add_mem_iff_left _ hcy]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← h2, hd'.f_add P _ h1 _ hcy, hf0, add_zero]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [hd'.f_add P _ h1 _ hcy, hf0, add_zero, h2]⟩
  have hiff : (∀ P : ST, ∀ y ∈ d.at P,
      (x + c • y₀) y ∈ d'.at P ∧ d'.f P ((x + c • y₀) y) = d.f P y) ↔
      (∀ P : ST, ∀ y ∈ d.at P, x y ∈ d'.at P ∧ d'.f P (x y) = d.f P y) :=
    forall_congr' fun P => forall₂_congr fun y hyP => key P y hyP
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.1 h1) h2
  · exact absurd (hiff.2 h2) h1
  · rfl

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} in
omit [NumberField E] [StarRing E] in
theorem _root_.GlobalTheory.inFr_add (f : _root_.Formalism.L2.Col.Sp E a ≃ₗ[E] _root_.Formalism.L2.Col.Sp E a) (f' : _root_.Formalism.L2.Col.Sp E b ≃ₗ[E] _root_.Formalism.L2.Col.Sp E b)
    (x y : _root_.Formalism.L2.Col.HomE E a b) :
    _root_.Formalism.L2.Col.inFr f f' (x + y) = _root_.Formalism.L2.Col.inFr f f' x + _root_.Formalism.L2.Col.inFr f f' y := by
  unfold _root_.Formalism.L2.Col.inFr
  rw [LinearMap.add_comp, LinearMap.comp_add]


open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} in
theorem _root_.GlobalTheory.intAt_inFr_smul_homAt {S : Finset (HeightOneSpectrum (𝓞 E))}
    {N : Submodule (𝓞 E) (_root_.Formalism.L2.Col.Sp E a)}
    {N' : Submodule (𝓞 E) (_root_.Formalism.L2.Col.Sp E b)} {P : HeightOneSpectrum (𝓞 E)} (hP : P ∈ S)
    (f : _root_.Formalism.L2.Col.Sp E a ≃ₗ[E] _root_.Formalism.L2.Col.Sp E a) (f' : _root_.Formalism.L2.Col.Sp E b ≃ₗ[E] _root_.Formalism.L2.Col.Sp E b)
    (hf : ∀ x, f x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ x ∈ _root_.Formalism.L2.Col.stdAt E a P)
    (hf' : ∀ x, f' x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' ↔ x ∈ _root_.Formalism.L2.Col.stdAt E b P)
    (c r : 𝓞 E) (e : E) (he : e ≠ 0) (hc : algebraMap (𝓞 E) E c = e * algebraMap (𝓞 E) E r)
    (y₀ : _root_.Formalism.L2.Col.HomE E a b) (hy : y₀ ∈ _root_.Formalism.L2.Col.homAt S N N') (s : Fin a) (l : Fin b) :
    _root_.Formalism.L2.Col.IntAt P (e⁻¹ * _root_.Formalism.L2.Col.inFr f f' (c • y₀) (Pi.single s 1) l) := by
  have hv : (Pi.single s 1 : _root_.Formalism.L2.Col.Sp E a) ∈ _root_.Formalism.L2.Col.stdAt E a P := by
    refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
    rw [one_smul]
    refine Submodule.mem_pi.2 fun i _ => ?_
    by_cases h : i = s
    · subst h
      rw [Pi.single_eq_same]
      exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]
      exact Submodule.zero_mem _
  have hz : y₀ (f (Pi.single s 1)) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' := hy P hP _ ((hf _).2 hv)
  have hw : f'.symm (y₀ (f (Pi.single s 1))) ∈ _root_.Formalism.L2.Col.stdAt E b P :=
    (hf' _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hz)
  obtain ⟨t, ht, htw⟩ := hw
  have hl : (t • f'.symm (y₀ (f (Pi.single s 1)))) l ∈ (1 : Submodule (𝓞 E) E) :=
    Submodule.mem_pi.1 htw l (Set.mem_univ l)
  obtain ⟨r', hr'⟩ := Submodule.mem_one.1 hl
  have hval : _root_.Formalism.L2.Col.inFr f f' (c • y₀) (Pi.single s 1) l =
      algebraMap (𝓞 E) E c * f'.symm (y₀ (f (Pi.single s 1))) l := by
    show (f'.symm (c • y₀ (f (Pi.single s 1)))) l = _
    rw [← algebraMap_smul E c (y₀ (f (Pi.single s 1))), map_smul, Pi.smul_apply, smul_eq_mul]
  unfold _root_.Formalism.L2.Col.IntAt
  refine ⟨r * r', t, ht, ?_⟩
  rw [hval, hc, map_mul, hr', Pi.smul_apply, Algebra.smul_def]
  calc _ = (e⁻¹ * e) * (algebraMap (𝓞 E) E t * (algebraMap (𝓞 E) E r *
        f'.symm (y₀ (f (Pi.single s 1))) l)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ he, one_mul]; ring

end General

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumSupportDivLatticeFinal
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

namespace GlobalTheory.SuppTop

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem intAt_nat (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) : IntAt P (c : E) := by
  simpa using IntAt.coe P (c : 𝓞 E)

theorem intAt_sum {ι : Type} (P : HeightOneSpectrum (𝓞 E)) (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    IntAt P (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IntAt P) (fun _ _ ha hb => ha.add hb) (by simpa using intAt_nat P 0) h

theorem smul_mem_of_inFr {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
    (hf : ∀ y, f y ∈ localization₂ P.asIdeal N ↔ y ∈ stdAt E a P) (hf' : ∀ y, f' y ∈ localization₂ P.asIdeal N' ↔ y ∈ stdAt E b P)
    (c : ℕ) (x : HomE E a b) (h : ∀ s l, IntAt P ((c : E) * inFr f f' x (Pi.single s 1) l)) :
    ∀ y ∈ localization₂ P.asIdeal N, (c : E) • x y ∈ localization₂ P.asIdeal N' := by
  intro y hy
  have hv : f.symm y ∈ stdAt E a P := (hf _).1 (by simpa using hy)
  have hv' : ∀ i, IntAt P (f.symm y i) := (mem_localization_standardLattice P _).1 hv
  have e : (c : E) • x y = f' ((c : E) • inFr f f' x (f.symm y)) := by simp [inFr]
  rw [e, hf']
  refine (mem_localization_standardLattice P _).2 fun l => ?_
  have e2 : inFr f f' x (f.symm y) = ∑ s, f.symm y s • inFr f f' x (Pi.single s 1) := by
    conv_lhs => rw [pi_eq_sum_univ' (f.symm y)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [e2]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine intAt_sum P _ _ fun s _ => ?_
  rw [mul_left_comm]
  exact (hv' s).mul (h s l)

theorem entB_zero {N' N : ℕ} (q k₀ c' n' n : ℕ) (hc : c' = 0) (ex' ex : ℕ → ℕ) (x : HomE E N' N) (p p' : ℕ) (hp : p < n)
    (hp' : p' < n') :
    LocE.entB q k₀ c' n' 0 n ex' ex x p p' = Loc.atN (x (Loc.eN E N' p')) p := by
  subst hc
  have h1 : ∀ m s, LocE.fIdx k₀ 0 m s = s := by
    intro m s
    unfold LocE.fIdx
    split_ifs <;> omega
  simp [LocE.entB, h1, LocE.scE, hp, hp']

end General

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem intAt_of_phiTop (sharp : Bool) (m2 : ℕ) (hm : R.m = m2 + 2) (P : HeightOneSpectrum (𝓞 X.E))
    (z : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) (hz : PhiTop Ch mu sharp m2 P z ≠ 0)
    (p p' : ℕ) (hp : p < R.N R.m - 1) (hp' : p' < R.N (m2 + 1)) :
    IntAt P (Loc.atN (z (Loc.eN X.E _ p')) p) := by
  have hc : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  have ha : p' < R.r + (R.m - 1) * R.t := by
    have : R.m - 1 = m2 + 1 := by omega
    unfold Ranks.N at hp'
    unfold Ranks.r
    rw [this]
    have : (m2 + 1) * (R.t + 1) = (m2 + 1) * R.t + (m2 + 1) := by ring
    omega
  unfold PhiTop at hz
  split_ifs at hz
  · unfold LocE.PhiGS at hz
    simp only at hz
    split_ifs at hz with h
    · have := h.1 p p' hp ha
      rwa [entB_zero _ _ _ _ _ hc _ _ _ _ _ hp hp'] at this
    · exact absurd rfl hz
  · unfold LocE.PhiG at hz
    simp only at hz
    split_ifs at hz with h
    · have := h.1 p p' hp ha
      rwa [entB_zero _ _ _ _ _ hc _ _ _ _ _ hp hp'] at this
    · exact absurd rfl hz
  · unfold LocE.PhiQ at hz
    split_ifs at hz with h
    · have := h.1 p p' hp (by omega)
      rwa [entB_zero _ _ _ _ _ hc _ _ _ _ _ hp hp'] at this
    · exact absurd rfl hz

theorem intAt_of_ftY {n : ℕ} (P : rowSG Pr sel mu) (η : Sp X.E n →ₗ[X.E] X.E) (y' : Sp X.E n)
    (h : ftY sel mu cst P η y' ≠ 0) (s : Fin n) : IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single s 1)) := by
  unfold ftY at h
  split_ifs at h with h1 h2 h3
  · have := (intAt_nat P.1 (qOf P.1 ^ cst.M)).mul (h2 s)
    simpa using this
  · exact absurd rfl h
  · exact h3 s
  · exact absurd rfl h

end Chain

end GlobalTheory.SuppTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumSupportDivLatticeInterior
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

namespace GlobalTheory.Proof.datum_support_div_lattice_interior

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem intAt_sum {P : HeightOneSpectrum (𝓞 E)} {ι : Type} (s : Finset ι) (f : ι → E)
    (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f (IntAt P) (fun _ _ ha hb => ha.add hb) ?_ h
  simpa using IntAt.coe P 0

theorem smul_mem_of_frames {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E a))
    (M' : Submodule (𝓞 E) (Sp E b)) (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
    (hf : ∀ x, f x ∈ M ↔ x ∈ stdAt E a P) (hf' : ∀ x, f' x ∈ M' ↔ x ∈ stdAt E b P)
    (x : HomE E a b) (c : E) (h : ∀ s l, IntAt P (c * inFr f f' x (Pi.single s 1) l)) :
    ∀ y ∈ M, c • x y ∈ M' := by
  classical
  intro y hy
  obtain ⟨z, rfl⟩ := f.surjective y
  have hz : ∀ i, IntAt P (z i) := (mem_localization_standardLattice P z).1 ((hf z).1 hy)
  have e : c • x (f z) = f' (c • inFr f f' x z) := by simp [inFr]
  rw [e, hf']
  refine (mem_localization_standardLattice P _).2 fun l => ?_
  have hz' : z = ∑ s, z s • (Pi.single s (1 : E) : Sp E a) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have e2 : (c • inFr f f' x z) l = ∑ s, z s * (c * inFr f f' x (Pi.single s 1) l) := by
    conv_lhs => rw [hz']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e2]
  exact intAt_sum _ _ fun s _ => (hz s).mul (h s l)

end General

end GlobalTheory.Proof.datum_support_div_lattice_interior
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteExtAbsIrrSub
section
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SplitField

theorem exists_finite_ext_absIrrSub : ∀ {K Γ ι : Type} [Field K] [Group Γ] [Finite ι] {a : ℕ} (ρ : ι → (Γ →* GL (Fin a) K)), (∀ j, IsSSRep (mapRep (algebraMap K (AlgebraicClosure K)) (ρ j))) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), ∀ j W, IsIrrSub (mapRep (algebraMap K K') (ρ j)) W → AbsIrrSub (mapRep (algebraMap K K') (ρ j)) W := by
  intro K Γ ι _ _ _ a ρ hss
  classical
  have hdec := fun j => GlobalTheory.semisimple_matrix_rep_decomp (mapRep (algebraMap K (AlgebraicClosure K)) (ρ j)) (hss j)
  choose n Vs hint hirr using hdec
  let b : ∀ j m, Module.Basis (Fin (Module.finrank (AlgebraicClosure K) (Vs j m))) (AlgebraicClosure K) (Vs j m) :=
    fun j m => Module.finBasis (AlgebraicClosure K) (Vs j m)
  let S : Set (AlgebraicClosure K) := Set.range (fun p : (Σ j, Σ m : Fin (n j), Fin (Module.finrank (AlgebraicClosure K) (Vs j m)) × Fin a) =>
    ((b p.1 p.2.1 p.2.2.1 : Vs p.1 p.2.1) : Fin a → AlgebraicClosure K) p.2.2.2)
  obtain ⟨K', _, _, _, f, hf, hS⟩ := exists_finite_field S (Set.finite_range _)
  refine ⟨K', inferInstance, inferInstance, inferInstance, ?_⟩
  intro j
  set τ := mapRep (algebraMap K K') (ρ j) with hτ
  have hcomp : mapRep f τ = mapRep (algebraMap K (AlgebraicClosure K)) (ρ j) := by
    rw [hτ, mapRep_mapRep]
    congr 1
    exact RingHom.ext hf
  have hsp : ∀ m, Vs j m ≤ Submodule.span (AlgebraicClosure K) ((fun v => f ∘ v) '' {v : Fin a → K' | f ∘ v ∈ Vs j m}) := by
    intro m
    have h1 : Vs j m = Submodule.span _ (Set.range fun k => ((b j m k : Vs j m) : Fin a → AlgebraicClosure K)) := by
      have := congrArg (Submodule.map (Vs j m).subtype) (b j m).span_eq
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at this
      refine this.symm.trans ?_
      rw [← Set.range_comp]; rfl
    conv_lhs => rw [h1]
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have hc : ∀ i, ∃ c : K', f c = ((b j m k : Vs j m) : Fin a → AlgebraicClosure K) i :=
      fun i => hS ⟨⟨j, m, k, i⟩, rfl⟩
    choose c hc using hc
    have hfc : f ∘ c = ((b j m k : Vs j m) : Fin a → AlgebraicClosure K) := funext hc
    refine Submodule.subset_span ⟨c, ?_, ?_⟩
    · show f ∘ c ∈ Vs j m
      rw [hfc]; exact (b j m k).2
    · exact hfc
  obtain ⟨Us, hUi, hUs⟩ := GlobalTheory.T.exists_internal_stable_decomposition_descends_to_subfield f τ (Vs j) (hint j) (fun m => hcomp ▸ (hirr j m).2.1) hsp
  have hES : ∀ m, EndSpanned τ (Us m) := by
    intro m
    apply GlobalTheory.T.endSpannedByRepMatrices_of_scalarExtension f τ (Us m)
    rw [(hUs m).2, hcomp]
    exact _root_.GlobalTheory.SplitField.endSpanned_of_isIrrSub_of_isAlgClosed _ _ (hirr j m)
  have hne : ∀ m, Us m ≠ ⊥ := by
    intro m h
    apply (hirr j m).1
    rw [← (hUs m).2, h]
    simp
  have hUirr : ∀ m, IsIrrSub τ (Us m) := fun m => isIrrSub_of_endSpanned τ (Us m) (hne m) (hUs m).1 (hES m)
  intro W hW
  obtain ⟨m, hm⟩ := GlobalTheory.T.irreducible_subrep_iso_summand_of_isInternal τ Us hUi hUirr W hW
  exact absIrrSub_of_endSpanned τ W hW.1 hW.2.1 (endSpanned_of_isoSub τ W (Us m) hW.2.1 hm (hES m))
end GlobalTheory.SplitField
end

