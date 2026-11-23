module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0101
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.GaussJetBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0067
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqNormV
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

namespace GlobalTheory.LiftAbsPow

open GlobalTheory.CuspRep.InfType

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

theorem v_map_eq_one {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) {x : v.adicCompletion K}
    (hx : Valued.v x = 1) : Valued.v (i x) = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have h0 : Valued.v (i x) ≠ 0 := by simpa using hx0
  have h1 : Valued.v (i x) ≤ 1 := (GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi x).2 hx.le
  have h2 : Valued.v (i x⁻¹) ≤ 1 := (GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi _).2 (by rw [map_inv₀, hx, inv_one])
  rw [map_inv₀, map_inv₀] at h2
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (i x) * (Valued.v (i x))⁻¹ := (mul_inv_cancel₀ h0).symm
    _ ≤ Valued.v (i x) * 1 := mul_le_mul' le_rfl h2
    _ = Valued.v (i x) := mul_one _

theorem v_map_unif {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) {p : v.adicCompletion K}
    (hp : Valued.v p = WithZero.exp (-1)) : Valued.v (i p) = WithZero.exp (-1) := by
  have hp0 : p ≠ 0 := by rintro rfl; rw [map_zero] at hp; exact WithZero.exp_ne_zero hp.symm
  have hlt : Valued.v (i p) < 1 := (GlobalTheory.TypeBlockFix.v_map_lt_one_iff v w i hi p).2 (by
    rw [hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have key : ∀ z : w.adicCompletion M, Valued.v z < 1 → Valued.v z ≤ Valued.v (i p) := fun z hz => by
    have hy : Valued.v (i.symm z) < 1 := (GlobalTheory.TypeBlockFix.v_map_lt_one_iff v w i hi _).1 (by simpa using hz)
    rw [GlobalTheory.SplitUnif.lt_one_iff, ← hp] at hy
    have h3 : Valued.v (i.symm z / p) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ hy zero_le
    have h4 := (GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi _).2 h3
    rw [map_div₀, map_div₀, RingEquiv.apply_symm_apply] at h4
    have hip : 0 < Valued.v (i p) := by
      rw [zero_lt_iff]; simpa using hp0
    exact (div_le_one₀ hip).1 h4
  obtain ⟨q, hq⟩ := w.valuation_exists_uniformizer M
  have hq' : Valued.v ((q : M) : w.adicCompletion M) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hq]
  refine le_antisymm ((GlobalTheory.SplitUnif.lt_one_iff _).1 hlt) ?_
  rw [← hq']
  exact key _ (by rw [hq', ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)

theorem v_map_eq {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) (x : v.adicCompletion K) :
    Valued.v (i x) = Valued.v x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨p0, hp0⟩ := v.valuation_exists_uniformizer K
  set p : v.adicCompletion K := (p0 : v.adicCompletion K)
  have hp : Valued.v p = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hp0]
  have hpne : p ≠ 0 := by rintro h; rw [h, map_zero] at hp; exact WithZero.exp_ne_zero hp.symm
  have hvx : Valued.v x ≠ 0 := by simpa using hx
  set k := WithZero.log (Valued.v x)
  have hk : Valued.v x = WithZero.exp k := (WithZero.exp_log hvx).symm
  obtain ⟨u, hu, e⟩ : ∃ u, Valued.v u = 1 ∧ x = u * (p ^ k)⁻¹ := by
    refine ⟨x * p ^ k, ?_, ?_⟩
    · rw [map_mul, map_zpow₀, hp, hk, ← WithZero.exp_zsmul, ← WithZero.exp_add, smul_eq_mul]
      simp
    · field_simp
  rw [e]
  simp only [map_mul, map_inv₀, map_zpow₀]
  rw [v_map_eq_one i hi hu, hu, v_map_unif i hi hp, hp]

theorem card_residue (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = Ideal.absNorm v.asIdeal := by
  have hF : ∀ s : 𝓞 K, Valued.v (algebraMap K (v.adicCompletion K) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  exact GlobalTheory.SplitUnif.card_residueField v (algebraMap K (v.adicCompletion K)) v (fun _ => rfl) fun s => by
    rw [hF, HeightOneSpectrum.intValuation_lt_one_iff_mem]

theorem absNorm_eq {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) :
    Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal := by
  let ψ : v.adicCompletionIntegers K ≃+* w.adicCompletionIntegers M :=
    { toFun := fun a => ⟨i a, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
        ((v_map_eq i hi a).le.trans ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 a.2))⟩
      invFun := fun b => ⟨i.symm b, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by
        rw [← v_map_eq i hi, RingEquiv.apply_symm_apply]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 b.2)⟩
      left_inv := fun a => Subtype.ext (i.symm_apply_apply a)
      right_inv := fun b => Subtype.ext (i.apply_symm_apply b)
      map_mul' := fun a b => Subtype.ext (map_mul i (a : v.adicCompletion K) (b : v.adicCompletion K))
      map_add' := fun a b => Subtype.ext (map_add i (a : v.adicCompletion K) (b : v.adicCompletion K)) }
  rw [← card_residue v, ← card_residue w]
  exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv ψ).toEquiv

end GlobalTheory.LiftAbsPow

namespace GlobalTheory.LiftAbsPow

open GlobalTheory.CuspRep.InfType GlobalTheory.HeckeGal.Model

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

end GlobalTheory.LiftAbsPow

namespace GlobalTheory.LiftAbsPow

open GlobalTheory.CuspRep.InfType GlobalTheory.HeckeGal.Model

theorem absNorm_eq_normV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm v.asIdeal = normV v := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

end GlobalTheory.LiftAbsPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamWeightDirectSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc

theorem exists_model : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)),
    Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    ∀ L₀ : FinExt l, ∃ (LL' : FinExt l) (_ : L₀.1 ≤ LL'.1) (ρ₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1),
      Continuous (fun g => ((ρ₁ g : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1)) ∧
      mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ₁ = ρ := _root_.GlobalTheory.CompactRepField.exists_continuous_model

theorem dsum_local : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O]
      [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (LL' : FinExt l) (a b : ℕ)
      (r₁ : ↥Gw →* GL (Fin a) ↥LL'.1) (r₂ : ↥Gw →* GL (Fin b) ↥LL'.1),
      (Bw.IsdRE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) ↔ Bw.IsdRE P LL' r₁ ∧ Bw.IsdRE P LL' r₂) ∧
      ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) (c : ℤ),
        Bw.multE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) τ' c = Bw.multE P LL' r₁ τ' c + Bw.multE P LL' r₂ τ' c := _root_.GlobalTheory.DirectSumLocal.isdRE_sumRep_and_multE_add

theorem exists_place : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (τ : D.host.E →+* Qbar l), ∃ w : PlE D.host,
    w ∈ placesOver D.host.E l ∧ ∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal := _root_.GlobalTheory.PlaceOfEmb.exists_place_of_emb

theorem exists_ext : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (w : PlE D.host) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O),
    GlobalTheory.Pst.Induces Bw → ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) →
    ∀ LL' : FinExt l, Bw.LL.1 ≤ LL'.1 → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1, GlobalTheory.Pst.IsInduced Bw τ τ' := GlobalTheory.T.exists_completionEmbedding_inducing_hostEmbedding

theorem wdOf_sumRep_away : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a b : ℕ)
    (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (w : PlE D.host) (hw : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
    Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))) →
    GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') =
      (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ).lpSum (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ') := _root_.GlobalTheory.WeilDeligne.wdOf_sumRep_awayFrom

theorem wdAt_sumRep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (ι : Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
      [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw)
      (a b : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (r' : ↥(Dec (F := E) A) →* GL (Fin b) (Om l)),
      GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw r' → GlobalTheory.Pst.IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') →
      GlobalTheory.Pst.wdAt P ι Bw h hj (Formalism.MainNotions.SumRepresentations.At.sumRep r r') =
        (GlobalTheory.Pst.wdAt P ι Bw h hj r).lpSum (GlobalTheory.Pst.wdAt P ι Bw h hj r') := GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable

theorem wdAt_bridge : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (ι : Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O]
      [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O')
      (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw')
      (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)),
      Continuous (fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) →
      GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r →
      GlobalTheory.Pst.wdAt P ι Bw h hj r = GlobalTheory.Pst.wdAt P ι Bw' h hj' r := GlobalTheory.T.weilDeligneParamAbove_l_independent_localEmbedding

end GlobalTheory.SumRepAdd

namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc

section Gen
variable {Γ : Type} [Group Γ] {k k' : Type} [CommRing k] [CommRing k'] {a b : ℕ}

theorem sumRep_apply (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin (a + b)) :
    ((Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂ g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) i j =
      Matrix.fromBlocks (r₁ g : Matrix (Fin a) (Fin a) k) 0 0 (r₂ g : Matrix (Fin b) (Fin b) k)
        (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := rfl

theorem mapRep_sumRep (f : k →+* k') (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) :
    mapRep f (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) = Formalism.MainNotions.SumRepresentations.At.sumRep (mapRep f r₁) (mapRep f r₂) := by
  ext g i j
  change f (((Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂ g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) i j) = _
  rw [sumRep_apply, sumRep_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [mapRep]

theorem comp_sumRep {Δ : Type} [Group Δ] (φ : Δ →* Γ) (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) :
    (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂).comp φ = Formalism.MainNotions.SumRepresentations.At.sumRep (r₁.comp φ) (r₂.comp φ) := by
  ext g i j
  rfl

theorem cont_sumRep [TopologicalSpace Γ] [TopologicalSpace k] (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k)
    (h₁ : Continuous fun g => ((r₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (h₂ : Continuous fun g => ((r₂ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) :
    Continuous fun g => ((Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂ g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) := by
  refine continuous_matrix fun i j => ?_
  simp only [sumRep_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
  · exact h₁.matrix_elem i j
  · exact continuous_const
  · exact continuous_const
  · exact h₂.matrix_elem i j
end Gen

end GlobalTheory.SumRepAdd

namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc

section W
variable (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

theorem model_enlarge {a : ℕ} {L₁ L₂ : FinExt l} (h : L₁.1 ≤ L₂.1) (ρ₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥L₁.1)
    (hc : Continuous (fun g => ((ρ₁ g : GL (Fin a) ↥L₁.1) : Matrix (Fin a) (Fin a) ↥L₁.1))) :
    Continuous (fun g => ((mapRep (IntermediateField.inclusion h).toRingHom ρ₁ g : GL (Fin a) ↥L₂.1) :
      Matrix (Fin a) (Fin a) ↥L₂.1)) ∧
    mapRep (algebraMap ↥L₂.1 (Qbar l)) (mapRep (IntermediateField.inclusion h).toRingHom ρ₁) =
      mapRep (algebraMap ↥L₁.1 (Qbar l)) ρ₁ := by
  refine ⟨continuous_matrix fun i j => continuous_induced_rng.2 ?_, ?_⟩
  · exact (continuous_subtype_val.comp (hc.matrix_elem i j)).congr fun g => rfl
  · ext g i j; rfl

theorem two_models {a b : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (hρ' : Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))))
    (L₀ : FinExt l) :
    ∃ (LL' : FinExt l) (_ : L₀.1 ≤ LL'.1) (ρ₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1)
      (ρ₂ : G D.host.E D.nd.Om →* GL (Fin b) ↥LL'.1),
      Continuous (fun g => ((ρ₁ g : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1)) ∧
      Continuous (fun g => ((ρ₂ g : GL (Fin b) ↥LL'.1) : Matrix (Fin b) (Fin b) ↥LL'.1)) ∧
      mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ₁ = ρ ∧ mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ₂ = ρ' := by
  obtain ⟨L₁, h₁, ρ₁, c₁, e₁⟩ := exists_model D l a ρ hρ L₀
  obtain ⟨L₂, h₂, ρ₂, c₂, e₂⟩ := exists_model D l b ρ' hρ' L₁
  obtain ⟨c, e⟩ := model_enlarge D l h₂ ρ₁ c₁
  exact ⟨L₂, h₁.trans h₂, _, ρ₂, c, c₂, e.trans e₁, e₂⟩

theorem dR_sum {a b : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (hρ' : Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E l) :
    W.IsdRW l ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w ↔ W.IsdRW l ι ρ w ∧ W.IsdRW l ι ρ' w := by
  obtain ⟨LL, Bw, hj, -⟩ := W.above l ι ρ w hw
  obtain ⟨LL', hL, ρ₁, ρ₂, c₁, c₂, rfl, rfl⟩ := two_models D l ρ ρ' hρ hρ' Bw.LL
  obtain ⟨-, H⟩ := W.loc l ι w hw _ Bw hj ((algebraMap ↥Bw.LL.1 (Om l)).comp Bw.toLL) (fun _ => rfl)
  rw [← mapRep_sumRep, (H LL' hL a ρ₁ c₁).2.1, (H LL' hL b ρ₂ c₂).2.1,
    (H LL' hL (a + b) _ (cont_sumRep ρ₁ ρ₂ c₁ c₂)).2.1, comp_sumRep]
  exact (dsum_local l (D.loc l) (D.locA l) ⟨D.locT l⟩ _ _ _ _ Bw LL' a b _ _).1

end W
end GlobalTheory.SumRepAdd

namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc

section W2
variable (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

theorem jumps_sum {a b : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (hρ' : Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))))
    (τ : D.host.E →+* Qbar l)
    (hτ : ∀ w : PlE D.host, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) →
      W.IsdRW l ι ρ w ∧ W.IsdRW l ι ρ' w) :
    W.jumpsW l ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') τ = W.jumpsW l ι ρ τ + W.jumpsW l ι ρ' τ := by
  obtain ⟨w, hw, hτw⟩ := exists_place D l τ
  obtain ⟨d₁, d₂⟩ := hτ w hτw
  have d₃ := (dR_sum D T W l ι ρ ρ' hρ hρ' w hw).2 ⟨d₁, d₂⟩
  obtain ⟨LL, Bw, hj, -⟩ := W.above l ι ρ w hw
  obtain ⟨LL', hL, ρ₁, ρ₂, c₁, c₂, rfl, rfl⟩ := two_models D l ρ ρ' hρ hρ' Bw.LL
  obtain ⟨τ', hτ'⟩ := exists_ext D l w _ Bw hj τ hτw LL' hL
  obtain ⟨-, H⟩ := W.loc l ι w hw _ Bw hj ((algebraMap ↥Bw.LL.1 (Om l)).comp Bw.toLL) (fun _ => rfl)
  obtain ⟨-, dd₁, -, J₁⟩ := H LL' hL a ρ₁ c₁
  obtain ⟨-, dd₂, -, J₂⟩ := H LL' hL b ρ₂ c₂
  obtain ⟨-, dd₃, -, J₃⟩ := H LL' hL (a + b) _ (cont_sumRep ρ₁ ρ₂ c₁ c₂)
  rw [← mapRep_sumRep] at d₃ ⊢
  ext c
  have k₁ := (J₁ τ τ' hτ').2 (dd₁.1 d₁) c
  have k₂ := (J₂ τ τ' hτ').2 (dd₂.1 d₂) c
  have k₃ := (J₃ τ τ' hτ').2 (dd₃.1 d₃) c
  rw [comp_sumRep, (dsum_local l (D.loc l) (D.locA l) ⟨D.locT l⟩ _ _ _ _ Bw LL' a b _ _).2 τ' c, ← k₁, ← k₂] at k₃
  rw [Multiset.count_add]
  exact_mod_cast k₃

theorem wd_sum_away {a b : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (hρ' : Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))))
    (w : PlE D.host) (hw : w ∉ placesOver D.host.E l) :
    W.wdOf l ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w = D.naut.lpSum (W.wdOf l ι ρ w) (W.wdOf l ι ρ' w) := by
  apply (T.e w).injective
  rw [T.sum, W.away l ι _ w hw, W.away l ι ρ w hw, W.away l ι ρ' w hw]
  exact wdOf_sumRep_away D l ι a b ρ ρ' w hw hρ hρ'

theorem pst_of_dR (hB : GlobalTheory.Published.DeRhamPotSemistable) {m : ℕ} (r : G D.host.E D.nd.Om →* GL (Fin m) (Qbar l))
    (hr : Continuous (fun g => ((r g : GL (Fin m) (Qbar l)) : Matrix (Fin m) (Fin m) (Qbar l))))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E l) (hd : W.IsdRW l ι r w) {LL : FinExt l}
    (B : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) ↥(OL LL)) (hj : GlobalTheory.Pst.Induces B) :
    GlobalTheory.Pst.IsPstAt (D.loc l) B (GlobalTheory.Pst.resDec D.nd.plOm.1 r w) := by
  obtain ⟨LL', hL, r₁, c₁, rfl⟩ := exists_model D l m r hr B.LL
  obtain ⟨-, H⟩ := W.loc l ι w hw _ B hj ((algebraMap ↥B.LL.1 (Om l)).comp B.toLL) (fun _ => rfl)
  have hd' := (H LL' hL m r₁ c₁).2.1
  have hm : GlobalTheory.Pst.IsModel B (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (algebraMap ↥LL'.1 (Qbar l)) r₁) w) LL'
      (r₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := ⟨hL, rfl⟩
  have hdR : GlobalTheory.Pst.IsdRAt (D.loc l) B (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (algebraMap ↥LL'.1 (Qbar l)) r₁) w) :=
    (hm.isdRAt_iff (D.loc l)).2 (hd'.1 hd)
  exact hB.isPstAt (D.locT l) B _ (hr.comp continuous_subtype_val) hdR

theorem wd_sum_above (hB : GlobalTheory.Published.DeRhamPotSemistable) {a b : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (hρ' : Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E l) (d₁ : W.IsdRW l ι ρ w) (d₂ : W.IsdRW l ι ρ' w) :
    W.wdOf l ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w = D.naut.lpSum (W.wdOf l ι ρ w) (W.wdOf l ι ρ' w) := by
  have d₃ := (dR_sum D T W l ι ρ ρ' hρ hρ' w hw).2 ⟨d₁, d₂⟩
  have c₃ := cont_sumRep ρ ρ' hρ hρ'
  obtain ⟨p_power_smul_sub_sum, B1, j1, E1⟩ := W.above l ι ρ w hw
  obtain ⟨logJacobianTwoPoints, B2, j2, E2⟩ := W.above l ι ρ' w hw
  obtain ⟨ColumnLift, B3, j3, E3⟩ := W.above l ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w hw
  have tie : Nonempty (LocTied l (D.loc l) (D.locA l)) := ⟨D.locT l⟩
  apply (T.e w).injective
  rw [T.sum, E1, E2, E3]
  have p31 := pst_of_dR D T W l ι hB _ c₃ w hw d₃ B1 j1
  have p33 := pst_of_dR D T W l ι hB _ c₃ w hw d₃ B3 j3
  have p11 := pst_of_dR D T W l ι hB _ hρ w hw d₁ B1 j1
  have p21 := pst_of_dR D T W l ι hB _ hρ' w hw d₂ B1 j1
  have p22 := pst_of_dR D T W l ι hB _ hρ' w hw d₂ B2 j2
  rw [wdAt_bridge l (D.loc l) (D.locA l) tie ι D.host.E D.nd.Om (D.nd.plOm.1 w) w _ _ B3 B1 (D.nd.plOm.2 w) j3 j1 (a + b) _
      (c₃.comp continuous_subtype_val) p33 p31,
    wdAt_bridge l (D.loc l) (D.locA l) tie ι D.host.E D.nd.Om (D.nd.plOm.1 w) w _ _ B2 B1 (D.nd.plOm.2 w) j2 j1 b _
      (hρ'.comp continuous_subtype_val) p22 p21]
  rw [GlobalTheory.Pst.resDec, comp_sumRep] at p31 ⊢
  exact wdAt_sumRep l (D.loc l) (D.locA l) tie ι D.host.E D.nd.Om (D.nd.plOm.1 w) w _ B1 (D.nd.plOm.2 w) j1 a b _ _ p11 p21 p31

end W2

end GlobalTheory.SumRepAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstLetterTwistTensorEquivStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dpstLetter_twist_tensor_equiv : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a : ℕ} (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (m : ↥(Dec (F := E) A) →* GL (Fin 1) ↥L.1) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L s))] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L m))] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))))], IsPst P (Bw.repE L s) → IsPst P (Bw.repE L m) → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) → ∃ e : WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m) ≃ₗ[ℂ] WDSpace P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))), (∀ (σ : ↥(Weil h)) x, e (TensorProduct.map (wdRho P ι Bw h hj (Bw.repE L s) σ) (wdRho P ι Bw h hj (Bw.repE L m) σ) x) = wdRho P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) σ (e x)) ∧ ∀ x, e (((wdN P ι (Bw.repE L s)).rTensor (WDSpace P ι (Bw.repE L m)) + (wdN P ι (Bw.repE L m)).lTensor (WDSpace P ι (Bw.repE L s)) : Module.End ℂ (WDSpace P ι (Bw.repE L s) ⊗[ℂ] WDSpace P ι (Bw.repE L m))) x) = wdN P ι (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m))) (e x) := by
  first | exact @GlobalTheory.Pst.TwistLetters.wdSpace_twist_equiv | exact GlobalTheory.Pst.TwistLetters.wdSpace_twist_equiv | (intros; apply GlobalTheory.Pst.TwistLetters.wdSpace_twist_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumEntriesIntegralAwayFromD
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

namespace GlobalTheory.Ggeo.AdmEntInt

theorem mod_three_eq_two_of_jacobiSym_neg_eq_one (d : ℕ) (h : jacobiSym (-(d : ℤ)) 3 = 1) : d % 3 = 2 := by
  rw [jacobiSym.mod_left] at h
  simp only [Nat.cast_ofNat] at h
  have : (-(d : ℤ)) % 3 = 0 ∨ (-(d : ℤ)) % 3 = 1 ∨ (-(d : ℤ)) % 3 = 2 := by omega
  rcases this with h0 | h0 | h0 <;> rw [h0] at h
  · norm_num at h
  · omega
  · norm_num at h

end GlobalTheory.Ggeo.AdmEntInt

theorem GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hIn D L hT Gi Gl K Y cX ex t hHyp h3 ep be sg
  intro u μ w hlf hd i hi _heven c c'
  have hlf' : LevFree Y u μ w := hlf
  obtain ⟨hAdm, hComb⟩ := GlobalTheory.Ggeo.KerComb.comb_of_tied hIn.algT D L hT Gi Gl K Y cX ex t hHyp u μ w hlf' i hi c c'
  have hd3 : D.what₂.places.resChar w = 3 → D.host.d % 3 = 2 := fun _ =>
    GlobalTheory.Ggeo.AdmEntInt.mod_three_eq_two_of_jacobiSym_neg_eq_one _ (D.host.split_small 3 Nat.prime_three (by norm_num) h3)
  have hJ := _root_.GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.jetsAll hIn D t.cc t.δ t.cc_ok t.δ_ok t.B t.χ t.χ_ok t.X t.seam t.seam_ok _ _ _ _ hAdm
    (D.what₂.places.resChar w) (t.ent.lam w) hd hd3 _ hComb
  let T := t.kf u μ w hlf'
  have hB := T.B_bas i hi.le c
  have hB' := T.B_bas (i + 1) hi c'
  have hK := _root_.GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR D (t.O u μ).dgen (t.O u μ).dgen_gen _ _ _ _ hAdm (D.what₂.places.resChar w) (t.ent.lam w)
    (T.B i c) (T.B (i + 1) c') (fun τ => T.c0 i c c' τ * TaylorLogMetric.lamC (t.ent.lam w) ((t.O u μ).dgen τ)) hB hB'
    (fun τ => by rw [norm_mul, T.unitAbs_eq_one, one_mul]) _ hJ
  rw [← T.th i hi c c'] at hK
  exact _root_.GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero _ _ _ _ _ _ hK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLatticesStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_theta_unitary_lattice_equivariant : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → TaylorLogMetric.IsChi D χ → B.LatAll → B.VecP χ → B.EqP χ → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N N' → DatLoc D cc SS cl N N' Ξ → ∀ (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E), e * star e = 1 → e' * star e' = 1 → kerTh B χ SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') (fun x => Ξ (Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e)) = TaylorLogMetric.pull D B.tor e e' (kerTh B χ SS cl N N' Ξ) := by
  first | exact @GlobalTheory.TwU.KerMove.kerTh_move | exact GlobalTheory.TwU.KerMove.kerTh_move | (intros; apply GlobalTheory.TwU.KerMove.kerTh_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RamifiedColumnsTrueColumnsEqConcreteStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedColumns_trueColumns_eq_concrete : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word), ∃ eM : ((I.rec7 l Z).div.Nu u).V ≃+ Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u, (∀ (r : (I.rec7 l Z).what₂.LL) x, eM (r • x) = (show B.fields.K from r) • eM x) ∧ (∀ x, x ∈ DV.MramL (I.rec7 l Z) u ↔ eM x ∈ Formalism.L2.Col.MramL (Pr := B.primes X) B.wts I.Ch u) ∧ (∀ x, (I.rec7 l Z).nuIn u x = GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 (eM x).1) ∧ ∀ a φ, (I.fm l u a).emb 0 (GlobalTheory.Mem.Col2.KerRat.colForm I l h u a φ) = (I.cols l).e0Tw u a ((I.fm l u I.mu0).emb 0 (GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 φ)) := by
  first | exact @GlobalTheory.AtG.ramCols_true | exact GlobalTheory.AtG.ramCols_true | (intros; apply GlobalTheory.AtG.ramCols_true <;> assumption)
end

