module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0003
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0259
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0841
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicLocalComponentFixed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SepLoc

theorem exists_sep {K F V : Type*} [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V]
    (r : K → F →ₗ[ℂ] F) (ρ : K → V →ₗ[ℂ] V)
    (hirr : ∀ W : Submodule ℂ V, (∀ k, ∀ v ∈ W, ρ k v ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : (V →ₗ[ℂ] F) → Prop) (hP : ∀ T, P T → ∀ k v, T (ρ k v) = r k (T v))
    (f : F) (hf : f ∈ ⨆ (T : V →ₗ[ℂ] F) (_ : P T), LinearMap.range T) (hf0 : f ≠ 0) :
    ∃ φ : F →ₗ[ℂ] V, φ f ≠ 0 ∧ ∀ k, ∀ f' ∈ ⨆ (T : V →ₗ[ℂ] F) (_ : P T), LinearMap.range T,
      φ (r k f') = ρ k (φ f') := by
  first
  | exact @_root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional
  | exact _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional
  | (apply _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional ..)

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), GlobalTheory.HeightCounting.IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] σ.V, φ f ≠ 0 ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f' ∈ NG.isoTyp a.ρ S, φ (NG.rt L n x f') = σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) (φ f') := by
  intro L _ _ _ n a S hS s σ hloc c hc hcL f hf hf0
  have hle := GlobalTheory.SpanLoc.main L n a S hS s σ hloc c hc hcL
  have hirr : ∀ W : Submodule ℂ σ.V, (∀ k : {x : GAf L n // TrivOutside {s.v} x}, ∀ v ∈ W,
      σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n k.1)) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let R : Subrepresentation σ.ρ := ⟨W, fun g v hv => by
      obtain ⟨x, hx, hxe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s
        (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)
      have hg : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = g := by
        rw [hxe]; ext i j; simp
      have := hW ⟨x, hx⟩ v hv
      rwa [hg] at this⟩
    haveI := σ.irr
    rcases eq_bot_or_eq_top R with h | h
    · left; exact congrArg Subrepresentation.toSubmodule h
    · right; exact congrArg Subrepresentation.toSubmodule h
  obtain ⟨φ, hφf, hφ⟩ := exists_sep (K := {x : GAf L n // TrivOutside {s.v} x}) (fun k => NG.rt L n k.1)
    (fun k => σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n k.1))) hirr
    (fun (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) => (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v,
      T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v))
    (fun T hT k v => hT.2 k.1 k.2 v) f (hle hf) hf0
  exact ⟨φ, hφf, fun x hx f' hf' => hφ ⟨x, hx⟩ f' (hle hf')⟩

end GlobalTheory.SepLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumConditionsAtStandardKernelComparison
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.PdvTie

theorem at_of_stdTie : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ (D : D7) (O : Obj D) (t : KerEntTied O.ex), StdTie D O t → 3 ≤ D.host.splitBound → 5 ≤ O.K.dl1 → 4 ≤ O.K.dl2 → (∀ Ee : OrbitPlaces.Ent D, OrbitPlaces.Shape D O.L O.Gx Ee ∧ ∀ u, ∀ j < D.R.m, ∀ s ∈ D.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * O.L.sc.a) → GlobalTheory.Pdv.At O.ex t.ent := by
  intro hA hG hC hI D O t hT hs h1 h2 hE
  refine StdTie.ind (R := fun D O t => 3 ≤ D.host.splitBound → 5 ≤ O.K.dl1 → 4 ≤ O.K.dl2 →
      (∀ Ee : OrbitPlaces.Ent D, OrbitPlaces.Shape D O.L O.Gx Ee ∧ ∀ u, ∀ j < D.R.m, ∀ s ∈ D.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * O.L.sc.a) →
      GlobalTheory.Pdv.At O.ex t.ent) ?_ hT hs h1 h2 hE
  intro B X I l l0 Z O t h hs h1 h2 hE
  exact GlobalTheory.PdvClose.at_of_true_columns hA hG hC hI I h.ok h.pins l Z l0 O.L O.gatT O.Gx O.Gy O.K O.X O.cX O.ex t
    (GlobalTheory.Pdv.colNorm_of_tw I h.isTw) h.jets h.tw h.ker h.entC h.adapted h.top hs h1 h2 hE

end GlobalTheory.PdvTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentUnitarisableTwist
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.UnitLocWeight

open GlobalTheory.ResW

section Trace

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem zc_eq_sum_Eop : zc E a = ∑ τ : E →+* ℂ, ∑ i : Fin a, Eop τ i i := _root_.GlobalTheory.ResW.zc_eq_sum_Eop E a

theorem sum_Eop_apply {π : CuspSub E a} {τ : E →+* ℂ} {m : Multiset ℂ} (h : π.HasInfChar τ m) {φ : Sm E a}
    (hφ : φ ∈ π.V) : (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := GlobalTheory.T.cuspidal_traceMatrixUnits_acts_by_sum_infinitesimalCharacter E a π τ m h φ hφ

theorem cex_eq (π : CuspSub E a) : cex (⟨a, π⟩ : Letter E) = ∑ τ : E →+* ℂ, ((CG.mk π).infChar τ).sum := by
  refine (letter_centralExponent E ⟨a, π⟩).2.2.2.2 _ ?_
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  refine ⟨φ, hφ, h0, ?_⟩
  change zc E a φ = _
  rw [zc_eq_sum_Eop, LinearMap.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun τ _ => sum_Eop_apply (ParLaws.hasInfChar_infChar (CG.mk π) τ) hφ

end Trace

end GlobalTheory.UnitLocWeight

namespace GlobalTheory.UnitLocWeight

open GlobalTheory.ResW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem sum_infChar_of_isWeight {π : CuspSub E a} {wt : ℤ} (h : IsWeight π wt) :
    ∑ τ : E →+* ℂ, ((CG.mk π).infChar τ).sum =
      (Module.finrank ℚ E : ℂ) * ((a : ℂ) * ((a : ℂ) - 1 - (wt : ℂ))) / 2 := by
  set c : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hc : Function.Bijective fun τ : E →+* ℂ => τ.comp c := by
    refine Finite.injective_iff_bijective.1 fun τ τ' e => RingHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := (IsCMField.complexConj E).surjective x
    exact RingHom.congr_fun e y
  have h1 : ∑ τ : E →+* ℂ, ((CG.mk π).infChar (τ.comp c)).sum = ∑ τ : E →+* ℂ, ((CG.mk π).infChar τ).sum :=
    Function.Bijective.sum_comp hc (fun τ => ((CG.mk π).infChar τ).sum)
  have h2 : ∀ τ : E →+* ℂ, ((CG.mk π).infChar (τ.comp c)).sum =
      (a : ℂ) * ((a : ℂ) - 1 - (wt : ℂ)) - ((CG.mk π).infChar τ).sum := fun τ => by
    rw [h τ, Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, CG.card_infChar, Multiset.map_id',
      nsmul_eq_mul]
  have h3 := Embeddings.card E ℂ
  simp only [h2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, h3, nsmul_eq_mul] at h1
  linear_combination -h1 / 2

end GlobalTheory.UnitLocWeight

namespace GlobalTheory.UnitLocWeight

open GlobalTheory.ResW

theorem rexp_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} {wt : ℤ}
    (h : IsWeight π wt) : rexp (⟨a, π⟩ : Letter E) = ((a : ℝ) - 1 - wt) / 2 := by
  have e := (cex_eq π).trans (sum_infChar_of_isWeight h)
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have e2 : (cex (⟨a, π⟩ : Letter E)).re = (Module.finrank ℚ E : ℝ) * ((a : ℝ) * ((a : ℝ) - 1 - wt)) / 2 := by
    rw [e]
    have : (Module.finrank ℚ E : ℂ) * ((a : ℂ) * ((a : ℂ) - 1 - (wt : ℂ))) / 2 =
        (((Module.finrank ℚ E : ℝ) * ((a : ℝ) * ((a : ℝ) - 1 - wt)) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  unfold rexp
  change (cex (⟨a, π⟩ : Letter E)).re / ((a : ℝ) * Module.finrank ℚ E) = _
  rw [e2]
  field_simp

end GlobalTheory.UnitLocWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalLanglandsSplitQp
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SerChar

open GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.SplitRead

theorem det_map_units {R S : Type} [CommRing R] [CommRing S] (f : R ≃+* S) {n : Type} [Fintype n] [DecidableEq n]
    (g : GL n R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f.toRingHom g) =
      Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp [RingHom.map_det]

end GlobalTheory.SerChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsSplitPlaceOfInertOverRealSubfieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_isSplitPlace_of_inert_over_realSubfield : ∀ (D : D7) (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.UG.IsInertAt (↥D.host.F) D.host.E (HeightOneSpectrum.under (𝓞 ↥D.host.F) Pp) Pp → ¬ Formalism.BasicNotions.IsSplitPl D.host Pp := by
  first | exact @GlobalTheory.not_isSplitPl_of_isInertAt | exact GlobalTheory.not_isSplitPl_of_isInertAt | (intros; apply GlobalTheory.not_isSplitPl_of_isInertAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorOfMono0
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PlainMono

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem linked_single {ρ ρ' : IrrGL (k := k)} (hρ : ρ.IsCusp) (hρ' : ρ'.IsCusp) (hne : ρ ≠ ρ.nu 1) (e : ρ' = ρ.nu 1) :
    (Segment.single ρ hρ).Linked (Segment.single ρ' hρ') := by
  subst e
  refine ⟨⟨Segment.ofFirst ρ hρ 2 two_pos, ?_⟩, ?_, ?_⟩
  · rw [Segment.carrier_single, Segment.carrier_single]
    ext z
    rw [Segment.mem_carrier]
    simp only [Segment.first_ofFirst, Segment.len_ofFirst, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      interval_cases i
      · left; simp
      · right; simp
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_iff, Set.mem_singleton_iff]
    exact hne
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_iff, Set.mem_singleton_iff]
    exact fun e => hne e.symm

theorem eq_single_of_len {Δ : Segment k} (h : Δ.len = 1) : Δ = Segment.single Δ.first Δ.isCusp_first :=
  Segment.ext_first (by simp [Segment.single]) (by simp [Segment.single, h])

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem ne_nu_one {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (L : UpperTheory.Zero.LLC.LawsT a ha rc) {ρ : IrrGL (k := w.adicCompletion E)}
    (hρ : ρ.IsCusp) : ρ ≠ ρ.nu 1 := by
  intro e0
  refine WD.lpTw_one_ne (rc ρ) (by rw [L.dim]; exact hρ.1) ?_
  calc (rc ρ).lpTw 1 = rc (ρ.nu ((1 : ℝ) : ℂ)) := (L.nu ρ 1).symm
    _ = rc ρ := by rw [Complex.ofReal_one, ← e0]

end GlobalTheory.PlainMono
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatake
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct

namespace GlobalTheory.LabelTransport


open Classical in
theorem coset_transport {G H : Type} [Group G] [Group H] (ψ : G →* H) (T U J : Subgroup G) (K : Set H) (α : H)
    (R : Finset H) (hK : ∀ x, ψ x ∈ K ↔ x ∈ U ∧ x ∈ T) (hKr : ∀ k ∈ K, ∃ x, ψ x = k)
    (hJ : ∀ x ∈ T, x ∈ J ↔ x ∈ U) (pre : H → G) (hpre : ∀ γ ∈ R, ψ (pre γ) = γ ∧ pre γ ∈ T)
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂)
    (h2 : ∀ x : H, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K) :
    ∃ Ds : Set G, (∀ x ∈ Ds, x ∈ T) ∧ (∀ x ∈ Ds, ∀ κ ∈ U, κ ∈ T → x * κ ∈ Ds ∧ κ * x ∈ Ds) ∧
      {c : G ⧸ J | ∃ x ∈ Ds, (x : G ⧸ J) = c}.Finite ∧
      ∀ (W : Type) [AddCommMonoid W] (F : G → W), (∀ x, ∀ κ ∈ J, κ ∈ T → F (x * κ) = F x) → ∀ g,
        (∑ᶠ c : G ⧸ J, if hc : ∃ x ∈ Ds, (x : G ⧸ J) = c then F (g * hc.choose) else 0) = ∑ γ ∈ R, F (g * pre γ) := by
  have hmul : ∀ a ∈ K, ∀ b ∈ K, a * b ∈ K := by
    intro a ha b hb
    obtain ⟨x, rfl⟩ := hKr a ha
    obtain ⟨y, rfl⟩ := hKr b hb
    rw [← map_mul, hK]
    exact ⟨mul_mem ((hK x).1 ha).1 ((hK y).1 hb).1, mul_mem ((hK x).1 ha).2 ((hK y).1 hb).2⟩
  let Ds : Set G := {x | x ∈ T ∧ ∃ k₁ ∈ K, ∃ k₂ ∈ K, ψ x = k₁ * α * k₂}
  have hpD : ∀ γ ∈ R, pre γ ∈ Ds := fun γ hγ => ⟨(hpre γ hγ).2, by rw [(hpre γ hγ).1]; exact h1 γ hγ⟩
  have hrel : ∀ γ ∈ R, ∀ x ∈ T, ((pre γ : G ⧸ J) = (x : G ⧸ J) ↔ γ⁻¹ * ψ x ∈ K) := by
    intro γ hγ x hx
    have ht : (pre γ)⁻¹ * x ∈ T := mul_mem (inv_mem (hpre γ hγ).2) hx
    have e : ψ ((pre γ)⁻¹ * x) = γ⁻¹ * ψ x := by rw [map_mul, map_inv, (hpre γ hγ).1]
    rw [QuotientGroup.eq, hJ _ ht, ← e, hK]
    exact (and_iff_left ht).symm
  have hset : ∀ c : G ⧸ J, (∃ x ∈ Ds, (x : G ⧸ J) = c) ↔ c ∈ R.image fun γ => (pre γ : G ⧸ J) := by
    intro c
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h2 _ hx.2
      exact ⟨γ, hγ, (hrel γ hγ x hx.1).2 e⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨_, hpD γ hγ, rfl⟩
  refine ⟨Ds, fun x hx => hx.1, ?_, ?_, ?_⟩
  · rintro x ⟨hx, a, ha, b, hb, e⟩ κ hκ hκ'
    have hk : ψ κ ∈ K := (hK κ).2 ⟨hκ, hκ'⟩
    refine ⟨⟨mul_mem hx hκ', a, ha, _, hmul b hb _ hk, ?_⟩, ⟨mul_mem hκ' hx, _, hmul _ hk a ha, b, hb, ?_⟩⟩
    · rw [map_mul, e, mul_assoc]
    · rw [map_mul, e]; simp only [mul_assoc]
  · exact (R.image fun γ => (pre γ : G ⧸ J)).finite_toSet.subset fun c hc => (hset c).1 hc
  · intro W _ F hF g
    rw [finsum_eq_sum_of_support_subset (s := R.image fun γ => (pre γ : G ⧸ J))]
    · rw [Finset.sum_image]
      · refine Finset.sum_congr rfl fun γ hγ => ?_
        have hc : ∃ x ∈ Ds, (x : G ⧸ J) = (pre γ : G ⧸ J) := ⟨_, hpD γ hγ, rfl⟩
        rw [dite_eq_left hc]
        have hj : hc.choose⁻¹ * pre γ ∈ J := QuotientGroup.eq.1 hc.choose_spec.2
        have ht : hc.choose⁻¹ * pre γ ∈ T := mul_mem (inv_mem hc.choose_spec.1.1) (hpre γ hγ).2
        rw [← hF (g * hc.choose) _ hj ht, mul_assoc, mul_inv_cancel_left]
      · intro a ha b hb e
        have ha' : a ∈ R := ha
        have hb' : b ∈ R := hb
        have e1 := (hrel a ha' _ (hpre b hb').2).1 e
        have e2 := (hrel b hb' _ (hpre b hb').2).1 rfl
        rw [(hpre b hb').1] at e1 e2
        exact (h2 b (h1 b hb')).unique ⟨ha', e1⟩ ⟨hb', e2⟩
    · intro c hc
      by_contra hn
      exact hc (dif_neg fun h => hn ((hset c).1 h))

theorem tensCast_under {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (P : HeightOneSpectrum (𝓞 E)) (α : FiniteAdeleRing (𝓞 F1) F1) (h1 : α (P.under (𝓞 F1)) = 1)
    (h0 : ∀ v', v' ≠ P.under (𝓞 F1) → α v' = 0) :
    ∃ α' : FiniteAdeleRing (𝓞 F2) F2,
      GlobalTheory.NJoin.tensCast h (α ⊗ₜ[F1] (1 : E)) = (1 : E) ⊗ₜ[F2] α' ∧ α' (P.under (𝓞 F2)) = 1 ∧
        ∀ v', v' ≠ P.under (𝓞 F2) → α' v' = 0 := by
  subst h
  exact ⟨α, rfl, h1, h0⟩

theorem idem_mul_iff {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (α : AFplus L) (h1 : α v = 1) (h0 : ∀ v', v' ≠ v → α v' = 0)
    (z : AL L) : ((1 : L) ⊗ₜ[maximalRealSubfield L] α) * z = z ↔ ∀ v', v' ≠ v → compAt L v' z = 0 := by
  have hc : ∀ u, compAt L u ((1 : L) ⊗ₜ[maximalRealSubfield L] α) = (1 : L) ⊗ₜ[maximalRealSubfield L] (α u) := by
    intro u
    rw [compAt, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  constructor
  · intro h u hu
    rw [← h, map_mul, hc, h0 u hu, TensorProduct.tmul_zero, zero_mul]
  · intro h
    rw [← sub_eq_zero]
    apply GlobalTheory.AL_eq_zero_of_compAt
    intro u
    rw [map_sub, map_mul, hc]
    by_cases hu : u = v
    · subst hu
      rw [h1, ← Algebra.TensorProduct.one_def, one_mul, sub_self]
    · rw [h u hu, mul_zero, sub_zero]

theorem conj_supp {B : Type} [CommRing B] {m k : ℕ} (φ : B) (β : Matrix (Fin m) (Fin k) B)
    (K : Matrix (Fin k) (Fin k) B) (β' : Matrix (Fin k) (Fin m) B) (h1 : β * β' = 1) (M : Matrix (Fin m) (Fin m) B)
    (hM : M = β * K * β') (h : ∀ i j, φ * (K - 1) i j = (K - 1) i j) : ∀ i j, φ * (M - 1) i j = (M - 1) i j := by
  have e : M - 1 = β * (K - 1) * β' := by
    rw [hM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have e1 : φ • (K - 1) = K - 1 := Matrix.ext h
  have e2 : φ • (β * (K - 1) * β') = β * (K - 1) * β' := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, e1]
  rw [e]
  exact fun i j => congrFun (congrFun e2 i) j

theorem conj_supp_iff {B : Type} [CommRing B] {m k : ℕ} (φ : B) (β : Matrix (Fin m) (Fin k) B)
    (K : Matrix (Fin k) (Fin k) B) (β' : Matrix (Fin k) (Fin m) B) (h1 : β * β' = 1) (h2 : β' * β = 1)
    (M : Matrix (Fin m) (Fin m) B) (hM : M = β * K * β') :
    (∀ i j, φ * (M - 1) i j = (M - 1) i j) ↔ ∀ i j, φ * (K - 1) i j = (K - 1) i j := by
  refine ⟨conj_supp φ β' M β h2 K ?_, conj_supp φ β K β' h1 M hM⟩
  rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]


attribute [local instance] Formalism.BasicNotions.Host.cmStar in
set_option maxHeartbeats 2000000 in
theorem suppF_iff_trivOutside (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hV : GlobalTheory.NJoin.StdFrame hF PV)
    (e f : Formalism.L2.Theta.AE D) (hef : Formalism.IndefR.Mult.IsPrimeIdem s.w e f) (κ : GAf D.host.E n) :
    Formalism.IndefR.Mult.SuppF V f (PV.ψ κ) ↔ TrivOutside {s.v} κ := by
  obtain ⟨⟨β, β', h1, h2, hm⟩, -⟩ := hV
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, ⟨α, rfl, hα1, hα0⟩, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hef
  obtain ⟨α', hT, hw1, hw0⟩ := tensCast_under hF s.w α hα1 hα0
  have hv : s.w.under (𝓞 (maximalRealSubfield D.host.E)) = s.v := HeightOneSpectrum.ext s.w_under
  rw [hv] at hw1 hw0
  set x := algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) with hx
  have hfin : Formalism.L2.Theta.finPart D x = α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  set K := (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm with hKdef
  set M := (Formalism.L2.Theta.mt V (PV.ψ κ)).map (Formalism.L2.Theta.finPart D) with hMdef
  have e6 : (Formalism.L2.Theta.mt V (PV.ψ κ) - 1).map (Formalism.L2.Theta.finPart D) = M - 1 := by
    rw [Matrix.map_sub _ (map_sub (Formalism.L2.Theta.finPart D)),
      Matrix.map_one _ (map_zero (Formalism.L2.Theta.finPart D)) (map_one (Formalism.L2.Theta.finPart D))]
  have e2 : ((Formalism.L2.Theta.mt V (PV.ψ κ)) - 1).map (Formalism.L2.Theta.infPart D) = 0 := by
    have hk := MonoidHom.mem_ker.1 (PV.into κ)
    rw [Matrix.map_sub _ (map_sub (Formalism.L2.Theta.infPart D)),
      Matrix.map_one _ (map_zero (Formalism.L2.Theta.infPart D)) (map_one (Formalism.L2.Theta.infPart D))]
    have e3 : (Formalism.L2.Theta.mt V (PV.ψ κ)).map (Formalism.L2.Theta.infPart D) = (Formalism.L2.Theta.infHom V (PV.ψ κ)).val := rfl
    rw [e3, hk, Units.val_one, sub_self]
  have s1 : Formalism.IndefR.Mult.SuppF V x (PV.ψ κ) ↔ ∀ i j, Formalism.L2.Theta.finPart D x * (M - 1) i j = (M - 1) i j := by
    rw [← e6]
    refine forall_congr' fun i => forall_congr' fun j => ⟨fun h => ?_, fun h => ?_⟩
    · exact ((Formalism.L2.Theta.finPart D).map_mul _ _).symm.trans (congrArg (Formalism.L2.Theta.finPart D) h)
    · rw [← sub_eq_zero]
      apply GlobalTheory.PlaceSupp.AE_eq_zero D
      · have h0 : Formalism.L2.Theta.infPart D ((Formalism.L2.Theta.mt V (PV.ψ κ) - 1) i j) = 0 := congrFun (congrFun e2 i) j
        rw [RingHom.map_sub, RingHom.map_mul, h0, mul_zero, sub_zero]
      · rw [RingHom.map_sub, RingHom.map_mul, sub_eq_zero]
        exact h
  have s2 := conj_supp_iff (Formalism.L2.Theta.finPart D x) β K β' h1 h2 M (hm κ)
  have e7 : (K - 1).map (GlobalTheory.NJoin.tensCast hF) = (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1 := by
    rw [Matrix.map_sub _ (map_sub (GlobalTheory.NJoin.tensCast hF)),
      Matrix.map_one _ (map_zero (GlobalTheory.NJoin.tensCast hF)) (map_one (GlobalTheory.NJoin.tensCast hF))]
    congr 1
    exact Matrix.ext fun a b => (GlobalTheory.NJoin.tensCast hF).apply_symm_apply ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) a b)
  have s3 : ∀ i j, Formalism.L2.Theta.finPart D x * (K - 1) i j = (K - 1) i j ↔
      ∀ v', v' ≠ s.v → compAt D.host.E v' (((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1) i j) = 0 := by
    intro i j
    have e8 : GlobalTheory.NJoin.tensCast hF ((K - 1) i j) = ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1) i j :=
      congrFun (congrFun e7 i) j
    rw [← idem_mul_iff s.v α' hw1 hw0, ← (GlobalTheory.NJoin.tensCast hF).injective.eq_iff, (GlobalTheory.NJoin.tensCast hF).map_mul,
      hfin, hT, e8]
  have e9 : ∀ v', ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1).map (compAt D.host.E v') =
      (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (compAt D.host.E v') - 1 := fun v' => by
    rw [Matrix.map_sub _ (map_sub (compAt D.host.E v')),
      Matrix.map_one _ (map_zero (compAt D.host.E v')) (map_one (compAt D.host.E v'))]
  rw [s1, s2]
  constructor
  · intro h v' hv'
    rw [← sub_eq_zero, ← e9]
    exact Matrix.ext fun i j => (s3 i j).1 (h i j) v' hv'
  · intro h i j
    refine (s3 i j).2 fun v' hv' => ?_
    have := e9 v'
    rw [h v' hv', sub_self] at this
    exact congrFun (congrFun this i) j


end GlobalTheory.LabelTransport
end

