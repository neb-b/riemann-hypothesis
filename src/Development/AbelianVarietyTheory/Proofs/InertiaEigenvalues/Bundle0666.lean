module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0321
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0662
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0656

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicPeriodLocalPrime
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.LTPeriod

variable {l : ℕ} [Fact l.Prime]

theorem iter_φB_alg (k : ℕ) (y : Per.Acris l) :
    (⇑(Per.φB l))^[k] (algebraMap (Per.Acris l) (Per.Bcris l) y) =
      algebraMap (Per.Acris l) (Per.Bcris l) ((⇑(GlobalTheory.MemLoc.phiA l))^[k] y) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, GlobalTheory.MemLoc.fund_phiB_alg, ih]

theorem phiA_alg (a : Per.Ainf l) :
    GlobalTheory.MemLoc.phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) :=
  (GlobalTheory.CrisMaps.phiA_extends l).alg a

theorem iter_phiA_alg (k : ℕ) (a : Per.Ainf l) :
    (⇑(GlobalTheory.MemLoc.phiA l))^[k] (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      algebraMap (Per.Ainf l) (Per.Acris l) ((⇑(Per.φA l))^[k] a) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, phiA_alg, ih]

theorem iter_mul {A : Type} [CommRing A] (f : A →+* A) (k : ℕ) (a b : A) :
    (⇑f)^[k] (a * b) = (⇑f)^[k] a * (⇑f)^[k] b := by
  rw [← RingHom.coe_pow, map_mul]

theorem iter_natCast {A : Type} [CommRing A] (f : A →+* A) (k m : ℕ) :
    (⇑f)^[k] (m : A) = m := by
  rw [← RingHom.coe_pow, map_natCast]

theorem concrete (C : GlobalTheory.MemLoc.Core l) (n : ℕ) (hn : 0 < n) :
    ∃ x : Per.Bcris l, IsUnit x ∧ (⇑(Per.φB l))^[n] x = (l : Per.Bcris l) * x ∧ C.ι x ∈ Per.FilD l 1 ∧
      C.ι x ∉ Per.FilD l 2 ∧ ∀ j : ℕ, 0 < j → j < n →
        C.ι ((⇑(Per.φB l))^[j] x) ∈ Per.FilD l 0 ∧ C.ι ((⇑(Per.φB l))^[j] x) ∉ Per.FilD l 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have he := GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨w, hw0, hw⟩ := _root_.GlobalTheory.PeriodSol.period_solution l C.ε he (m + 1) hn
  obtain ⟨u, hu, hlu, hconv⟩ := _root_.GlobalTheory.MemLoc.phi_xi_unit_tendsto l C
  obtain ⟨c, hc, hcφ⟩ :=
    _root_.GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq (Per.Acris l) l (GlobalTheory.MemLoc.acris_basic l).1 (GlobalTheory.MemLoc.phiA l) u hu hconv (m + 1) hn
  rw [Nat.add_sub_cancel] at hcφ
  set ξ := GlobalTheory.MemLoc.xi C.ε with hξ
  have h1 : (l : Per.Acris l) * (⇑(GlobalTheory.MemLoc.phiA l))^[m] u =
      algebraMap (Per.Ainf l) (Per.Acris l) ((⇑(Per.φA l))^[m + 1] ξ) := by
    rw [← iter_natCast (GlobalTheory.MemLoc.phiA l) m l, ← iter_mul, hlu, iter_phiA_alg,
      ← Function.iterate_succ_apply]
  have hkey : algebraMap (Per.Ainf l) (Per.Acris l) ((⇑(Per.φA l))^[m + 1] ξ) *
      (⇑(GlobalTheory.MemLoc.phiA l))^[m + 1] c = (l : Per.Acris l) * c := by
    rw [← h1]
    linear_combination (l : Per.Acris l) * hcφ
  set a : Per.Acris l := algebraMap (Per.Ainf l) (Per.Acris l) (ξ * w) * c with ha
  have hA : (⇑(GlobalTheory.MemLoc.phiA l))^[m + 1] a = (l : Per.Acris l) * a := by
    rw [ha, iter_mul, iter_phiA_alg, iter_mul, hw, map_mul, map_mul]
    linear_combination (algebraMap (Per.Ainf l) (Per.Acris l) ξ *
      algebraMap (Per.Ainf l) (Per.Acris l) w) * hkey
  set x : Per.Bcris l := algebraMap (Per.Acris l) (Per.Bcris l) a with hx
  have hxφ : (⇑(Per.φB l))^[m + 1] x = (l : Per.Bcris l) * x := by
    rw [hx, iter_φB_alg, hA, map_mul, map_natCast]
  have hxa : x = Per.aB l (ξ * w) * algebraMap (Per.Acris l) (Per.Bcris l) c := by
    have e : algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (ξ * w)) =
        Per.aB l (ξ * w) := by
      apply (GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.2.1
      rw [GlobalTheory.MemLoc.PrimeEx.iota_aB, C.ι_j, GlobalTheory.MemLoc.TFil.j_alg C.j_cris]
    rw [hx, ha, map_mul, e]
  have hx0 : x ≠ 0 := by
    intro h0
    rw [hxa, (hc.map (algebraMap (Per.Acris l) (Per.Bcris l))).mul_left_eq_zero] at h0
    exact hw0 (GlobalTheory.MemLoc.PrimeEx.aB_inj C (h0.trans (map_zero _).symm))
  have hx1 : C.ι x ∈ Per.FilD l 1 := by
    rw [hxa, map_mul, C.ι_j, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ ((GlobalTheory.MemLoc.PrimeEx.fil1 C _).2 ⟨w, rfl⟩)
  have hx0' : ∀ j : ℕ, j < m + 1 → C.ι ((⇑(Per.φB l))^[j] x) ∈ Per.FilD l 0 := by
    intro j _
    rw [hx, iter_φB_alg, C.ι_j]
    exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero _
  obtain ⟨hunit, h2, hj⟩ := _root_.GlobalTheory.MemLoc.EigenDegree.main l C (m + 1) hn x hxφ hx0 hx1 hx0'
  exact ⟨x, hunit, hxφ, hx1, h2, fun j hj0 hjn => ⟨hx0' j hjn, hj j hj0 hjn⟩⟩

end GlobalTheory.LTPeriod

theorem GlobalTheory.LTPeriod.main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (n : ℕ), 0 < n → ∃ x : P.R.B, IsUnit x ∧ (⇑P.φB)^[n] x = (l : P.R.B) * x ∧
      P.ιB x ∈ (P.PD K).Fil 1 ∧ P.ιB x ∉ (P.PD K).Fil 2 ∧ ∀ j : ℕ, 0 < j → j < n →
        P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1 := by
  intro l _ P AI T K n hn
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨x, hu, hφ, h1, h2, hj⟩ := GlobalTheory.LTPeriod.concrete C n hn
  have hit : ∀ (k : ℕ) (b : P.R.B), T.eB ((⇑P.φB)^[k] b) = (⇑(Per.φB l))^[k] (T.eB b) := by
    intro k
    induction k with
    | zero => intro b; rfl
    | succ k ih =>
      intro b
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', T.frob, ih]
  have hfil : ∀ (a : ℤ) (b : P.R.B), P.ιB b ∈ (P.PD K).Fil a ↔ C.ι (T.eB b) ∈ Per.FilD l a := by
    intro a b
    rw [T.fil, hC.ι]
  refine ⟨T.eB.symm x, hu.map T.eB.symm, T.eB.injective ?_, ?_, ?_, fun j hj0 hjn => ?_⟩
  · rw [hit, RingEquiv.apply_symm_apply, hφ, map_mul, map_natCast, RingEquiv.apply_symm_apply]
  · rw [hfil, RingEquiv.apply_symm_apply]
    exact h1
  · rw [hfil, RingEquiv.apply_symm_apply]
    exact h2
  · rw [hfil, hfil, hit, RingEquiv.apply_symm_apply]
    exact hj j hj0 hjn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardAdelicAddChar
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem sFin_sLoc_eq (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    sFin E (sLoc E w y) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA E 0 (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV E w y) := by
  classical
  refine Prod.ext rfl ?_
  refine Subtype.ext (funext fun v => ?_)
  change (sLoc E w y) v = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV E w y v
  by_cases h : v = w
  · subst h
    rw [GlobalTheory.StdDual.singleV_self]
    exact (Pi.single_eq_same v y : (Pi.single v y : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) v = y)
  · rw [GlobalTheory.StdDual.singleV_of_ne _ h]
    exact (Pi.single_eq_of_ne h y : (Pi.single w y : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) v = 0)

theorem exists_stdPsi : ∀ (E : Type) [Field E] [NumberField E], ∃ ψ : AddChar (Ad E) ℂ, StdPsi ψ := by
  intro E _ _
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.StdCharUnique.existsUnique_isStdChar E
  let L : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf E →+ ℂ :=
    AddMonoidHom.mk' (fun x => (GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℂ)) fun a b => by
      rw [GlobalTheory.StdCharUnique.traceInf_add, Complex.ofReal_add]
  have hL : Continuous L := Complex.continuous_ofReal.comp (GlobalTheory.StdCharUnique.continuous_traceInf E)
  have hT : ∀ x : E, L (algebraMap E _ x) = ((Algebra.trace ℚ E x : ℚ) : ℂ) := fun x => by
    show ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E (algebraMap E _ x) : ℝ) : ℂ) = _
    rw [GlobalTheory.StdCharUnique.traceInf_algebraMap, Complex.ofReal_ratCast]
  have hinf : ∀ x, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf E ψ x = Complex.exp (-(2 * Real.pi * Complex.I * L x)) := fun x => by
    rw [hψ.2, GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.stdInf]
    congr 1
    show _ * ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℝ) : ℂ) = -(_ * ((GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf E x : ℝ) : ℂ))
    ring
  have hv : ∀ v, ∃ y, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV E ψ v y ≠ 1 := fun v => by
    obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one_of_trace (GlobalTheory.StdAdelicChar.isCharAF_inv hψ.1) (fun a => by
      rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf, AddChar.inv_apply', ← Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiInf, hinf, hT, ← Complex.exp_neg, neg_neg]) v
    refine ⟨y, fun h1 => hy ?_⟩
    rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV] at h1 ⊢
    rw [AddChar.inv_apply', h1, inv_one]
  refine ⟨ψ, hψ.1.1, hψ.1.2.1, hψ.1.2.2.1, fun x h => GlobalTheory.RatAnnih.adele_rat hψ.1 hv L hL hT hinf x h, ?_⟩
  intro w
  obtain ⟨y, hy⟩ := hv w
  refine ⟨y, ?_⟩
  rw [sFin_sLoc_eq]
  exact hy

end GlobalTheory.CuspGeneric

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ArtinLocalInj

theorem artin_localIdele_injective : ChevalleyUnits → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ w : HeightOneSpectrum (𝓞 E), Function.Injective fun x : (w.adicCompletion E)ˣ => art (Neutral.B1.localIdele E w x) := by
  intro hC E Ω _ _ _ _ _ art ha w
  have hker : ∀ x : (w.adicCompletion E)ˣ, art (Neutral.B1.localIdele E w x) = 1 → x = 1 := by
    intro x hx
    have hx' : art (Neutral.B1.localIdele E w x⁻¹) = 1 := by rw [map_inv, map_inv, hx, inv_one]
    have hv : Valued.v (x : w.adicCompletion E) = 1 := by
      rcases le_total (Valued.v (x : w.adicCompletion E)) 1 with h | h
      · exact _root_.GlobalTheory.OrdZeroUnit.valuation_eq_one_of_approx E w x x.ne_zero h (_root_.GlobalTheory.ArtinApprox.exists_global_approx E Ω art ha w x hx)
      · have h2 : Valued.v ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1 := by
          rw [Units.val_inv_eq_inv_val, map_inv₀]
          exact inv_le_one_of_one_le₀ h
        have h3 := _root_.GlobalTheory.OrdZeroUnit.valuation_eq_one_of_approx E w _ (x⁻¹).ne_zero h2 (_root_.GlobalTheory.ArtinApprox.exists_global_approx E Ω art ha w x⁻¹ hx')
        rw [Units.val_inv_eq_inv_val, map_inv₀, inv_eq_one] at h3
        exact h3
    exact Units.ext (_root_.GlobalTheory.eq_one_of_approx_by_congruent_units hC E w x hv (_root_.GlobalTheory.ArtinApprox.exists_global_approx E Ω art ha w x hx))
  intro x y hxy
  have : art (Neutral.B1.localIdele E w (x * y⁻¹)) = 1 := by
    simp only at hxy
    rw [map_mul, map_mul, map_inv, map_inv, hxy, mul_inv_cancel]
  exact mul_inv_eq_one.mp (hker _ this)

end GlobalTheory.ArtinLocalInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorConvMirabolicAvgEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.GoodNoChiTr

open Polynomial

theorem not_root_of_good (N g : ℕ) [Fact g.Prime] {PP J : Type} (f : PP → (ZMod g)[X])
    (χ : PP → J → (ZMod g)ˣ) (h : Formalism.CyclotomicNorms.IsGood N g f χ) (v : PP) (j : J) :
    ¬ (f v).IsRoot (χ v j : ZMod g) := by
  intro hr
  have hne : f v ≠ 0 := (h.1 v).1.ne_zero
  have hmem : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (χ v j : ZMod g) ∈ Formalism.CyclotomicNorms.rootsBar (f v) := by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [Polynomial.mem_roots (Polynomial.map_ne_zero hne), Polynomial.IsRoot, Polynomial.eval_map,
      Polynomial.eval₂_hom, hr.eq_zero, map_zero]
  obtain ⟨ℓ, hℓ, hℓg⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ g := by
    by_cases h2 : g = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, fun e => h2 e.symm⟩
  exact h.2.2.2.1 ℓ hℓ hℓg v j _ hmem rfl

theorem conv_mirC_eC : GlobalTheory.MirAvg.SeriesKillsAvg → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), GlobalTheory.LiftRows.Given R F → ∀ (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 →
    ∀ (b : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ x : G,
      ∑ y : G, GlobalTheory.DownLift.mirC R i PP a b ε y * RealDat.eC (A := A) (sg0 D A) (y⁻¹ * x) = 0 := by
  intro hS D G _ _ Pl0 T A Ks _ _ _ R F hG i PP a ha b ε hε x
  obtain ⟨eR, plg, iso, hcoef, hdiv, hrec⟩ := hG.core.grp.record
  obtain ⟨kv0, rfl⟩ := plg.surjective PP
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  have heC : ∀ g, RealDat.eC (A := A) (sg0 D A) g = D.ntypes.e0.coeff (eR g) := by
    intro g
    rw [← hcoef g]
    unfold RealDat.eC sg0
    rw [sgAt_mk _ R.hv0]
  rw [Finset.sum_congr rfl (fun y _ => by rw [GlobalTheory.T.mirabolicAverage_eq_coeff_singlePlaceElement D G Pl0 T A Ks R eR plg iso hrec i kv0 a b ε y, heC])]
  refine GlobalTheory.T.convolution_singleFactor_goodProjector_eq_zero D G eR kv0 _ ?_ x
  intro a' hgood
  obtain ⟨L, hL, c, hc, hcc⟩ := GlobalTheory.T.levelCharacter_teichmullerLabel_of_goodTypes D G Pl0 T A Ks R hG.types kv0.1 kv0.2 i (plg kv0).1 (hdiv kv0) (iso kv0) ε hε
  rw [← D.ntypes.eSer_central, hL]
  have h1 := not_root_of_good _ _ _ _ (hgood kv0.1).1 kv0.2 i
  have h2 := not_root_of_good _ _ _ _ (hgood kv0.1).2 kv0.2 i
  have ha' : (fun j => (iso kv0).symm (a j)) ≠ 0 := by
    intro h; apply ha; funext j
    have := congrArg (iso kv0) (congrFun h j)
    simpa using this
  refine hS _ L _ _ _ c hc ?_ ?_ _ b ha'
  · rcases hcc with rfl | rfl
    · exact h1
    · exact h2
  · rcases hcc with rfl | rfl
    · rw [← Units.val_inv_eq_inv_val]; exact h2
    · rw [Units.val_inv_eq_inv_val, inv_inv]; exact h1

end GlobalTheory.GoodNoChiTr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralTwistStable
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace GlobalTheory.RecT

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GoodCusp.tw {y : IrrGL (k := k)} (hy : GoodCusp y) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    GoodCusp (y.tw χ hχ) := by
  rcases hy with h1 | ⟨hf, y₀, χ₀, hχ₀, hfix, rfl⟩
  · exact Or.inl h1
  · exact Or.inr ⟨hf, y₀, χ₀ * χ, hχ₀.mul hχ, hfix, IrrGL.tw_tw _ _ _ _ _⟩

theorem Good.tw {x : IrrGL (k := k)} (hx : Good x) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Good (x.tw χ hχ) := by
  obtain ⟨s, hs, hg⟩ := hx
  refine ⟨s.map (·.tw χ hχ), (hs.tw χ hχ).of_equiv (x.twEquiv χ hχ), ?_⟩
  intro y hy
  obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
  exact (hg y' hy').tw χ hχ

theorem good_tw_iff (x : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Good (x.tw χ hχ) ↔ Good x :=
  ⟨fun h => by simpa only [IrrGL.tw_tw_inv] using h.tw χ⁻¹ hχ.inv, fun h => h.tw χ hχ⟩

theorem good_nu_iff (x : IrrGL (k := k)) (s : ℂ) : Good (x.nu s) ↔ Good x := good_tw_iff x _ _

end GlobalTheory.RecT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
section
noncomputable section

open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
  GlobalTheory.CuspRep GlobalTheory.DefiniteBC

namespace GlobalTheory.LFun.SatBridge

theorem hasSatGL_of_hasSatake : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (α : Fin n → ℂˣ),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    HasSatake π α → GlobalTheory.LFun.HasSatGL w π (Finset.univ.val.map α) := by
  intro E _ _ w n V _ _ π α
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  intro h
  exact GlobalTheory.LFun.SatCompare.hasSatGL_of_hasSatakeGL
    ((GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ π _).2 ⟨α, rfl, h⟩)

end GlobalTheory.LFun.SatBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.SplitCoef

variable {D : D7}

def InvForm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ u : WO S T, IsHalf (cA D a) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f


open Classical in
def coef (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) (f : WO S T → ℂ)
    (x : WO S T) : ℂ :=
  if IsHalf a x then ℓ (heisO ψ S T x f) else 0

def HasShape (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (Φ f : WO S T → ℂ) : Prop :=
  ∀ ℓ, InvForm ψ S T a ℓ → ∃ c : ℂ, ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) = c * Φ x

def locSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ) : Submodule ℂ (WO S T → ℂ) :=
  Submodule.span ℂ {φ | ∃ u : WO S T, IsHalf (a + cA D a) u ∧ φ = heisO ψ S T u f}


open Classical in
def adjDat (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D)
    (ω : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)) → ℂ) (x : WO S T) : ℂ :=
  if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then ω (fun PP => redM PP (frMapAdj S T βS βT x)) else 0

def translT (S T : HSp D) (a : AE D) (Φ : WO S T → ℂ) : Set (WO S T → ℂ) :=
  {Ψ | ∃ g : GA D T, SuppAt a T g ∧ Ψ = fun x => Φ (actO S T 1 g x)}

abbrev latH (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : AddSubgroup (WO S T) :=
  latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True

def LevChart (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)) : Prop :=
  Function.Surjective φ ∧ (∀ z, φ z = 0 ↔ toEAf D e * z = 0) ∧
    (∀ z, toEAf D e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ φ z ∈ v.adicCompletionIntegers D.host.F) ∧
    ∀ (s : Formalism.L2.Herm.intAf D.host.F D.host.E) (o : GlobalTheory.SplitHecke.Ov D v), (o : Fv D.host.F v) = φ s →
      ι (resS D.host.F PP s) = IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) o

def rdAdj (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (x : WO S T) :
    Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) :=
  (frMapAdj S T βS βT x).map φ

end GlobalTheory.DownLift.SplitCoef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleGL1IsCharacterStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_GL1_is_character : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)), x.1 = 1 → ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), x = IrrGL.ofChar χ hχ := by
  first | exact @GlobalTheory.LocLanglands.DegreeOne.classOfDegreeOne_eq_ofChar | exact GlobalTheory.LocLanglands.DegreeOne.classOfDegreeOne_eq_ofChar | (intros; apply GlobalTheory.LocLanglands.DegreeOne.classOfDegreeOne_eq_ofChar <;> assumption)
end

