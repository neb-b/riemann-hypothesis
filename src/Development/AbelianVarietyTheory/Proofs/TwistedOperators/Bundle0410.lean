module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPointCarryingFrameLat
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.FramePointMove

open scoped Matrix

theorem conj_maps_iff {A : Type} [CommRing A] {n : ℕ} (J x : GL (Fin n) A) {P Q : Set (Fin n → A)}
    (hJ : J.1.mulVec '' P = Q) :
    (∀ y ∈ Q, (J * x * J⁻¹).1 *ᵥ y ∈ Q) ↔ ∀ w ∈ P, x.1 *ᵥ w ∈ P := by
  have hinj : Function.Injective J.1.mulVec := fun a b h => by
    have := congrArg (fun z => (J⁻¹).1 *ᵥ z) h
    simpa [Matrix.mulVec_mulVec] using this
  have mem : ∀ z, J.1 *ᵥ z ∈ Q ↔ z ∈ P := fun z => by
    rw [← hJ, hinj.mem_set_image]
  have e : ∀ w, (J * x * J⁻¹).1 *ᵥ (J.1 *ᵥ w) = J.1 *ᵥ (x.1 *ᵥ w) := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    simp [Matrix.mul_assoc]
  constructor
  · intro h w hw
    have := h _ ((mem w).2 hw)
    rwa [e, mem] at this
  · intro h y hy
    rw [← hJ] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    rw [e, mem]
    exact h w hw

theorem conj_maps_inv_iff {A : Type} [CommRing A] {n : ℕ} (J x : GL (Fin n) A) {P Q : Set (Fin n → A)}
    (hJ : J.1.mulVec '' P = Q) :
    (∀ y ∈ Q, ((J * x * J⁻¹)⁻¹).1 *ᵥ y ∈ Q) ↔ ∀ w ∈ P, (x⁻¹).1 *ᵥ w ∈ P := by
  have hinv : (J * x * J⁻¹)⁻¹ = J * x⁻¹ * J⁻¹ := by group
  rw [hinv]
  exact conj_maps_iff J x⁻¹ hJ


set_option maxHeartbeats 800000 in
theorem exists_point_carrying_frameLat : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∃ a : GfC V, GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V (frameLat V) Λ (finE V (a : GA D V)).val ∧ ∀ g : GfC V, finE V ((a * g * a⁻¹ : GfC V) : GA D V) ∈ St β ↔ ∀ v, finLoc V v g ∈ Kv V v := by
  intro D V β Λ N hβ
  obtain ⟨β₀, -, hβ₀⟩ := _root_.GlobalTheory.SelfDualBaseFrame.exists_baseFrame_frameLat D V
  obtain ⟨j, hj, -⟩ := GlobalTheory.FinAdIdent.exists_latIsom V V rfl (frameLat V) Λ β₀ β 1 N hβ₀ hβ ∅
    (fun _ h => absurd h (Set.notMem_empty _))
  obtain ⟨j', h1, h2⟩ := GlobalTheory.FinAdIdent.exists_inv hj.1.1
  let J : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) := ⟨j, j', h1, h2⟩
  have hJ : J ∈ Formalism.L2.DIV.UA D.sp.cm V.gram := hj.1.2
  obtain ⟨k, hk, e⟩ := GlobalTheory.AdIsomCorrection.exists_finE V J hJ
  refine ⟨⟨k, hk⟩, ?_, fun g => ?_⟩
  · show GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V (frameLat V) Λ (finE V k).val
    rw [e]
    exact hj
  · have hg : finE V ((⟨k, hk⟩ * g * ⟨k, hk⟩⁻¹ : GfC V) : GA D V) = J * finE V (g : GA D V) * J⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, e]
    have hJP : J.1.mulVec '' (Formalism.L2.Herm.hatL (F := D.host.F) (frameLat V) : Set _) =
        (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set _) := hj.2
    rw [hg, GlobalTheory.LevSplit.mem_St_iff β Λ hβ.1]
    have hs := GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β₀ (frameLat V) hβ₀.1 (g : GA D V)
    rw [GlobalTheory.LevSplit.mem_St_iff β₀ (frameLat V) hβ₀.1] at hs
    refine Iff.trans ?_ hs
    exact and_congr (conj_maps_iff J _ hJP) (conj_maps_inv_iff J _ hJP)

end GlobalTheory.FramePointMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerLargerSourceMirrorCase
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealItLarge

open GlobalTheory.Chain GlobalTheory.Chain.RealIt

theorem exists_isCoverIt_swap (p q r s : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q)
    (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (Tm : R₁.U.H →L[ℂ] R₂.U.H →L[ℂ] F.H)
    (hI : ∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y')
    (hE : ∀ g h x y, F.π (g, h) (Tm x y) = Tm (R₁.U.π g x) (R₂.U.π h y)) :
    ∃ B : Pol r s p q →ₗ[ℂ] R₁.U.H →ₛₗ[starRingEnd ℂ] R₂.U.H, IsCoverIt R₂ R₁ B := by
  let A : R₁.U.H → F.H →L[ℂ] R₂.U.H := fun x => ContinuousLinearMap.adjoint (Tm x)
  have hC : ∀ x φ y, inner ℂ y (A x φ) = inner ℂ (Tm x y) φ := fun x φ y => by
    simp only [A]
    rw [ContinuousLinearMap.adjoint_inner_right]
  have hn : ∀ x y, ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
    intro x y
    have h := hI x x y y
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
    have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hall : ∀ g h φ x, A (R₁.U.π g x) (F.π (g, h) φ) = R₂.U.π h (A x φ) := by
    intro g h φ x
    apply ext_inner_left ℂ
    intro y
    obtain ⟨y, rfl⟩ : ∃ y', R₂.U.π h y' = y := ⟨R₂.U.π h⁻¹ y, by
      change (R₂.U.π h * R₂.U.π h⁻¹) y = y
      rw [← map_mul]; simp⟩
    rw [hC, ← hE, GlobalTheory.Chain.CoverContr.inner_map_of_norm _ (R₂.U.isom h), hC]
    exact GlobalTheory.Chain.CoverContr.inner_map_of_norm _ (F.isom _) _ _
  have he : ∀ h φ x, A x (F.π (1, h) φ) = R₂.U.π h (A x φ) := fun h φ x => by
    simpa using hall 1 h φ x
  have hi : ∀ g φ x, A (R₁.U.π g x) (F.π (g, 1) φ) = A x φ := fun g φ x => by
    simpa using hall g 1 φ x
  let sw : Pol r s p q →ₗ[ℂ] Pol p q r s := (MvPolynomial.rename Prod.swap).toLinearMap
  have hsw : ∀ P, sw P = MvPolynomial.rename Prod.swap P := fun _ => rfl
  let B : Pol r s p q →ₗ[ℂ] R₁.U.H →ₛₗ[starRingEnd ℂ] R₂.U.H :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P x => A x (F.ι (sw P)))
      (fun P Q x => by simp only [map_add (f := _)])
      (fun c P x => by simp only [map_smul, RingHom.id_apply])
      (fun P x x' => by simp only [A, map_add (f := _), ContinuousLinearMap.add_apply])
      (fun c P x => by simp only [A, map_smul, map_smulₛₗ, ContinuousLinearMap.smul_apply])
  have hB : ∀ P x, B P x = A x (F.ι (sw P)) := fun _ _ => rfl
  obtain ⟨-, hd1, hd2⟩ := _root_.GlobalTheory.FockEmbExp.fock_derived p q r s T₀ T₁ T₂ F
  have hsym := GlobalTheory.FockSwap.swap_symmetry r s p q
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · intro P
    refine ⟨‖F.ι (sw P)‖, fun x => ?_⟩
    rw [hB]
    set φ := F.ι (sw P)
    have h := hC x φ (A x φ)
    have h1 : ‖A x φ‖ * ‖A x φ‖ ≤ ‖A x φ‖ * (‖φ‖ * ‖x‖) := by
      have := norm_inner_le_norm (𝕜 := ℂ) (Tm x (A x φ)) φ
      rw [← h, hn, inner_self_eq_norm_sq_to_K] at this
      simp at this
      nlinarith
    rcases (norm_nonneg (A x φ)).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · exact le_of_mul_le_mul_left h1 h0
  · intro P x
    rw [R₂.ι_range, hB]
    have hf := (GlobalTheory.FockKFin.kfin_fock p q r s T₀ T₁ T₂ F
      (GlobalTheory.FockDegree.Om_Kset_homog p q r s T₀ T₁ T₂ F) (sw P)).2
    unfold KFin at *
    have : (Set.range fun k : T₂.Kset => R₂.U.π k (A x (F.ι (sw P)))) =
        (A x).toLinearMap '' Set.range fun k : T₂.Kset => F.π (1, k) (F.ι (sw P)) := by
      rw [← Set.range_comp]; congr 1; funext k; simp [he]
    rw [this, ← Submodule.map_span]
    infer_instance
  · intro x hx
    by_contra hcon
    push_neg at hcon
    have hcon' : ∀ P : Pol p q r s, A x (F.ι P) = 0 := fun P => by
      have := hcon (MvPolynomial.rename Prod.swap P)
      rwa [hB, hsw, MvPolynomial.rename_rename, Prod.swap_swap_eq, MvPolynomial.rename_id_apply] at this
    have h0 : ∀ φ, A x φ = 0 := fun φ =>
      congrFun (Continuous.ext_on F.dense (A x).continuous (continuous_const (y := (0 : R₂.U.H)))
        (by rintro _ ⟨P, rfl⟩; exact hcon' P)) φ
    have := R₂.nontriv
    obtain ⟨y, hy⟩ := exists_ne (0 : R₂.U.H)
    have h := hC x (Tm x y) y
    rw [h0, inner_zero_right, eq_comm, inner_self_eq_zero, ← norm_eq_zero, hn, mul_eq_zero,
      norm_eq_zero, norm_eq_zero] at h
    tauto
  · intro Z hZ P x
    have := (((A x).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) (hd2 Z hZ (sw P))
    have e1 : sw (fockAct1 r s p q Z P) = fockAct2 p q r s Z (sw P) := hsym.1 Z P
    simpa [hB, Function.comp_def, he, e1] using this
  · intro Z hZ P x
    have h1 := (((A x).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) (hd1 Z hZ (sw P))
    have h2 := h1.scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp)
    have e2 : sw (fockAct2 r s p q Z P) = fockAct1 p q r s Z (sw P) := hsym.2.1 Z P
    have h3 : (fun t : ℝ => B P (R₁.U.π (T₁.expt (t • Z)) x)) =
        fun t : ℝ => A x (F.π (T₁.expt ((-t) • Z), 1) (F.ι (sw P))) := by
      funext t
      rw [hB, ← hi (T₁.expt (t • Z)) (F.π (T₁.expt ((-t) • Z), 1) (F.ι (sw P))) x]
      congr 1
      change _ = (F.π (T₁.expt (t • Z), 1) * F.π (T₁.expt ((-t) • Z), 1)) _
      rw [← map_mul, Prod.mk_mul_mk, ← T₁.expt_add Z hZ, add_neg_cancel, zero_smul, T₁.expt_zero,
        mul_one, Prod.mk_one_one, map_one, ContinuousLinearMap.one_apply]
    rw [h3, hB, e2]
    simpa [Function.comp_def] using h2

end GlobalTheory.Chain.RealItLarge

namespace GlobalTheory.Chain.RealItLarge

open GlobalTheory.Chain GlobalTheory.Chain.RealIt Formalism.MainNotions.SchurIrreducible

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem isParam_lamM' {t : ℕ} {al be ga de : List ℚ} (h : HypA t al be ga de) : IsParam (lamM' t al be ga de) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have mem : ∀ e, e ∈ ga ++ de ++ al ++ be → e ∈ al ++ be ++ ga ++ de := fun e he => by
    simp only [List.mem_append] at he ⊢
    tauto
  have h' : HypA t ga de al be := by
    refine ⟨h1, by omega, h5, h6, h3, h4, ?_, fun e he => h8 e ?_, fun e he => h9 e ?_, fun e he => h10 e (mem e he),
      fun e he => h11 e (mem e he)⟩
    · refine (List.Perm.nodup_iff ?_).1 h7
      rw [List.append_assoc (al ++ be), List.append_assoc (ga ++ de)]
      exact List.perm_append_comm
    · simp only [List.mem_append] at he ⊢
      tauto
    · simp only [List.mem_append] at he ⊢
      tauto
  obtain ⟨-, -, ⟨p1, p2, p3, p4⟩, -⟩ := _root_.GlobalTheory.LowestTypes.lowest_types t ga de al be h'
  let σ : Ix (al.length + de.length) (ga.length + be.length + t) → Ix (ga.length + be.length + t) (al.length + de.length) :=
    Sum.swap
  have e : ∀ a, lamM' t al be ga de a = lamA' t ga de al be (σ a) := fun a => by rcases a with a | a <;> rfl
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, fun a => ?_, fun a b => ?_⟩
  · rw [e, e] at hab
    exact Sum.swap_leftInverse.injective (p1 hab)
  · rw [e, e]
    refine p2 _ _ ?_
    rcases a with a | a <;> rcases b with b | b <;> exact hab
  · rw [e]; exact p3 _
  · rw [e, e]; exact p4 _ _

theorem exists_locIt_large {X : ProvA} (hX : ChosenSeries X) (h1 : ArchimedeanRallisFirst X) (h2 : ArchimedeanRallisSecond X)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {t : ℕ}
    {al be ga de : List ℚ} (hd : DataARm t al be ga de) {aS aT : ℚ}
    (hS : S τ = dualPar (signed (al ++ de) (ga ++ block t ++ be) aT))
    (hS' : S' τ = dualPar (signed (al ++ be) (ga ++ de) aS)) :
    (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ aS aT A := by
  obtain ⟨-, p1, -⟩ := _root_.GlobalTheory.LowestTypes.lowest_types t al be ga de hd.1
  have p2 := isParam_lamM' hd.1
  have ht := hd.1.1
  have hn := hd.1.2.1
  obtain ⟨⟨e, he⟩, m, hm, hU⟩ := hB.1 X V S M τ (al.length + de.length) (ga.length + be.length + t) _ _ aT
    ⟨by omega, by simp, by simp [block]; omega, p2, hX _ _ _ p2, hS⟩
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hB.2 X W S' M' τ (al.length + be.length) (ga.length + de.length) _ _ aS
    ⟨by omega, by simp, by simp, p1, hX _ _ _ p1, hS'⟩
  obtain ⟨U, hU⟩ := hU e he
  obtain ⟨U', hU'⟩ := hU' e' he'
  obtain ⟨Φ, hΦ⟩ := (h1.2 t al be ga de hd).1
  obtain ⟨Tm, hi, hq, -⟩ := h2.2 t al be ga de hd Φ hΦ
  obtain ⟨B, hB⟩ := exists_isCoverIt_swap _ _ _ _ _ _ _ _ _ _ Tm hi hq
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_fockPolynomialIso_unitaryPair _ _ _ _ _ _ _ _ e e' he he'
  obtain ⟨v, hv, -⟩ := (hX _ _ _ p1).1
  have c1 := Fintype.card_congr e
  have c2 := Fintype.card_congr e'
  simp only [Fintype.card_sum, Fintype.card_fin] at c1 c2
  exact ⟨⟨by omega, by omega⟩,
    GlobalTheory.T.exists_localFockIntertwiner_realPlace_of_coverContraction D V W S S' M M' τ _ _ _ _ _ _ _ _ e e' m m' aS aT U U' κ B hm hm' hU hU' ⟨v, 0, hv⟩ hκ hB⟩

end GlobalTheory.Chain.RealItLarge

theorem GlobalTheory.Chain.RealItLarge.itLarge : ∀ {D : D7} (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (t : ℕ) (aS aT : D.what₂.Tau → ℚ), GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → IsInfFam θ → (∀ τ, ∃ be de : List ℚ, Formalism.MainNotions.SchurIrreducible.DataARm t [] be [] de ∧ S τ = dualPar (GlobalTheory.Chain.signed de (Formalism.BasicNotions.TH.block t ++ be) (aT τ)) ∧ S' τ = dualPar (GlobalTheory.Chain.signed be de (aS τ))) → ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → (∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ)) → ∀ f, GlobalTheory.Chain.IsVacVec ψ θ M M' f → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It := by
  intro D V W S S' M M' θ ψ t aS aT hD hH hθ hP χS χT ω hω hexp f hf
  obtain ⟨X, hX, h1, h2⟩ := GlobalTheory.Chain.ItPairObj.exists_record hD hH
  have hB := _root_.GlobalTheory.modelsAreCoverSeries_of_hypotheses hD hH D
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, GlobalTheory.Chain.RealIt.LocIt M M' τ (aS τ) (aT τ) A := fun τ => by
    obtain ⟨be, de, hd, e1, e2⟩ := hP τ
    exact GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M M' τ (al := []) (ga := []) hd e1 e2
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.Contr.contraction.2 (_root_.GlobalTheory.Chain.RealIt.GlueProof.glueLaw D _ _) hA
  have hc := fun τ => _root_.GlobalTheory.vacChar_of_record D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (hexp τ).1 (hexp τ).2 hf
  exact ⟨It, GlobalTheory.Chain.RealIt.isItW_of_globIt hθ hI hr (_root_.GlobalTheory.vacuumFock_all_records D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2
    (fun τ => (hc τ).2.1) fun τ => (hc τ).2.2⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRowPartNeBotPositiveDimension
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
noncomputable section

namespace GlobalTheory.RowsPartNe


open GlobalTheory.Mem.RowSides in
theorem jX_injective_of_models {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (hM : R.IsModels) (t : T) :
    Function.Injective (R.jX t) := by
  intro f g hfg
  refine semi_injective_of_basis (A.MtildeCSD t).basis (R.B.R t).pres.extL
    (classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R t).pres).2.1.1 ?_
  exact (hM.jX t f).symm.trans ((congrArg (R.HX t).e hfg).trans (hM.jX t g))

theorem exists_rowPart_ne_bot_positiveDimension : GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → ∃ p, R.EEp3 p ≠ ⊥ := by
  intro hH hP D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hC hEx hIn hGE hPos
  by_contra hne
  push_neg at hne
  have hcar := GlobalTheory.Hk3.carries_of_rows_top hP hH R F (GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hP D) hOk hC hEx hIn hGE hPos
  have hc0 : ∀ c, R.EEc c = ⊥ := by
    intro c
    by_contra h
    obtain ⟨p, hp⟩ := hcar c h
    have hle : R.EEc c ≤ R.EEp3 p := by
      unfold RealDat3.EEp3
      exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) => R.EEc c) c hp le_rfl
    rw [hne p, le_bot_iff] at hle
    exact h hle
  obtain ⟨hCore, hSF, hEq, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx
  obtain ⟨h, -, -, htop, -⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R.toRealDat F.lv2 hCore
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hP R.toRealDat) R.SF hSF
  have hbot : (⊤ : Submodule ℂ R.HE.H) = ⊥ := by
    rw [← htop]
    simp only [← hEq, hc0, iSup_bot]
  have hzero : ∀ x : R.HE.H, x = 0 := fun x => by
    have hx : x ∈ (⊤ : Submodule ℂ R.HE.H) := Submodule.mem_top
    rw [hbot] at hx
    exact (Submodule.mem_bot ℂ).1 hx
  have hM := (RealDat3.characterisation_of_weak hC hEx).models
  have hL : R.toRealDat.LPos F.lv2 := fun b => by
    cases b
    · exact hPos false
    · exact hPos true
  refine (GlobalTheory.QPosCompare.lPos_iff_ne_bot R.toRealDat F.lv2).1 hL false ?_
  have hZ : (R.toRealDat.toCx F.lv2).Z A3.A.μ0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, hy⟩ := hx
    have hy0 : y = 0 := hzero (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y)
    rw [hy0, map_zero] at hy
    have h1 : R.jX A3.A.μ0 x = 0 := hy.symm
    rw [Submodule.mem_bot]
    exact jX_injective_of_models hM A3.A.μ0 (h1.trans (map_zero _).symm)
  rw [hZ]
  exact BlockDat.good_part_coordinates_bot _ _

end GlobalTheory.RowsPartNe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVacX
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin.VacX

variable {D : D7}

theorem transport (ψ ψ' : AddChar (AF D.host.F) ℂ) (θ θ' : InfFam D) (hψ : ψ' = ψ) (hθ : θ' = θ)
    {S S' T T' : HSp D} (hS : S = S') (hT : T = T')
    {cS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {cS' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ}
    (hcS : HEq cS cS')
    {cT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {cT' : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ}
    (hcT : HEq cT cT')
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)}
    (hΛS : HEq ΛS ΛS')
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {ΛT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}
    (hΛT : HEq ΛT ΛT')
    {f : WO (negSp S') T' → ℂ}
    (h : IsVacO ψ' θ' (negSp S') T' (fun τ => -cS' τ) cT' (ΛS' : Set _) (ΛT' : Set _) f) :
    ∃ f' : WO (GlobalTheory.Grid.sgn true S) T → ℂ,
      IsVacO ψ θ (GlobalTheory.Grid.sgn true S) T (fun τ => GlobalTheory.Grid.sgnM true (cS τ)) cT (ΛS : Set _) (ΛT : Set _) f' ∧ HEq f' f := by
  subst hS hT hψ hθ
  obtain rfl := eq_of_heq hcS
  obtain rfl := eq_of_heq hcT
  obtain rfl := eq_of_heq hΛS
  obtain rfl := eq_of_heq hΛT
  exact ⟨f, h, HEq.rfl⟩

end GlobalTheory.GridJoin.VacX


open GlobalTheory.GridJoin.VacX in
theorem GlobalTheory.GridJoin.exists_vacX : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∃ f : WO (G.V (i + 1) j).V (G.V i j).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f ∧ (j = 0 → HEq f (W.vac i)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hag _ i j hi hj
  have hS := hag.vert (i + 1) j (by omega) hj
  have hT := hag.vert i j (by omega) hj
  have key : ∀ f, W.IsVac (.chi i j) f → ∃ f' : WO (G.V (i + 1) j).V (G.V i j).V → ℂ,
      GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f' ∧ HEq f' f := fun f hf =>
    transport R.ψ W.ψ R.θ W.θ hW.ψ hW.θ hS.sp hT.sp hS.cart hT.cart hS.lat hT.lat hf
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · obtain ⟨f, h1, h2⟩ := key (W.vac i) (W.vac_is i hi)
    exact ⟨f, h1, fun _ => h2⟩
  · obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev (p := .chi i j) ⟨hi, hj⟩
    obtain ⟨f', h1, -⟩ := key f hf
    exact ⟨f', h1, fun h => by omega⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteMatrixIotaEqFinitePart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

noncomputable section
namespace GlobalTheory.SeeConjGroup

theorem fmat_iota_eq_finE : ∀ {D : D7} (κ : GA D (Yc D 0)), (GlobalTheory.SeeConjGroup.II D).fmat ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 = (finE (Yc D 0) κ).val := by
  intro D κ
  have e : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D κ) = κ := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ
  have hf := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
  rw [e] at hf
  have hv := congrArg Units.val hf
  exact hv.symm ▸ rfl
end GlobalTheory.SeeConjGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedHermitianLatticeUniqueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedHermitianLattice_unique : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D) (L L' : Submodule (𝓞 D.host.E) Y.V), IsGlued Y X ι z u π L₀ f₀ L → IsGlued Y X ι z u π L₀ f₀ L' → L = L' := by
  first | exact @GlobalTheory.GlueUnique.glued_unique | exact GlobalTheory.GlueUnique.glued_unique | (intros; apply GlobalTheory.GlueUnique.glued_unique <;> assumption)
end

