module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0799
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipMapsHalfTranslatesSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0807
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApplyScalar
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.JSW.Central

def centralFns (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ω : HChar E) :
    Submodule ℂ (GA E a → ℂ) where
  carrier := {F | ∀ (z : Neutral.B1.Ideles E) (g : GA E a),
    F (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * F g}
  add_mem' hF hG z g := by simp [hF z g, hG z g, mul_add]
  zero_mem' _ _ := by simp
  smul_mem' c F hF z g := by simp [hF z g, mul_left_comm]

end GlobalTheory.JSW.Central
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArchTranslatedSqrtWeightedFunGoodMirabolicTop
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.ZUnf

section H

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem secRow_eq_rowMat {R : Type} [CommRing R] (y : Fin (m + 1) → R) :
    secRow y = GlobalTheory.RSTheta.rowMat (Fin.last m) y := by
  ext i j
  simp only [secRow, GlobalTheory.RSTheta.rowMat, Matrix.of_apply, Matrix.updateRow_apply]
  by_cases h : i = Fin.last m
  · subst h; simp
  · rw [if_neg h, if_neg (fun e => h (Fin.ext (by simpa using e)))]


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem secInv_eq_inv_rowGL {y : Fin (m + 1) → Cinf E} (hy : y ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m)) :
    secInv y = (GlobalTheory.RSTheta.rowGL (Fin.last m) y)⁻¹ := by
  have hu := GlobalTheory.RSTheta.isUnit_of_mem_rowSet hy
  have hd : IsUnit (secRow y).det := by rw [secRow_eq_rowMat, GlobalTheory.RSTheta.det_rowMat]; exact hu
  rw [secInv, dite_eq_left hd]
  congr 1
  apply Units.ext
  rw [GlobalTheory.RSTheta.val_rowGL hu, ← secRow_eq_rowMat]
  rfl

theorem continuous_yInf : Continuous (yInf : GA E (m + 1) → Fin (m + 1) → Cinf E) :=
  continuous_pi fun i => GlobalTheory.ShortVecDecay.continuous_pInf.comp
    (Units.continuous_val.matrix_elem (Fin.last m) i)

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_sqrtC {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : Continuous Φ) : Continuous (sqrtC Φ) :=
  Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (Complex.continuous_re.comp hΦ))

theorem lastRow_mul_of_row {h g : GA E (m + 1)}
    (hr : ∀ l, (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l) :
    GlobalTheory.ZEul.lastRow (h * g) = GlobalTheory.ZEul.lastRow g := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, Matrix.mul_apply, hr]
  rw [← Matrix.mul_apply, Matrix.one_mul]

theorem blkU_lastRow {r : ℕ} (hr : r ≤ m) (x : UnipotentBlockColumnIndex (m + 1) r m → Ad E) (l : Fin (m + 1)) :
    ((blkU x : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l := by
  change (1 + posM Subtype.val x : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l = _
  rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_zero, add_zero]
  intro t _
  rw [Matrix.single_apply_of_ne]
  rintro ⟨e1, -⟩
  have h1 : (t.1.1 : ℕ) = m := by rw [e1]; simp
  have h2 := t.2.1
  omega

omit [_root_.NumberField.IsTotallyComplex E] in
theorem ratGL_lastRow {γ : GL (Fin (m + 1)) E} (hγ : IsMir m γ) (l : Fin (m + 1)) :
    ((ratGL E (m + 1) γ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l := by
  change algebraMap E (Ad E) (γ.val (Fin.last m) l) = _
  rw [hγ (Fin.last m) l (Or.inl (by simp))]
  by_cases h : Fin.last m = l
  · simp [Matrix.one_apply, h]
  · simp [Matrix.one_apply, h]

theorem continuous_fT {φ : GA E (m + 1) → ℂ} (hφ : Continuous φ) {Φ : (Fin (m + 1) → Cinf E) → ℂ}
    (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m)) : Continuous (fT φ Φ) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  by_cases hp : yInf g ∈ tsupport Φ
  · have hU : GlobalTheory.RSTheta.rowSet E (Fin.last m) ∈ nhds (yInf g) :=
      (GlobalTheory.RSTheta.isOpen_rowSet (E := E) (Fin.last m)).mem_nhds (hs hp)
    have hc : ContinuousOn (fun u => infGL E (m + 1) (secInv u)) (GlobalTheory.RSTheta.rowSet E (Fin.last m)) := by
      refine (GlobalTheory.RSTheta.continuousOn_inv_rowGL (E := E) (Fin.last m)).congr fun u hu => ?_
      simp only [secInv_eq_inv_rowGL hu, map_inv]
    have h1 : ContinuousAt (fun g : GA E (m + 1) => g * infGL E (m + 1) (secInv (yInf g))) g :=
      continuousAt_id.mul ((hc.continuousAt hU).comp continuous_yInf.continuousAt)
    exact (hφ.continuousAt.comp h1).mul ((continuous_sqrtC hΦ).comp continuous_yInf).continuousAt
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [continuous_yInf.continuousAt.eventually (notMem_tsupport_iff_eventuallyEq.1 hp)] with q hq
    simp [fT, sqrtC, hq]

end H

theorem good_fT : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (φ : GA E (m + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => φ (blkU x * g)) = 0) →
    ∀ Φ : (Fin (m + 1) → Cinf E) → ℂ, Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    ∀ ψ : AddChar (Ad E) ℂ, Good ψ m (GlobalTheory.ZUnf.fT φ Φ) := by
  intro E _ _ _ m φ hφ hl hv Φ hΦ hs ψ
  refine ⟨continuous_fT hφ hΦ hs, ?_, ?_, ?_⟩
  · intro γ hγ g
    rw [fT_of_lastRow (lastRow_mul_of_row (ratGL_lastRow hγ)), mul_assoc, hl, fT]
  · intro k hk y g
    have he : IsEmpty (UnipotentBlockColumnIndex (m + 1) k k) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast (m + 1) k) (0 : UnipotentBlockColumnIndex (m + 1) k k → Ad E) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul]
  · intro r hr hrm g
    have e : (fun x : UnipotentBlockColumnIndex (m + 1) r m → Ad E => fT φ Φ (blkU x * g)) = fun x =>
        sqrtC Φ (yInf g) * φ (blkU x * (g * infGL E (m + 1) (secInv (yInf g)))) := by
      funext x
      rw [fT_of_lastRow (lastRow_mul_of_row (blkU_lastRow hrm x)), mul_comm, mul_assoc]
    rw [e, avg_const_mul, hv r hr hrm, mul_zero]

end GlobalTheory.ZUnf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinMapSplitPlaceUniformiserEqFrobeniusInvStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SeriesTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artinMap_splitPlaceUniformiser_eq_frobenius_inv : ∀ (D : D7) (Ω : Type) [Field Ω] [Algebra D.host.E Ω] (A : Type) [CommGroup A] (a : Recip D Ω), a.Good → ∀ φ : G D.host.E Ω →* A, IsOpen (φ.ker : Set (G D.host.E Ω)) → ∀ (P : Pl D.host.E) (e : AE D), IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → ∀ B : ValuationSubring Ω, IsPlaceOver B P → (∀ τ ∈ Ine (F := D.host.E) B, φ τ = 1) → ∀ σ : G D.host.E Ω, IsFrob (F := D.host.E) B (normV P) σ → a.pull φ x = (φ σ)⁻¹ := by
  first | exact @GlobalTheory.SeriesTie.Recip.pull_locUnif | exact GlobalTheory.SeriesTie.Recip.pull_locUnif | (intros; apply GlobalTheory.SeriesTie.Recip.pull_locUnif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipMapsHalfTranslatesSpanStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralFlip_maps_halfTranslates_span : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D) (z : GA D V) (s : ℂ) (Y : Finset (WO V W)), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → s ≠ 0 → (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → om (z⁻¹, 1) f₀ = s • ∑ y ∈ Y, heisO ψ V W y f₀ → ∀ (M u : ℕ) (e e' : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (O : Subring ℂ), M = m * u → (∀ PP ∈ T, ((u : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e P → T ⊆ P → e' = e - eT + cA D eT → zeta M ∈ O → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, ∃ F ∈ trSp ψ V W ΛV ΛW f₀ e' M O, om (z, 1) (s • F) = f := by
  first | exact @GlobalTheory.FlipTranslates.flip_translates | exact GlobalTheory.FlipTranslates.flip_translates | (intros; apply GlobalTheory.FlipTranslates.flip_translates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipSplitPlacesInvariantFormPhase
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

theorem cflip_flipElt_add {a b : AE D} (m : ℕ) (h1 : a * b = 0) (h2 : a * cA D b = 0) (h3 : cA D a * b = 0)
    (h4 : cA D a * cA D b = 0) : flipElt (a + b) m = flipElt a m * flipElt b m := by
  unfold flipElt
  rw [map_add (f := _)]
  linear_combination (-((m : AE D) - 1) ^ 2) * h1 - ((m : AE D) - 1) * (incA D ((m : D.host.E)⁻¹) - 1) * h2
    - ((m : AE D) - 1) * (incA D ((m : D.host.E)⁻¹) - 1) * h3 - (incA D ((m : D.host.E)⁻¹) - 1) ^ 2 * h4

theorem cflip_sum_idem {S : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ PP ∈ S, Formalism.L2.NTheta.IsIdemAt (es PP) PP) : (∑ PP ∈ S, es PP) * (∑ PP ∈ S, es PP) = ∑ PP ∈ S, es PP := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun PP hPP => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem PP hPP]
  · exact (hes PP hPP).1.1
  · intro Q hQ hne
    exact GlobalTheory.Tow.idemAt_orth (hes PP hPP) (hes Q hQ) (Ne.symm hne)

theorem cflip_mul_cA_eq_zero {e u v : AE D} (he : e * cA D e = 0) (hu : e * u = u) (hv : e * v = v) : u * cA D v = 0 := by
  rw [← hu, ← hv, map_mul]
  linear_combination (u * cA D v) * he

theorem cflip_isHalf_mono {m n : ℕ} {e u : AE D} (hu : e * u = u) {y : Mx D m n} (hy : Formalism.IndefR.Datum.IsHalf (cA D u) y) :
    Formalism.IndefR.Datum.IsHalf (cA D e) y := by
  intro i j
  rw [← hy i j, ← mul_assoc, ← map_mul, hu]

theorem cflip_det_split {R : Type*} [CommRing R] {a b t x : R} (hab : a * b = 0)
    (hx : x * ((a + b) * t + (1 - (a + b))) = 1) : x * ((a * t + (1 - a)) * (b * t + (1 - b))) = 1 := by
  linear_combination hx + (x * (t - 1) ^ 2) * hab

theorem cflip_smul_one_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c d : R)
    (X : Matrix n n R) : ((c * d) • (1 : Matrix n n R)) * X = c • ((d • (1 : Matrix n n R)) * X) := by
  rw [mul_smul, Matrix.smul_mul]

theorem cflip_unit_split {R : Type*} [CommRing R] {x u v : R} (h : x * (u * v) = 1) : x = x * v * (x * u) := by
  linear_combination (-x) * h

set_option maxHeartbeats 1000000 in
theorem centralFlip_phase : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (m : ℕ) (z : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), IsIdemSum eT T → m ≠ 0 → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V eT m x → (∀ y : WO V W, IsHalf (cA D eT) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (z⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  intro D ψ V W χV χW om hW T
  induction T using Finset.induction_on with
  | empty =>
    intro eT m z x ℓ hS hm hz hx hℓ
    obtain ⟨⟨es, -, he⟩, -⟩ := hS
    rw [Finset.sum_empty] at he
    subst he
    have h1 : flipElt (0 : AE D) m = 1 := by unfold flipElt; simp
    have hz1 : z = 1 := GlobalTheory.IdemSupport.mt_inj V (by rw [hz, h1, one_smul, GlobalTheory.IdemSupport.mt_one])
    have hx1 : x = 1 := by simpa [IsFlipDet] using hx
    subst hz1 hx1
    refine ⟨1, one_pos, fun f hf => ?_⟩
    simp only [inv_one, Circle.coe_one, map_one, inv_one, Complex.ofReal_one, one_mul]
    show ℓ ((om 1) f) = ℓ f
    rw [map_one]
    rfl
  | @insert P T' hP ih =>
    intro eT m z x ℓ hS hm hz hx hℓ
    obtain ⟨⟨es, hes, heT⟩, hT⟩ := hS
    have hesP := hes P (Finset.mem_insert_self P T')
    have hes' : ∀ Q ∈ T', Formalism.L2.NTheta.IsIdemAt (es Q) Q := fun Q hQ => hes Q (Finset.mem_insert_of_mem hQ)
    have heT' : eT = es P + ∑ Q ∈ T', es Q := by rw [heT, Finset.sum_insert hP]
    have hab : es P * ∑ Q ∈ T', es Q = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun Q hQ => GlobalTheory.Tow.idemAt_orth hesP (hes' Q hQ) (fun h => hP (h ▸ hQ))
    have hbb := cflip_sum_idem hes'
    have heA : eT * es P = es P := by
      rw [heT', add_mul, hesP.1.1, mul_comm, hab, add_zero]
    have heB : eT * ∑ Q ∈ T', es Q = ∑ Q ∈ T', es Q := by
      rw [heT', add_mul, hab, hbb, zero_add]
    have hSa : IsIdemSum (es P) {P} :=
      ⟨⟨es, by simpa using hesP, by simp⟩, cflip_mul_cA_eq_zero hT heA heA⟩
    have hSb : IsIdemSum (∑ Q ∈ T', es Q) T' := ⟨⟨es, hes', rfl⟩, cflip_mul_cA_eq_zero hT heB heB⟩
    have hflip : flipElt eT m = flipElt (es P) m * flipElt (∑ Q ∈ T', es Q) m := by
      rw [heT']
      refine cflip_flipElt_add m hab (cflip_mul_cA_eq_zero hT heA heB) ?_ (by rw [← map_mul, hab, map_zero])
      rw [mul_comm]
      exact cflip_mul_cA_eq_zero hT heB heA
    obtain ⟨zP, -, -, hzP⟩ := _root_.GlobalTheory.LevelSeries.flip_central_exists D V {P} m (es P) hSa hm

    have h1 : Formalism.L2.Theta.mt V zP * Formalism.L2.Theta.mt V zP⁻¹ = 1 := by
      rw [← GlobalTheory.IdemSupport.mt_mul, mul_inv_cancel, GlobalTheory.IdemSupport.mt_one]
    have hz' : Formalism.L2.Theta.mt V (z * zP⁻¹) =
        flipElt (∑ Q ∈ T', es Q) m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
      rw [hzP] at h1
      calc Formalism.L2.Theta.mt V (z * zP⁻¹)
          = (flipElt (∑ Q ∈ T', es Q) m * flipElt (es P) m) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) *
              Formalism.L2.Theta.mt V zP⁻¹ := by
            rw [GlobalTheory.IdemSupport.mt_mul, hz, hflip, mul_comm (flipElt (es P) m)]
        _ = flipElt (∑ Q ∈ T', es Q) m • (flipElt (es P) m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) *
              Formalism.L2.Theta.mt V zP⁻¹) := cflip_smul_one_mul _ _ _
        _ = _ := by rw [h1]

    have hx0 : (x : AE D) * ((es P * (m : AE D) ^ V.rank + (1 - es P)) * ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + (1 - ∑ Q ∈ T', es Q))) = 1 := by
      rw [heT'] at hx
      exact cflip_det_split hab hx
    have hxa : (x : AE D) * ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + (1 - ∑ Q ∈ T', es Q)) * (es P * (m : AE D) ^ V.rank + (1 - es P)) = 1 := by
      rw [mul_assoc, mul_comm ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + _)]; exact hx0
    have hxb : (x : AE D) * (es P * (m : AE D) ^ V.rank + (1 - es P)) * ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + (1 - ∑ Q ∈ T', es Q)) = 1 := by
      rw [mul_assoc]; exact hx0
    let xa : (AE D)ˣ := ⟨_, _, hxa, by rw [mul_comm]; exact hxa⟩
    let xb : (AE D)ˣ := ⟨_, _, hxb, by rw [mul_comm]; exact hxb⟩
    have hxx : x = xa * xb := by
      apply Units.ext
      simp only [xa, xb, Units.val_mul]
      exact cflip_unit_split hx0
    have hxaD : IsFlipDet V (es P) m xa := hxa
    have hxbD : IsFlipDet V (∑ Q ∈ T', es Q) m xb := hxb
    obtain ⟨rP, hrP, hPstep⟩ := _root_.GlobalTheory.LevelSeries.FlipScalStep.om_inv_flip_eq D ψ V W χV χW om hW P (es P) m zP xa ℓ hesP hm hzP hxaD
      (fun y hy φ hφ => hℓ y (cflip_isHalf_mono heA hy) φ hφ)
    obtain ⟨r', hr', hrest⟩ := ih (∑ Q ∈ T', es Q) m (z * zP⁻¹) xb ℓ hSb hm hz' hxbD
      (fun y hy φ hφ => hℓ y (cflip_isHalf_mono heB hy) φ hφ)
    refine ⟨rP * r', mul_pos hrP hr', fun f hf => ?_⟩
    have hsplit : ((z⁻¹ : GA D V), (1 : GA D W)) = (zP⁻¹, 1) * ((z * zP⁻¹)⁻¹, 1) := by
      ext <;> simp
    rw [hsplit, map_mul, Module.End.mul_apply, hPstep _ (hW.om_pres _ _ hf), hrest f hf, hxx, map_mul]
    push_cast
    ring

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidSpanContinuousAutomorphicCuspidal
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.JSW.SpanProps

theorem avg_eq_zero {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {F : GA E a → ℂ}
    (hcont : Continuous F) (hleft : ∀ γ g, F (ratGL E a γ * g) = F g) (hc : IsCuspidal F)
    (r : ℕ) (hr : 0 < r) (hra : r ≤ a - 1) (g : GA E a) :
    avg (ratV E (UnipotentBlockColumnIndex a r (a - 1))) (fun x => F (blkU x * g)) = 0 := by
  have hra' : r < a := by omega
  have hper := per_blk (E := E) (r := r) (m := a - 1) hcont (fun c g => hleft _ g) g
  have hper2 : Per (ratN E a r) (fun x => F (blkU (blkIxHomeo r x) * g)) :=
    ⟨hper.1.comp (blkIxHomeo r).continuous, fun γ hγ x => by
      simp only [map_add (f := _)]
      exact hper.2 _ ((blkIxHomeo_mem r γ).2 hγ) _⟩
  have key := _root_.GlobalTheory.CuspGeneric.avg_equiv _ _ (ratN E a r) (ratV E _) (isCoLat_ratV E (BlockIx a r))
    (isCoLat_ratV E _) (blkIxHomeo r) (blkIxHomeo_mem r) _ hper
  rw [← key]
  have hfun : (fun x => F (blkU (blkIxHomeo r x) * g)) = fun x => F (unip x * g) :=
    funext fun x => by rw [← blkU_comp_equiv]; rfl
  rw [hfun] at hper2 ⊢
  letI : MeasurableSpace (BlockIx a r → Ad E) := borel _
  haveI : BorelSpace (BlockIx a r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := _root_.GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one _ (ratN E a r) (isCoLat_ratV E (BlockIx a r))
  obtain ⟨-, -, -, hint⟩ := _root_.GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg _ _ (isCoLat_ratV E (BlockIx a r)) μ 𝓕 hμ hF _ hper2
  have hc' := hc r hr hra' μ 𝓕 hμ hF g
  rw [hint, h1] at hc'
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hc'
  exact hc'

end GlobalTheory.JSW.SpanProps

theorem GlobalTheory.JSW.mspanR_cont_left_avg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π : CuspSub E (m + 1))
    (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → ∀ φ ∈ GlobalTheory.JSW.mspanR π, Continuous φ ∧
    (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) ∧
    ∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => φ (blkU x * g)) = 0 := by
  intro E _ _ _ m π ω hω hc F hF
  have hπ : π.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hc⟩
  obtain ⟨ψ, rfl, h⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hπ F hF
  have h0 := (h []).2
  rw [GlobalTheory.JSW.word_nil] at h0
  refine ⟨h0.cont, h0.left, fun r hr hrm g => ?_⟩
  exact GlobalTheory.JSW.SpanProps.avg_eq_zero (a := m + 1) h0.cont h0.left h0.cusp r hr hrm g
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentMapNonzeroOfSmallFieldFormStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.NX
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_map_nonzero_of_small_field_form : ∀ (D : D7) (S : RatDat D.ntw) (j : ℕ), (S.A j).IsKsForm → ∀ (i : D.ntw.Tw) (b : Bool) (x : S.WL j), x ≠ 0 →
    ∃ Φ : S.WL j →+ Fm S i j b, Φ x ≠ 0 ∧
      (∀ (c : ↥D.LL0) (w : S.WL j), Φ (((c : ↥D.LL0) : D.what₂.LL) • w) = readLL0 S i b c • Φ w) ∧
      ∀ (T : Module.End D.what₂.LL (S.WL j)) (hT : ∀ w ∈ (S.A j).WK, T w ∈ (S.A j).WK) (w : S.WL j),
        Φ (T w) = Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j)
          ((T.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hT) (Φ w) := by
  first | exact @GlobalTheory.exists_desc_of_isKsForm | exact GlobalTheory.exists_desc_of_isKsForm | (intros; apply GlobalTheory.exists_desc_of_isKsForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardFrameKeepsMatrices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.MtRead.IdFrameStd

variable {D : D7}


open GlobalTheory.StdFrameExist in
theorem exists_idFrame_of (hF : D.host.F = maximalRealSubfield D.host.E) (V : HSp D) (hg : V.gram = 1)
    (hV : Seed.FrmC.StdLat V) (n : ℕ) (hn : V.rank = n) :
    ∃ P : principalLevelFrame.RowPsi V n, IdFrame hF P ∧ GlobalTheory.Mem.R3.StdFrame hF P := by
  subst hn
  have hO : IsOrthF V (1 : GL (Fin V.rank) (Lev.EAf D)) := by
    show Formalism.UG.cT (sgA D) (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) * gA V * 1 = 1
    have : gA V = 1 := by
      show V.gram.map _ = 1
      rw [hg]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [this, Formalism.UG.cT_one, Matrix.mul_one, Matrix.mul_one]
  have hI : IntM (SI D) ((1 : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) := fun i j => by
    rw [Units.val_one, Matrix.one_apply]
    split_ifs
    · exact (SI D).one_mem
    · exact (SI D).zero_mem
  refine ⟨rowPsi V 1 hO, ⟨rfl, fun κ a b => ?_⟩, stdFrame_rowPsi hF hV hO hI (by rw [inv_one]; exact hI)⟩
  rw [← GlobalTheory.HeckeTrans.finE_unswap]
  show (Formalism.IndefR.Lev.finE V (psiF V 1 hO κ)).1.map _ a b = _
  rw [finE_psiF, inv_one, mul_one, one_mul]
  rfl

theorem exists_idFrame : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (j : Fin D.R.m), FWT.VStd D j →
    ∃ P : principalLevelFrame.RowPsi (Vc D j) D.R.nV, IdFrame hF P ∧ GlobalTheory.Mem.R3.StdFrame hF P := by
  intro D hF j hV
  have hL := (GlobalTheory.Equiv.StdSpace.lattice_clause_iff (Vc D j)).1 hV.2
  have hS : Seed.FrmC.StdLat (Vc D j) := fun x => by
    rw [hL]
    exact forall_congr' fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).symm
  exact exists_idFrame_of hF (Vc D j) hV.1 hS D.R.nV (GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne.rank_Vc j).1

end GlobalTheory.MtRead.IdFrameStd

end
end

