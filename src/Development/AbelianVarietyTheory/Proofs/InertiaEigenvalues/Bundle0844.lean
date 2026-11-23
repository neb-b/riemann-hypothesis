module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0835
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0734
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0815
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightSpanOfIndep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0009
public import Formalism.LocalToGlobal.Columns.MtAdWt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeTieMoveOfPin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.Move


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem heckeTie_of_same {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (h3 : GlobalTheory.TwistChoice.SameForms Y Y')
    (hsp : HEq D.sp D'.sp) {ρ : Setup X} {ρ' : Setup X'} {i : X.Tw} {i' : X'.Tw} (hi : HEq i i')
    {j : Fin D.R.m} {j' : Fin D'.R.m} (hj : (j : ℕ) = j') {b : Bool}
    (hmu : HEq (ρ.B i j b).mu (ρ'.B i' j' b).mu) (hlev : HEq (ρ.levK i j b) (ρ'.levK i' j' b))
    (r : Rd ρ Y i j b) (r' : Rd ρ' Y' i' j' b)
    (hR : ∀ (f : Y.Fm i ((j : ℕ) + 1) b) (f' : Y'.Fm i' ((j' : ℕ) + 1) b), HEq f f' → HEq (r' f') (r f))
    (ht : HeckeTie r) : HeckeTie r' := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  obtain ⟨yFm, yacgFm, ymodFmK, ymodFmO, yactG, yU, ypsiU, yeAlg, yDat, yth, ylev, ythPsi, yMtV, yacgMt, ymodMtK, ymodMtO, yMtLat, ythP, yhkF⟩ := h3
  cases D; cases D'
  dsimp only at a1 a2 a3 hsp
  subst a1; subst a2; subst a3; subst hsp
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yU ypsiU yeAlg yDat yth ylev ythPsi yMtV yacgMt ymodMtK ymodMtO yMtLat ythP yhkF
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yU; subst ypsiU; subst yeAlg; subst yDat; subst yth; subst ylev; subst ythPsi; subst yMtV; subst yacgMt; subst ymodMtK; subst ymodMtO; subst yMtLat; subst ythP; subst yhkF
  subst hi
  obtain rfl : j = j' := Fin.ext hj
  have e : ∀ x, r' x = r x := fun x => eq_of_heq (hR x x HEq.rfl)
  have hmu' : (ρ'.B i j b).mu = (ρ.B i j b).mu := eq_of_heq hmu.symm
  have hlev' : ρ'.levK i j b = ρ.levK i j b := eq_of_heq hlev.symm
  have hk : ∀ k P R z F, ρ'.hecke i j b k P R z F = ρ.hecke i j b k P R z F := fun k P R z F => by
    funext x
    rw [Setup.hecke_apply, Setup.hecke_apply, hmu']
  have hd : ∀ k P α R z, ρ'.IsHeckeDatum i j b k P α R z ↔ ρ.IsHeckeDatum i j b k P α R z := fun k P α R z =>
    ⟨fun d => ⟨d.1, hlev' ▸ d.2, d.3⟩, fun d => ⟨d.1, hlev'.symm ▸ d.2, d.3⟩⟩
  have ha : ∀ k P f g, HeckeAt r' k P f g ↔ HeckeAt r k P f g := fun k P f g =>
    ⟨fun hg α R z d => by have := hg α R z ((hd k P α R z).2 d); rwa [e, e, hk] at this,
      fun hg α R z d => by rw [e, e, hk]; exact hg α R z ((hd k P α R z).1 d)⟩
  intro k P hkP f hf
  exact (ha k P f _).2 (ht k P hkP f (by obtain ⟨g, hg⟩ := hf; exact ⟨g, (ha k P f g).1 hg⟩))

theorem heckeTie_move_of_pin : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw},
    (∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) (b : Bool),
      HEq (ρ.B i j b).mu (ρ'.B i' (h.cm j) b).mu ∧ HEq (ρ.levK i j b) (ρ'.levK i' (h.cm j) b)) →
    ∀ (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ'), RdRel h rd rd' → ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' →
      ∀ (j : Fin D.R.m) b, HeckeTie (rd i j b) → HeckeTie (rd' i' (h.cm j) b) := by
  intro D D' ι e h ρ ρ' hB rd rd' hr i i' hi j b ht
  have hR : ∀ (f : D.nexp.Fm i ((j : ℕ) + 1) b) (f' : D'.nexp.Fm i' ((h.cm j : ℕ) + 1) b), HEq f f' →
      HEq (rd' i' (h.cm j) b f') (rd i j b f) := fun f f' hf => by
    have h1 : h.fmCast hi ((j : ℕ) + 1) b f = f' := eq_of_heq ((h.fmCast_heq hi _ b f).trans hf)
    rw [← h1]
    exact hr i i' hi j b f
  exact heckeTie_of_same h.gal h.set h.frm h.sp hi (h.cm_val j).symm (hB i i' hi j b).1 (hB i i' hi j b).2
    (rd i j b) (rd' i' (h.cm j) b) hR ht


set_option maxHeartbeats 4000000 in
theorem SameData.mu_levK {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e)
    {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (hs : SameData ρ ρ') (i : D.ntw.Tw) (i' : D'.ntw.Tw) (hi : HEq i i')
    (j : Fin D.R.m) (b : Bool) :
    HEq (ρ.B i j b).mu (ρ'.B i' (h.cm j) b).mu ∧ HEq (ρ.levK i j b) (ρ'.levK i' (h.cm j) b) := by
  have hj : (j : ℕ) = h.cm j := rfl
  generalize h.cm j = j' at hj
  obtain ⟨r, rfl⟩ := h.exists_rest
  cases SameData.eq_up r hs
  cases hi
  cases (Fin.ext hj : j = j')
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem heckeTie_move : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw}, SameData ρ ρ' →
    ∀ (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ'), RdRel h rd rd' → ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' →
      ∀ (j : Fin D.R.m) b, HeckeTie (rd i j b) → HeckeTie (rd' i' (h.cm j) b) :=
  fun h _ _ hs => heckeTie_move_of_pin h (hs.mu_levK h)

end GlobalTheory.TwInputs.Move

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleModuleDetDiagonalUniformiserMul
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.CellDec.DetMod

theorem prod_adl {E : Type} [Field E] [NumberField E] {ι : Type} (s : Finset ι)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m : ι → HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    ∏ i ∈ s, GlobalTheory.CellDec.adl ϖ (m i) = GlobalTheory.CellDec.adl ϖ (∑ i ∈ s, m i) := by
  induction s using Finset.induction_on with
  | empty => simp [GlobalTheory.CellDec.adl_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, GlobalTheory.CellDec.adl_add]

theorem det_finGL' {E : Type} [Field E] [NumberField E] {a : ℕ} (k : GL (Fin a) (Af E)) :
    GeneralLinearGroup.det (finGL E a k) = finId E (GeneralLinearGroup.det k) := by
  let p : Ad E →+* InfiniteAdeleRing E := RingHom.fst (InfiniteAdeleRing E) (Af E)
  refine Units.ext (Prod.ext ?_ ?_)
  · have h := GlobalTheory.CuspRep.det_map p (finGL E a k)
    have h0 : GeneralLinearGroup.map p (finGL E a k) = 1 :=
      map_cornerGL_of_zero (sFin E) p (fun x => rfl) k
    rw [h0, map_one, Units.val_one] at h
    change p _ = _
    rw [← h]
    change (1 : InfiniteAdeleRing E) = (1 : InfiniteAdeleRing E) - 0 + 0
    simp
  · have h := GlobalTheory.CuspRep.det_map (pFin E) (finGL E a k)
    have h0 : GeneralLinearGroup.map (pFin E) (finGL E a k) = GeneralLinearGroup.map (RingHom.id _) k :=
      map_cornerGL_of_hom (sFin E) (pFin E) (RingHom.id _) (fun x => rfl) k
    rw [h0] at h
    change pFin E _ = _
    rw [← h]
    change _ = (1 : Af E) - 1 + (GeneralLinearGroup.det k : (Af E)ˣ)
    rw [sub_self, zero_add]
    rfl

end GlobalTheory.CellDec.DetMod

theorem GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n),
      (ideleModule E (GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l * g)) : ℝ) =
        (∏ v ∈ l.support, ((qV E v : ℝ) ^ (∑ i, l v i))⁻¹) * (ideleModule E (GeneralLinearGroup.det g) : ℝ) := by
  intro E _ _ n ϖ hϖ l g
  rw [map_mul, map_mul, Positive.val_mul]
  congr 1
  have hdet : GeneralLinearGroup.det (GlobalTheory.SmGL.diagT (Af E) (Fin n)
      fun i => GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l)) =
      ∏ i, GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, GlobalTheory.SmGL.val_diagT, Matrix.det_diagonal, Units.coe_prod]
  unfold GlobalTheory.CellDec.tl
  rw [GlobalTheory.CellDec.DetMod.det_finGL', hdet, GlobalTheory.CellDec.DetMod.prod_adl]
  rw [GlobalTheory.AdeleScale.ideleModule_finId_adl ϖ hϖ _ l.support]
  · refine Finset.prod_congr rfl fun v _ => ?_
    congr 2
    rw [Finsupp.finsetSum_apply]
    rfl
  · intro v hv
    rw [Finsupp.notMem_support_iff] at hv
    rw [Finsupp.finsetSum_apply]
    simp [hv]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdelicAbsDetPowDiagonalUniformizerMul
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
namespace GlobalTheory.CellEvalDet

open Matrix

variable {E : Type} [Field E] [NumberField E]

theorem detPow_eq_rpow {n : ℕ} (x : ℝ) (g : GA E n) :
    GlobalTheory.RSJ.detPow E n x g =
      ((GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ) := by
  have hpos := (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g)).2
  rw [Real.rpow_def_of_pos hpos, ← GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule]
  simp only [GlobalTheory.RSJ.detPow, chiDet, GlobalTheory.HeckeGal.Model.absPow, MonoidHom.coe_comp, Function.comp_apply]
  change ‖Complex.exp ((x : ℂ) * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det g) : ℂ))‖ = _
  rw [Complex.norm_exp]
  congr 1
  simp [mul_comm]

theorem det_diagT {R : Type} [CommRing R] {n : ℕ} (t : Fin n → Rˣ) :
    GeneralLinearGroup.det (GlobalTheory.SmGL.diagT R (Fin n) t) = ∏ i, t i := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GlobalTheory.SmGL.val_diagT, det_diagonal, Units.coe_prod]

def posVal : {r : ℝ // 0 < r} →* ℝ where
  toFun r := r
  map_one' := rfl
  map_mul' _ _ := rfl

theorem qV_pos (v : HeightOneSpectrum (𝓞 E)) : (0 : ℝ) < qV E v :=
  lt_of_le_of_ne (Nat.cast_nonneg _) (GlobalTheory.AdeleScale.qV_ne_zero v).symm

end GlobalTheory.CellEvalDet


open GlobalTheory.CellEvalDet Matrix in
theorem GlobalTheory.CellEvalDet.detPow_tl_mul : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (x : ℝ) (g : GA E n),
    GlobalTheory.RSJ.detPow E n x (GlobalTheory.CellDec.tl n ϖ l * g) =
      (∏ w ∈ l.support, (qV E w : ℝ) ^ (-x * ∑ i, (l w i : ℝ))) * GlobalTheory.RSJ.detPow E n x g := by
  intro E _ _ _ n ϖ hϖ l x g
  rw [GlobalTheory.RSJ.Model.detPow_mul, detPow_eq_rpow x (GlobalTheory.CellDec.tl n ϖ l)]
  congr 1
  have hdet : GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l) =
      ∏ i, finId E (GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun y : Fin n → ℤ => y i) rfl l)) := by
    unfold GlobalTheory.CellDec.tl
    rw [det_finGL, det_diagT, map_prod]
  have hmod : ((GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l)) : ℝ)) =
      ∏ i, ∏ v ∈ l.support, ((qV E v : ℝ) ^ (l v i))⁻¹ := by
    rw [hdet, map_prod]
    change posVal (∏ i, _) = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    change ((GroundTheory.Global.IdeleGroup.ideleModule E _ : ℝ)) = _
    rw [GlobalTheory.AdeleScale.ideleModule_finId_adl ϖ hϖ _ l.support (fun v hv => by
      rw [Finsupp.notMem_support_iff] at hv; simp [hv])]
    simp
  rw [hmod, Finset.prod_comm, ← Real.finsetProd_rpow _ _ (fun v _ =>
    Finset.prod_nonneg fun i _ => inv_nonneg.2 (zpow_nonneg (Nat.cast_nonneg _) _)) x]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hq := qV_pos (E := E) v
  have e : ∀ i, ((qV E v : ℝ) ^ (l v i))⁻¹ = (qV E v : ℝ) ^ (-(l v i : ℝ)) := fun i => by
    rw [Real.rpow_neg hq.le, Real.rpow_intCast]
  simp_rw [e]
  rw [← Real.rpow_sum_of_pos hq, ← Real.rpow_mul hq.le]
  congr 1
  rw [Finset.sum_neg_distrib]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgWeightOfContragredientHighestWeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AlgWtDualRead

theorem isAlgWeight_of_hwAtF_dual : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (κ : Type) [Fintype κ] [DecidableEq κ] (b : Module.Basis κ K W) (ρC : Representation ℂ (ReciprocityTheory.Aut.GQ L n) (κ → ℂ)), (∀ γ, LinearMap.toMatrix' (ρC γ) = (LinearMap.toMatrix b b (ρ γ)).map e) → ∀ (τ : L →+* K) (lam : Fin n → ℤ), NX.HWAtF c ρ.dual τ lam → Formalism.AUTREP.IsAlgWeight L n ρC := by
  intro L _ _ _ n K _ e c hc W _ _ _ ρ κ _ _ b ρC hρC τ lam hw
  obtain ⟨ι, _, _, b', P, hP, -⟩ := hw
  classical
  let bd := b.dualBasis
  let A : Matrix κ ι K := bd.toMatrix b'
  let B : Matrix ι κ K := b'.toMatrix bd
  let f : (L →+* K) × Fin n × Fin n → (L →+* K) × Fin n × Fin n := fun p => (p.1.comp c, p.2.2, p.2.1)
  let Q : κ → κ → MvPolynomial ((L →+* K) × Fin n × Fin n) K := fun i j =>
    ∑ l, ∑ k, MvPolynomial.C (A j k) * MvPolynomial.rename f (P k l) * MvPolynomial.C (B l i)
  have key : ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L),
      (((γ : Formalism.AUTREP.GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
      ∀ i j, LinearMap.toMatrix b b (ρ γ) i j =
        MvPolynomial.eval (fun p => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) (Q i j) := by
    intro γ γ₀ hm i j
    have hinv := hP γ⁻¹ γ₀⁻¹ (GlobalTheory.WtDual.match_inv γ γ₀ hm)
    have hγ := GlobalTheory.WtDual.mem_rationalUnitaryGroup_of_matrix_match γ γ₀ hm
    have e1 : LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) = Matrix.transpose (LinearMap.toMatrix b b (ρ γ)) := by
      rw [Representation.dual_apply, inv_inv, LinearMap.toMatrix_transpose]
    have e2 : LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) = A * LinearMap.toMatrix b' b' (ρ.dual γ⁻¹) * B :=
      (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bd b' bd b' _).symm
    have e3 : LinearMap.toMatrix b b (ρ γ) i j = LinearMap.toMatrix bd bd (ρ.dual γ⁻¹) j i := by
      rw [e1]; rfl
    rw [e3, e2]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    simp only [hinv]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Q, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_rename]
    refine Finset.sum_congr rfl fun l _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    refine congrArg (fun g => MvPolynomial.eval g (P k l)) (funext fun p => ?_)
    simp only [Function.comp_apply, f, RingHom.comp_apply]
    rw [GlobalTheory.WtDual.inv_entry γ₀ hγ, hc]
    rfl
  refine ⟨inferInstance, κ, inferInstance, inferInstance, Pi.basisFun ℂ κ,
    fun i j => MvPolynomial.rename (fun p : (L →+* K) × Fin n × Fin n => (e.comp p.1, p.2)) (MvPolynomial.map e (Q i j)), ?_⟩
  intro γ γ₀ hm
  ext i j
  rw [LinearMap.toMatrix_eq_toMatrix', hρC γ, Matrix.map_apply, key γ γ₀ hm i j, MvPolynomial.eval_rename,
    MvPolynomial.eval_map]
  simp only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.hom_eval₂, RingHom.comp_id]
  rfl

end GlobalTheory.AlgWtDualRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceIndicatorDiagonalUniformizerMul
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellLastRow

open GlobalTheory.CellDec GlobalTheory.ZEul

variable {E : Type} [Field E] [NumberField E]

theorem one_lt_v_zpow {v : HeightOneSpectrum (𝓞 E)} {ϖ : v.adicCompletion E} (h : IsUnifV E v ϖ) {a : ℤ}
    (ha : a < 0) : 1 < Valued.v (ϖ ^ a) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -((n + 1 : ℕ) : ℤ) := ⟨(-a - 1).toNat, by omega⟩
  have h0 : ϖ ≠ 0 := fun e => by simp [IsUnifV, e] at h
  have h1 : Valued.v ϖ < 1 := by
    rw [h]; exact (by decide : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1)
  rw [zpow_neg, zpow_natCast, map_inv₀, map_pow]
  have hp : Valued.v ϖ ^ (n + 1) < 1 := pow_lt_one₀ zero_le' h1 (Nat.succ_ne_zero n)
  have hp0 : Valued.v ϖ ^ (n + 1) ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).2 h0)
  exact (one_lt_inv₀ (zero_lt_iff.2 hp0)).2 hp

end GlobalTheory.CellLastRow

namespace GlobalTheory.CellLastRow

open GlobalTheory.CellDec GlobalTheory.ZEul

theorem indN_lastRow_tl : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ N : ℕ,
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) →
    (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) →
    ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) S), ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S,
    ((∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) =
        GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i))) ∧
    ((∃ w, l.1 w (Fin.last m) < 0) →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) = 0) := by
  intro E _ _ _ m S ϖ hϖ N hlat hloc l g hg
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  have hk' : ∀ v ∉ S, compV E (m + 1) v k ∈ GlobalTheory.LFun.KGL v (n := (m + 1)) := by
    simpa only [US, Subgroup.mem_iInf, Subgroup.mem_comap] using hk
  set c : (Af E)ˣ := adl ϖ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x (Fin.last m)) rfl l.1) with hc
  have hev : ∀ (x : Af E) v, x v = pLoc E v x := fun _ _ => rfl
  have hcv : ∀ v, pLoc E v (c : Af E) = ((ϖ v ^ l.1 v (Fin.last m) : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
    intro v
    change ((ϖ v ^ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x (Fin.last m)) rfl l.1) v :
      (v.adicCompletion E)ˣ) : v.adicCompletion E) = _
    rw [Finsupp.mapRange_apply]
  have hrow : ∀ i, lastRow (u * k) i = (k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) i := by
    intro i
    have := congrFun (GlobalTheory.RSLocalPart.single_vecMul_unip (ℓ := Fin.last m) (fun j => Fin.le_last j) hu k) i
    simpa [lastRow, Units.val_mul, Matrix.single_one_vecMul] using this
  have hrow' : ∀ i, GlobalTheory.RSJ.pFin E (lastRow (tl (m + 1) ϖ l.1 * (u * k)) i) =
      (c : Af E) * GlobalTheory.RSJ.pFin E (lastRow (u * k) i) := by
    intro i
    simp only [lastRow, tl_eq_diagT, Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul, map_mul]
    congr 1
    change GlobalTheory.RSJ.pFin E (1 - sFin E 1 + sFin E (c : Af E)) = _
    rw [map_add (f := _), map_sub, map_one]
    change 1 - 1 + (c : Af E) = _
    ring
  have hcomp : ∀ v i, pLoc E v (GlobalTheory.RSJ.pFin E (lastRow (u * k) i)) = (compV E (m + 1) v k).val (Fin.last m) i := by
    intro v i; rw [hrow]; rfl
  have hint : ∀ v ∉ S, ∀ i j, (compV E (m + 1) v k).val i j ∈ v.adicCompletionIntegers E := by
    intro v hv i j
    obtain ⟨k0, hk0⟩ := hk' v hv
    rw [← hk0]
    exact (k0.val i j).2
  have hinv : ∀ v ∉ S, ∀ i j, ((compV E (m + 1) v k)⁻¹).val i j ∈ v.adicCompletionIntegers E := by
    intro v hv i j
    obtain ⟨k0, hk0⟩ := hk' v hv
    rw [← hk0, ← map_inv]
    exact ((k0⁻¹).val i j).2
  have hδ : ∀ v (i : Fin (m + 1)), pLoc E v (if (i : ℕ) + 1 = m + 1 then (1 : Af E) else 0) ∈ v.adicCompletionIntegers E := by
    intro v i
    split_ifs
    · rw [map_one]; exact one_mem _
    · rw [map_zero]; exact zero_mem _
  refine ⟨fun hpos => ?_, fun ⟨w, hw⟩ => ?_⟩
  · have key : ∀ i : Fin (m + 1),
        (GlobalTheory.RSJ.pFin E (lastRow (tl (m + 1) ϖ l.1 * (u * k)) i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈
          GlobalTheory.RSJ.natLat E N ↔
        GlobalTheory.RSJ.pFin E (lastRow (u * k) i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ GlobalTheory.RSJ.natLat E N) := by
      intro i
      refine (hloc _ _ (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)).symm
      · rw [hev, hev, map_sub, map_sub, hrow', map_mul, hcv, l.2 v hv]
        simp
      · rw [hev, map_sub, hcomp]
        exact sub_mem (hint v hv _ _) (hδ v i)
      · rw [hev, map_sub, hrow', map_mul, hcomp, hcv]
        refine sub_mem (mul_mem ?_ (hint v hv _ _)) (hδ v i)
        rw [Units.val_zpow_eq_zpow_val, ← Int.toNat_of_nonneg (hpos v), zpow_natCast]
        exact pow_mem (GlobalTheory.LFun.mem_Ov_of_isUnifV (hϖ v)) _
    unfold GlobalTheory.RSJ.indN
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (fun i => (key i).1 (h1 i)) h2
    · exact absurd (fun i => (key i).2 (h2 i)) h1
    · rfl
  · have hwS : w ∉ S := fun h => by
      have h0 := l.2 w h
      rw [h0] at hw
      exact lt_irrefl _ hw
    have hex : ∃ j, ¬ Valued.v ((compV E (m + 1) w k).val (Fin.last m) j) < 1 := by
      by_contra hcon
      push_neg at hcon
      have h1 : ((compV E (m + 1) w k).val * ((compV E (m + 1) w k)⁻¹).val) (Fin.last m) (Fin.last m) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
      rw [Matrix.mul_apply] at h1
      have h2 : Valued.v (∑ j, (compV E (m + 1) w k).val (Fin.last m) j * ((compV E (m + 1) w k)⁻¹).val j (Fin.last m)) < 1 := by
        refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
        rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (hcon j) (hinv w hwS j (Fin.last m))
      rw [h1, map_one] at h2
      exact lt_irrefl _ h2
    obtain ⟨j, hj⟩ := hex
    have hj1 : Valued.v ((compV E (m + 1) w k).val (Fin.last m) j) = 1 :=
      le_antisymm (hint w hwS _ _) (not_lt.1 hj)
    unfold GlobalTheory.RSJ.indN
    rw [if_neg]
    intro hall
    have hz := hlat _ (hall j) w
    dsimp only at hz
    rw [hev, map_sub, hrow', map_mul, hcomp, hcv] at hz
    have ha := add_mem hz (hδ w j)
    rw [sub_add_cancel, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hj1, mul_one,
      Units.val_zpow_eq_zpow_val] at ha
    exact not_le.2 (one_lt_v_zpow (hϖ w) hw) ha

end GlobalTheory.CellLastRow
end
end

