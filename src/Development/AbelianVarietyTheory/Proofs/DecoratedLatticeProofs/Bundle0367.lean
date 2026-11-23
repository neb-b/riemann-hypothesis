module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0327
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.SeeSawFourier
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0340
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelBoxProductOrthogonalSumTarget
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitComponentIntegerResidueZeroIffMemPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal

theorem residue_pr_int_eq_zero_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P → ∀ c : 𝓞 D.host.E,
    ∃ h : p.pr (incA D (algebraMap (𝓞 D.host.E) D.host.E c)) ∈ 𝒪[k], (residue 𝒪[k] ⟨_, h⟩ = 0 ↔ c ∈ P.asIdeal) := by
  intro D k _ _ _ _ p P hP c
  have h : p.pr (incA D (c : D.host.E)) ∈ 𝒪[k] := GlobalTheory.LocMod.FullLatFrame.pr_int_mem p c
  refine ⟨h, ?_⟩
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  by_cases hc : c = 0
  · subst hc
    have h0 : (⟨_, h⟩ : 𝒪[k]) = 0 := by
      apply Subtype.ext
      simp
    refine ⟨fun _ => zero_mem _, fun _ hu => ?_⟩
    exact not_isUnit_zero (h0 ▸ hu)
  have hc' : (c : D.host.E) ≠ 0 := fun h0 => hc (Subtype.ext h0)
  have hinv : p.pr (incA D (c : D.host.E)) * p.pr (incA D (c : D.host.E)⁻¹) = 1 := by
    rw [← RingHom.map_mul, ← map_mul (incA D), mul_inv_cancel₀ hc', map_one, map_one]
  rw [hP.2 c hc, ← p.sec_pr, ← p.int_iff]
  apply not_congr
  constructor
  · intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have hy' : p.pr (incA D (c : D.host.E)) * (y : k) = 1 := congrArg Subtype.val hy
    have hne : p.pr (incA D (c : D.host.E)) ≠ 0 := left_ne_zero_of_mul_eq_one hinv
    have : p.pr (incA D (c : D.host.E)⁻¹) = y := mul_left_cancel₀ hne (hinv.trans hy'.symm)
    rw [this]; exact y.2
  · intro hi
    exact IsUnit.of_mul_eq_one (⟨_, hi⟩ : 𝒪[k]) (Subtype.ext hinv)

end GlobalTheory.PhiOneVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

namespace GlobalTheory.StabOff

set_option synthInstance.maxHeartbeats 200000

theorem prV_comm_tmul {D : D7} (v : Pl D) (a : Af ↥D.host.F) (e : D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) (a ⊗ₜ e)) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (a ⊗ₜ e)) := by
  rw [Algebra.TensorProduct.comm_tmul]
  simp only [Formalism.UG.prV, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
  rfl

theorem prV_comm {D : D7} (v : Pl D) (z : Af ↥D.host.F ⊗[↥D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) z) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e => exact prV_comm_tmul v a e
  | add a b ha hb =>
    simp only [map_add (f := _)]
    exact congrArg₂ (· + ·) ha hb

theorem prV_toEAf_eq_zero {D : D7} (v : Pl D) (y : AE D) (h : FinPl.compAt D v y = 0) :
    Formalism.UG.prV (E := D.host.E) v (toEAf D y) = 0 := by
  unfold FinPl.compAt at h
  unfold toEAf
  simp only [RingHom.comp_apply] at h ⊢
  generalize finPart D y = z at h ⊢
  refine (prV_comm v z).trans ?_
  rw [h, map_zero]

theorem compAt_mt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k) (v : Pl D)
    (hv : v ≠ p.v) (i j : Fin S.rank) :
    FinPl.compAt D v (Formalism.L2.Theta.mt S (β.gl g) i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) = 0 := by
  have hmem : β.gl g ∈ grpAt S (· = p.v) := ((_root_.GlobalTheory.FrameAt.frame_facts D k p S n β).1 _).2 ⟨g, rfl⟩
  unfold grpAt congGrp at hmem
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hmem
  have h1 := congrArg (fun u => u.1 i j) hmem
  simp only [GeneralLinearGroup.map_apply, Units.val_one] at h1
  have h2 : Ideal.Quotient.mk (idAt D (· = p.v)) (Formalism.L2.Theta.mt S (β.gl g) i j) =
      Ideal.Quotient.mk (idAt D (· = p.v)) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) := by
    refine h1.trans ?_
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Ideal.Quotient.eq] at h2
  unfold idAt at h2
  rw [Ideal.mem_inf] at h2
  have h3 := h2.2
  rw [Submodule.mem_iInf] at h3
  exact (RingHom.mem_ker).1 (h3 ⟨v, hv⟩)

theorem bc_prV_finM_eq_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k) (m : ℕ) (hm : S.rank = m) (x : GL (Fin m) (EF D)), x.1 = finM S hm (β.gl g) → ∀ v : Pl D, v ≠ p.v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  intro D k _ _ _ _ p S n _ _ β g m hm x hx v hv
  apply Units.ext
  ext i j
  change Formalism.UG.prV (E := D.host.E) v (x.1 i j) = (1 : Matrix (Fin m) (Fin m) _) i j
  rw [hx]
  simp only [GlobalTheory.AdForm.finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have h := prV_toEAf_eq_zero v _ (compAt_mt β g v hv ((finCongr hm).symm i) ((finCongr hm).symm j))
  rw [map_sub, map_sub, sub_eq_zero] at h
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply]
  · have hij' : (finCongr hm).symm i ≠ (finCongr hm).symm j := fun e => hij ((finCongr hm).symm.injective e)
    simp [Matrix.one_apply, hij, hij']

end GlobalTheory.StabOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitModelToPlaceModel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.LocFlat.CFac
open GlobalTheory.FinPl (SplitPt)
open GlobalTheory.IndefiniteRowSideFullHecke.SeeSawLineFourier (atW beta nrm OppLines IsLineFrame ofCol ofRow LineFourier SeeSawFourier)
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastCompare

theorem map_mem_integer {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (φ : k →* k') (hφ : Continuous φ)
    {a : k} (ha : a ∈ 𝒪[k]) : φ a ∈ 𝒪[k'] := by
  by_contra h
  rw [Valuation.mem_integer_iff, not_le] at h
  have hK : IsCompact (φ '' (𝒪[k] : Set k)) := (isCompact_iff_compactSpace.2 (inferInstance : CompactSpace 𝒪[k])).image hφ
  haveI : MulArchimedean (ValueGroupWithZero k') := ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  have h0 : valuation k' (φ a) ≠ 0 := (zero_lt_one.trans h).ne'
  have hU : ∀ n : ℕ, IsOpen {y : k' | valuation k' y < valuation k' (φ a) ^ n} := fun n => by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    refine Filter.mem_of_superset ((IsValuativeTopology.hasBasis_nhds y).mem_of_mem (i := Units.mk0 _ (pow_ne_zero n h0)) trivial) ?_
    intro z hz
    have := (valuation k').map_add_lt hz hy
    simpa using this
  obtain ⟨n, hn⟩ := hK.elim_directed_cover _ hU (fun y _ => by
      obtain ⟨n, hn⟩ := MulArchimedean.arch (valuation k' y) h
      exact Set.mem_iUnion.2 ⟨n + 1, hn.trans_lt (pow_lt_pow_right₀ h n.lt_succ_self)⟩)
    (directed_of_isDirected_le fun m n hmn y hy => lt_of_lt_of_le hy (pow_le_pow_right₀ h.le hmn))
  have := hn ⟨a ^ n, pow_mem ha n, rfl⟩
  simp at this

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {Y Y' n n' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n']

variable {q : SplitPt D k} {S T : HSp D} {s : k} {σ : Y' ≃ n'} {σ' : Y ≃ n} {FS : Frame k S.rank Y'} {FT : Frame k T.rank Y}
  {α : GlobalTheory.FinPl.Frame q S n'} {β : GlobalTheory.FinPl.Frame q T n}

section Lines

variable {L L'' : HSp D} {ζ₁ : Fin L.rank → D.host.E} {ζ : Fin L''.rank → D.host.E}

end Lines

end GlobalTheory.LastCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCombinationExtendByZeroOrthSumLine
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem ext_zero : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∀ (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛA : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT → α.IsLat LA ΛA → α₀.IsLat LS (lastKer ΛA) → β.IsLat LT ΛT → (∀ (Ψ : Matrix n n' k → ℂ) (c : WO A T →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ A T LA LT (· = p.v) f₀ → Over ψ α β LA LT f₀ Ψ (comb ψ A T c f₀)) → ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → Over ψ α₀ β LS LT f₀ (tensCol Ψ (vecInd ΛT)) (comb ψ S T (extS o T c) f₀)) ∧ ∀ (Ψ : Matrix n' n k → ℂ) (c : WO T A →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ T A LT LA (· = p.v) f₀ → Over ψ β α LT LA f₀ Ψ (comb ψ T A c f₀)) → ∀ f₀, Vac ψ T S LT LS (· = p.v) f₀ → Over ψ β α₀ LT LS f₀ (tensRow Ψ (dualInd ΛT)) (comb ψ T S (extT o T c) f₀) := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ hU S A L T o ζ hζ α α₀ β hsum LA LS LT ΛA ΛT hA hS hT hαA hα₀ hβ
  have : ΛT.IsFullLattice k := GlobalTheory.FinPl.isLattice_of_isLat_selfDual β LT hT ΛT hβ
  have sdA := _root_.GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ A T LA LT hA hT (· = p.v)
  have sdS := _root_.GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT (· = p.v)
  have sdA' := _root_.GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ T A LT LA hT hA (· = p.v)
  have sdS' := _root_.GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ T S LT LS hT hS (· = p.v)
  have facS : halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) =
      o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (colFun β ζ (vecInd ΛT)) := by
    rw [← _root_.GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd D k p n (n' ⊕ Fin 1) S T α₀ β LS LT hS hT hU _ _ hα₀ hβ,
      ← _root_.GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd D k p n n' A T α β LA LT hA hT hU _ _ hαA hβ, latInd_lastKer,
      _root_.GlobalTheory.FinPl.ExtZero.extFun_tensCol_sum D k p n n' S A L T o ζ α α₀ β hsum]
  have facT : halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) =
      o.boxT T (halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v))) (rowFun β ζ (dualInd ΛT)) := by
    rw [← _root_.GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd D k p (n' ⊕ Fin 1) n T S β α₀ LT LS hT hS hU _ _ hβ hα₀,
      ← _root_.GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd D k p n' n T A β α LT LA hT hA hU _ _ hβ hαA, latInd_lastKer_row,
      GlobalTheory.T.extendByZero_target_tensor_row_product D k p n n' S A L T o ζ hζ α α₀ β hsum]
  have latS := _root_.GlobalTheory.FinPl.ExtZero.extZero_mem_latO D k p n ψ S A L T o ζ β LA LS LT ΛT sdA sdS facS
  have latT := _root_.GlobalTheory.FinPl.ExtZero.extZero_mem_latO_target D k p n ψ S A L T o ζ β LA LS LT ΛT sdA' sdS' facT
  have vacS : ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → ∀ y,
      Vac ψ A T LA LT (· = p.v) (fun w => f₀ ((o.resS T).symm (w, y))) := by
    intro f₀ hf y
    refine ⟨_root_.GlobalTheory.MixModel.OrthDec.isThetaFunO_slice D ψ S A L T o f₀ y hf.1, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
    · funext w
      rw [← heisO_resS_symm ψ o (2 • u) f₀ w y]
      have h2 : (o.resS T).symm (2 • u, 0) = 2 • (o.resS T).symm (u, 0) := by
        rw [← map_nsmul]; simp
      rw [h2, hf.2.1 _ (latS u hu)]
    · funext w
      rw [← heisO_resS_symm ψ o u f₀ w y, hf.2.2 e' he' _ (latS u hu) (half_resS_symm o hh)]
  have vacT : ∀ f₀, Vac ψ T S LT LS (· = p.v) f₀ → ∀ y,
      Vac ψ T A LT LA (· = p.v) (fun w => f₀ ((o.resT T).symm (w, y))) := by
    intro f₀ hf y
    refine ⟨_root_.GlobalTheory.FinPl.ExtZero.isThetaFunO_sliceT D ψ S A L T o f₀ y hf.1, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
    · funext w
      rw [← heisO_resT_symm ψ o (2 • u) f₀ w y]
      have h2 : (o.resT T).symm (2 • u, 0) = 2 • (o.resT T).symm (u, 0) := by
        rw [← map_nsmul]; simp
      rw [h2, hf.2.1 _ (latT u hu)]
    · funext w
      rw [← heisO_resT_symm ψ o u f₀ w y, hf.2.2 e' he' _ (latT u hu) (half_resT_symm o hh)]
  refine ⟨fun Ψ c _ hyp f₀ hf₀ => ?_, fun Ψ c _ hyp f₀ hf₀ => ?_⟩
  · have hΨ : Ψ ∈ SB (Matrix n n' k) := (hyp _ (vacS f₀ hf₀ 0)).2.2.2.1
    have hΨ' : tensCol Ψ (vecInd ΛT) ∈ SB (Matrix n (n' ⊕ Fin 1) k) :=
      GlobalTheory.FinPl.Comm.tensCol_mem hΨ (GlobalTheory.FinPl.Comm.vecInd_mem ΛT)
    obtain ⟨f, hf, -⟩ := (_root_.GlobalTheory.FinPl.overBasic D k p n (n' ⊕ Fin 1) ψ hψ S T α₀ β LS LT hS hT f₀ hf₀).1 _ hΨ'
    refine ⟨hS, hT, hf₀, hΨ', hf.2.2.2.2.1, fun T' hT' => ?_⟩
    funext t
    obtain ⟨⟨w, y⟩, rfl⟩ : ∃ q, (o.resS T).symm q = t := ⟨_, (o.resS T).symm_apply_apply t⟩
    have hmod := _root_.GlobalTheory.FinPl.ExtZero.restrModel_isPlaceModel D ψ (symplO S T) (heisO ψ S T) (symplO A T) (heisO ψ A T) (o.resS T) p.e _ _
      (colFun β ζ (vecInd ΛT)) f₀ T' hT' (fun a F w y => heisO_resS_symm ψ o a F w y)
      (fun t a => symplO_resS_symm o t a) (fun a ha => half_resS_symm o ha) (fun a ha => half_resS_symm o ha)
      (_root_.GlobalTheory.FinPl.ExtZero.SBBox.isSBHalf_boxS D k p n S A L T o ζ β LA LS LT ΛT facS) facS y
    have key := congrFun ((hyp _ (vacS f₀ hf₀ y)).2.2.2.2.2 _ hmod) w
    rw [_root_.GlobalTheory.FinPl.ExtZero.comb_extS_slice] at key
    rw [key, restrModel_apply, _root_.GlobalTheory.FinPl.ExtZero.extFun_tensCol_sum D k p n n' S A L T o ζ α α₀ β hsum]
    rfl
  · have hΨ : Ψ ∈ SB (Matrix n' n k) := (hyp _ (vacT f₀ hf₀ 0)).2.2.2.1
    have hΨ' : tensRow Ψ (dualInd ΛT) ∈ SB (Matrix (n' ⊕ Fin 1) n k) :=
      GlobalTheory.FinPl.Comm.tensRow_mem hΨ (GlobalTheory.FinPl.Comm.dualInd_mem ΛT)
    obtain ⟨f, hf, -⟩ := (_root_.GlobalTheory.FinPl.overBasic D k p (n' ⊕ Fin 1) n ψ hψ T S β α₀ LT LS hT hS f₀ hf₀).1 _ hΨ'
    refine ⟨hT, hS, hf₀, hΨ', hf.2.2.2.2.1, fun T' hT' => ?_⟩
    funext t
    obtain ⟨⟨w, y⟩, rfl⟩ : ∃ q, (o.resT T).symm q = t := ⟨_, (o.resT T).symm_apply_apply t⟩
    have hmod := _root_.GlobalTheory.FinPl.ExtZero.restrModel_isPlaceModel D ψ (symplO T S) (heisO ψ T S) (symplO T A) (heisO ψ T A) (o.resT T) p.e _ _
      (rowFun β ζ (dualInd ΛT)) f₀ T' hT' (fun a F w y => heisO_resT_symm ψ o a F w y)
      (fun t a => symplO_resT_symm o t a) (fun a ha => half_resT_symm o ha) (fun a ha => half_resT_symm o ha)
      (_root_.GlobalTheory.FinPl.ExtZero.isSBHalf_boxT_rowFun_dualInd D k p n S A L T o ζ β LA LS LT ΛT facT) facT y
    have key := congrFun ((hyp _ (vacT f₀ hf₀ y)).2.2.2.2.2 _ hmod) w
    rw [_root_.GlobalTheory.FinPl.ExtZero.comb_extT_resT_symm] at key
    rw [key, restrModel_apply, GlobalTheory.T.extendByZero_target_tensor_row_product D k p n n' S A L T o ζ hζ α α₀ β hsum]
    rfl

end GlobalTheory.FinPl.ExtZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameGLMemCompactRealTrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

noncomputable section

namespace GlobalTheory.FrameGfC

theorem gl_mem_GfC : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k), β.gl g ∈ GfC S := by
  intro D k _ _ _ _ p S n _ _ β g
  have hg := β.gl_supp g
  have he := p.split
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt S (β.gl g) - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt S (β.gl g) i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

end GlobalTheory.FrameGfC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulEqZeroOfNePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.SplitOrth

theorem place_mul_place {D : D7} {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := h
  obtain ⟨β, rfl, -, k0⟩ := h'
  refine Prod.ext (mul_zero (0 : Ainf D.host.F)) (show α * β = 0 from FiniteAdeleRing.ext _ fun w => ?_)
  change evalV D.host.F w (α * β) = evalV D.host.F w 0
  rw [map_mul, map_zero]
  by_cases hw : w = v
  · rw [k0 w (hw ▸ hv), mul_zero]
  · rw [h0 w hw, zero_mul]

theorem split_mul_split : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : SplitPt D k) (q' : SplitPt D k'), q.v ≠ q'.v → q.e * q'.e = 0 := by
  intro D k k' _ _ _ _ _ _ _ _ q q' hv
  obtain ⟨ε, hε, he⟩ := q.above
  obtain ⟨ε', hε', he'⟩ := q'.above
  have h1 : q.e * q.e = q.e := q.split.1
  have h2 : q.e * cA D q.e = 0 := q.split.2.1
  have h1' : q'.e * q'.e = q'.e := q'.split.1
  have h2' : q'.e * cA D q'.e = 0 := q'.split.2.1
  have a : q.e = q.e * algebraMap _ _ ε := by rw [← he, mul_add, h1, h2, add_zero]
  have a' : q'.e = q'.e * algebraMap _ _ ε' := by rw [← he', mul_add, h1', h2', add_zero]
  rw [a, a', mul_mul_mul_comm, ← map_mul, place_mul_place hε hε' hv, map_zero, mul_zero]

end GlobalTheory.SplitOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulIdemSumEqZeroOfNotMem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.OutsideOrth

theorem mul_eq_zero : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D),
    PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → e * p.e = 0 := by
  intro D k _ _ _ _ p P PP e hPP hp he
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun P' hP' => ?_
  rw [mul_comm]
  exact Formalism.IndefR.Fin.idem_orth (Formalism.IndefR.Fin.idemAt_split hp) hp (hes P' hP')
    (fun h => hPP (h ▸ hP'))

end GlobalTheory.LocMod.OutsideOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralMatrixIndicatorMemSchwartzBruh
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

namespace GlobalTheory.LocMod.Place

theorem intInd_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'],
    Place.intInd (k := k) Y Y' ∈ SB (Matrix Y Y' k) := by
  intro k _ _ _ _ Y Y' _ _ _ _
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have hc : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  set K : Set (Matrix Y Y' k) := {x | ∀ r q, x r q ∈ 𝒪[k]} with hK
  have hKeq : K = Set.univ.pi fun _ : Y => Set.univ.pi fun _ : Y' => (𝒪[k] : Set k) := by
    ext x
    exact ⟨fun h r _ q _ => h r q, fun h r q => h r (Set.mem_univ r) q (Set.mem_univ q)⟩
  have hKo : IsOpen K := by
    rw [hKeq]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => ho
  have hKc : IsCompact K := by
    rw [hKeq]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc
  have hcl : IsClosed K := by
    rw [hKeq]
    exact isClosed_set_pi fun _ _ => isClosed_set_pi fun _ _ => (Valuation.isClosed_integer (v := valuation k))
  refine ⟨?_, ?_⟩
  · show IsLocallyConstant (K.indicator fun _ => (1 : ℂ))
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
    by_cases hx : x ∈ K
    · filter_upwards [hKo.mem_nhds hx] with y hy
      simp [hx, hy]
    · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
      simp [hx, Set.notMem_of_mem_compl hy]
  · show HasCompactSupport (K.indicator fun _ => (1 : ℂ))
    exact HasCompactSupport.intro hKc fun x hx => Set.indicator_of_notMem hx _

end GlobalTheory.LocMod.Place
end

