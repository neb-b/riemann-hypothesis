module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHeightBasePairEqModuleProduct
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0365
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalDenominators
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0368
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0367
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ScWlocExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HCReprodM

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentLocalIdentityFamiliesLemmaH
section
namespace GlobalTheory.HTieLeaf

theorem main : Formalism.L2.SG.FamDefs.HTie :=
  Formalism.L2.SG.NGHTie.hTie_of _root_.GlobalTheory.HTPlaceLeaf.htPlace GlobalTheory.DiffModProd.htDelta _root_.GlobalTheory.HTThetaLeaf.main

end GlobalTheory.HTieLeaf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameScaleIsUnitAtPrimeOverLevel
section
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameFactorG

open IsDedekindDomain ValuativeRel

variable {D : D7}

theorem exists_diff_not_mem (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ∃ m : 𝓞 D.host.F, m ∈ differentIdeal ℤ (𝓞 D.host.F) ∧ m ∉ (below D P).asIdeal := by
  have h := Formalism.L2.SG.Pf.LatEx.ddG_of D Formalism.L2.SG.Pf.LatEx.splitDiff_holds P hP
  rw [Ideal.map_le_iff_le_comap] at h
  obtain ⟨m, hm, hmP⟩ := Set.not_subset.1 h
  exact ⟨m, hm, hmP⟩

theorem coe_algebraMap_int (m : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) m : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (m : D.host.F) := by
  first
  | rfl
  | simp
  | exact (IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E m).symm

theorem iota_mem_of_inv_pow (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (k : ℕ) (y : D.host.E) (hy : y ∈ (ddS D)⁻¹ ^ k) :
    (D.s.atP (below D P)).ιE y ∈ (D.s.atP (below D P)).O := by
  obtain ⟨m, hm, hmP⟩ := exists_diff_not_mem P hP
  set c : D.host.E := ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) m : 𝓞 D.host.E) : D.host.E) with hc
  have hmE : c ∈ ddS D := by
    unfold ddS
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨_, Ideal.mem_map_of_mem _ hm, rfl⟩
  have hpow : c ^ k ∈ ddS D ^ k := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_pow]
    exact Submodule.pow_mem_pow _ (FractionalIdeal.mem_coe.2 hmE) k
  have h1 : y * c ^ k ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    have := FractionalIdeal.mul_mem_mul hy hpow
    rwa [← mul_pow, inv_mul_cancel₀ GlobalTheory.FrameFactorUnit.ddS_ne_zero, one_pow] at this
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
  have hu := Formalism.L2.SG.Pf.LocalDenominators.iF_unit (D.s.atP (below D P)) hmP
  set t := (D.s.atP (below D P)).ιF (m : D.host.F) with ht
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, map_zero] at hu; exact zero_ne_one hu
  have htinv : t⁻¹ ∈ 𝒪[(D.s.atP (below D P)).Fp] := by
    rw [Valuation.mem_integer_iff, map_inv₀, hu, inv_one]
  have hcE : (D.s.atP (below D P)).ιE c = algebraMap _ (D.s.atP (below D P)).Ep t := by
    rw [hc, coe_algebraMap_int, (D.s.atP (below D P)).compat]
  have e : (D.s.atP (below D P)).ιE y =
      (D.s.atP (below D P)).ιE (o : D.host.E) *
        (algebraMap _ (D.s.atP (below D P)).Ep t⁻¹) ^ k := by
    have h2 := congrArg (D.s.atP (below D P)).ιE ho
    have h3 : (D.s.atP (below D P)).ιE (algebraMap (𝓞 D.host.E) D.host.E o) =
        (D.s.atP (below D P)).ιE (o : D.host.E) := rfl
    rw [h3, map_mul, map_pow, hcE] at h2
    rw [h2, mul_assoc, ← mul_pow, ← map_mul, mul_inv_cancel₀ ht0, map_one, one_pow, mul_one]
  rw [e]
  exact mul_mem (Formalism.L2.SG.Pf.LocalDenominators.iE_int _ (RingOfIntegers.isIntegral_coe o))
    (pow_mem (Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O _ htinv) _)

end GlobalTheory.FrameFactorG


open GlobalTheory.FrameFactorG in
theorem GlobalTheory.FrameFactorG.frFac_unit_at_g : ∀ (D : D7) (Tn T'n : ℕ) (F0 : FlagG (VS D) D.R.rS (Tn : D.host.E)) (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP Tn T'n F F' → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g : GV D, Adapt g (lf D F0) F → IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ a, frFac Z.δ (below D P) a ∈ (Z.M (below D P)).L.O ∧ Ring.inverse (frFac Z.δ (below D P) a) ∈ (Z.M (below D P)).L.O := by
  intro D Tn T'n F0 F F' Z FP _ Λ y _ g _ _ P hP a
  have hO := Formalism.L2.SG.Pf.LocFacts.lf_hO Z (below D P)
  have hD := Formalism.L2.SG.Pf.locDiffC_holds D Z (below D P) a
  have hexp : (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))) = -((D.R.rS - a.val : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : a.val ≤ D.R.rS)]
  have hpw : (ddS D) ^ (-((D.R.rS - a.val : ℕ) : ℤ)) = (ddS D)⁻¹ ^ (D.R.rS - a.val) := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hexp, hpw] at hD
  constructor
  · have h : frFac Z.δ (below D P) a ∈ Submodule.span (Z.M (below D P)).L.O
        ((D.s.atP (below D P)).ιE '' ((((ddS D)⁻¹ ^ (D.R.rS - a.val) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : Set D.host.E)) := by
      rw [hD]; exact Submodule.mem_span_singleton_self _
    suffices key : ∀ x ∈ Submodule.span (Z.M (below D P)).L.O
        ((D.s.atP (below D P)).ιE '' ((((ddS D)⁻¹ ^ (D.R.rS - a.val) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : Set D.host.E)), x ∈ (Z.M (below D P)).L.O from
      key _ h
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      rw [hO]; exact iota_mem_of_inv_pow P hP _ w hw
    | zero => exact zero_mem _
    | add x w _ _ hx hw => exact add_mem hx hw
    | smul o x _ hx => rw [Subring.smul_def]; exact mul_mem o.2 hx
  · have h1 : (1 : (D.s.atP (below D P)).Ep) ∈ Submodule.span (Z.M (below D P)).L.O {frFac Z.δ (below D P) a} := by
      rw [← hD]
      exact Submodule.subset_span ⟨1, GlobalTheory.FrameFactorUnit.one_mem_inv_pow _, map_one _⟩
    obtain ⟨o1, ho1⟩ := Submodule.mem_span_singleton.1 h1
    have ho1' : (o1 : (D.s.atP (below D P)).Ep) * frFac Z.δ (below D P) a = 1 := by
      simpa [Subring.smul_def, smul_eq_mul] using ho1
    have hu : IsUnit (frFac Z.δ (below D P) a) :=
      ⟨⟨frFac Z.δ (below D P) a, o1, by rw [mul_comm]; exact ho1', ho1'⟩, rfl⟩
    have hinv : Ring.inverse (frFac Z.δ (below D P) a) = o1 := by
      calc Ring.inverse (frFac Z.δ (below D P) a)
          = ((o1 : (D.s.atP (below D P)).Ep) * frFac Z.δ (below D P) a) * Ring.inverse (frFac Z.δ (below D P) a) := by
            rw [ho1', one_mul]
        _ = o1 := by rw [mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]
    rw [hinv]; exact o1.2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericTermsScalarClassesFormFamily
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SnFamGen

theorem genFam : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t = 1 ∧ (Y.tO u u').scal t' t) → (∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet, ∀ t'' ∈ (Y.tO u u').genSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t'' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t'' = 1 → (Y.tO u u').scal t' t'' → (Y.tO u u').s0 t t'' = 1 ∧ (Y.tO u u').scal t t'') → FamQ Y u u' Not (Y.tO u u').genSet (gCls Y u u') := by
  intro D X Y u u' hsym htr
  have hG : ∀ t : TauC Y u u', t ∈ (Y.tO u u').genSet → t.G ≠ 0 := by
    intro t ht h0
    have h1 : (Y.tO u u').G t ≠ 0 := ht.1
    apply h1
    show Gt t = 0
    simp [Gt, h0]
  have hrefl : ∀ t : TauC Y u u', t ∈ (Y.tO u u').genSet → t ∈ gCls Y u u' t := by
    intro t ht
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.SnFamCoset.scalar_of_same_coset D X Y u u' t t (hG t ht) rfl rfl
    exact ⟨ht, rfl, h1, h2⟩

  have hrow : ∀ t t' : TauC Y u u', t' ∈ gCls Y u u' t → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t :=
    fun t t' h => h.2.1

  have hsub : ∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet,
      (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' →
      gCls Y u u' t' ⊆ gCls Y u u' t := by
    intro t ht t' ht' hr hs hc x hx
    obtain ⟨hxg, hxr, hxs, hxc⟩ := hx
    obtain ⟨h1, h2⟩ := htr t ht t' ht' x hxg hr hxr.symm hs hc hxs hxc
    exact ⟨hxg, hxr.trans hr.symm, h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · ext t
    simp [setQ, Formalism.FourierDecayAlt.PB.Terms.genSet]
  · intro t ht t' ht' hn
    constructor
    · intro he
      have : t' ∈ gCls Y u u' t := he ▸ hrefl t' ht'
      exact (hrow t t' this).symm
    · intro hr
      obtain ⟨hs, hc⟩ := _root_.GlobalTheory.SnFamCoset.scalar_of_same_coset D X Y u u' t t' (hG t ht) hr hn
      obtain ⟨hs', hc'⟩ := hsym t ht t' ht' hr hs hc
      exact Set.Subset.antisymm (hsub t' ht' t ht hr.symm hs' hc') (hsub t ht t' ht' hr hs hc)
  · intro t ht t' ht' he
    have : t' ∈ gCls Y u u' t := he ▸ hrefl t' ht'
    exact (hrow t t' this).symm

end GlobalTheory.SnFamGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserIffRationalCoords
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.StabIntCoord

theorem mem_maxUnramifiedSubfield_conj_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) (r k : ℕ) (S : Frames L r k)
    (x : S.GLV) (hx : x ∈ S.St) (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : IsUni s) (hs' : IsUni s')
    (h1 : ∀ j, x (S.f j) = ∑ i, s i j • S.f i) (h2 : ∀ j, x (S.f' j) = ∑ i, s' i j • S.f' i) :
    x ∈ S.K0 ↔ IsIntM L s' := by
  have heq := ((GlobalTheory.HL.FrameStab.stab_eq L r k S).2 s s' hs hs').2 ⟨x, hx, h1, h2⟩
  have hint := ((GlobalTheory.HL.BlockStab.stabiliser_blockDiag L r k S).1 s s' hs hs' heq).2
  have hli := (GlobalTheory.FrameBasic.main L r k S).1
  have hl1 : LinearIndependent E S.f := hli.comp Sum.inl Sum.inl_injective
  have hl2 : LinearIndependent E S.f' := hli.comp Sum.inr Sum.inr_injective
  have e1 := _root_.GlobalTheory.HL.unistab_iff L S.f hl1 x s hs h1
  have e2 := _root_.GlobalTheory.HL.unistab_iff L S.f' hl2 x s' hs' h2
  unfold Frames.K0
  simp only [Subgroup.mem_inf]
  rw [e1, e2, hint]
  tauto

end GlobalTheory.HL.StabIntCoord

namespace GlobalTheory.HL.StabIntCoord

open IsDedekindDomain

theorem loc_act {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    (A : Places F E sig) {n r : ℕ} (p : HeightOneSpectrum (𝓞 F)) (c : ((A.loc p).Fp)ˣ)
    (x : (Fin n → E) ≃ₗ[E] (Fin n → E)) (g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))
    (hE : A.Ext p x g') (v : Fin (r + 1) → Fin n → E) (vl : Fin (r + 1) → Fin n → (A.loc p).Ep)
    (hv : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ))) • vl a = A.bc p (v a))
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hM : ∀ b : Fin (r + 1), x (v b) = ∑ a, M a b • v a) (b : Fin (r + 1)) :
    g' (vl b) = ∑ a : Fin (r + 1), (algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ)) /
      (c : (A.loc p).Fp) ^ (r - (b : ℕ))) * (A.loc p).ιE (M a b)) • vl a := by
  have hc : ∀ m : ℕ, ((c : (A.loc p).Fp) ^ m) ≠ 0 := fun m => pow_ne_zero _ c.ne_zero
  have hvl : ∀ a : Fin (r + 1), vl a = algebraMap (A.loc p).Fp (A.loc p).Ep (((c : (A.loc p).Fp) ^ (r - (a : ℕ)))⁻¹) • A.bc p (v a) := by
    intro a
    rw [← hv a, smul_smul, ← map_mul, inv_mul_cancel₀ (hc _), map_one, one_smul]
  have hbc : ∀ (l : Fin (r + 1) → E) (w : Fin (r + 1) → Fin n → E),
      A.bc p (∑ a, l a • w a) = ∑ a, (A.loc p).ιE (l a) • A.bc p (w a) := by
    intro l w
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Places.bc, Finset.sum_apply, map_sum, smul_eq_mul, map_mul]
  rw [hvl b, map_smul, hE, hM b, hbc, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hv a, smul_smul, smul_smul]
  congr 1
  rw [div_eq_mul_inv, map_mul]
  ring

end GlobalTheory.HL.StabIntCoord

namespace GlobalTheory.HL.StabIntCoord


set_option maxHeartbeats 1000000 in
theorem integralStabiliser_iff_rational_coords_alt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ x ∈ G.St, ∀ B : Formalism.L2.SG.PairVal.MatR D, (∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) → (x ∈ G.K0 ↔ ∀ a b : Fin (D.R.rS + 1), a < b → B a b ∈ ((ddS D ^ (-((b : ℤ) - (a : ℤ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))) := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ _ G c x hx B hB
  obtain ⟨s, s', hs, hs', hsf, hsf'⟩ := _root_.GlobalTheory.HL.StTri.stab_unitriangular _ _ _ G x hx
  have key : ∀ p : PlF D, (∃ g' ∈ (G.S p).K0, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p x g') ↔
      ∀ a b : Fin (D.R.rS + 1), a < b → (D.s.atP p).ιE (B a b) * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) ∈ (Y.M p).L.O := by
    intro p
    haveI := (D.s.atP p).lf
    haveI := (D.s.atP p).char0
    haveI : IsNonarchimedeanLocalField ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp := (D.s.atP p).lf
    haveI : CharZero ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp := (D.s.atP p).char0
    obtain ⟨xp, hxp, hExt⟩ := hx p
    have huniq := ((GlobalTheory.HL.RatExt.rational_extend (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ p).2.2.1 x)
    have hK : (∃ g' ∈ (G.S p).K0, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p x g') ↔ xp ∈ (G.S p).K0 := by
      constructor
      · rintro ⟨g', hg', hgE⟩
        rwa [huniq.unique hExt hgE]
      · intro h; exact ⟨xp, h, hExt⟩
    rw [hK]
    have h1 := loc_act (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) p (G.c p) x xp hExt G.f (G.S p).f (G.f_eq p) s hsf
    have h2 := loc_act (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) p (G.c p) x xp hExt G.f' (G.S p).f' (G.f'_eq p) s' hsf'
    have h3 := loc_act (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) p (G.c p) x xp hExt G.f' (G.S p).f' (G.f'_eq p) B hB
    have hceq : algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (G.c p).val = algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (Y.δ p) *
        ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (uP p : D.host.E) := c.c_eq p
    show _ ↔ ∀ a b : Fin (D.R.rS + 1), a < b → ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (B a b) * (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (Y.δ p) *
        ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) ∈ (Y.M p).L.O
    have hcne : ∀ m : ℕ, ((G.c p).val ^ m) ≠ 0 := fun m => pow_ne_zero _ (G.c p).ne_zero
    have huni : ∀ M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsUni M →
        IsUni (fun a b : Fin (D.R.rS + 1) => algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep
          ((G.c p).val ^ (D.R.rS - (a : ℕ)) / (G.c p).val ^ (D.R.rS - (b : ℕ))) *
            ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (M a b)) := by
      intro M hM
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · simp [hM.1 i j hij]
      · simp [hM.2 i, div_self (hcne _)]
    rw [mem_maxUnramifiedSubfield_conj_iff _ _ _ (G.S p) xp hxp _ _ (huni s hs) (huni s' hs') h1 h2]
    have hli : LinearIndependent ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (G.S p).f' :=
      (GlobalTheory.FrameBasic.main _ _ _ (G.S p)).1.comp Sum.inr Sum.inr_injective
    have hsB : ∀ a b, ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (s' a b) = ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (B a b) := by
      intro a b
      have e := (h2 b).symm.trans (h3 b)
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at e
      simp_rw [← sub_smul] at e
      have h0 := Fintype.linearIndependent_iff.1 hli _ e a
      have hu : IsUnit (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep
          ((G.c p).val ^ (D.R.rS - (a : ℕ)) / (G.c p).val ^ (D.R.rS - (b : ℕ)))) :=
        (isUnit_iff_ne_zero.2 (div_ne_zero (hcne _) (hcne _))).map _
      rw [← mul_sub, hu.mul_right_eq_zero, sub_eq_zero] at h0
      exact h0
    have hent : ∀ a b : Fin (D.R.rS + 1), a < b → algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep
        ((G.c p).val ^ (D.R.rS - (a : ℕ)) / (G.c p).val ^ (D.R.rS - (b : ℕ))) *
          ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (s' a b) = ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (B a b) * (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Ep (Y.δ p) *
            ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) := by
      intro a b hab
      have hab' : (a : ℕ) < b := hab
      have hb := b.isLt
      rw [show D.R.rS - (a : ℕ) = (D.R.rS - b) + ((b : ℕ) - a) by omega, pow_add,
        mul_div_cancel_left₀ _ (hcne _), map_pow, hceq, hsB, mul_comm]
    constructor
    · intro h a b hab
      rw [← hent a b hab]
      exact h a b
    · intro h a b
      rcases lt_trichotomy a b with hab | rfl | hab
      · beta_reduce
        rw [hent a b hab]
        exact h a b hab
      · show _ ∈ _
        simp [hs'.2 a, div_self (hcne _)]
      · show _ ∈ _
        simp [hs'.1 a b hab]
  have hK0 : x ∈ G.K0 ↔ ∀ p, ∃ g' ∈ (G.S p).K0, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p x g' := Iff.rfl
  rw [hK0, forall_congr' key]
  have hI : ∀ a b : Fin (D.R.rS + 1), a < b → (B a b ∈ ((ddS D ^ (-((b : ℤ) - (a : ℤ))) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔
      ∀ p : PlF D, (D.s.atP p).ιE (B a b) * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ ((b : ℕ) - (a : ℕ)) ∈ (Y.M p).L.O) := by
    intro a b hab
    have hab' : (a : ℕ) < b := hab
    have hb := b.isLt
    have hn : (b : ℕ) - (a : ℕ) ≤ D.R.rS := by omega
    have e : (-((b : ℤ) - (a : ℤ))) = -((((b : ℕ) - (a : ℕ) : ℕ)) : ℤ) := by
      rw [Nat.cast_sub hab'.le]
    rw [e]
    exact _root_.GlobalTheory.DiffLoc.mem_ddPow_neg_iff D ⟨Y.δ, Y.M, Y.agree⟩ _ hn (B a b)
  constructor
  · intro h a b hab
    exact (hI a b hab).2 fun p => h p a b hab
  · intro h p a b hab
    exact (hI a b hab).1 (h a b hab) p

end GlobalTheory.HL.StabIntCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroCmElementLocalUnitAlmostAllStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_cm_element_local_unit_almost_all : ∀ (D : D7) (Z : LocDat D) (x : D.host.E), x ≠ 0 →
    {p : PlF D | ¬ Formalism.MainNotions.S.LocNG.IsUnitO (Z.M p) ((D.s.atP p).ιE x)}.Finite := by
  have exists_nat_mul_integral {D : D7} (x : D.host.E) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : D.host.E) * x) := by
    have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have : Algebra.IsAlgebraic ℤ D.host.E := Algebra.IsAlgebraic.trans ℤ ℚ D.host.E
    obtain ⟨y, hy0, hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x).exists_integral_multiple
  
    refine ⟨y.natAbs * y.natAbs, by simpa using hy0, ?_⟩
    have hsq : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := by
      rw [Nat.cast_mul]
      exact Int.natAbs_mul_self' y
    have e : ((y.natAbs * y.natAbs : ℕ) : D.host.E) * x = (y : D.host.E) * (y • x) := by
      rw [zsmul_eq_mul, ← mul_assoc]
      have hc : ((y.natAbs * y.natAbs : ℕ) : D.host.E) = (((y.natAbs * y.natAbs : ℕ) : ℤ) : D.host.E) :=
        (Int.cast_natCast _).symm
      rw [hc, hsq, Int.cast_mul]
    rw [e]
    have hyi : IsIntegral ℤ (y : D.host.E) := by
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ D.host.E y))
    exact hyi.mul hy
  
  have iota_mem_O {D : D7} (Z : LocDat D) (p : PlF D) (x : D.host.E) (n : ℕ)
      (hint : IsIntegral ℤ ((n : D.host.E) * x)) (hn : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal)) :
      (D.s.atP p).ιE x ∈ (Z.M p).L.O := by
    rw [(show (Z.M p).L.O = (D.s.atP p).O from (Z.agree p).2.2.2.1), (D.s.atP p).O_def]
    have : CharZero (D.s.atP p).Fp := (D.s.atP p).char0
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hn (by simp)
    have hcn : (D.s.atP p).ιF (n : D.host.F) = (n : (D.s.atP p).Fp) := map_natCast _ n
    have hc0 : (n : (D.s.atP p).Fp) ≠ 0 := by exact_mod_cast hn0
  
    have hv : p.valuation D.host.F (n : D.host.F) = 1 := by
      have := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
        (v := p) (K := D.host.F) (r := (n : 𝓞 D.host.F))).mpr hn
      rwa [map_natCast] at this
    have hle : (1 : (D.s.atP p).Fp) ≤ᵥ (n : (D.s.atP p).Fp) := by
      have := ((D.s.atP p).val 1 (n : D.host.F)).mpr (by rw [hv, map_one])
      rwa [map_one, hcn] at this
    have hinv : (n : (D.s.atP p).Fp)⁻¹ ∈ (ValuativeRel.valuation (D.s.atP p).Fp).integer := by
      rw [Valuation.mem_integer_iff, map_inv₀]
      have h1 := (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (D.s.atP p).Fp) 1
        (n : (D.s.atP p).Fp)).mp hle
      rw [map_one] at h1
      exact inv_le_one_of_one_le₀ h1
    have hx : (D.s.atP p).ιE x = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (n : (D.s.atP p).Fp)⁻¹ *
        (D.s.atP p).ιE ((n : D.host.E) * x) := by
      have hE : (n : D.host.E) = algebraMap D.host.F D.host.E (n : D.host.F) := (map_natCast _ n).symm
      rw [map_mul, hE, (D.s.atP p).compat, hcn, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
    rw [hx]
    refine IsIntegral.mul ?_ ?_
    · exact isIntegral_algebraMap (R := (ValuativeRel.valuation (D.s.atP p).Fp).integer) (x := ⟨(n : (D.s.atP p).Fp)⁻¹, hinv⟩)
    · exact (hint.map (D.s.atP p).ιE.toIntAlgHom).tower_top
  
  intro D Z x hx
  obtain ⟨n, hn0, hn⟩ := exists_nat_mul_integral x
  obtain ⟨m, hm0, hm⟩ := exists_nat_mul_integral x⁻¹

  have hI : Ideal.span {((n * m : ℕ) : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast Nat.mul_ne_zero hn0 hm0
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hnm
  apply hp
  have hn' : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal) := fun h => hnm (by
    push_cast
    exact Ideal.mul_mem_right _ _ h)
  have hm' : ¬ ((m : 𝓞 D.host.F) ∈ p.asIdeal) := fun h => hnm (by
    push_cast
    exact Ideal.mul_mem_left _ _ h)
  refine ⟨iota_mem_O Z p x n hn hn', (D.s.atP p).ιE x⁻¹, iota_mem_O Z p x⁻¹ m hm hm', ?_⟩
  rw [← map_mul, mul_inv_cancel₀ hx, map_one]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WlocExistsReal
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory

theorem wlocExists_real : WlocExists :=
  scWlocExists Formalism.L2.SG.HCReprodM.hcReprodDSm

end GlobalTheory
end

