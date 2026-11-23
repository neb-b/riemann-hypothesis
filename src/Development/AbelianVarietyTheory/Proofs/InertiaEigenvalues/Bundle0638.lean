module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPointOverLetter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0398
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XNygaardExtComesFromBaseFieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0562
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0441
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0632
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0633

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionRulesCriterionOddRootOfUnityCaseA
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

noncomputable section

namespace GlobalTheory.ExpansionsOdd


set_option maxHeartbeats 800000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL),
      Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing ((HW l).W K 1 LL hA.2.2) ∧ Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules ((HW l).W K 1 LL hA.2.2) ∧
        Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F Cm hN l _ K LL hA
  obtain ⟨p1, -, p3, p4, p5, -, -, -, p9, -⟩ := hN
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) :=
    Formalism.MainNotions.N.Pv.LocalLengthBound.OLC.complete_max LL
  have hLT := GlobalTheory.LevelClauseOdd.main D HW F Cm p4 p9 l K LL hA
  have C := ((Cm l).C K 1 LL hA.2.2).tie
  have hs : ((HW l).W K 1 LL hA.2.2).s = 1 := (HW l).W_s K 1 LL hA.2.2
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie _ hs C
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hA.2.2) := p9 l K 1 LL hA.2.2
  refine ⟨fun hCA => ?_, Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of _ hLT.1 hG.1 hG.2, ?_⟩
  · have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL hA.2.2) :=
      (((h9 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL hA.2.2))) hs hCA.2.2).2.2 (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hA.1)).1
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of _ hring hCA
  · have hlm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
      rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.N.Pv.LocalLengthBound.l_mem_maxOL (D.loc l) LL
    have hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris ((D.loc l).PD K) ↥LL.1 :=
      GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL
    have hB : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool ((HW l).W K 1 LL hA.2.2) := Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of _ h9
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.expCrit_of _ Subtype.val_injective hlm (Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL)
      (p1 l K 1 LL hA.2.2) (p3 l K 1 LL hA.2.2) hLT.1 (p5 l K 1 LL hA.2.2) h9 hD hB C
      (p4 l K 1 LL hA.2.2) hLT.2

end GlobalTheory.ExpansionsOdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisPhiFixedAddFinrankMonLe
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory

theorem finrank_dcris_phi_fixed_add_finrank_mon_le : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) + finrank ℚ_[l] ↥((Dst P ρ).map (monV P ℚ_[l] V)) ≤ finrank ℚ_[l] ↥(Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) := by
  intro l _ P AI T K V _ _ _ V' _ _ _ ρ ρ' m hD hS
  obtain ⟨B, h1, h2, h3⟩ := GlobalTheory.T.exists_pairing_Dst_Dcris_frobenius_fixed l P AI T K V V' ρ ρ' m hD hS
  haveI := _root_.GlobalTheory.Pst.finiteDimensional_Dst_of_isSst l P K V ρ hS
  refine _root_.GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id ℚ_[l] _ _ (Dst P ρ) ((Dst P ρ).map (monV P ℚ_[l] V))
    ((l : ℚ_[l]) • phiV P ℚ_[l] V) B ?_ ?_ ?_ ?_ h3
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_Dst] at hx
    rw [mem_Dst]
    intro g
    rw [← Module.End.mul_apply, ← monV_stRep, Module.End.mul_apply, hx g]
  · intro x hx
    rw [mem_Dst] at hx ⊢
    intro g
    rw [LinearMap.smul_apply, map_smul, ← Module.End.mul_apply, ← phiV_stRep, Module.End.mul_apply,
      hx g]
  · rintro _ ⟨x, hx, rfl⟩ w
    exact h1 x hx w
  · intro x hx w
    exact h2 x hx w

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorBaseChangeForms
section
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.NX
open scoped TensorProduct

namespace GlobalTheory.GoodSS

variable {D : D7} (S : RatDat D.ntw)

def opK (j : ℕ) (f : Module.End D.what₂.LL (S.WL j)) (hf : ∀ x ∈ (S.A j).WK, f x ∈ (S.A j).WK) :
    Module.End S.Ks (FmK S j) :=
  (f.restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) hf

def goodProjectorBaseChangeForms (j : ℕ) (hst : RhoStab S j) (hχ : ChiInLL0 S j) (eC : G0g D.nd → ↥D.LL0) :
    Module.End ↥D.LL0 (↥D.LL0 ⊗[S.Ks] FmK S j) :=
  ∑ᶠ g : G0g D.nd, (eC g * (chiL S j hχ (S.eG.symm g))⁻¹) •
    LinearMap.baseChange ↥D.LL0 (rhoKG S j hst (S.eG.symm g))

end GlobalTheory.GoodSS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorFormsIdempotent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms NumberField Polynomial Formalism.IndefR.NX
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GoodSS.Idem

def rhoTw {D : D7} (S : RatDat D.ntw) (j : ℕ) : G0g D.nd →* Module.End D.what₂.LL (S.WL j) where
  toFun g := ((((S.A j).chi (S.eG.symm g))⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • (S.A j).ρ (S.eG.symm g)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv, Units.val_mul]
    rw [smul_mul_smul_comm]

theorem goodProjW_idem : ∀ (D : D7) (S : RatDat D.ntw) (j : ℕ), D.ntw.Tw →
    goodProjW S j D.nexp.eLL0 * goodProjW S j D.nexp.eLL0 = goodProjW S j D.nexp.eLL0 := by
  intro D S j i
  set s := (D.nexp.eAlg i true).coeff.support with hs
  have hsupp : ∀ g, g ∉ s → D.nexp.eLL0 g = 0 := fun g hg => by
    have h0 : (D.nexp.eAlg i true).coeff g = 0 := Finsupp.notMem_support_iff.1 hg
    have hcoef : (D.nexp.eAlg i true).coeff g = readLL0 S i true (D.nexp.eLL0 g) := by
      rw [D.nexp.eAlg_def]; rfl
    rw [hcoef] at h0
    exact (map_eq_zero_iff _ (readLL0 S i true).injective).1 h0
  let rd : ↥D.LL0 →+* FractionRing (D.ntw.O i) := readLL0 S i true
  have hrd : Function.Injective rd := (readLL0 S i true).injective
  let eL : MonoidAlgebra ↥D.LL0 (G0g D.nd) :=
    MonoidAlgebra.ofCoeff (Finsupp.onFinset s D.nexp.eLL0 fun g hg => by
      by_contra h
      exact hg (hsupp g h))
  have heL : ∀ g, eL.coeff g = D.nexp.eLL0 g := fun g => by
    simp only [eL, MonoidAlgebra.coeff_ofCoeff, Finsupp.onFinset_apply]
  have hmap : MonoidAlgebra.mapRingHom (G0g D.nd) rd eL = D.nexp.eAlg i true := by
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    rw [MonoidAlgebra.coeff_mapRingHom, heL, D.nexp.eAlg_def]
    rfl
  have hinj : Function.Injective (MonoidAlgebra.mapRingHom (G0g D.nd) rd) := by
    intro x y hxy
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    apply hrd
    rw [← MonoidAlgebra.coeff_mapRingHom, ← MonoidAlgebra.coeff_mapRingHom, hxy]
  have hidem : eL * eL = eL := hinj (by rw [map_mul, hmap, D.nexp.eAlg_idem])
  let eLL := MonoidAlgebra.mapRingHom (G0g D.nd) (algebraMap ↥D.LL0 D.what₂.LL) eL
  have hP : goodProjW S j D.nexp.eLL0 =
      MonoidAlgebra.lift D.what₂.LL (Module.End D.what₂.LL (S.WL j)) (G0g D.nd) (rhoTw S j) eLL := by
    rw [MonoidAlgebra.lift_apply]
    unfold goodProjW
    rw [finsum_eq_sum_of_support_subset _ (s := s) fun g hg => by
      by_contra hgs
      exact hg (by simp only [hsupp g hgs, IntermediateField.coe_zero, zero_mul, zero_smul])]
    rw [Finsupp.sum_of_support_subset _ (s := s) (fun g hg => by
      by_contra hgs
      apply Finsupp.mem_support_iff.1 hg
      simp only [eLL, MonoidAlgebra.coeff_mapRingHom, heL, hsupp g hgs, map_zero]) (fun a b => b • rhoTw S j a) (fun _ _ => zero_smul _ _)]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [eLL, MonoidAlgebra.coeff_mapRingHom, heL, rhoTw, MonoidHom.coe_mk, OneHom.coe_mk, mul_smul,
      Units.val_inv_eq_inv_val]
    rfl
  rw [hP, ← map_mul, ← map_mul, hidem]

end GlobalTheory.GoodSS.Idem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fClassWachPairJumps
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.CrystallineDescent

set_option maxHeartbeats 40000000 in
private theorem descend_element_of_le_of_eq_K0 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ) (m : ℕ)
    (y' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) :
    ∃ y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m),
      ((F l).E K s LL h).tie.jD T y = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') := by
  obtain ⟨y, hy, hjy⟩ := GlobalTheory.T.inv_Q_pow_nygaard_ext_comes_from_base_field D HW F l K s LL h K' h' hle hK0 T hT m y' hy'
  exact ⟨y, hy, hjy⟩

set_option maxHeartbeats 60000000 in
private theorem descend_of_eq_K0_of_isCrys (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (htop : ((HW l).W K' s LL h').GKs = ⊤)
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs)
    (hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K')
    (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (m : ℕ) (y' z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)) (hyz' : (y', z') ∈ ((HW l).W K' s LL h').divisibleCocycles (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) (hz' : z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X) :
    ∃ (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T), y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m) ∧ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X ∧
      ∃ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (c' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').GKs))),
        Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧
        Submodule.Quotient.mk c' = ((HW l).W K' s LL h').cl (resLt (K := K) (K' := K') (LL := LL) hle T) ⟨(y', z'), hyz'⟩ ∧
        ∀ g, (c : ↥((HW l).W K s LL h).GKs → T.V) g = (c' : ↥((HW l).W K' s LL h').GKs → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g) := by
  obtain ⟨y, hy, hjy⟩ := descend_element_of_le_of_eq_K0 D HW F l K s LL h K' h' hle hK0 T hT m y' hy'
  obtain ⟨z, hz, hjz⟩ := GlobalTheory.T.X_nygaard_ext_comes_from_base_field D HW F l K s LL h K' h' hle hK0 T hT z' hz'
  obtain ⟨b', hb'⟩ := (GlobalTheory.WittTensorFixed.main l K' LL (resLt (K := K) (K' := K') (LL := LL) hle T)).1
    (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y')
  obtain ⟨c', hc'cl, hc'0, hc'g⟩ := cl_fit D HW F K' s LL h' (resLt (K := K) (K' := K') (LL := LL) hle T) y' z' hyz' b' hb'
  obtain ⟨c, hcc', hZf⟩ := push_cocycle (D.locA l) hle T ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop c'
  have hb : TWmap (φRW LL) T (toTW hle T b') - toTW hle T b' = ((F l).E K s LL h).tie.jD T y := by
    rw [toTW_φ, hb', hjy]
  have hone : ∀ g : ↥((HW l).W K s LL h).GKs,
      ((HW l).W K' s LL h').resΓ ((fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g : ↥((HW l).W K' s LL h').GKs) : ↥(GK K')) = 1 ↔
        ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 := fun g =>
    (resΓ_one_iff (D.loc l) K' LL _ ((HW l).W K' s LL h') _).trans
      (resΓ_one_iff (D.loc l) K LL _ ((HW l).W K s LL h) _).symm
  have hzero : ∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 →
      Zf (D.locA l) T ((HW l).W K s LL h).GKs c (toTW hle T b') g = 0 := by
    intro g hg
    rw [hZf b' g, hc'0 _ ((hone g).2 hg), toTW_zero]
  obtain ⟨lam', hlam'c, hlam'1, hlam'g, ⟨g', hg'⟩, -⟩ := lam_exists D HW K' s LL h'
  let lam : ↥((HW l).W K s LL h).GKs →* Multiplicative ℤ_[l] := lam'.comp (fHom ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop)
  have hlamc : Continuous lam := hlam'c.comp (fMap_cont ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop)
  have hlam1 : ∀ g, lam g = 1 → ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 := fun g hg =>
    (hone g).1 ((hlam'1 _).1 hg)
  have hfe : fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g') = g' := Subtype.ext (Subtype.ext rfl)
  have hg₁ : lam (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g') = Multiplicative.ofAdd 1 := by
    show lam' (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g')) = _
    rw [hfe, hg']
  have hZ₁ : Zf (D.locA l) T ((HW l).W K s LL h).GKs c (toTW hle T b') (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g') =
      ((F l).E K s LL h).tie.jD T z := by
    rw [hZf b' _, hfe, hc'g g' ((hlam'g g').1 hg'), hjz]
  have hall := _root_.GlobalTheory.NL.ZVal.zval D HW F l K s LL h T hT c (toTW hle T b') lam hlamc hlam1 hzero _ hg₁ z hz hZ₁
  obtain ⟨lamK, -, -, hlamKg, ⟨g₀, hg₀⟩, -⟩ := lam_exists D HW K s LL h
  have hγ := (hlamKg g₀).1 hg₀
  obtain ⟨z₀, hz₀, hZ₀⟩ := hall g₀
  have hyz := _root_.GlobalTheory.NL.HerrCocycleCriterion.cocyc D HW F l K s LL h T c (toTW hle T b') y z₀ g₀ hγ hb hZ₀
  exact ⟨y, z₀, hyz, hy, hz₀, c, c',
    GlobalTheory.T.herr_class_of_cocycle_values D HW F l K s LL h T c (toTW hle T b') y z₀ hyz g₀ hγ hb hzero hZ₀, hc'cl, hcc'⟩


set_option maxHeartbeats 4000000 in
theorem descend (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (htop : ((HW l).W K' s LL h').GKs = ⊤)
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs)
    (hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K')
    (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (m : ℕ) (y' z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)) (hyz' : (y', z') ∈ ((HW l).W K' s LL h').divisibleCocycles (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) (hz' : z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X) :
    ∃ (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T), y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m) ∧ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X ∧
      ∃ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (c' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').GKs))),
        Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧
        Submodule.Quotient.mk c' = ((HW l).W K' s LL h').cl (resLt (K := K) (K' := K') (LL := LL) hle T) ⟨(y', z'), hyz'⟩ ∧
        ∀ g, (c : ↥((HW l).W K s LL h).GKs → T.V) g = (c' : ↥((HW l).W K' s LL h').GKs → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g) := descend_of_eq_K0_of_isCrys D HW F l K s LL h K' h' hle hK0 htop hm hm' T hT m y' z' hyz' hy' hz'

set_option maxHeartbeats 60000000 in
private theorem wach_pow_smul_of_good_ext : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := by
  intro D HW F Cm l _ K s LL h W E C T hT M hh hJ κ hκ
  obtain ⟨K', h', hle, hK0, htop, hiff⟩ := base_setup D HW K s LL h
  have hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs :=
    fun g => (hiff _).2 g.2
  have hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K' := fun g => (hiff _).1 g.2
  have hT' := restrict_crys D hle T hT
  have hJ' := restrict_jumps D HW K s LL h K' h' hle T hT M hh hJ
    (fun τ' a hj => @_root_.GlobalTheory.Per.JumpRestrict.jump_restrict l _ (D.loc l) (D.locA l) (D.locT l) K K' LL hle T.V _ _ _ _ _ T.ρ hT τ' a hj)
  obtain ⟨cκ, cκ', hcκ, hcκ'f, hcκ'⟩ := pull_h1f (D.loc l) hle T ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm κ hκ
  obtain ⟨n, y', z', hyz', hy', hz', hcl'⟩ := GlobalTheory.T.H1f_class_of_wach_pair D HW F Cm l K' s LL h' (resLt (K := K) (K' := K') (LL := LL) hle T) hT' htop
    (fun _ => mx M) (fun _ => mx hh) hJ' _ hcκ'f
  haveI : Nonempty (Let K') := ⟨0⟩
  have hmx : mx (fun _ : Let K' => mx M) = mx M := ciSup_const
  rw [hmx] at hy'
  obtain ⟨y, z, hyz, hy, hz, c, c', hc, hc', hcc'⟩ :=
    descend D HW F l K s LL h K' h' hle hK0 htop hm hm' T hT (mx M) y' z' hyz' hy' hz'
  exact ⟨n, y, z, hyz, hy, hz, hc.symm.trans ((push_class hle T ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm hm' htop c cκ c' cκ' hcc' hcκ'
    _ (hc'.trans hcl')).trans (congrArg ((l ^ n : ℕ) • ·) hcκ))⟩


set_option maxHeartbeats 4000000 in
theorem pow_smul_from_complex : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := wach_pow_smul_of_good_ext

end GlobalTheory.NL.CrystallineDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
section
noncomputable section

namespace GlobalTheory.SerSys.Bridge

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.TypeLeaf
open scoped Classical

local instance factT (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

theorem trace_alg {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G) (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ τ (Representation.asAlgebraHom τ.ρ a) = tr a τ.character := by
  have e : Representation.asAlgebraHom τ.ρ a = ∑ x, a.coeff x • τ.ρ x :=
    LinearMap.ext fun w => by rw [alg_apply, LinearMap.sum_apply]; rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum, tr]
  exact Finset.sum_congr rfl fun x _ => map_smul _ _ _

section Finite

variable {g : ℕ} [Fact g.Prime]

theorem tr_eSerC_eq (L : LabelDatum g) {n : ℕ} {χ : Gn g n → ℂ} {f : (ZMod g)[X]} (hχ : IsIrr χ)
    (hf : HasLabel L χ f) : tr (eSerC L n f) χ = χ 1 ∧ χ 1 ≠ 0 := by
  have hfin := (GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)).1
  have hz : eSerC L n f * zOf χ = 1 * zOf χ := by
    rw [eSerC_eq_sum L n hfin, Finset.sum_mul, Finset.sum_eq_single_of_mem χ (by simp [hχ, hf]), one_mul]
    · simpa using (_root_.GlobalTheory.GLq.ZOrth.zorth _ χ χ hχ hχ).1
    · intro b hb hne
      have hb' : IsIrr b := by simpa using (Finset.mem_filter.1 hb).1
      rw [(_root_.GlobalTheory.GLq.ZOrth.zorth _ b χ hb' hχ).1, if_neg hne]
  have h := congrArg (fun a : MonoidAlgebra ℂ (Gn g n) => a.coeff 1) hz
  simp only [(_root_.GlobalTheory.GLq.trIdem _ _ χ).2.2] at h
  obtain ⟨d, hd, e⟩ := (_root_.GlobalTheory.GLq.trIdem _ 1 χ).2.1 hχ
  have h1 : χ 1 ≠ 0 := e ▸ Nat.cast_ne_zero.2 hd.ne'
  rw [MonoidAlgebra.one_def, Opp.tr_single, one_mul] at h
  exact ⟨mul_left_cancel₀ (div_ne_zero h1 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) h, h1⟩

theorem hasLabel_of_isCuspOf (L : LabelDatum g) {d : ℕ} {P : (ZMod g)[X]} {χ : Gn g d → ℂ} (h : IsCuspOf L P χ) :
    HasLabel L χ P := by
  have hχ : IsIrr χ := h.2.1.2.1
  refine ⟨[(P, ⟨d, χ⟩)], fun p hp => by rw [List.mem_singleton.1 hp]; exact h, by simp [degL], by simp, ?_⟩
  have hc : IsClass χ := fun x y => by
    obtain ⟨V, -, hV⟩ := hχ
    rw [← hV, ← hV, FDRep.char_conj]
  have e : hcL ([(P, (⟨d, χ⟩ : Pc g))].map Prod.snd) d = χ := GLq.Model.hc_full χ hc
  rw [e, (_root_.GlobalTheory.GLq.ZOrth.zorth _ χ χ hχ hχ).2.2, if_pos rfl]
  exact one_ne_zero

theorem labelsCusp (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) :
    TameGen.LabelsCusp (OfLabel.ofLabel L h5 hG) L := fun d τ P hP h0 => by
  obtain ⟨h1, h2⟩ := tr_eSerC_eq L hP.2.1.2.1 (hasLabel_of_isCuspOf L hP)
  rw [← trace_alg] at h1
  exact h2 (h1.symm.trans ((congrArg _ h0).trans (map_zero _)))

end Finite

theorem five_le (D : D7) (k : Fin 2) : 5 ≤ D.host.g k := by
  have hc := D.ntypes.g_cond k
  have h4 : D.host.g k % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd (D.host.g k)
      (show 4 ∣ D.host.QS * D.host.q * D.host.d from
        ((((show (4 : ℕ) ∣ 2 ^ (D.R.e + 2) from ⟨2 ^ D.R.e, by ring⟩).trans D.host.tower_dvd).mul_right _).mul_right _)), hc]
  have := (D.host.g_prime k).two_le
  omega

end GlobalTheory.SerSys.Bridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsQuotientOfIrreducibleUnitarySegmentPrStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLanglandsQuotient_of_irreducible_unitary_segment_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) k) V), σ.IsIrreducible →
    ∀ (m : ℕ) (δ : Fin m → IrrGL (k := k)) (Δ : Fin m → Segment k) (s : Fin m → ℝ), (∀ j, IsLSeg (Δ j) (δ j).rep) →
      (∀ j, IsUnitarisable (δ j).rep) → (∀ j, |s j| < 1 / 2) → ∀ hd : ∑ j, ((δ j).nu (s j)).1 = a,
      Nonempty (σ.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) →
      IsL ↑(List.ofFn fun j => (Δ j).nu (s j)) σ := by
  first | exact @GlobalTheory.isL_of_irreducible_prod_unitarisable_nu | exact GlobalTheory.isL_of_irreducible_prod_unitarisable_nu | (intros; apply GlobalTheory.isL_of_irreducible_prod_unitarisable_nu <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LambdaDataAtSide
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie GlobalTheory.ToricRational GlobalTheory.ToricDistribution

namespace GlobalTheory.LamTie

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_th_of (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hG : RatioConj) (hL : ToricSumFormula) {i : X.Tw} {ι : ℂ →+* Kbar X i}
    (hE : ∀ (σ : D.host.E →+* ℂ) (x : D.host.E), ι (σ x) ∈ (algebraMap (FractionRing (X.O i)) (Kbar X i)).range)
    {lam : X.abelian₂ i} {I : Type} [Fintype I] {φ : I → D.host.E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF D.host.E)} {χ : HChar D.host.E}
    (hD : IsHostDatum D.host φ s κ 𝔣 χ) (h𝔣 : ∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i)
    (hX : ∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (χ.val P : ℂ) = 1) :
    ∃ t : ∀ Q, X.RCG i Q → FractionRing (X.O i), ∀ th : ∀ i Q, X.abelian₂ i → X.RCG i Q → FractionRing (X.O i),
      (∀ Q, th i Q lam = t Q) → IsThOf (setTh X th) i ι lam φ s κ 𝔣 χ := by
  obtain ⟨T₀, hT₀, h0⟩ := exists_toricSum_ne_zero hL host_unramFin hD
  have := X.O_complete i
  have key : ∀ Q, ∃ t : X.RCG i Q → FractionRing (X.O i), BlochKatoReduction.Gen.QOk X i Q → Finite (PicO (condQ 𝔣 (belowSet Q))) ∧
      ∃ (π : PicO (condQ 𝔣 (belowSet Q)) →* X.RCG i Q) (T : PicO (condQ 𝔣 (belowSet Q)) → ℂ),
        IsRecMap X i Q π ∧ (∀ q, IsClassTerm φ s κ (condQ 𝔣 (belowSet Q)) χ q.out (T q)) ∧
        ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (t δ) = (ι T₀)⁻¹ * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q) := fun Q => by
    by_cases hQ : BlochKatoReduction.Gen.QOk X i Q
    · obtain ⟨hfin, T, hT⟩ := exists_classTerms hL host_unramFin hD (placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣).1
      obtain ⟨π, hπ, hπl⟩ := exists_isRecMap hA hQ 𝔣
      choose t ht using partialSum_mem hA hG host_unramFin hD (X.resO_ac i) (X.lPrime i).out.ne_zero (X.O_l i) ι hE (X.S0 i)
        (fun P hP => ⟨(algebraMap (X.O i) _ (X.Xv i lam P))⁻¹, by
          rw [map_inv₀, ← IsScalarTower.algebraMap_apply]
          exact (eq_inv_of_mul_eq_one_right (hX P hP)).symm⟩) hT₀ h0 (placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣).1 hT π hπl
      exact ⟨t, fun _ => ⟨hfin, π, T, hπ, hT, ht⟩⟩
    · exact ⟨0, fun h => absurd h hQ⟩
  choose t ht using key
  refine ⟨t, fun th e => ⟨(ι T₀)⁻¹, inv_ne_zero ((map_ne_zero ι).2 h0), fun Q hQ => ?_⟩⟩
  obtain ⟨h1, π, T, h2, h3, h4⟩ := ht Q hQ
  exact ⟨h1, π, T, h2, h3, fun δ => (congrArg _ (congrFun (e Q) δ)).trans (h4 δ)⟩

end GlobalTheory.LamTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationUnitaryStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_classification_unitary : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.StandardCosocleGL → (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, ∃ (δ : IrrGL (k := k)) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep := by
  first | exact @GlobalTheory.LocGL.exists_isL_of_unitary_twists | exact GlobalTheory.LocGL.exists_isL_of_unitary_twists | (intros; apply GlobalTheory.LocGL.exists_isL_of_unitary_twists <;> assumption)
end

