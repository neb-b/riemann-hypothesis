module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceFinal
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasisOfFive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1198
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMaximalCompactIntertwinesFockDerivati
section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.KInfComm

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb,
    ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
    ∀ a b : Fin n × Fin d → mixedEmbedding.mixedSpace F, ∃ a' b' : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      ∀ f : SInf F (Fin n × Fin d), A (GlobalTheory.ThK.EvAt0.PolD.dOp a b f) = GlobalTheory.ThK.EvAt0.PolD.dOp a' b' (A f) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk A hA a b
  have hB := hP.base
  have hw := hP.weil
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  have hpres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om x Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun x Φ hΦ => hW.pres x Φ hΦ
  have h1 : (1 : UA σ X.J) ∈ UAt σ X (evI F) := by
    intro u _
    simp [mat]
  have hk1 : k ∈ UAt σ W (evI F) := hk.1
  obtain ⟨T₂, hT₂⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hB.std hw ((1 : UA σ X.J)⁻¹, k⁻¹)
    (GlobalTheory.RealConjFac.inv_mem_UAt h1) (GlobalTheory.RealConjFac.inv_mem_UAt hk1)
  have hid : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (1 : Module.End ℂ _) (⇑f) (⇑f) := fun f r _ => rfl
  have e21 : ∀ f, T₂ (A f) = f := by
    intro f
    have hc := GlobalTheory.RealConjFac.acts_comp (hpres _) (hA f) (hT₂ (A f))
    rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (T₂ (A f)) f).2.2.2.1 _ hc (hid f))
  have e12 : ∀ f, A (T₂ f) = f := by
    intro f
    have hc := GlobalTheory.RealConjFac.acts_comp (hpres _) (hT₂ f) (hA (T₂ f))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (A (T₂ f)) f).2.2.2.1 _ hc (hid f))
  let T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d) :=
    LinearEquiv.ofLinear A T₂ (LinearMap.ext e12) (LinearMap.ext e21)
  set u := M.co.e.symm (fun i => GlobalTheory.ThK.EvAt0.PolD.liftA (a i), fun i => GlobalTheory.ThK.EvAt0.PolD.liftA (b i)) with hu_def
  have hu := GlobalTheory.ThK.EvAt0.PolEv.at_symm M a b
  set u' := mat (1 : UA σ X.J) * u * (mat k).transpose with hu'_def
  have hu' : At (evI F) u' := by
    intro c hc
    rw [hu'_def, ← Matrix.smul_mul, ← Matrix.mul_smul, hu c hc, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨GlobalTheory.ThK.EvAt0.PolD.arc (M.co.e u').1, GlobalTheory.ThK.EvAt0.PolD.arc (M.co.e u').2, fun f => ?_⟩
  have hf : ActsD (evI F) (M.heisLine B.ψ u) f (GlobalTheory.ThK.EvAt0.PolD.dOp a b f) := by
    refine (GlobalTheory.ThK.EvAt0.PolEv.actsD_iff_dOp hB.std M u hu _ _).2 ?_
    rw [hu_def, LinearEquiv.apply_symm_apply, GlobalTheory.ThK.EvAt0.PolEv.arc_liftA, GlobalTheory.ThK.EvAt0.PolEv.arc_liftA]
  have ht := GlobalTheory.HeisTransport.actsD_heisLine_transport F E σ B n d X W M χX χW om r s r' s' hB hP.herm hP.skew hP.good hw
    1 h1 k hk1 T (fun f => hA f) (fun f => hT₂ f) u hu f _ hf
  exact (GlobalTheory.ThK.EvAt0.PolEv.actsD_iff_dOp hB.std M u' hu' _ _).1 ht

end GlobalTheory.KInfComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjIdealIndicatorUnitBlockTranslateReadsWeilOpe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.BotSmallTransl

open GlobalTheory.PlaceModel GlobalTheory.LocReduction Formalism.IndefR.Fin.LevelGroupLemmas.Lat
open scoped TensorProduct

variable {D : D7}

theorem mul_finOne {z : Formalism.L2.Theta.AE D} (hz : infPart D z = 0) :
    z * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = z := by
  have h : finPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := rfl
  conv_lhs => rw [eq_lift_of_infPart z hz]
  rw [lift_mul, h, mul_one, ← eq_lift_of_infPart z hz]

theorem one_mem_AA (h : D.host.ccK = ⊤) : (1 : D.host.E) ∈ D.host.AA := by
  have h1 : (1 : D.host.E) ∈ D.host.AA0 := by
    refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  rwa [Host.AA, Host.ccE, h, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]

theorem single_mem {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : IsStdLat L) (j : Fin n) :
    (Pi.single j 1 : Fin n → D.host.E) ∈ L :=
  (h _).2 fun i => by
    by_cases hi : i = j
    · exact ⟨1, by rw [hi, Pi.single_eq_same]; rfl⟩
    · exact ⟨0, by rw [Pi.single_eq_of_ne hi]; rfl⟩

variable {S T : HSp D} {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem mem_latO_of_int (hc : D.host.ccK = ⊤) (hG : S.gram = 1) (hS : IsStdLat LS) (hT : IsStdLat LT) {t : WO S T}
    (h0 : ∀ i j, infPart D (t i j) = 0) (h1 : ∀ i j, finPart D (t i j) ∈ intAE D) :
    t ∈ latO S T LS LT fun _ => True := by
  have e : t = ∑ i, ∑ j, t i j • genL S T 1 1 (Pi.single j 1) (Pi.single i 1) := by
    ext k l
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, genL, Matrix.of_apply, hG]
    rw [Finset.sum_eq_single k, Finset.sum_eq_single l]
    · have : (1 : D.host.E) * (Pi.single k 1 : Fin T.rank → D.host.E) k *
          ∑ m, star ((Pi.single l 1 : Fin S.rank → D.host.E) m) * (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) m l = 1 := by
        simp [Matrix.one_apply]
      rw [this, mul_finOne (h0 k l)]
    · intro j _ hj
      have : (1 : D.host.E) * (Pi.single k 1 : Fin T.rank → D.host.E) k *
          ∑ m, star ((Pi.single j 1 : Fin S.rank → D.host.E) m) * (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) m l = 0 := by
        simp [Matrix.one_apply, Pi.single_eq_of_ne hj.symm]
      rw [this, TensorProduct.tmul_zero, mul_zero]
    · exact fun h => (h (Finset.mem_univ _)).elim
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Pi.single_eq_of_ne hi.symm, mul_zero, zero_mul, TensorProduct.tmul_zero, mul_zero]
    · exact fun h => (h (Finset.mem_univ _)).elim
  rw [e]
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ => smul_mem_latAll (h1 i j) ?_
  exact genL_mem (fun v => by rw [map_one]; exact one_mem _) (one_mem_AA hc) (single_mem hS j) (single_mem hT i)

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem heis_off (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) {vac : WO S T → ℂ} (hv : IsThetaFunO ψ S T vac)
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm)
    (hfix : ∀ u ∈ latO S T LS LT fun _ => True, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u vac = vac)
    {u : WO S T} (h1 : ∀ x, IsHalf (cA D e) x → symplO S T u x = 0)
    (h2 : ∀ x, IsHalf (cA D (cA D e)) x → symplO S T u x = 0) {c : ℂ} (hc : c ≠ 0) (hu : heisO ψ S T u vac = c • vac)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf (cA D e) (latO S T LS LT fun _ => True) Φ) :
    heisO ψ S T u (Tm Φ) = c • Tm Φ := by
  obtain ⟨T0, -, huniq, -⟩ := Formalism.IndefR.Fin.placeModelAtF D ψ hψ S T LS LT hS hT P e he vac hv hfix (cA D e) (Or.inr rfl)
  have ap : ∀ Φ, (c⁻¹ • (heisL S T ψ u ∘ₗ Tm)) Φ = c⁻¹ • heisO ψ S T u (Tm Φ) := fun _ => rfl
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac
      (c⁻¹ • (heisL S T ψ u ∘ₗ Tm)) := by
    refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ x hx => ?_, ?_⟩
    · rw [ap, ap, hTm.trans Φ hΦ x hx, heis_comm, h1 x hx, AddChar.map_zero_eq_one, one_smul, heis_smul]
    · rw [ap, ap, hTm.modul Φ hΦ x hx, heis_comm, h2 x hx, AddChar.map_zero_eq_one, one_smul, heis_smul]
    · rw [ap, hTm.vac, hu, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h := (huniq _ hT' Φ hΦ).trans (huniq _ hTm Φ hΦ).symm
  rw [ap] at h
  rw [← h, smul_smul, mul_inv_cancel₀ hc, one_smul, h]


set_option maxHeartbeats 1600000 in
theorem heis_model (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : Formalism.L2.Theta.AE D}
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) {vac : WO S T → ℂ} (hv : IsThetaFunO ψ S T vac)
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm)
    {w : WO S T} (hw : w ∈ latO S T LS LT fun _ => True) {c : ℂ} (hc : c ≠ 0) (hu : heisO ψ S T w vac = c • vac)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf (cA D e) (latO S T LS LT fun _ => True) Φ)
    (hsupp : ∀ t, Φ t ≠ 0 → t ∈ latO S T LS LT fun _ => True) :
    heisO ψ S T w (Tm Φ) = c • Tm fun t => Φ (t + cA D e • w) := by
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hec := he.2
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hLL := (lattice_facts (S := S) (T := T) hψ hS hT hcc hinf).1
  have hb : cA D (cA D e) = e := GlobalTheory.DualPairCheck.cA_cA e
  have hfix : ∀ u ∈ latO S T LS LT fun _ => True, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u vac = vac :=
    fun u hu h => h.elim (fun h => fix_conj hLL hTm hu (by rwa [hb])) fun h => fix_half hTm hu h
  have hA : IsHalf (cA D e) (cA D e • w) := isHalf_smul.2 (by rw [smul_smul, hcc])
  have hB : IsHalf e (e • w) := isHalf_smul.2 (by rw [smul_smul, hee])
  have hAL := GlobalTheory.PlaceModelSum.idem_smul_latO hcc hw
  have hBL := GlobalTheory.PlaceModelSum.idem_smul_latO hee hw
  have k : cA D (1 - cA D e - e) = 1 - e - cA D e := by rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, hb]
  have h1 : ∀ x : WO S T, IsHalf (cA D e) x → symplO S T ((1 - cA D e - e) • w) x = 0 := fun x hx => by
    have : (1 - e - cA D e) * cA D e = 0 := by linear_combination -hec - hcc
    rw [← isHalf_smul.1 hx, symplO_smul, k, smul_smul, this, zero_smul, symplO_zero_right]
  have h2 : ∀ x : WO S T, IsHalf e x → symplO S T ((1 - cA D e - e) • w) x = 0 := fun x hx => by
    have : (1 - e - cA D e) * e = 0 := by linear_combination -hec - hee
    rw [← isHalf_smul.1 hx, symplO_smul, k, smul_smul, this, zero_smul, symplO_zero_right]
  have hp : ψ (symplOH S T (cA D e • w) (e • w)) ≠ 0 := (AddChar.val_isUnit ψ _).ne_zero
  have dec : ∀ f, ψ (symplOH S T (cA D e • w) (e • w)) • heisO ψ S T w f =
      heisO ψ S T ((1 - cA D e - e) • w) (heisO ψ S T (cA D e • w) (heisO ψ S T (e • w) f)) := fun f => by
    have e1 : w = (1 - cA D e - e) • w + (cA D e • w + e • w) := by
      rw [← add_smul, ← add_smul, sub_sub, sub_add_cancel, one_smul]
    have e2 : heisO ψ S T (cA D e • w) (heisO ψ S T (e • w) f) =
        ψ (symplOH S T (cA D e • w) (e • w)) • heisO ψ S T (cA D e • w + e • w) f := heisL_heisL S T ψ _ _ f
    rw [e2, heis_smul, ← heis_add (by rw [symplO_add_right, h1 _ hA, h2 _ hB, add_zero]), ← e1]
  have hvu := dec vac
  rw [hfix _ hBL (Or.inl hB), hfix _ hAL (Or.inr hA), hu, smul_smul] at hvu
  have hoff := heis_off hψ hS hT he hv hTm hfix h1 (by rwa [hb]) (mul_ne_zero hp hc) hvu.symm hΦ
  have hm : heisO ψ S T (e • w) (Tm Φ) = Tm Φ := by
    rw [← hTm.modul Φ hΦ _ (by rwa [hb])]
    congr 1
    funext t
    by_cases ht : Φ t = 0
    · rw [ht, mul_zero]
    · rw [hLL t (hsupp t ht) (hΦ.1 t ht) _ hBL (by rwa [hb]), one_mul]
  have hF := dec (Tm Φ)
  rw [hm, heis_comm, h1 _ hA, AddChar.map_zero_eq_one, one_smul, hoff, heis_smul, ← hTm.trans Φ hΦ _ hA, mul_smul] at hF
  exact smul_right_injective _ hp hF


set_option maxHeartbeats 1600000 in
theorem reads_transl : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
    D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 →
    ∀ (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsStdLat LS → IsStdLat LT → IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    IsSBHalf (cA D e) (latO S T LS LT fun _ => True) (cosetFn (cA D e) (D.host.conj • modul P c) (0 : WO S T)) →
    ∀ (κ : ℂ) (e0 : VC D a d → ℂ) (vac : WO S T → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) →
    Reads ψ θ hS hT ⊤ δ 1 (κ • e0) vac → IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) vac →
    ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm →
    ∀ (G : VC D a d → ℂ) (o : ℕ), Reads ψ θ hS hT ⊤ δ 1 G (Tm (cosetFn (cA D e) (D.host.conj • modul P c) 0)) →
    ∃ ζ : ℂ, IsRootOne ζ ∧ Reads ψ θ hS hT ⊤ δ 1 (ζ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d)) G)
      (Tm (cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o))) := by
  intro D ψ θ S T a d hS hT δ hcc hset LS LT hLS hLT hSd hTd e P c hge hSB κ e0 vac he0 hrd _ Tm hTm G o hG
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hge.1)
  set x := pt D (tor0 D ⊤ δ) δ (unitBlock D o a d) with hx
  have hph : wdPh D (tor0 D ⊤ δ) x ≠ 0 := Complex.exp_ne_zero _
  have hW : ∀ F, Wd D (tor0 D ⊤ δ) x F = wdPh D (tor0 D ⊤ δ) x • U D (tor0 D ⊤ δ) x F := fun _ => rfl
  have hfix : Wd D (tor0 D ⊤ δ) x e0 = e0 :=
    GlobalTheory.NormSum.VacMove.wd_fix (GlobalTheory.InducedType.induced_type D).1 hset.crv
      (GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D _) (GlobalTheory.NormSum.VacMove.moves_one D _)) he0
      (pt_unitBlock_mem δ o a d)
  have hU : U D (tor0 D ⊤ δ) x (κ • e0) = (wdPh D (tor0 D ⊤ δ) x)⁻¹ • κ • e0 := by
    have e1 : U D (tor0 D ⊤ δ) x (κ • e0) = κ • U D (tor0 D ⊤ δ) x e0 := by
      funext z
      simp only [U, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [e1, smul_comm]
    conv_rhs => rw [← hfix, hW, smul_smul _ (wdPh D _ x), inv_mul_cancel₀ hph, one_smul]
  have hvac : heisO ψ S T (finPt hS hT 1 (unitBlock D o a d)) vac = (wdPh D (tor0 D ⊤ δ) x)⁻¹ • vac := by
    have h := heisO_finPt_reads ψ θ S T hS hT ⊤ δ 1 hset _ _ hrd (unitBlock D o a d)
    rw [← hx, hU] at h
    exact h.unique (hrd.smul _)
  have hent : ∀ i j, finPt hS hT 1 (unitBlock D o a d) i j =
      if i.1 = o + j.1 then -(pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) else 0 := fun i j => by
    show pairA D.host.F 0 1 ⊗ₜ[D.host.F] (-((1 : D.host.E)⁻¹ * if i.1 = o + j.1 then 1 else 0)) = _
    split_ifs
    · rw [inv_one, mul_one, TensorProduct.tmul_neg]
    · rw [mul_zero, neg_zero, TensorProduct.tmul_zero]
  have hw : finPt hS hT 1 (unitBlock D o a d) ∈ latO S T LS LT fun _ => True := by
    refine mem_latO_of_int hcc hset.gS hLS hLT (fun i j => congrFun (congrFun (GlobalTheory.VacUnique.finRat_inf S T _) i) j)
      fun i j => ?_
    rw [hent]
    split_ifs
    · have h : finPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := rfl
      rw [RingHom.map_neg, h]
      exact neg_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (mul_one _))
    · rw [RingHom.map_zero]
      exact zero_mem _
  have hsupp : ∀ t : WO S T, cosetFn (cA D e) (D.host.conj • modul P c) 0 t ≠ 0 → t ∈ latO S T LS LT fun _ => True := by
    intro t ht
    have h : IsHalf (cA D e) t ∧ ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (D.host.conj • modul P c) (toEAf D (t i j - (0 : WO S T) i j)) := by
      by_contra h
      exact ht (if_neg h)
    refine mem_latO_of_int hcc hset.gS hLS hLT (fun i j => ?_) fun i j => GlobalTheory.PlaceVec.finPart_mem_intAE ?_
    · rw [← h.1 i j, RingHom.map_mul, hinf, zero_mul]
    · obtain ⟨h1, -⟩ := h.2 i j
      rwa [Matrix.zero_apply, sub_zero] at h1
  have hmod := heis_model hset.std hSd hTd hge.1 hrd.1 hTm hw (inv_ne_zero hph) hvac hSB hsupp
  have hcc' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self hge.1]
  have hA : ∀ i j, (cA D e • finPt hS hT 1 (unitBlock D o a d)) i j = -unitPt S T (cA D e) o i j := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, hent, unitPt]
    split_ifs
    · rw [mul_neg, mul_finOne hinf]
    · rw [mul_zero, neg_zero]
  have hΦ : (fun t => cosetFn (cA D e) (D.host.conj • modul P c) (0 : WO S T) (t + cA D e • finPt hS hT 1 (unitBlock D o a d))) =
      cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) := by
    funext t
    refine if_congr (and_congr ?_ (forall_congr' fun i => forall_congr' fun j => ?_)) rfl rfl
    · rw [isHalf_smul, isHalf_smul, smul_add, smul_smul, hcc', add_left_inj]
    · rw [Matrix.add_apply, hA, Matrix.zero_apply, sub_zero, ← sub_eq_add_neg]
  have h := (heisO_finPt_reads ψ θ S T hS hT ⊤ δ 1 hset _ _ hG (unitBlock D o a d)).smul (wdPh D (tor0 D ⊤ δ) x)
  rw [hmod, hΦ, smul_smul, mul_inv_cancel₀ hph, one_smul] at h
  exact ⟨1, IsRootOne.one, by rw [one_smul]; exact h⟩

end GlobalTheory.BotSmallTransl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateCharactersEmbeddingsOfCharacterisation
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.GalLift.overK_iff_good_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ ↔ GoodEmb T.Q.c (res T σ) :=
  GlobalTheory.GalLift.overK_iff_good_ofFive

theorem GlobalTheory.EtaValues.etaVals_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R := by
  classical
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ P e he x hx
  have htie := hR.fam.tie
  obtain ⟨_, _, _, hT⟩ := htie
  have hok := hT.ok A.μ0
  have h := GlobalTheory.EtaValues.hv_mem_host D R.C.eta R.C.isEta (R.Sb ∪ R.Q A.μ0) (fun v hs => by
    rw [Finset.coe_union] at hs
    obtain ⟨Q, rfl⟩ := hR.fam.pl_onto v (GlobalTheory.EtaValues.splitOff_mono hs Set.subset_union_left)
    exact ⟨_, (hR.fam.etaVal Q ((hok Q).2 hs)).trans (GlobalTheory.EtaValues.valTw_eq _ _)⟩) P
  obtain ⟨y, hy⟩ := h
  refine ⟨y, hy.trans ?_⟩
  rw [hR.lev.eta.2 P e he _ x hx]
  simp [GlobalTheory.EtaValues.hv, Formalism.L2.Host.HChar.val, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem GlobalTheory.EtaConjExist.exists_isEtaConj_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ η', IsEtaConj σ R.eta η' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ hV σ hσ
  refine GlobalTheory.EtaConjExist.exists_conj R.eta R.C.eta hR.lev.eta R.C.isEta (fun P => ?_) σ hσ
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨y, hy⟩ := hV P e he (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl
  refine ⟨y, hy.trans ?_⟩
  rw [hR.lev.eta.2 P e he _ (Formalism.L2.JoinChr.locU he.1 (Formalism.L2.Host.unif P)) rfl]
  simp [Formalism.L2.Host.HChar.val, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ η', IsEtaConj σ R.eta η' → ResEta D η' 1 ∧ ∀ ρ, HasInfExp D η' ρ (1 / 2) :=
  GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_ofFive

theorem GlobalTheory.GalLift.hypConj_of_chars_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), Function.Bijective (lab (D := D) σ) → (∀ ρ, labE σ (lab σ ρ) = tauE D ρ) → logHookSum i (lab σ) = logHookSum i id ∧ ∀ (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → ResEta D η' 1 → (∀ ρ, HasInfExp D η' ρ (1 / 2)) → HypConj R i σ μ' η' :=
  GlobalTheory.GalLift.hypConj_of_chars_ofFive

theorem GlobalTheory.ConjCharUnique.conjChar_unique_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), (∀ μ' μ'', ChiAt R i σ μ' → ChiAt R i σ μ'' → μ' = μ'') ∧ ∀ η' η'', IsEtaConj σ R.eta η' → IsEtaConj σ R.eta η'' → η' = η'' :=
  GlobalTheory.ConjCharUnique.conjChar_unique_ofFive

theorem GlobalTheory.GalLift.ConjWeil.exists_conj_weil_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → HypConj R i σ μ' η' → ∃ ω, IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ μ' η' hμ hη hH
  have hV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  exact GlobalTheory.GalLift.ConjWeil.exists_of_datum (hR.thP.ωP i A.μ0) hμ.1 (GlobalTheory.GalLift.ConjWeil.hecke_mul_inv hμ.1 hη.1)
    (resEta_parity hH.mu_res ((GlobalTheory.GalLift.ConjWeil.even_im_hermitian_sub D.R).1.trans (congrArg (· % 2) hV.symm)))
    (resEta_parity (resEta_mul hH.mu_res (resEta_inv hH.eta_res))
      ((GlobalTheory.GalLift.ConjWeil.even_im_hermitian_sub D.R).2.trans (congrArg (· % 2) hW.symm)))

theorem GlobalTheory.GalLift.reading_base_injective_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → JUnif T R κw v₀ → Function.Injective ((R.FW i).j (sg0 D A)) := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ _ fw i hev hinj hu
  have hg : GoodEmb T.Q.c (res T (sg0 D A)) := base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := fw.laws.spaceW _ (inR i) _ hg
  have h1 := fw.jK_eq hev hinj hg hV
  have h2 : ∀ f, fw.jK i (sg0 D A) f = (1 : ℂ) • jTop T R κw v₀ i (sg0 D A) f := fun f =>
    (LinearMap.congr_fun h1 f).trans (one_smul ℂ _).symm
  have h3 := GlobalTheory.TiedUnif.indep_span (C := Cu T κw i) (R.FW i) (fw.ks i) (fw.e i) (sg0 D A) one_ne_zero h2
    (hu i _).1 (hu i _).2
  exact GlobalTheory.TiedUnif.injective_of_indep (W := fun σ => (R.HW i σ).H) _ h3.1

theorem GlobalTheory.GalLift.conjChars_five : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ ↔ GoodEmb T.Q.c (res T σ)) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), EtaVals R → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∃ η', IsEtaConj σ R.eta η') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ η', IsEtaConj σ R.eta η' → ResEta D η' 1 ∧ ∀ ρ, HasInfExp D η' ρ (1 / 2)) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), Function.Bijective (lab (D := D) σ) → (∀ ρ, labE σ (lab σ ρ) = tauE D ρ) → logHookSum i (lab σ) = logHookSum i id ∧ ∀ (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → ResEta D η' 1 → (∀ ρ, HasInfExp D η' ρ (1 / 2)) → HypConj R i σ μ' η') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), (∀ μ' μ'', ChiAt R i σ μ' → ChiAt R i σ μ'' → μ' = μ'') ∧ ∀ η' η'', IsEtaConj σ R.eta η' → IsEtaConj σ R.eta η'' → η' = η'') ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → HypConj R i σ μ' η' → ∃ ω, IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → JUnif T R κw v₀ → Function.Injective ((R.FW i).j (sg0 D A))) :=
  ⟨GlobalTheory.GalLift.overK_iff_good_five, GlobalTheory.EtaValues.etaVals_five, GlobalTheory.EtaConjExist.exists_isEtaConj_five,
    GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_five, GlobalTheory.GalLift.hypConj_of_chars_five,
    GlobalTheory.ConjCharUnique.conjChar_unique_five, GlobalTheory.GalLift.ConjWeil.exists_conj_weil_five,
    GlobalTheory.GalLift.reading_base_injective_five⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalTraceMultiplicityGiven
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

namespace GlobalTheory.MultEqTrace

def conjEquiv {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W)
    (Φ Φ₀ : G ≃* H) (b : G) (hb : ∀ g, Φ g = Φ₀ (b * g * b⁻¹)) :
    Representation.Equiv (σ.comp Φ.symm.toMonoidHom : Representation ℂ H W)
      (σ.comp Φ₀.symm.toMonoidHom : Representation ℂ H W) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinear (σ b) (σ b⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl))
    fun h => by
      have e : Φ.symm h = b⁻¹ * Φ₀.symm h * b := by
        apply Φ.injective
        rw [Φ.apply_symm_apply, hb]
        simp [mul_assoc]
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply, e]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group

end GlobalTheory.MultEqTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeCorrespondingLatticesStatement
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_correspondingLattices : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type} [Fintype D] [Fintype D₂], IsLocIso j → ∀ (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}, LatCorr j cD Λ Λ₂ → LatCorr j cD (dualLat Λ) (dualLat Λ₂) := by
  first | exact @GlobalTheory.PureMatch.Transport.dualLat_latCorr | exact GlobalTheory.PureMatch.Transport.dualLat_latCorr | (intros; apply GlobalTheory.PureMatch.Transport.dualLat_latCorr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualL6OfLowerBound
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop

namespace GlobalTheory.Fc.Ind

def lowScalarPt (C CH : ℝ) : PtP := fun _ _ _ p => (p.S true).L6 (p.N C CH)

end GlobalTheory.Fc.Ind

end
end

