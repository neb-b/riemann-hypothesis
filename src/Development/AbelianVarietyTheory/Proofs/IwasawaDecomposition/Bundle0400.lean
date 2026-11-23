module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerLiftModNatIntegralAdeleTensor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftModG

theorem exists_lift_mod_g : ∀ (D : D7) (X : HidaSetting D) (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F), s ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E → ∃ α : 𝓞 D.host.E, ZMod' X.B.I X.B.g (s - Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E))) := by
  intro D X s hs
  have hg : X.B.g ≠ 0 := by
    rw [X.g_eq]; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  set I : Ideal (𝓞 X.B.I.E) := Ideal.span {((X.B.g : ℕ) : 𝓞 X.B.I.E)} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg
  obtain ⟨q, hq⟩ := cmpS_surj (F := X.B.I.F) I hI0 (Ideal.Quotient.mk _ ⟨s, hs⟩)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  have h1 : Ideal.Quotient.mk (idS X.B.I.F I) (oToS X.B.I.F X.B.I.E a) = Ideal.Quotient.mk _ ⟨s, hs⟩ := hq
  rw [Ideal.Quotient.eq] at h1
  have h2 : (⟨s, hs⟩ - oToS X.B.I.F X.B.I.E a) ∈ Ideal.span {oToS X.B.I.F X.B.I.E ((X.B.g : ℕ) : 𝓞 X.B.I.E)} := by
    have := (Ideal.neg_mem_iff _).2 h1
    rw [neg_sub] at this
    simpa [idS, hI, Ideal.map_span] using this
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h2
  refine ⟨RingOfIntegers.mapRingEquiv X.ιE a, t, t.2, ?_⟩
  have e1 : X.ιE.symm ((RingOfIntegers.mapRingEquiv X.ιE a : 𝓞 D.host.E) : D.host.E) = (a : X.B.I.E) := by
    rw [RingOfIntegers.mapRingEquiv_apply]; exact X.ιE.symm_apply_apply _
  rw [e1]
  have := congrArg (fun y : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E => (y : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ht
  simp only [Subring.coe_mul, AddSubgroupClass.coe_sub, map_natCast, Subring.coe_natCast] at this
  rw [mul_comm] at this
  exact this.symm

end GlobalTheory.Mem.LiftModG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepChartsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_memberStep_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m), ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u I.mu0 i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), I.ReadsK l Z u I.mu0 i hi chOf K ∧ (∀ c, ((K (chOf c)).y ⟨c, rfl⟩).1 = I.yStd u i c) ∧ ((i = 0 ∨ i = B.R.m) → Nonempty (Unique Ch)) := by
  first | exact @GlobalTheory.Mem.Col2.MemChart.exists_charts | exact GlobalTheory.Mem.Col2.MemChart.exists_charts | (intros; apply GlobalTheory.Mem.Col2.MemChart.exists_charts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameGeneratorsGreenCuspidalLabelling
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.TameGrp

theorem isGenSys_gen {g : ℕ} [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) : IsGenSys L.gen := by
  intro d hd
  refine ⟨L.gen_order d hd, fun d' hdd hd' => ?_⟩
  obtain ⟨e, rfl⟩ := hdd
  have he : 0 < e := Nat.pos_of_mul_pos_left hd'
  exact L.gen_norm d e hd he

theorem prod_rootsBar_X_sub_one_pow {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (n : ℕ) :
    ((Formalism.CyclotomicNorms.rootsBar ((X - 1 : (ZMod g)[X]) ^ n)).map fun x => X - Polynomial.C (t x)).prod = (X - 1 : ℂ[X]) ^ n := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, Polynomial.roots_pow,
    ← Polynomial.C_1, Polynomial.roots_X_sub_C, Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.map_singleton,
    Multiset.prod_singleton, map_one, Polynomial.C_1]


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_tame_generators_cuspidal_labelling : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : Formalism.L2.Host.CharFrame D), (∀ j g, ∃ z : ℤ, Formalism.L2.Host.eExp D j g = z) → GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W → ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk), IsEmpty L.nd.Loc ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∃ Gs : GrpSide (setK D L hZ hη), ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Gs.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ ChiTOk (setK D L hZ hη) (cfK L hZ hη cf) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) := by
  intro hG _ D hE cf _ hT
  haveI : IsEmpty D.nd.Loc := hE

  have htame : ∀ k (v : D.nd.PlG k), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k),
        ∃ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
          TameGenAt (D.nd.plOm.1 (D.naut.plGw k v)) σ ∧
            TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ σ (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen := by
    intro k v
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    haveI := D.nd.acOm
    exact GlobalTheory.T.exists_coupled_tame_inertia_generator D.host.E D.nd.Om (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.nd.plOm.2 _)
      (D.host.g k) (D.naut.plGw_over k v)
      (Formalism.MainNotions.Gaps.LevGap.natCast_notMem_sq_of_split _ (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v))
      _ (isGenSys_gen _)
  choose kv tg tg_mem tg_gen tg_coup using htame

  let N1 := ndLab D.nd D.nd.lab D.nd.lab_monic
  haveI : IsEmpty N1.Loc := hE
  let A : NAut N1 := GlobalTheory.Mem.GaloisStage.nAut N1 D.naut.plGw D.naut.plGw_over D.naut.plGw_inj D.naut.plGw_nconj
  obtain ⟨C⟩ := GlobalTheory.MemN.nonempty_nbc_of_isEmpty_loc _ _ _ N1 A hE
  have hl1 : ∀ k v (L : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) L).natDegree = A.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.inePol L (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar (A.items₂ k (A.plGw k v) L)).map fun x => X - Polynomial.C (D.ntypes.teichC k x)).prod :=
    fun k v L _ => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      (prod_rootsBar_X_sub_one_pow (D.ntypes.teichC k) _).symm
  let D1 := setAut D hE D.nd.lab D.nd.lab_monic A C D.ntypes.tg_mem D.ntypes.tg_gen hl1
  let X1 : NTypes D1.naut :=
    { D1.ntypes with
      tg := tg
      tg_mem := tg_mem
      tg_gen := tg_gen
      heckeLoc_gamma_places := fun i => hE.elim i
      inertiaCharpoly_type := fun k v L _ => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        (prod_rootsBar_X_sub_one_pow (D.ntypes.teichC k) _).symm
      chiT_tg := fun i => hE.elim i }
  let D2 := setTy D1 hE X1 D1.nStage_trivialCharacter_compat D1.nStage_trivialCharacter_coeff_eq
  let L : Lay0 D := lay0 D2
  have hZ : L.ZOk := ⟨fun i => hE.elim i, fun i => hE.elim i⟩
  have hη : L.EtaOk := D.etaJ_tie
  refine ⟨L, hZ, hη, hE, ⟨hT.pl, hT.teich, hT.chi, hT.ser⟩, rfl, HEq.rfl, HEq.rfl, HEq.rfl, ?_, ?_, rfl,
    HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  · have hteich := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      _root_.GlobalTheory.TeichPlace.exists_place_isTeich (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
    choose tA tκ hTe using hteich
    have hlab : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k))
          (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen (isGenSys_gen _)),
          Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧
            ∀ f, D.ntypes.eSer k f = eSerO O D.R.r f := by
      intro k
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      obtain ⟨O, hO1, hO2, hO3⟩ := _root_.GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel (ZMod (D.host.g k)) _
        (_root_.GlobalTheory.GreenParam.cuspParam_of_green hG (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
          (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen (isGenSys_gen _))
      have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
      exact ⟨O, hO1, hO2, fun f => (hT.ser k f).trans
        (_root_.GlobalTheory.SerCmp.eSerC_eq_eSerO hG _ _ _ _ _ (hT.teich k) O hO3 D.R.r f hr)⟩
    choose O hOe hOt hOs using hlab
    exact ⟨{ tA := tA, tκ := tκ, teichC_def := hTe
             ζ := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen
             ζ_gen := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; isGenSys_gen _
             O := O, eSer_def := hOs, kv := kv, tg_tame := tg_coup, O_equiv := hOe, O_tw := hOt }, fun _ => rfl⟩
  · intro k v j u hu hrep
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    haveI := D.nd.acOm
    have hP := D.nd.plOm.2 (D.naut.plGw k v)
    obtain ⟨a, ha, hua, hga⟩ := GlobalTheory.T.tameInertia_representative_residue D.host.E D.nd.Om (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v)
      (D.host.g k) hP (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v))
      (D.naut.plGw_over k v)
      (Formalism.MainNotions.Gaps.LevGap.natCast_notMem_sq_of_split _ (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v))
      (kv k v) (tg k v) _ (tg_mem k v) (isGenSys_gen _) (tg_coup k v)
      (fun A' hA' hσ hne => GlobalTheory.T.inertia_two_places_over_same_prime_trivial_meet D.host.E D.nd.Om _ _ _ hP hA' (tg k v) (tg_mem k v) hσ hne) u hrep
    refine ⟨(D.nd.chiT k v j)⁻¹, Or.inr rfl, ?_⟩
    change ((((cf.mu0 j).locK (D.naut.plGw k v)) (Units.mk0 (((show 𝓞 D.host.E from u) : 𝓞 D.host.E) : D.host.E) hu) : ℂˣ) : ℂ) =
      (D.ntypes.teichC k) ((algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)))
        (((D.nd.chiT k v j)⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)))
    rw [_root_.GlobalTheory.MuZeroCong.locK_eq_of_sub_mem cf.P cf.W _ _ _ (cf.isMu0 j) k _ (hT.pl k v) u hu a ha hua, hT.teich k, hT.chi k v j]
    have hlabel := (GlobalTheory.Mem.Top.isCharLab_omLab cf.W k).2 (ZMod.unitOfCoprime a ha) (by simpa using hga)
    have key : ∀ z : Formalism.CyclotomicNorms.Fbar (D.host.g k), z ≠ 0 →
        (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).teich z⁻¹ = ((GlobalTheory.Mem.TypePl.labDat (D.host.g k)).teich z)⁻¹ :=
      fun z hz => eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hz, map_one])
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hlabel, Units.val_inv_eq_inv_val, map_inv₀, key _ (by
      rw [Units.val_pow_eq_pow_val, map_pow]
      exact pow_ne_zero _ ((_root_.map_ne_zero _).2 (Units.ne_zero _))), Units.val_pow_eq_pow_val, map_pow, map_pow]

end GlobalTheory.HeightCounting.TameGrp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpDivMulEqStdAddCharMulOfCoprime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exp_two_pi_I_div_mul_eq_stdAddChar_mul (p q : ℕ) [NeZero p] [NeZero q] (hpq : Nat.Coprime p q) (T : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (T : ℂ) / ((p * q : ℕ) : ℂ)) =
      ZMod.stdAddChar (((q : ZMod p))⁻¹ * (T : ZMod p)) *
        ZMod.stdAddChar (((p : ZMod q))⁻¹ * (T : ZMod q)) := by
  set A : ℤ := Nat.gcdA q p
  set B : ℤ := Nat.gcdB q p
  have hb : (1 : ℤ) = (q : ℤ) * A + (p : ℤ) * B := by
    have h := Nat.gcd_eq_gcd_ab q p
    rw [Nat.Coprime.gcd_eq_one hpq.symm] at h
    simpa using h
  have hA : ((q : ZMod p))⁻¹ = ((A : ℤ) : ZMod p) := by
    apply ZMod.inv_eq_of_mul_eq_one
    have := congrArg (fun z : ℤ => (z : ZMod p)) hb
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, add_zero] at this
    exact this.symm
  have hB : ((p : ZMod q))⁻¹ = ((B : ℤ) : ZMod q) := by
    apply ZMod.inv_eq_of_mul_eq_one
    have := congrArg (fun z : ℤ => (z : ZMod q)) hb
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, zero_add] at this
    exact this.symm
  have e1 : ((q : ZMod p))⁻¹ * (T : ZMod p) = ((A * T : ℤ) : ZMod p) := by
    rw [hA]; push_cast; ring
  have e2 : ((p : ZMod q))⁻¹ * (T : ZMod q) = ((B * T : ℤ) : ZMod q) := by
    rw [hB]; push_cast; ring
  rw [e1, e2, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hbC : (1 : ℂ) = (q : ℂ) * (A : ℂ) + (p : ℂ) * (B : ℂ) := by exact_mod_cast hb
  push_cast
  field_simp
  linear_combination (T : ℂ) * hbC

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyConnectedOfAlgClosedInFunctionField
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

namespace GlobalTheory.GeomConnFn

theorem isConnected_preimage {F : Type} [Field F] [CharZero F] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp F)
    [LocallyOfFiniteType p]
    (h : ∀ a : X.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) a = 0) →
      a ∈ (GlobalTheory.Cartier.constFn p).range)
    (K : Type) [Field K] [Algebra F K] (U : X.Opens) (hU : IsAffineOpen U) (hx : genericPoint X ∈ U) :
    _root_.IsConnected
      (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap F K))) ⁻¹' (U : Set X)) := by
  let : Algebra F Γ(X, U) := (algX p U).toAlgebra
  let : Algebra F X.functionField := (GlobalTheory.Cartier.constFn p).toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType F Γ(X, U) := hft
  let j : Γ(X, U) →ₐ[F] X.functionField :=
    { GlobalTheory.Cartier.fnOf U hx with
      commutes' := fun a => RingHom.congr_fun (GlobalTheory.Cartier.fnOf_comp_algX p U hx) a }
  have : IsDomain (K ⊗[F] Γ(X, U)) :=
    GlobalTheory.GeomConn.isDomain_tensor j (GlobalTheory.Cartier.fnOf_injective U hx) (fun a ha => h a ha) K
  have : IsDomain (Γ(X, U) ⊗[F] K) := (Algebra.TensorProduct.comm F Γ(X, U) K).toMulEquiv.isDomain
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have h1 : IsIntegral (pullback (hU.fromSpec ≫ p) (Spec.map (CommRingCat.ofHom (algebraMap F K)))) := by
    rw [hg]
    exact IsIntegral.of_isIso (pullbackSpecIso F Γ(X, U) K).inv
  have h2 := IsIntegral.of_isIso
    (pullbackRightPullbackFstIso p (Spec.map (CommRingCat.ofHom (algebraMap F K))) hU.fromSpec).inv
  rw [← hU.range_fromSpec, ← Scheme.Pullback.range_snd]
  exact isConnected_range (Scheme.Hom.continuous _)

theorem geometricallyConnected_of_locallyOfFiniteType {F : Type} [Field F] [CharZero F] {X : Scheme.{0}}
    [IsIntegral X] (p : X ⟶ Sp F) [LocallyOfFiniteType p]
    (h : ∀ a : X.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) a = 0) →
      a ∈ (GlobalTheory.Cartier.constFn p).range) : GeometricallyConnected p := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.2 fun K _ _ => ?_⟩
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap F K))) :=
    ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  obtain ⟨x₀, hx₀⟩ := (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap F K)))).surjective (genericPoint X)
  refine connectedSpace_iff_univ.2 ⟨⟨x₀, trivial⟩, isPreconnected_of_forall x₀ fun y _ => ?_⟩
  obtain ⟨U, hU, hy, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (Opens.mem_top (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap F K))) y))
  have hg := GlobalTheory.Cartier.gen_mem hy
  refine ⟨_, Set.subset_univ _, ?_, hy, (isConnected_preimage p h K U hU hg).isPreconnected⟩
  rw [Set.mem_preimage, hx₀]
  exact hg

end GlobalTheory.GeomConnFn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianE0SymmetricFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar

theorem hA_e0_symVec : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (b : Fin D.R.rS) (j : Fin D.R.r), hA X.B.I (X.e0 b) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = 2 * D.R.rS + D.R.k - b.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X kv hg b j
  have hW : ∀ i, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 b) (GlobalTheory.Mem.SymFrame.epsW X (D.naut.plGw kv.1 kv.2) i)) := by
    intro i
    unfold GlobalTheory.Mem.SymFrame.epsW
    split_ifs
    · exact ((X.weightVectorsIntegral _).2.2 b).1
    · exact ((X.weightVectorsIntegral _).2.2 b).2.2.1
  refine wInt_of_zmod X kv.1 hg ?_
  have hb := b.2
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dite_eq_left h1, if_neg (by omega), sub_zero]; exact (X.gramIntegral _ _).1
  rw [dite_eq_right h1]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dite_eq_left h2, if_neg (by omega), sub_zero]; exact hW _
  rw [dite_eq_right h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dite_eq_left h4, if_neg (by omega), sub_zero]; exact (X.formsAtZero.2 b).1
  rw [dite_eq_right h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dite_eq_left h3]
    have h := (X.gramIntegral b ⟨2 * D.R.rS + D.R.k - j.1, by omega⟩).2.2
    by_cases e : j.1 = 2 * D.R.rS + D.R.k - b.1
    · rw [if_pos e]
      rwa [if_pos (Fin.ext (by simp only; omega))] at h
    · rw [if_neg e]
      rwa [if_neg (fun h' => e (by have := congrArg Fin.val h'; simp only at this; omega))] at h
  · rw [dite_eq_right h3, if_neg (by omega), sub_zero, hA_zero_right']
    exact ⟨0, zero_mem _, by simp⟩

end GlobalTheory.Mem.SymChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormMiddleSymmetricFrameNotOneAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section


open GlobalTheory.Mem.SymFrame GlobalTheory.Mem.SymChar in
theorem GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → sigA X.B.I X.ew - 1 ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) → ∀ (m : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bw m) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k - 1 - m.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X kv hg hEw hs m j
  have hm := m.2
  have hZ : ∀ c, ZMod' X.B.I X.B.g c → c ∈ wInt X (D.naut.plGw kv.1 kv.2) :=
    fun c hc => wInt_of_zmod X kv.1 hg hc
  have hS : ∀ v, ZMod' X.B.I X.B.g (hA X.B.I v (X.bw m)) → hA X.B.I (X.bw m) v ∈ wInt X (D.naut.plGw kv.1 kv.2) := by
    intro v hv
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I v (X.bw m)]
    exact hZ _ (Formalism.L2.SG.Pf.unitaryCongruence.Z_sig _ _ hv)
  have hB : ∀ l : Fin D.R.k, hA X.B.I (X.bw m) (X.bwd l) - (if l = m then 1 else 0) ∈
      wInt X (D.naut.plGw kv.1 kv.2) := by
    intro l
    have h := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig _ _ (X.bw_dual l m)
    rw [map_sub, apply_ite (sigA X.B.I), map_zero] at h
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I (X.bwd l) (X.bw m)]
    by_cases hl : l = m
    · simp only [hl, if_true] at h ⊢
      have := add_mem (hZ _ h) hs
      convert this using 1
      ring
    · simp only [hl, if_false] at h ⊢
      simpa using hZ _ h
  unfold symVec epsW
  rw [if_neg hEw]
  unfold GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dite_eq_left h1, if_neg (by omega), sub_zero]
    exact hS _ ((X.weightVectorsIntegral m).2.2 ⟨j.1, h1⟩).1
  rw [dite_eq_right h1]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dite_eq_left h2]
    have e : ((Fin.rev (⟨j.1 - D.R.rS, by omega⟩ : Fin D.R.k)) = m) ↔ j.val = D.R.rS + D.R.k - 1 - m.val := by
      rw [Fin.ext_iff, Fin.val_rev]; simp only [Fin.val_mk]; constructor <;> intro h <;> omega
    have := hB (Fin.rev ⟨j.1 - D.R.rS, by omega⟩)
    by_cases h' : j.val = D.R.rS + D.R.k - 1 - m.val
    · rw [if_pos h']; rwa [if_pos (e.2 h')] at this
    · rw [if_neg h']; rwa [if_neg (fun hh => h' (e.1 hh))] at this
  rw [dite_eq_right h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dite_eq_left h4, if_neg (by omega), sub_zero]
    exact hS _ (X.weightVectorsIntegral m).1
  rw [dite_eq_right h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dite_eq_left h3, if_neg (by omega), sub_zero]
    exact hS _ ((X.weightVectorsIntegral m).2.2 _).2.1
  · rw [dite_eq_right h3, if_neg (by omega), sub_zero, hA_zero_right']
    exact zero_mem _

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianZ0SymmetricFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf

namespace GlobalTheory.Mem.SymChar.ZPair
open GlobalTheory.Mem.SymFrame

theorem rank_eq' (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  unfold Ranks.r Ranks.rS
  obtain ⟨t, ht⟩ := D.R.m_even
  have := D.R.two_le_m
  omega

theorem zmod_hA_z0_symVec (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (j : Fin D.R.r) :
    ZMod' X.B.I X.B.g (hA X.B.I X.z0 (symVec X w j) - (if j.val = D.R.rS + D.R.k then -1 else 0)) := by
  have hr := rank_eq' D
  have hj := j.2
  unfold symVec GlobalTheory.SeeConjRead.flagV epsW
  split_ifs
  · exfalso; omega
  · rw [sub_zero, unitaryCongruence.hA_symm]; exact unitaryCongruence.Z_sig _ _ (X.formsAtZero.2 _).1
  · exfalso; omega
  · rw [sub_zero]; exact (X.weightVectorsIntegral _).1
  · exfalso; omega
  · rw [sub_zero]; exact (X.weightVectorsIntegral _).2.1
  · rw [sub_neg_eq_add]; exact X.formsAtZero.1
  · rw [sub_zero, unitaryCongruence.hA_symm]; exact unitaryCongruence.Z_sig _ _ (X.formsAtZero.2 _).2
  · exfalso; omega

theorem hA_z0_symVec : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (j : Fin D.R.r), hA X.B.I X.z0 (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k then -1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X kv hg j
  exact GlobalTheory.Mem.SymChar.wInt_of_zmod X kv.1 hg (zmod_hA_z0_symVec D X _ j)

end GlobalTheory.Mem.SymChar.ZPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharEqOneInertPrimeOffLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelChar_eq_one_inert_prime_off_level : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (j : (LiftBrg.envL X I hX U Xg tr L cV i t).lev.J),
    IsLocElt (Vc X.toD7 i) (q.1.1 : PlI X.B px).1 (j : Bridge.Gf (Vc X.toD7 i)) → (LiftBrg.envL X I hX U Xg tr L cV i t).lev.χ j = 1 := by
  first | exact @GlobalTheory.Mem.R3.LiftInertChi.levChi_eq_one_of_isLocElt | exact GlobalTheory.Mem.R3.LiftInertChi.levChi_eq_one_of_isLocElt | (intros; apply GlobalTheory.Mem.R3.LiftInertChi.levChi_eq_one_of_isLocElt <;> assumption)
end

