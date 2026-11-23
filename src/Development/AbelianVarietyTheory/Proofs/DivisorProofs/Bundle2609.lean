module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1638
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndicatorReadsNormPowerUnitVector
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

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SkewLevel

theorem sum_section {M Q : Type} [AddCommGroup M] [AddCommGroup Q] [Fintype Q] (π : M →+ Q) (Z : Q → M) (hZ : ∀ q, π (Z q) = q)
    (χ : M → ℂ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (hker : ∀ x, π x = 0 → χ x = 1) {m : M} (hm : χ m ≠ 1) :
    ∑ q, χ (Z q) = 0 := by
  have h1 : ∀ q, χ (Z (q + π m)) = χ m * χ (Z q) := fun q => by
    have e : Z (q + π m) = (Z (q + π m) - (m + Z q)) + (m + Z q) := by abel
    rw [e, hadd, hker _ (by rw [map_sub, map_add (f := _), hZ, hZ]; abel), one_mul, hadd]
  have h2 : ∑ q, χ (Z q) = χ m * ∑ q, χ (Z q) := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight (π m)) (fun q => χ (Z q))]
    exact Finset.sum_congr rfl fun q _ => h1 q
  have h3 : (χ m - 1) * ∑ q, χ (Z q) = 0 := by linear_combination -h2
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hm)

variable {D : D7}

theorem pt_mem_iff {δ : ℂ} {a d : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin d → D.host.E)) (y : VC D a d) :
    y ∈ La D (tor0 D ⊤ δ) L L' ↔ ∃ z ∈ YYl D L L', GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d z = y := by
  constructor
  · intro hy
    have h : La D (tor0 D ⊤ δ) L L' ≤ (YYl D L L').toAddSubgroup.map (GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d) := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨w, hw, A, hA, rfl⟩
      obtain ⟨c, -, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ w).1 hw
      exact ⟨((c : D.host.K) : D.host.E) • A, (YYl D L L').smul_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) hA,
        GlobalTheory.ThetaLatticePoints.ptHom_smul D ⊤ δ a d c A⟩
    exact h hy
  · rintro ⟨z, hz, rfl⟩
    exact AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, z, hz, rfl⟩

theorem reads_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d}
    {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E} {ι : Type} (s : Finset ι) (G : ι → VC D a d → ℂ) (f : ι → WO S T → ℂ)
    (h : ∀ i, Reads ψ θ hS hT cc δ r (G i) (f i)) : Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i).add ih

theorem reads_level : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
    D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 →
    ∀ (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsStdLat LS → IsStdLat LT → IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    IsSBHalf (cA D e) (latO S T LS LT fun _ => True) (cosetFn (cA D e) (D.host.conj • modul P c) (0 : WO S T)) →
    ∀ (κ : ℂ) (e0 : VC D a d → ℂ) (vac : WO S T → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) →
    Reads ψ θ hS hT ⊤ δ 1 (κ • e0) vac → IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) vac →
    ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm →
    ∃ ζ : ℂ, IsRootOne ζ ∧ Reads ψ θ hS hT ⊤ δ 1
      ((κ * ζ) • ((Real.sqrt ((Ideal.absNorm (D.host.conj • modul P c) : ℝ) ^ (a * d)) : ℂ))⁻¹ •
        Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • modul P c) d)) e0)
      (Tm (cosetFn (cA D e) (D.host.conj • modul P c) 0)) := by
  intro D ψ θ S T a d hS hT δ hcc hset LS LT hLS hLT hSd hTd e P c he _ κ e0 vac he0 hread hvac Tm hTm
  subst hS hT
  have hc := hset.crv
  have hψ := hset.std
  have gS := hset.gS
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have hne := conj_ne_bot P c
  have hidx := GlobalTheory.SkewIndex.index_inter_skew D δ hc _ hne
    (by rw [conj_conj_smul]; exact isCoprime_conj he.1 c) S.rank T.rank
  have hN0 : 0 < Ideal.absNorm (D.host.conj • modul P c) := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hne)
  have kp : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank)) :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacMove.sd_of_moves (GlobalTheory.NormSum.VacMove.moves_one D S.rank),
      GlobalTheory.SkewLatSD.skewLat_sd D _ T.rank hne, rfl⟩
  obtain ⟨-, -, hIm, -, -, -, hq⟩ := GlobalTheory.ThetaLine.theta_line D hG ⊤ δ hc S.rank T.rank _ kp
  have hrep := GlobalTheory.ThetaConj.repInd_of_thSp D _ _ _ (La0 D (tor0 D ⊤ δ) S.rank T.rank) _ e0 hq
    (fun x hx y hy => hIm _ (GlobalTheory.GalTheta.weilElement_smul_mem_thetaLattice D hG ⊤ δ _ _ x hx) y hy) he0
  have hmem0 := pt_mem_iff (δ := δ) (stdL D S.rank) (stdL D T.rank)
  have hmem2 := pt_mem_iff (δ := δ) (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank)
  have hinj := GlobalTheory.ThetaLatticePoints.ptHom_injective D ⊤ (delta_ne_zero hc) S.rank T.rank
  have hkI := fun t ht htΛ hk => inId_of_kill hψ hcc gS hLS hLT hSd hTd he c (t := t) ht htΛ hk
  have hsm := fun z hz => smul_finRat_mem hψ hcc gS hLS hLT hSd hTd P c (z := z) hz
  have hhalf := fun z hz => heisO_eq_half hψ hcc gS hLS hLT hSd hTd he.1 c hvac (z := z) hz
  have hsk := fun z hz m hm => smul_skew_mem (conj_conj_ne_bot P c) (a := S.rank) (d := T.rank) (z := z) hz (m := m) hm
  rw [conj_conj_smul] at hsk
  set I := D.host.conj • modul P c with hI
  set p := GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ S.rank T.rank with hp
  set Y := YYl D (stdL D S.rank) (skewLat D I T.rank) with hY
  set A₁ := La0 D (tor0 D ⊤ δ) S.rank T.rank with hA₁
  set A₂ := La D (tor0 D ⊤ δ) (stdL D S.rank) (skewLat D I T.rank) with hA₂
  haveI : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := AddSubgroup.index_ne_zero_iff_finite.1 (by rw [hidx]; positivity)
  letI : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := Fintype.ofFinite _
  have hcard : Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂) = Ideal.absNorm I ^ (S.rank * T.rank) := by
    rw [← hidx, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
  obtain ⟨m, hm, u, hmu⟩ := exists_add_two he c
  have hz : ∀ q : A₂ ⧸ A₁.addSubgroupOf A₂, ∃ z ∈ Y, ((Quotient.out q : A₂) : VC D S.rank T.rank) - p (2 • z) ∈ A₁ := fun q => by
    obtain ⟨z, hz, ez⟩ := (hmem2 _).1 (Quotient.out q).2
    refine ⟨u • z, Y.smul_mem u hz, (hmem0 _).2 ⟨m • z, hsk z hz m hm, ?_⟩⟩
    rw [← ez, ← map_sub, two_nsmul, ← add_smul, ← mul_two, eq_sub_of_add_eq hmu, sub_smul, one_smul]
  choose z hzY hzq using hz
  have hp2 : ∀ w ∈ Y, p w ∈ A₂ := fun w hw => (hmem2 _).2 ⟨w, hw, rfl⟩
  let π : Y →+ A₂ ⧸ A₁.addSubgroupOf A₂ := (QuotientAddGroup.mk' _).comp
    ((p.comp Y.toAddSubgroup.subtype).codRestrict A₂ fun w => hp2 w w.2)
  have hπ : ∀ q, π ⟨2 • z q, nsmul_mem (hzY q) 2⟩ = q := fun q => by
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    refine QuotientAddGroup.eq.2 ?_
    rw [AddSubgroup.mem_addSubgroupOf, neg_add_eq_sub]
    exact hzq q
  have hπ0 : ∀ w : Y, π w = 0 → GlobalTheory.VacUnique.finRat S T (-w.1) ∈ latO S T LS LT (fun _ => True) := fun w hw => by
    obtain ⟨w', hw', ew⟩ := (hmem0 (p w.1)).1
      ((QuotientAddGroup.eq_zero_iff (N := A₁.addSubgroupOf A₂) (⟨p w.1, hp2 w w.2⟩ : A₂)).1 hw)
    rw [finRat_mem_iff hψ hcc gS hLS hLT hSd hTd, ← hinj ew]
    exact neg_mem hw'
  have hn : ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  have hfun : cosetFn (cA D e) I (0 : WO S T) = ∑ q, ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹ • fun t =>
      ψ (symplO S T t (e • GlobalTheory.VacUnique.finRat S T (2 • -z q))) * halfInd (cA D e) (latO S T LS LT fun _ => True) t := by
    funext t
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    simp only [cosetFn, halfInd, Matrix.zero_apply, sub_zero]
    by_cases h1 : t ∈ latO S T LS LT (fun _ => True) ∧ IsHalf (cA D e) t
    · have e1 : ∀ y, symplO S T t (e • y) = symplO S T t y := fun y => by
        rw [← cA_cA e, ← GlobalTheory.PlaceModel.symplO_smul, (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 h1.2)]
      simp only [e1]
      rw [if_pos h1, mul_one]
      by_cases h2 : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (t i j))
      · rw [if_pos ⟨h1.2, h2⟩, Finset.sum_congr rfl fun q _ =>
          kill_of_inId hψ hcc hLS hLT hSd hTd he h1.2 h2 (hsm _ (nsmul_mem (neg_mem (hzY q)) 2)),
          Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hn]
      · rw [if_neg fun h => h2 h.2]
        obtain ⟨w, hw, hw1⟩ : ∃ w ∈ Y, ψ (symplO S T t (GlobalTheory.VacUnique.finRat S T w)) ≠ 1 := by
          by_contra h
          push_neg at h
          exact h2 (hkI t h1.2 h1.1 h)
        have h3 := sum_section π (fun q => ⟨2 • z q, nsmul_mem (hzY q) 2⟩) hπ
          (fun w => ψ (symplO S T t (GlobalTheory.VacUnique.finRat S T (-w.1))))
          (fun x y => by
            rw [Submodule.coe_add, neg_add, map_add (f := _), GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul])
          (fun x hx => GlobalTheory.LatVac.char_sympl_eq_one hψ hSd hTd h1.1 (hπ0 x hx)) (m := ⟨-w, neg_mem hw⟩)
          (by simpa only [neg_neg] using hw1)
        simp only [smul_neg]
        rw [h3, mul_zero]
    · rw [if_neg h1, mul_zero, mul_zero, if_neg fun h => h1 ⟨(half_mem_iff hcc hLS hLT hSd hTd he t h.1).2 fun i j => (h.2 i j).1, h.1⟩]
  have hv : Tm (halfInd (cA D e) (latO S T LS LT fun _ => True)) = vac := by simpa using hTm.vac
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he.1
  have hTmΦ : Tm (cosetFn (cA D e) I 0) = ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹ •
      ∑ q, heisO ψ S T (finPt rfl rfl 1 (2 • z q)) vac := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfun, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e1 : finPt (rfl : S.rank = S.rank) (rfl : T.rank = T.rank) 1 (2 • z q) = GlobalTheory.VacUnique.finRat S T (2 • -z q) := by
      unfold finPt
      congr 1
      refine Matrix.ext fun i j => ?_
      simp
    rw [map_smul, hTm.modul _ (GlobalTheory.isSBHalf_halfInd _ _) _ (fun i j => by
      change cA D (cA D e) * (e * _) = e * _
      rw [cA_cA, ← mul_assoc, hee]), hv, hhalf _ (neg_mem (hzY q)), e1]
  have hR := (reads_sum Finset.univ _ _ fun q =>
    heisO_finPt_reads ψ θ S T rfl rfl ⊤ δ 1 hset _ _ hread (2 • z q)).smul ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹
  refine ⟨1, IsRootOne.one, ?_⟩
  rw [hTmΦ]
  convert hR using 1
  have hU : ∀ q : A₂ ⧸ A₁.addSubgroupOf A₂, ∀ y, al D (tor0 D ⊤ δ) ((Quotient.out q : A₂) : VC D S.rank T.rank) *
      U D (tor0 D ⊤ δ) ((Quotient.out q : A₂) : VC D S.rank T.rank) e0 y =
        U D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (2 • z q)) e0 y := fun q y => by
    have h1 := congrFun (hrep _ (Quotient.out q).2 _ (hp2 _ (nsmul_mem (hzY q) 2)) (hzq q)) y
    obtain ⟨k, hk⟩ := hq _ (hp2 _ (hzY q))
    have h2 : al D (tor0 D ⊤ δ) (p (2 • z q)) = 1 := by
      rw [GlobalTheory.ThetaConj.al_of_qH D _ _ (2 * (2 * k)) (by
        rw [map_nsmul, GlobalTheory.NormSum.Expand.qH_nsmul, hk]; push_cast; ring), zpow_mul]
      norm_num
    simp only [GlobalTheory.ThetaConj.aU, h2, one_mul] at h1
    exact h1
  have hs : ((Real.sqrt ((Ideal.absNorm I : ℝ) ^ (S.rank * T.rank)) : ℂ))⁻¹ *
      ((Real.sqrt (((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℝ)) : ℂ))⁻¹ =
        ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹ := by
    have h1 : (((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℝ)) = (Ideal.absNorm I : ℝ) ^ (S.rank * T.rank) := by
      push_cast; rfl
    rw [h1, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; rfl
  funext y
  simp only [Pi.smul_apply, smul_eq_mul, Iop, finsum_eq_sum_of_fintype, hidx, hU, Finset.sum_apply]
  rw [← hs]
  simp only [U, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

end GlobalTheory.SkewLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormLogAffForm
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

noncomputable section

namespace GlobalTheory.LogHermHess

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {ι : Type*} [Fintype ι]

def affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x : E) : ℂ :=
  ∑ i, ∑ j, (c i + L i x) * Q i j * (starRingEnd ℂ) (c j + L j x)

theorem hasFDerivAt_aff (c : ℂ) (L : E →L[ℂ] ℂ) (x : E) :
    HasFDerivAt (fun y => c + L y) L x := L.hasFDerivAt.const_add c

theorem contDiff_aff (c : ℂ) (L : E →L[ℂ] ℂ) : ContDiff ℝ 2 (fun y => c + L y) :=
  contDiff_const.add (L.restrictScalars ℝ).contDiff

theorem contDiff_conj_aff (c : ℂ) (L : E →L[ℂ] ℂ) :
    ContDiff ℝ 2 (fun y => (starRingEnd ℂ) (c + L y)) :=
  Complex.conjCLE.contDiff.comp (contDiff_aff c L)

theorem del_aff (c : ℂ) (L : E →L[ℂ] ℂ) (x v : E) : del (fun y => c + L y) x v = L v := by
  rw [del_eq_fderiv (hasFDerivAt_aff c L x).differentiableAt, (hasFDerivAt_aff c L x).fderiv]

theorem dbar_aff (c : ℂ) (L : E →L[ℂ] ℂ) (x v : E) : dbar (fun y => c + L y) x v = 0 := by
  rw [dbar_eq_zero (hasFDerivAt_aff c L x).differentiableAt]; rfl

theorem contDiff_term (c c' q : ℂ) (L L' : E →L[ℂ] ℂ) :
    ContDiff ℝ 2 (fun y => (c + L y) * q * (starRingEnd ℂ) (c' + L' y)) :=
  ((contDiff_aff c L).mul contDiff_const).mul (contDiff_conj_aff c' L')

theorem del_term (c c' q : ℂ) (L L' : E →L[ℂ] ℂ) (x v : E) :
    del (fun y => (c + L y) * q * (starRingEnd ℂ) (c' + L' y)) x v
      = L v * q * (starRingEnd ℂ) (c' + L' x) := by
  have h1 := (contDiff_aff c L).differentiable two_ne_zero x
  have h2 := (contDiff_conj_aff c' L').differentiable two_ne_zero x
  rw [del_mul (a := fun y => (c + L y) * q) (h1.mul_const q) h2,
    del_mul h1 (differentiableAt_const q), del_conj, dbar_aff, del_aff]
  simp

theorem dbar_term (c c' q : ℂ) (L L' : E →L[ℂ] ℂ) (x v : E) :
    dbar (fun y => (c + L y) * q * (starRingEnd ℂ) (c' + L' y)) x v
      = (c + L x) * q * (starRingEnd ℂ) (L' v) := by
  have h1 := (contDiff_aff c L).differentiable two_ne_zero x
  have h2 := (contDiff_conj_aff c' L').differentiable two_ne_zero x
  rw [dbar_mul (a := fun y => (c + L y) * q) (h1.mul_const q) h2,
    dbar_mul h1 (differentiableAt_const q), dbar_conj, dbar_aff, del_aff]
  simp

theorem contDiff_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) :
    ContDiff ℝ 2 (affForm Q c L) :=
  ContDiff.sum fun _ _ => ContDiff.sum fun _ _ => contDiff_term _ _ _ _ _

theorem del_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x v : E) :
    del (affForm Q c L) x v = ∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (c j + L j x) := by
  unfold affForm
  rw [del_sum fun i _ => (ContDiff.sum fun j _ =>
    contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [del_sum fun j _ =>
    (contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => del_term _ _ _ _ _ _ _

theorem dbar_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x v : E) :
    dbar (affForm Q c L) x v = ∑ i, ∑ j, (c i + L i x) * Q i j * (starRingEnd ℂ) (L j v) := by
  unfold affForm
  rw [dbar_sum fun i _ => (ContDiff.sum fun j _ =>
    contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dbar_sum fun j _ =>
    (contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => dbar_term _ _ _ _ _ _ _

theorem ddbar_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x v w : E) :
    ddbar (affForm Q c L) x v w = ∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (L j w) := by
  rw [ddbar_eq_del_dbar (contDiff_affForm Q c L).contDiffAt]
  have : (fun y => dbar (affForm Q c L) y w)
      = affForm Q c L ∘ id - affForm Q c L ∘ id + fun y => ∑ i, ∑ j,
        (c i + L i y) * Q i j * (starRingEnd ℂ) (L j w + (0 : E →L[ℂ] ℂ) y) := by
    funext y; simp [dbar_affForm]
  rw [this, sub_self, zero_add,
    del_sum fun i _ => (ContDiff.sum fun j _ =>
    contDiff_term (c i) (L j w) (Q i j) (L i) 0).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [del_sum fun j _ =>
    (contDiff_term (c i) (L j w) (Q i j) (L i) 0).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [del_term]; simp

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem ofReal_re_affForm {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) (c : ι → ℂ)
    (L : ι → E →L[ℂ] ℂ) (x : E) : ((affForm Q c L x).re : ℂ) = affForm Q c L x := by
  rw [← Complex.conj_eq_iff_re, affForm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : (starRingEnd ℂ) (Q j i) = Q i j := hQ.apply i j
  rw [this]; ring

theorem leviForm_log_affForm {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) (c : ι → ℂ)
    (L : ι → E →L[ℂ] ℂ) (x v w : E) (hx : affForm Q c L x ≠ 0) :
    leviForm (fun y => Real.log (affForm Q c L y).re) x v w
      = (∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (L j w)) / affForm Q c L x
        - (∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (c j + L j x))
          * (∑ i, ∑ j, (c i + L i x) * Q i j * (starRingEnd ℂ) (L j w)) / affForm Q c L x ^ 2 := by
  have hre : (fun y => ((affForm Q c L y).re : ℂ)) = affForm Q c L :=
    funext (ofReal_re_affForm hQ c L)
  have hx' : (affForm Q c L x).re ≠ 0 := fun h => hx (by
    rw [← ofReal_re_affForm hQ c L x, h]; simp)
  have ht : ContDiffAt ℝ 2 (fun y => (affForm Q c L y).re) x :=
    (Complex.reCLM.contDiff.comp (contDiff_affForm Q c L)).contDiffAt
  rw [leviForm_real_comp (h := Real.log) (t := fun y => (affForm Q c L y).re)
    (Real.contDiffAt_log.2 hx') ht, leviForm, hre, ddbar_affForm, del_affForm, dbar_affForm,
    Real.deriv_log', deriv_inv]
  push_cast
  rw [ofReal_re_affForm hQ]
  ring

end General

theorem leviForm_log_herm : ∀ (n : ℕ) (B : Type) [Fintype B] [DecidableEq B] (e : B → Fin n), Function.Injective e → ∀ (Q : Matrix (Option B) (Option B) ℂ), Q.IsHermitian → ∀ (u : V n → ℝ) (z : V n), ContDiffAt ℝ 2 u z → (∀ t : B → ℂ, u (z + ∑ a, t a • coordVec (e a)) = Real.log ((∑ a, ∑ b, Option.elim a 1 (fun a => z (e a) + t a) * Q a b * star (Option.elim b 1 (fun b => z (e b) + t b))).re)) → ∀ q : ℂ, q = ∑ a, ∑ b, Option.elim a 1 (fun a => z (e a)) * Q a b * star (Option.elim b 1 (fun b => z (e b))) → q ≠ 0 → ∀ a b : B, leviForm u z (coordVec (e a)) (coordVec (e b)) = Q (some a) (some b) / q - (∑ c, Q (some a) c * star (Option.elim c 1 (fun c => z (e c)))) * (∑ c, Option.elim c 1 (fun c => z (e c)) * Q c (some b)) / q ^ 2 := by
  intro n B _ _ e _ Q hQ u z hu h q hq hq0 a b
  let c : Option B → ℂ := fun i => Option.elim i 1 (fun a => z (e a))
  let L : Option B → (B → ℂ) →L[ℂ] ℂ := fun i => Option.elim i 0 (fun a => ContinuousLinearMap.proj a)
  let M : (B → ℂ) →L[ℂ] V n :=
    ∑ a, (ContinuousLinearMap.proj a : (B → ℂ) →L[ℂ] ℂ).smulRight (coordVec (e a))
  have hM : ∀ t, M t = ∑ a, t a • coordVec (e a) := fun t => by
    simp [M, ContinuousLinearMap.sum_apply]
  have hM1 : ∀ a, M (Pi.single a 1) = coordVec (e a) := fun a => by
    rw [hM]; simp [Pi.single_apply, ite_smul]
  have hφ : HasFDerivAt (fun t => z + M t) M 0 := M.hasFDerivAt.const_add z
  have h0 : z + M 0 = z := by simp
  have hc := leviForm_comp_holo (u := u) (φ := fun t => z + M t) (z := 0) (by rw [h0]; exact hu)
    (contDiff_const.add M.contDiff).contDiffAt (Pi.single a 1) (Pi.single b 1)
  rw [hφ.fderiv, hM1, hM1, h0] at hc
  have hw : ∀ (t : B → ℂ) i, Option.elim i 1 (fun a => z (e a) + t a) = c i + L i t := by
    intro t i; cases i <;> simp [c, L]
  have hf : (fun t => u (z + M t)) = fun t => Real.log (affForm Q c L t).re := by
    funext t
    rw [hM, h, affForm]
    simp only [hw]
    rfl
  have hq' : affForm Q c L 0 = q := by
    rw [hq, affForm]; simp [c]
  rw [← hc, hf, leviForm_log_affForm hQ _ _ _ _ _ (hq' ▸ hq0), hq']
  have hL : ∀ (a : B) i, L i (Pi.single a 1) = if i = some a then 1 else 0 := by
    intro a i; cases i <;> simp [L, Pi.single_apply]
  simp only [hL, map_zero, add_zero, apply_ite (starRingEnd ℂ), map_one, ite_mul, mul_ite, one_mul,
    zero_mul, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  rfl

end GlobalTheory.LogHermHess
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangePadicIntInjectiveSaturatedOfModL
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatticeModL

theorem exists_one_tmul_add_smul (l : ℕ) [Fact l.Prime] (H : Type) [AddCommGroup H]
    (x : ℤ_[l] ⊗[ℤ] H) :
    ∃ (h : H) (y : ℤ_[l] ⊗[ℤ] H), x = (1 : ℤ_[l]) ⊗ₜ h + (l : ℤ_[l]) • y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a h =>
    obtain ⟨c, hc⟩ : ∃ c : ℤ_[l], a - (a.zmodRepr : ℤ_[l]) = (l : ℤ_[l]) * c := by
      have := PadicInt.sub_zmodRepr_mem a
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
      exact this
    refine ⟨(a.zmodRepr : ℤ) • h, c ⊗ₜ h, ?_⟩
    have ha : a = ((a.zmodRepr : ℤ) : ℤ_[l]) + (l : ℤ_[l]) * c := by
      rw [← hc]; push_cast; ring
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul, zsmul_eq_mul, _root_.mul_one, ← TensorProduct.add_tmul, ← ha]
  | add x y hx hy =>
    obtain ⟨h₁, y₁, rfl⟩ := hx
    obtain ⟨h₂, y₂, rfl⟩ := hy
    exact ⟨h₁ + h₂, y₁ + y₂, by rw [TensorProduct.tmul_add, smul_add]; abel⟩

end GlobalTheory.LatticeModL


open GlobalTheory.LatticeModL in
theorem GlobalTheory.latticeMap_liftBaseChange_injective_saturated :
    ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [Module.Finite ℤ H] [Module.Free ℤ H]
      [AddCommGroup T] [Module ℤ_[l] T], (∀ t : T, (l : ℤ_[l]) • t = 0 → t = 0) →
      ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') →
      Function.Injective (φ.toIntLinearMap.liftBaseChange ℤ_[l]) ∧
      ∀ t : T, (l : ℤ_[l]) • t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) →
        t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) := by
  intro l _ H T _ _ _ _ _ htor φ hsat
  set F := φ.toIntLinearMap.liftBaseChange ℤ_[l] with hFdef
  have hF : ∀ h, F ((1 : ℤ_[l]) ⊗ₜ h) = φ h := by
    intro h; simp [F]
  have key : ∀ (x : ℤ_[l] ⊗[ℤ] H) (t : T), F x = (l : ℤ_[l]) • t →
      ∃ x', x = (l : ℤ_[l]) • x' := by
    intro x t hx
    obtain ⟨h, y, rfl⟩ := exists_one_tmul_add_smul l H x
    rw [map_add (f := _), map_smul, hF] at hx
    have h1 : φ h = (l : ℤ_[l]) • (t - F y) := by rw [smul_sub, ← hx]; abel
    obtain ⟨h', rfl⟩ := hsat h _ h1
    refine ⟨(1 : ℤ_[l]) ⊗ₜ h' + y, ?_⟩
    rw [smul_add, TensorProduct.tmul_smul]
    simp only [Nat.cast_smul_eq_nsmul]
  have hl : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal ℤ_[l]) _
      (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
    intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨x', rfl⟩ := key x 0 (by rw [hx, smul_zero])
    have : F x' = 0 := htor _ (by rw [← map_smul, hx])
    exact Submodule.smul_mem_smul hl this
  · rintro t ⟨x, hx⟩
    obtain ⟨x', rfl⟩ := key x t hx
    refine ⟨x', ?_⟩
    have : (l : ℤ_[l]) • (F x' - t) = 0 := by rw [smul_sub, ← map_smul, hx, sub_self]
    exact sub_eq_zero.mp (htor _ this)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsAlgClosureFieldBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundlePowSections_algClosure_fieldBaseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), letI : Algebra (Kb R) F := em.toRingHom.toAlgebra; GlobalTheory.FieldBaseChange.IsExtension (secExt A em N) := by
  first | exact @GlobalTheory.Mum.Desc.isExtension_secExt | exact GlobalTheory.Mum.Desc.isExtension_secExt | (intros; apply GlobalTheory.Mum.Desc.isExtension_secExt <;> assumption)
end

