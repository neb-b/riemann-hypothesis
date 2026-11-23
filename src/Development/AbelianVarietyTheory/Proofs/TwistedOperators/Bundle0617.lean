module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.PairingCommutesLiftOperators
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharInvertibleMatrixBallMemSubfield
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.GLBallInt
open MeasureTheory
open scoped Pointwise

theorem integral_eq_sum_of_rightInv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKt : μ K ≠ ⊤) {S : Set G} (hS : IsCompact S)
    (hSK : ∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) (f : G → ℂ) (hf : ∀ s ∈ S, ∀ k ∈ K, f (s * k) = f s) :
    ∃ t : Finset (G ⧸ K), ∫ g in S, f g ∂μ = ∑ Q ∈ t, f Q.out * μ.real K := by
  classical
  set q : G → G ⧸ K := QuotientGroup.mk

  have hcov : S ⊆ ⋃ s ∈ S, s • (K : Set G) := fun s hs =>
    Set.mem_biUnion hs ⟨1, one_mem K, by simp⟩
  obtain ⟨b, hbS, hbf, hb⟩ := hS.elim_finite_subcover_image (fun s _ => hKo.smul s) hcov
  have hfin : (q '' S).Finite := by
    refine (hbf.image q).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨g, hg, hy⟩ := Set.mem_iUnion₂.1 (hb hs)
    refine ⟨g, hg, ?_⟩
    obtain ⟨y, hy, rfl⟩ := hy
    simp only [smul_eq_mul, q]
    exact (QuotientGroup.mk_mul_of_mem g hy).symm
  have hout : ∀ Q ∈ q '' S, Q.out ∈ S := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K s
    rw [hh]; exact hSK s hs h h.2
  obtain ⟨T, hT⟩ : ∃ T : Finset (G ⧸ K), ∀ Q, Q ∈ T ↔ Q ∈ q '' S :=
    ⟨hfin.toFinset, fun Q => hfin.mem_toFinset⟩
  have hSeq : S = ⋃ Q ∈ T, Q.out • (K : Set G) := by
    ext g
    simp only [Set.mem_iUnion, hT, exists_prop]
    constructor
    · intro hg
      refine ⟨q g, ⟨g, hg, rfl⟩, ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
      refine ⟨h⁻¹, (h⁻¹).2, ?_⟩
      simp [q, hh, mul_assoc]
    · rintro ⟨Q, hQ, y, hy, rfl⟩
      exact hSK _ (hout Q hQ) y hy
  have hconst : ∀ Q ∈ q '' S, ∀ y ∈ Q.out • (K : Set G), f y = f Q.out := by
    rintro Q hQ _ ⟨y, hy, rfl⟩
    exact hf _ (hout Q hQ) y hy
  refine ⟨T, ?_⟩
  rw [hSeq, integral_biUnion_finset]
  · refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [hT] at hQ
    rw [setIntegral_congr_fun (hKo.smul _).measurableSet (hconst Q hQ), setIntegral_const,
      measureReal_def, measure_smul, ← measureReal_def, Complex.real_smul, mul_comm]
  · exact fun Q _ => (hKo.smul _).measurableSet
  · intro Q _ Q' _ hne
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', he⟩
    apply hne
    have h1 : q (Q.out * y) = Q := by
      simp only [q]; rw [QuotientGroup.mk_mul_of_mem _ hy]; exact QuotientGroup.out_eq' Q
    have h2 : q (Q'.out * y') = Q' := by
      simp only [q]; rw [QuotientGroup.mk_mul_of_mem _ hy']; exact QuotientGroup.out_eq' Q'
    simp only [smul_eq_mul] at he
    rw [← h1, ← h2, he]
  · intro Q hQ
    rw [hT] at hQ
    refine (integrableOn_congr_fun (hconst Q hQ) (hKo.smul _).measurableSet).2 ?_
    refine integrableOn_const ?_
    rw [measure_smul]; exact hKt

end GlobalTheory.GLBallInt

namespace GlobalTheory.GLBallInt
open MeasureTheory
open scoped Pointwise

theorem measureReal_eq_inv_natCast {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] {J K : Subgroup G}
    (hJc : IsCompact (J : Set G)) (hJ1 : μ J = 1) (hKo : IsOpen (K : Set G)) (hKJ : K ≤ J) :
    ∃ n : ℕ, μ.real K = (n : ℝ)⁻¹ := by
  have hKt : μ K ≠ ⊤ := ((measure_mono (show (K : Set G) ⊆ J from hKJ)).trans_lt (by simp [hJ1])).ne
  obtain ⟨t, ht⟩ := integral_eq_sum_of_rightInv μ K hKo hKt hJc (fun s hs k hk => J.mul_mem hs (hKJ hk))
    (fun _ => (1 : ℂ)) (fun _ _ _ _ => rfl)
  rw [setIntegral_const, measureReal_def, hJ1, Finset.sum_const, nsmul_eq_mul, one_mul] at ht
  simp only [ENNReal.toReal_one, one_smul] at ht
  refine ⟨t.card, eq_inv_of_mul_eq_one_right ?_⟩
  exact_mod_cast ht.symm

def rightStab {G : Type} [Group G] (S : Set G) : Subgroup G where
  carrier := {k | ∀ g, g ∈ S ↔ g * k ∈ S}
  one_mem' := fun g => by simp
  mul_mem' := fun {a b} ha hb g => by rw [ha g, hb (g * a), mul_assoc]
  inv_mem' := fun {a} ha g => by rw [ha (g * a⁻¹), inv_mul_cancel_right]

theorem isOpen_rightStab {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {S : Set G}
    (hSc : IsCompact S) (hSo : IsOpen S) : IsOpen (rightStab S : Set G) := by
  obtain ⟨V, hV, hSV⟩ := compact_open_separated_mul_right hSc hSo subset_rfl
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (Filter.inter_mem hV (inv_mem_nhds_one G hV)) ?_)
  rintro k ⟨hk, hk'⟩ g
  refine ⟨fun hg => hSV (Set.mul_mem_mul hg hk), fun hg => ?_⟩
  have := hSV (Set.mul_mem_mul hg hk')
  rwa [mul_inv_cancel_right] at this

end GlobalTheory.GLBallInt

namespace GlobalTheory.GLBallInt
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A' : Type} [Fintype A'] [DecidableEq A']

def matBall (x : Matrix A' A' k) (c : kˣ) : Set (Matrix A' A' k) :=
  {y | ∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)}

theorem matBall_eq_preimage (x : Matrix A' A' k) (c : kˣ) :
    matBall x c = ⋂ i, ⋂ j, (fun y : Matrix A' A' k => (y i j - x i j) / (c : k)) ⁻¹' (𝒪[k] : Set k) := by
  have h0 : 0 < valuation k (c : k) := zero_lt_iff.2 (by simp)
  ext y
  simp only [matBall, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe,
    Valuation.mem_integer_iff, map_div₀, div_le_one₀ h0]

theorem isOpen_matBall (x : Matrix A' A' k) (c : kˣ) : IsOpen (matBall x c) := by
  rw [matBall_eq_preimage]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    IsOpen.preimage (by fun_prop) Valuation.isOpen_integer

theorem isCompact_matBall (x : Matrix A' A' k) (c : kˣ) : IsCompact (matBall x c) := by
  have hc : (c : k) ≠ 0 := c.ne_zero
  have e : matBall x c = (fun A : Matrix A' A' k => (c : k) • A + x) '' {A | ∀ i j, A i j ∈ 𝒪[k]} := by
    ext y
    constructor
    · intro hy
      refine ⟨fun i j => (y i j - x i j) / (c : k), fun i j => ?_, ?_⟩
      · have := (matBall_eq_preimage x c ▸ hy : y ∈ _)
        simp only [Set.mem_iInter, Set.mem_preimage] at this
        exact this i j
      · ext i j
        show (c : k) * ((y i j - x i j) / (c : k)) + x i j = y i j
        rw [mul_div_cancel₀ _ hc, sub_add_cancel]
    · rintro ⟨A, hA, rfl⟩ i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_right, map_mul]
      exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hA i j))
  rw [e]
  exact isCompact_intMatrix.image (by fun_prop)

theorem isCompact_isOpen_glBall (x : Matrix A' A' k) (c : kˣ) (hdet : ∀ y ∈ matBall x c, y.det ≠ 0) :
    IsCompact {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} ∧
    IsOpen {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} := by
  have e : {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} =
      (fun g : GL A' k => g.val) ⁻¹' matBall x c := rfl
  rw [e]
  refine ⟨?_, (isOpen_matBall x c).preimage Units.continuous_val⟩
  rw [isEmbedding_val_GL.isInducing.isCompact_iff]
  convert isCompact_matBall x c using 1
  ext y
  refine ⟨fun ⟨g, hg, hgy⟩ => hgy ▸ hg, fun hy => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero y (hdet y hy), hy, rfl⟩⟩

end GlobalTheory.GLBallInt

namespace GlobalTheory.GLBallInt
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel

theorem integral_glBall_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A' : Type} [Fintype A'] [DecidableEq A'] (F : Subfield ℂ) {J : Subgroup (GL A' k)}, IsOpen (J : Set (GL A' k)) → J ≤ KO k A' → ∀ (ν : kˣ →* ℂˣ) (z : ℂ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → CondLE ϖ e ν → (∀ u, (ν u : ℂ) ∈ F) → (∀ u : kˣ, apow u z ∈ F) → ∀ (c : kˣ) (x : Matrix A' A' k), (∀ y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)) → y.det ≠ 0) → ∫ g in {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}, (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol J) ∈ F := by
  intro k _ _ _ _ _ _ A' _ _ F J hJo hJK ν z ϖ e _ hcond hνF hapF c x hdet
  haveI := isHaarMeasure_haarVol hJo hJK
  obtain ⟨hSc, hSo⟩ := isCompact_isOpen_glBall x c hdet
  set S := {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} with hSdef
  set K : Subgroup (GL A' k) := J ⊓ GlobalTheory.SplitFlip.glLatCong (ϖ ^ e) (stdLat k A') ⊓ rightStab S with hKdef
  have hKo : IsOpen (K : Set (GL A' k)) := by
    simp only [hKdef, Subgroup.coe_inf]
    exact (hJo.inter (GlobalTheory.FunObj.GivenAdm.isOpen_glLatCong _)).inter (isOpen_rightStab hSc hSo)
  have hKJ : K ≤ J := inf_le_left.trans inf_le_left
  have hJc : IsCompact (J : Set (GL A' k)) := isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJo) hJK
  have hKt : haarVol J K ≠ ⊤ :=
    ((measure_mono (show (K : Set (GL A' k)) ⊆ J from hKJ)).trans_lt (by simp [haarVol_self hJo hJK])).ne
  have hinv : ∀ s ∈ S, ∀ k' ∈ K, ((ν (gdet (s * k')) : ℂ) * apow (gdet (s * k')) z) =
      (ν (gdet s) : ℂ) * apow (gdet s) z := by
    intro s _ k' hk
    have hu : gdet k' ∈ unitCong (ϖ ^ e) :=
      GlobalTheory.FunObj.GivenAdm.gdet_mem_unitCong (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).2
    rw [gdet_mul, map_mul, Units.val_mul, apow_mul, hcond _ hu, apow_of_valuation_eq_one hu.1]
    simp
  obtain ⟨t, ht⟩ := integral_eq_sum_of_rightInv (haarVol J) K hKo hKt hSc
    (fun s hs k' hk => ((Subgroup.mem_inf.1 hk).2 s).1 hs) (fun g => (ν (gdet g) : ℂ) * apow (gdet g) z) hinv
  rw [ht]
  obtain ⟨n, hn⟩ := measureReal_eq_inv_natCast (haarVol J) hJc (haarVol_self hJo hJK) hKo hKJ
  refine Subfield.sum_mem _ fun Q _ => F.mul_mem (F.mul_mem (hνF _) (hapF _)) ?_
  rw [hn]
  push_cast
  exact F.inv_mem (natCast_mem F n)

end GlobalTheory.GLBallInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRamifiedCharDetSingularMatrixCosetEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.CosetVanish

theorem integral_coset_singular_eq_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A' : Type} [Fintype A'] [DecidableEq A'] (μ : Measure (GL A' k)) [μ.IsMulLeftInvariant] (ν : kˣ →* ℂˣ) (z : ℂ), ¬ IsUnram ν → ∀ (c : kˣ) (x : Matrix A' A' k), x.det = 0 → ∫ g in {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}, (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
  intro k _ _ _ _ _ _ A' _ _ μ _ ν z hν c x hx
  classical
  obtain ⟨u, hu1, hνu⟩ : ∃ u : kˣ, valuation k (u : k) = 1 ∧ ν u ≠ 1 := by
    by_contra h
    push_neg at h
    exact hν fun y hy => h y hy
  obtain ⟨w0, hw0, hw0x⟩ := (Matrix.exists_vecMul_eq_zero_iff (M := x)).2 hx
  obtain ⟨j, hj⟩ : ∃ j, w0 j ≠ 0 := by
    by_contra h; push_neg at h; exact hw0 (funext h)
  haveI : Nonempty A' := ⟨j⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => valuation k (w0 i))
  have hwi₀ : w0 i₀ ≠ 0 := by
    intro h0
    have := hi₀ j
    rw [h0, map_zero] at this
    exact hj ((valuation k).zero_iff.1 (le_antisymm this zero_le'))
  set w : A' → k := (w0 i₀)⁻¹ • w0 with hwdef
  have hwi : w i₀ = 1 := by simp [w, hwi₀]
  have hwint : ∀ i, valuation k (w i) ≤ 1 := by
    intro i
    simp only [w, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    have hpos : valuation k (w0 i₀) ≠ 0 := by simpa using hwi₀
    calc (valuation k (w0 i₀))⁻¹ * valuation k (w0 i) ≤ (valuation k (w0 i₀))⁻¹ * valuation k (w0 i₀) :=
          by gcongr; exact hi₀ i
      _ = 1 := inv_mul_cancel₀ hpos
  have hwx : ∀ j, ∑ l, w l * x l j = 0 := by
    intro j
    have := congrFun hw0x j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
    simp only [w, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, this, mul_zero]
  set e : A' → k := Pi.single i₀ ((u : k) - 1) with hedef
  have he : ∀ i, valuation k (e i) ≤ 1 := by
    intro i
    by_cases h : i = i₀
    · subst h
      simp only [e, Pi.single_eq_same]
      refine ((valuation k).map_sub _ _).trans ?_
      simp [hu1]
    · simp [e, Pi.single_eq_of_ne h]
  have hwe : ∑ l, w l * e l = (u : k) - 1 := by
    simp [e, Pi.single_apply, hwi]
  set M : Matrix A' A' k := 1 + Matrix.vecMulVec e w with hMdef
  have hMdet : M.det = u := by
    rw [hMdef, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp only [dotProduct]
    rw [hwe]; ring
  have hMne : M.det ≠ 0 := by rw [hMdet]; exact u.ne_zero
  set m : GL A' k := Matrix.GeneralLinearGroup.mkOfDetNeZero M hMne with hmdef
  have hmdet : gdet m = u := by
    ext; simp [gdet, Matrix.GeneralLinearGroup.val_det_apply, m, hMdet]
  have hmval : (m : Matrix A' A' k) = M := rfl
  have hMG : ∀ (G : Matrix A' A' k) i j, (M * G) i j = G i j + e i * ∑ l, w l * G l j := by
    intro G i j
    rw [hMdef, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]
    simp only [Matrix.vecMulVec_apply, mul_assoc, Finset.mul_sum]
  have hsum : ∀ (G : Matrix A' A' k) j, ∑ l, w l * G l j = ∑ l, w l * (G l j - x l j) := by
    intro G j
    simp only [mul_sub, Finset.sum_sub_distrib, hwx, sub_zero]
  have hkey : ∀ g : GL A' k, (m * g ∈ {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}) ↔
      g ∈ {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} := by
    intro g
    simp only [Set.mem_setOf_eq, Units.val_mul, hmval, hMG]
    constructor
    · intro h i j
      set s := ∑ l, w l * (g.val l j) with hs
      have h2 : ∑ l, w l * ((g.val l j + e l * s) - x l j) = (u : k) * s := by
        have : ∀ l, w l * ((g.val l j + e l * s) - x l j) = w l * (g.val l j - x l j) + (w l * e l) * s := by
          intro l; ring
        simp only [this, Finset.sum_add_distrib, ← Finset.sum_mul, hwe, ← hsum, ← hs]
        ring
      have hsv : valuation k s ≤ valuation k (c : k) := by
        have : s = (u : k)⁻¹ * ∑ l, w l * ((g.val l j + e l * s) - x l j) := by
          rw [h2, ← mul_assoc, inv_mul_cancel₀ u.ne_zero, one_mul]
        rw [this, map_mul, map_inv₀, hu1, inv_one, one_mul]
        refine (valuation k).map_sum_le fun l _ => ?_
        rw [map_mul]
        exact (mul_le_of_le_one_left' (hwint l)).trans (h l j) |>.trans' (by rfl)
      have : g.val i j - x i j = ((g.val i j + e i * s) - x i j) + (-(e i * s)) := by ring
      rw [this]
      refine (valuation k).map_add_le (h i j) ?_
      rw [Valuation.map_neg, map_mul]
      exact (mul_le_of_le_one_left' (he i)).trans hsv
    · intro h i j
      have hsv : valuation k (∑ l, w l * g.val l j) ≤ valuation k (c : k) := by
        rw [hsum]
        refine (valuation k).map_sum_le fun l _ => ?_
        rw [map_mul]
        exact (mul_le_of_le_one_left' (hwint l)).trans (h l j)
      have : g.val i j + e i * (∑ l, w l * g.val l j) - x i j = (g.val i j - x i j) + e i * (∑ l, w l * g.val l j) := by ring
      rw [this]
      refine (valuation k).map_add_le (h i j) ?_
      rw [map_mul]
      exact (mul_le_of_le_one_left' (he i)).trans hsv
  set S := {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} with hSdef
  have hpre : (fun g => m * g) ⁻¹' S = S := Set.ext hkey
  set χ : GL A' k → ℂ := fun g => (ν (gdet g) : ℂ) * apow (gdet g) z with hχ
  have hχm : ∀ g, χ (m * g) = (ν u : ℂ) * χ g := by
    intro g
    simp only [χ, gdet, map_mul] at hmdet ⊢
    rw [hmdet, apow_mul, apow_of_valuation_eq_one hu1, Units.val_mul]
    ring
  have hmp : MeasurePreserving (fun g => m * g) μ μ := measurePreserving_mul_left μ m
  have hemb : MeasurableEmbedding (fun g => m * g) := (MeasurableEquiv.mulLeft m).measurableEmbedding
  have h1 := hmp.setIntegral_preimage_emb hemb χ S
  rw [hpre] at h1
  simp only [hχm, integral_const_mul] at h1
  change ∫ g in S, χ g ∂μ = 0
  have hne : (ν u : ℂ) ≠ 1 := by
    intro h; exact hνu (Units.ext h)
  have h3 : ((ν u : ℂ) - 1) * ∫ g in S, χ g ∂μ = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.CosetVanish
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsBesselFrameOfBesselDatumRealPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.BesselFrameReal

variable {D : D7}

theorem map_cT_gram_mul (V : HSp D) (τ : D.what₂.Tau) {a b : ℕ} (X : Matrix (Fin V.rank) (Fin a) D.host.E)
    (Z : Matrix (Fin V.rank) (Fin b) D.host.E) :
    (X.map (tauE D τ))ᴴ * gramAt D V τ * Z.map (tauE D τ) = (Xᴴ * V.gram * Z).map (tauE D τ) := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map _ (GlobalTheory.FockCompare.tauE_star τ)]; rfl

theorem map_cT_gram (V : HSp D) (τ : D.what₂.Tau) {a : ℕ} (X : Matrix (Fin V.rank) (Fin a) D.host.E) :
    (X.map (tauE D τ))ᴴ * gramAt D V τ = (Xᴴ * V.gram).map (tauE D τ) := by
  rw [Matrix.map_mul, Matrix.conjTranspose_map _ (GlobalTheory.FockCompare.tauE_star τ)]; rfl

theorem map_cT_gram_mulVec (V : HSp D) (τ : D.what₂.Tau) {a : ℕ} (X : Matrix (Fin V.rank) (Fin a) D.host.E)
    (z : Fin V.rank → D.host.E) :
    ((X.map (tauE D τ))ᴴ * gramAt D V τ) *ᵥ (fun k => tauE D τ (z k)) =
      fun i => tauE D τ (((Xᴴ * V.gram) *ᵥ z) i) := by
  funext i
  rw [map_cT_gram, RingHom.map_mulVec]
  rfl

theorem herm_gramAt (V : HSp D) (τ : D.what₂.Tau) (z : Fin V.rank → D.host.E) :
    Formalism.QuantumDeterminants.herm (gramAt D V τ) (fun k => tauE D τ (z k)) (fun k => tauE D τ (z k)) =
      tauE D τ (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram z z) := by
  have hσ : ∀ x : D.host.E, tauE D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = star (tauE D τ x) :=
    fun x => GlobalTheory.FockCompare.tauE_star τ x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.QuantumDeterminants.herm, Formalism.UG.hform, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, gramAt,
    Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

end GlobalTheory.BesselFrameReal

namespace GlobalTheory.BesselFrameReal

theorem linearIndependent_of_mul_eq_one {n r : ℕ} (e : Matrix (Fin n) (Fin r) ℂ) (L : Matrix (Fin r) (Fin n) ℂ)
    (hL : L * e = 1) : LinearIndependent ℂ eᵀ := by
  refine Fintype.linearIndependent_iff.mpr fun g hg => ?_
  have h1 : e *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using this
  have h2 := congrArg (fun v => L *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
  exact congrFun h2

theorem isFrame_of_besDat : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), HSpace.IsIsomEmb A B ι → ∀ (d : BesDat A B ι) (τ : D.what₂.Tau),
  GlobalTheory.RealBessel.IsFrame (gramAt D B τ) (gramAt D A τ) ((frameMat B A ι).map (tauE D τ)) (d.e.map (tauE D τ)) (fun k => tauE D τ (d.z k)) := by
  intro D A B ι hι d τ
  have hinj : Function.Injective (tauE D τ) := (tauE D τ).injective
  have hunit : ∀ V : HSp D, IsUnit (gramAt D V τ) := fun V => by
    rw [Matrix.isUnit_iff_isUnit_det]
    show IsUnit ((tauE D τ).mapMatrix (HSpace.gram V)).det
    rw [← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V))
  obtain ⟨L, hL⟩ := GlobalTheory.BesselChar.exists_leftInv d.e d.e_iso.1
  refine
    { herm := GlobalTheory.SepPer.gramAt_conjTranspose B τ
      unit := hunit B
      unit₀ := hunit A
      codim := d.codim
      gram := ?_
      e_indep := ?_
      e_iso := ?_
      e_perp := ?_
      z_perpF := ?_
      z_perpE := ?_
      z_ne := ?_ }
  · rw [map_cT_gram_mul]
    have h : (frameMat B A ι)ᴴ * B.gram * frameMat B A ι = A.gram := GlobalTheory.AutFunCounterexample.gram_pull B A ι hι
    rw [h]; rfl
  · refine linearIndependent_of_mul_eq_one _ (L.map (tauE D τ)) ?_
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [map_cT_gram_mul]
    have h : d.eᴴ * B.gram * d.e = 0 := d.e_iso.2
    rw [h, Matrix.map_zero _ (map_zero _)]
  · rw [map_cT_gram_mul]
    have h : (frameMat B A ι)ᴴ * B.gram * d.e = 0 := d.e_perp
    rw [h, Matrix.map_zero _ (map_zero _)]
  · rw [map_cT_gram_mulVec]
    have h : ((frameMat B A ι)ᴴ * B.gram) *ᵥ d.z = 0 := d.z_perpA
    rw [h]; funext i; simp
  · rw [map_cT_gram_mulVec]
    have h : (d.eᴴ * B.gram) *ᵥ d.z = 0 := d.z_perpE
    rw [h]; funext i; simp
  · rw [herm_gramAt]
    exact (map_ne_zero _).2 d.z_ne

end GlobalTheory.BesselFrameReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftOntoOfInjectiveEigenspaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.LiftOntoRed

theorem onto_red : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → LiftInj R.toRealDat → UpInjW R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hC hEx hLI hUI hH hPG hLU hW hTh j
  exact GlobalTheory.OntoLinAlg.ontoParts_of _ (fun i x => hTh.intw j _ i x)
    (U2.adjoint_closed_lift_operators hH (RealDat3.kFormL_of hC.base.models) (RealDat3.jIsoL_of hC.base.models) j)
    (_root_.GlobalTheory.LiftOntoGood.goodW_le_range R F hok hC hEx hUI hH hPG hLU j) (_root_.GlobalTheory.kerProj_goodL R F hok hC hEx hH hPG j)
    (_root_.GlobalTheory.InjEigen.inj_eig R F hok hC hEx hLI hH hPG j)

end GlobalTheory.LiftOntoRed
end

