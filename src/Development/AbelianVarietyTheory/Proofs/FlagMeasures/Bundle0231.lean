module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSquareIdxNOfCovBy
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0193
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0227
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSumEqTsumPairOrbits
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesBoundedDetLeSum
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.SubCount

theorem encard_biUnion_le_sum {ι β : Type} (s : Finset ι) (Y : ι → Set β) :
    ((⋃ i ∈ s, Y i).encard : ℝ≥0∞) ≤ ∑ i ∈ s, ((Y i).encard : ℝ≥0∞) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.set_biUnion_insert]
    refine le_trans (ENat.toENNReal_le.2 (Set.encard_union_le _ _)) ?_
    rw [ENat.toENNReal_add]
    gcongr

theorem encard_biUnion_le_mul {ι β : Type} (S : Set ι) (Y : ι → Set β) (c : ℝ≥0∞) (hc : c ≠ 0)
    (h : ∀ i ∈ S, ((Y i).encard : ℝ≥0∞) ≤ c) :
    ((⋃ i ∈ S, Y i).encard : ℝ≥0∞) ≤ (S.encard : ℝ≥0∞) * c := by
  rcases S.finite_or_infinite with hS | hS
  · lift S to Finset ι using hS
    refine (encard_biUnion_le_sum S Y).trans ((Finset.sum_le_card_nsmul S _ c h).trans (le_of_eq ?_))
    rw [Set.encard_coe_eq_coe_finsetCard, nsmul_eq_mul]
    simp
  · rw [hS.encard_eq, ENat.toENNReal_top, ENNReal.top_mul hc]
    exact le_top

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] [Module K V]
  [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]

theorem index_eq (M : Submodule (𝓞 K) V) (hM : M.FG) (j : ℕ) (hj : 1 ≤ j) :
    (({P : Submodule (𝓞 K) V | P ≤ M ∧ Nat.card (M ⧸ P.comap M.subtype) = j}).encard : ℝ≥0∞) ≤
      ENNReal.ofReal ((j : ℝ) ^ ((finrank K V : ℝ) + Real.logb 2 (finrank ℚ K))) := by
  haveI : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.2 hM
  haveI : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  haveI : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have hr : finrank (𝓞 K) M ≤ finrank K V := by
    refine Module.finrank_le_of_rank_le ((Submodule.rank_le M).trans (le_of_eq ?_))
    rw [Module.finrank_eq_rank, IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl]
  obtain ⟨h1, h2⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.c2a K M (finrank K V) j hj hr
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal h2)
  rw [ENNReal.ofReal_natCast, ← ENat.toENNReal_coe, h1.cast_ncard_eq, ENat.toENNReal_le]
  refine Set.encard_le_encard_of_injOn (f := fun P => P.comap M.subtype) (fun P hP => hP.2) ?_
  intro P hP Q hQ e
  have := congrArg (Submodule.map M.subtype) e
  simpa only [Submodule.map_comap_subtype, inf_eq_right.2 hP.1, inf_eq_right.2 hQ.1] using this

theorem index_le (M : Submodule (𝓞 K) V) (hM : M.FG) (x : ℝ) (hx : 0 < x) :
    (({P : Submodule (𝓞 K) V | P ≤ M ∧ 1 ≤ Nat.card (M ⧸ P.comap M.subtype) ∧
      (Nat.card (M ⧸ P.comap M.subtype) : ℝ) ≤ x}).encard : ℝ≥0∞) ≤
      ENNReal.ofReal (x ^ ((finrank K V : ℝ) + Real.logb 2 (finrank ℚ K) + 1)) := by
  have he : 0 ≤ (finrank K V : ℝ) + Real.logb 2 (finrank ℚ K) :=
    add_nonneg (Nat.cast_nonneg _) (Real.logb_nonneg one_lt_two (by exact_mod_cast Module.finrank_pos))
  calc _ ≤ ((⋃ j ∈ Finset.Icc 1 ⌊x⌋₊,
        {P : Submodule (𝓞 K) V | P ≤ M ∧ Nat.card (M ⧸ P.comap M.subtype) = j}).encard : ℝ≥0∞) := by
        refine ENat.toENNReal_le.2 (Set.encard_le_encard fun P hP => ?_)
        simp only [Set.mem_iUnion]
        exact ⟨_, Finset.mem_Icc.2 ⟨hP.2.1, Nat.le_floor hP.2.2⟩, hP.1, rfl⟩
    _ ≤ _ := encard_biUnion_le_sum _ _
    _ ≤ (Finset.Icc 1 ⌊x⌋₊).card • ENNReal.ofReal (x ^ ((finrank K V : ℝ) + Real.logb 2 (finrank ℚ K))) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun j hj => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
        refine (index_eq M hM j h1).trans (ENNReal.ofReal_le_ofReal ?_)
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) ((Nat.le_floor_iff hx.le).1 h2) he
    _ ≤ _ := by
        rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, Real.rpow_add_one hx.ne',
          ENNReal.ofReal_mul' hx.le, mul_comm, ← ENNReal.ofReal_natCast]
        gcongr
        exact Nat.floor_le hx.le

end Index

theorem main : ∀ (D : D7) (L : LatW D), IsPosDef (D.sp.X 0).hT → finrank D.host.E (D.sp.X 0).V = D.R.k → L.FG → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT L → ∀ (n : ℕ) (De : ℝ), 1 ≤ De → (Set.encard {P : LatW D | P ≤ L ∧ rkW D P = n ∧ detW D P ≤ De} : ℝ≥0∞) ≤ ∑ de ∈ Finset.Icc 1 ⌊De⌋₊, (cntPrim (D.sp.X 0).hT L n de : ℝ≥0∞) * ENNReal.ofReal ((De / (de : ℝ)) ^ ((D.R.k : ℝ) + lg2f D.R.f + 1)) := by
  intro D L hpos hk hL hint n De hDe
  have hf : ((finrank ℚ D.host.E : ℕ) : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [(GlobalTheory.real_places_facts D).2.1]; push_cast; rfl
  calc _ ≤ ((⋃ de ∈ Finset.Icc 1 ⌊De⌋₊, ⋃ M ∈ PrimSubs (D.sp.X 0).hT L n de,
        {P : LatW D | P ≤ M ∧ 1 ≤ Nat.card (M ⧸ P.comap M.subtype) ∧
          (Nat.card (M ⧸ P.comap M.subtype) : ℝ) ≤ De / (de : ℝ)}).encard : ℝ≥0∞) := by
        refine ENat.toENNReal_le.2 (Set.encard_le_encard ?_)
        rintro P ⟨hP, hr, hd⟩
        have hS : sat D L P ≤ L := inf_le_left
        have hPS : P ≤ sat D L P := fun x hx => ⟨hP hx, Submodule.subset_span hx⟩
        have hfg : (sat D L P).FG := hL.of_le hS
        have hi : Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (sat D L P) :=
          fun x hx y hy => hint x (hS hx) y (hS hy)
        have hsp : Submodule.span D.host.E (sat D L P : Set (D.sp.X 0).V) =
            Submodule.span D.host.E (P : Set (D.sp.X 0).V) :=
          le_antisymm (Submodule.span_le.2 fun x hx => hx.2) (Submodule.span_mono hPS)
        have hrk : rkW D P = rkW D (sat D L P) := by unfold rkW; rw [hsp]
        obtain ⟨h4, h5⟩ := (GlobalTheory.LoopC.DetCard.main D _ hfg hpos hi).2.2 P hPS hrk
        have ha : ∀ x : (D.sp.X 0).V, (D.sp.X 0).hT x x = 0 → x = 0 := by
          intro x hx
          by_contra h0
          obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
          have := hpos τ x h0
          rw [hx] at this
          simp at this
        obtain ⟨de, h1, h2⟩ := GlobalTheory.Mass.DetNat.main D.host.E (D.sp.X 0) D.sp.cm.cmUnram.2.1
          (GlobalTheory.InertSquareNorm.isSquare_absNorm _ D.sp.cm.cmUnram) ha _ hfg fun x hx =>
            ⟨(Formalism.HermitianLatticesTheory.dualBasic_mem_dual _ _ _).2 fun y hy => hi y hy x hx, Submodule.subset_span hx⟩
        have h3 : detW D (sat D L P) = de := h2
        have hde : (1 : ℝ) ≤ de := by exact_mod_cast h1
        have hj : (1 : ℝ) ≤ idxW D (sat D L P) P := by exact_mod_cast h4
        rw [h5, h3] at hd
        simp only [Set.mem_iUnion]
        refine ⟨de, Finset.mem_Icc.2 ⟨h1, Nat.le_floor (by nlinarith)⟩, sat D L P,
          ⟨⟨hS, by rw [hsp]; rfl⟩, hrk.symm.trans hr, h2⟩, hPS, h4, ?_⟩
        rw [le_div_iff₀' (by linarith)]
        exact hd
    _ ≤ _ := encard_biUnion_le_sum _ _
    _ ≤ _ := by
        refine Finset.sum_le_sum fun de hde => ?_
        have h1 : (0 : ℝ) < de := by exact_mod_cast (Finset.mem_Icc.1 hde).1
        have hx : 0 < De / (de : ℝ) := div_pos (by linarith) h1
        refine encard_biUnion_le_mul _ _ _ (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hx _)).ne' fun M hM => ?_
        have := index_le (K := D.host.E) M (hL.of_le hM.1.1) _ hx
        rwa [hk, hf] at this

end GlobalTheory.LoopC.SubCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExactRanksOfRecord
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem exact_ranks_of_record : ∀ D : D7, (∀ i, StandardLattice.SplitsF D (D.host.g i)) → StandardLattice.volY0 D = StandardLattice.massI D D.R.r → StandardLattice.FactDstar D → (∀ u, (D.duS u : ℝ) = StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f) → letI := D.host.cmStar; ∀ (V : Type) [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V] [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E) (L : Submodule (𝓞 D.host.E) V), h.IsSymm → (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.k → ∀ u : D.what₂.Word, (D.duS u : ℝ) = Formalism.HermitianLatticesTheory.mass h L * (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, ∏ i ∈ Finset.Icc 1 D.R.k, ((Ideal.absNorm p.asIdeal : ℝ) ^ i - 1)) * (∏ τ, Formalism.MainNotions.S.vand (fun i : Fin D.R.k => (((D.hcW u τ).u i : ℚ) : ℝ)) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f) ∧ (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.r → D.what₂.Dstar = Formalism.HermitianLatticesTheory.mass h L * (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, (∏ i ∈ Finset.range D.R.r, ((Ideal.absNorm p.asIdeal : ℝ) ^ D.R.r - (Ideal.absNorm p.asIdeal : ℝ) ^ i)) / ((Ideal.absNorm p.asIdeal : ℝ) ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * (Ideal.absNorm p.asIdeal : ℝ) ^ (D.R.k * (D.R.k - 1) / 2))) * ∏ τ, D.dsig τ) := by
  intro D hsp hvol hD hdu V _ _ _ _ h L hs
  letI := D.host.cmStar
  have hmass : ∀ n, Formalism.HermitianLatticesTheory.IsOrthoLattice h L n → Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D n :=
    fun n ho => StandardLattice.mass_ortho D.host.E D.sp.cm.cmUnram n V h L ho
  have hcol := _root_.GlobalTheory.TypedPlacesProduct.finprod_typed_places D (fun x : ℝ => ∏ i ∈ Finset.Icc 1 D.R.k, (x ^ i - 1)) hsp
  have hrow := _root_.GlobalTheory.TypedPlacesProduct.finprod_typed_places D (fun x : ℝ => (∏ i ∈ Finset.range D.R.r, (x ^ D.R.r - x ^ i)) /
    (x ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * x ^ (D.R.k * (D.R.k - 1) / 2))) hsp
  beta_reduce at hcol hrow
  obtain ⟨hc0, hr0⟩ := _root_.GlobalTheory.idxColLoc_idxRowLoc_exact D 0
  obtain ⟨hc1, hr1⟩ := _root_.GlobalTheory.idxColLoc_idxRowLoc_exact D 1
  refine ⟨fun ho u => ?_, fun ho => ?_⟩
  · rw [hdu u, hmass _ ho, hcol]
    unfold StandardLattice.duStarU StandardLattice.duStarP StandardLattice.idxPi
    rw [hc0, hc1]
    rfl
  · rw [show D.what₂.Dstar = StandardLattice.DstarD D from hD, hmass _ ho, hrow]
    unfold StandardLattice.DstarD StandardLattice.DstarP StandardLattice.idxSig
    rw [hvol, hr0, hr1]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCommonSublatticeSmallDet
section
namespace GlobalTheory.LoopC.CommonSub

section General

open NumberField

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] [Module K V]

theorem span_eq_of_relIndex_ne_zero {P M : Submodule (𝓞 K) V} (hPM : P ≤ M)
    (h : P.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0) :
    Submodule.span K (P : Set V) = Submodule.span K (M : Set V) := by
  refine le_antisymm (Submodule.span_mono hPM) ?_
  rw [Submodule.span_le]
  intro m hm

  have hn : (P.toAddSubgroup.relIndex M.toAddSubgroup) • m ∈ P :=
    AddSubgroup.nsmul_relIndex_mem P.toAddSubgroup (K := M.toAddSubgroup) hm
  have hnK : ((P.toAddSubgroup.relIndex M.toAddSubgroup : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr h
  have hm' : m = ((P.toAddSubgroup.relIndex M.toAddSubgroup : ℕ) : K)⁻¹ •
      (P.toAddSubgroup.relIndex M.toAddSubgroup • m) := by
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hnK, one_smul]
  rw [SetLike.mem_coe, hm']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hn)

omit [NumberField K] [Module K V] in
theorem relIndex_inf_bound {M A' A'' B' B'' : Submodule (𝓞 K) V} (h1 : M ≤ A') (h2 : M ≤ A'')
    (n1 : B'.toAddSubgroup.relIndex A'.toAddSubgroup ≠ 0)
    (n2 : B''.toAddSubgroup.relIndex A''.toAddSubgroup ≠ 0) :
    ((B' ⊓ B'') ⊓ M).toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 ∧
    ((B' ⊓ B'') ⊓ M).toAddSubgroup.relIndex M.toAddSubgroup ≤
      B'.toAddSubgroup.relIndex A'.toAddSubgroup * B''.toAddSubgroup.relIndex A''.toAddSubgroup := by
  have e : ((B' ⊓ B'') ⊓ M).toAddSubgroup.relIndex M.toAddSubgroup =
      (B'.toAddSubgroup ⊓ B''.toAddSubgroup).relIndex M.toAddSubgroup :=
    AddSubgroup.inf_relIndex_right (B'.toAddSubgroup ⊓ B''.toAddSubgroup) M.toAddSubgroup
  have h1' : M.toAddSubgroup ≤ A'.toAddSubgroup := fun x hx => h1 hx
  have h2' : M.toAddSubgroup ≤ A''.toAddSubgroup := fun x hx => h2 hx

  have m1 : B'.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 :=
    mt (AddSubgroup.relIndex_eq_zero_of_le_right h1') n1
  have m2 : B''.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 :=
    mt (AddSubgroup.relIndex_eq_zero_of_le_right h2') n2
  rw [e]
  refine ⟨AddSubgroup.relIndex_inf_ne_zero m1 m2, ?_⟩
  calc (B'.toAddSubgroup ⊓ B''.toAddSubgroup).relIndex M.toAddSubgroup
      ≤ B'.toAddSubgroup.relIndex M.toAddSubgroup * B''.toAddSubgroup.relIndex M.toAddSubgroup :=
        AddSubgroup.relIndex_inf_le
    _ ≤ _ := Nat.mul_le_mul (AddSubgroup.relIndex_le_of_le_right h1' n1)
        (AddSubgroup.relIndex_le_of_le_right h2' n2)

end General

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem idxW_eq (D : D7) (A B : LatW D) : idxW D A B = B.toAddSubgroup.relIndex A.toAddSubgroup := rfl

theorem main : ∀ (D : D7) (L M A' A'' B' B'' : LatW D), IsPosDef (D.sp.X 0).hT → L.FG → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT L → M ≤ A' → M ≤ A'' → A' ≤ L → A'' ≤ L → B' ≤ A' → B'' ≤ A'' → rkW D B' = rkW D A' → rkW D B'' = rkW D A'' → ∃ P : LatW D, P ≤ M ∧ P ≤ B' ∧ P ≤ B'' ∧ rkW D P = rkW D M ∧ detW D P ≤ detW D M * (idxW D A' B' : ℝ) * (idxW D A'' B'' : ℝ) := by
  intro D L M A' A'' B' B'' hPD hL hI hMA' hMA'' hA'L hA''L hB' hB'' r1 r2
  have hfg : ∀ N : LatW D, N ≤ L → N.FG := fun N hN => Submodule.FG.of_le hL hN
  have hint : ∀ N : LatW D, N ≤ L → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT N :=
    fun N hN x hx y hy => hI x (hN hx) y (hN hy)

  have k1 := ((GlobalTheory.LoopC.DetCard.main D A' (hfg _ hA'L) hPD (hint _ hA'L)).2.2 B' hB' r1).1
  have k2 := ((GlobalTheory.LoopC.DetCard.main D A'' (hfg _ hA''L) hPD (hint _ hA''L)).2.2 B'' hB'' r2).1
  rw [idxW_eq] at k1 k2
  obtain ⟨n0, nle⟩ := relIndex_inf_bound (K := D.host.E) hMA' hMA''
    (Nat.one_le_iff_ne_zero.mp k1) (Nat.one_le_iff_ne_zero.mp k2)
  have hrk : rkW D ((B' ⊓ B'') ⊓ M) = rkW D M := by
    unfold rkW
    rw [span_eq_of_relIndex_ne_zero (K := D.host.E) inf_le_right n0]
  have hML : M ≤ L := hMA'.trans hA'L
  have k3 := (GlobalTheory.LoopC.DetCard.main D M (hfg _ hML) hPD (hint _ hML)).2.2 _ inf_le_right hrk
  refine ⟨(B' ⊓ B'') ⊓ M, inf_le_right, fun x hx => hx.1.1, fun x hx => hx.1.2, hrk, ?_⟩
  have hd : 0 ≤ detW D M := Real.sqrt_nonneg _
  rw [k3.2, mul_assoc, idxW_eq, idxW_eq, idxW_eq]
  gcongr
  exact_mod_cast nle

end GlobalTheory.LoopC.CommonSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsInnerLatticeVectorAnisotropic
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.InnerDual

theorem unif_mem_maximal {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : Ideal L.O) (hm : m.IsMaximal) :
    (⟨algebraMap F E ϖ, (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 ϖ.2⟩ : L.O) ∈ m := by
  classical

  let φ : 𝒪[F] →+* L.O := ((algebraMap F E).comp (𝒪[F]).subtype).codRestrict L.O
    (fun c => (GlobalTheory.UnramOrder.algebraMap_mem_iff L c).2 c.2)
  have hcomp : (L.O.subtype).comp φ = algebraMap 𝒪[F] E := by
    ext c
    rfl
  have hint : φ.IsIntegral := by
    intro x
    obtain ⟨p, hp, hpx⟩ := (L.O_def x).1 x.2
    refine ⟨p, hp, Subtype.ext ?_⟩
    have key := Polynomial.hom_eval₂ p φ L.O.subtype x
    rw [hcomp] at key
    show L.O.subtype (Polynomial.eval₂ φ x p) = L.O.subtype 0
    rw [key, map_zero]
    exact hpx

  have := hm
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' φ hint m
  have h3 : ϖ ∈ m.comap φ := by
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  exact Ideal.mem_comap.1 h3

end GlobalTheory.LocOver.InnerDual

namespace GlobalTheory.LocOver.InnerDual


open GlobalTheory.LocOver.UnipOnto in
theorem exists_inner_lattice_vector_anisotropic' : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type}
    [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r)
    (L : Submodule M.L.O (H.Wb Fr.f)), Fr.IsInner L → ∃ y : ↥(H.perp (H.X Fr.f)),
    H.mkW Fr.f y ∈ L ∧ H.h (Fr.f (Fin.last r)) (y : V) = 1 ∧ ∀ a, H.h (y : V) (Fr.es a) = 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr L hL
  have : IsNonarchimedeanLocalField F := hM.loc
  have : CharZero F := hM.char0
  classical
  obtain ⟨_hfg, hdual, xz, hxz, hxzL, hprim⟩ := hL
  have hz : (xz : V) = Fr.f (Fin.last r) := hxz

  have hint : ∀ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L →
      H.h (Fr.f (Fin.last r)) (y : V) ∈ M.L.O := by
    intro y hy
    have h0 := (hdual xz).1 hxzL y hy
    rwa [hz] at h0

  obtain ⟨I, hI⟩ : ∃ I : Ideal M.L.O, ∀ c : M.L.O, c ∈ I ↔
      ∃ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L ∧ H.h (Fr.f (Fin.last r)) (y : V) = (c : E) :=
    ⟨{ carrier := {c | ∃ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L ∧
          H.h (Fr.f (Fin.last r)) (y : V) = (c : E)}
       add_mem' := by
         rintro a b ⟨y, hy, hya⟩ ⟨y', hy', hyb⟩
         refine ⟨y + y', by rw [map_add (f := _)]; exact L.add_mem hy hy', ?_⟩
         show H.h _ ((y : V) + (y' : V)) = (a : E) + (b : E)
         rw [h_add_right, hya, hyb]
       zero_mem' := by
         refine ⟨0, by rw [map_zero]; exact L.zero_mem, ?_⟩
         show H.h _ (0 : V) = 0
         exact h_zero_right H _
       smul_mem' := by
         rintro c a ⟨y, hy, hya⟩
         refine ⟨M.L.cj (c : E) • y, ?_, ?_⟩
         · rw [map_smul]
           exact L.smul_mem ⟨M.L.cj (c : E), GlobalTheory.UnramOrder.cj_mem M.L c.2⟩ hy
         · show H.h _ (M.L.cj (c : E) • (y : V)) = (c : E) * (a : E)
           rw [h_smul_right, M.L.cj_cj, hya] },
     fun c => Iff.rfl⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[F])
  have : IsPrincipalIdealRing M.L.O := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.1
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)

  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨π, hπ⟩ := Submodule.IsPrincipal.principal m
    have hϖm := unif_mem_maximal M.L ϖ hϖ m hm
    rw [hπ, Submodule.mem_span_singleton] at hϖm
    obtain ⟨t, ht⟩ := hϖm
    have htE : (t : E) * (π : E) = algebraMap F E ϖ := congrArg Subtype.val ht
    obtain ⟨πi, hπi⟩ : ∃ πi : E, πi = (t : E) * algebraMap F E (ϖ : F)⁻¹ := ⟨_, rfl⟩
    have hinv : πi * (π : E) = 1 := by
      rw [hπi, mul_right_comm, htE, ← map_mul, mul_inv_cancel₀ hϖ0, map_one]
    have hvL : H.mkW Fr.f (πi • xz) ∈ L := by
      refine (hdual (πi • xz)).2 fun y hy => ?_
      have hyI : (⟨_, hint y hy⟩ : M.L.O) ∈ I := (hI _).2 ⟨y, hy, rfl⟩
      have hym := hIm hyI
      rw [hπ, Submodule.mem_span_singleton] at hym
      obtain ⟨s, hs⟩ := hym
      have hsE : (s : E) * (π : E) = H.h (Fr.f (Fin.last r)) (y : V) := congrArg Subtype.val hs
      show H.h (πi • (xz : V)) (y : V) ∈ M.L.O
      rw [H.h_smul_left, hz, ← hsE, mul_left_comm, hinv, mul_one]
      exact s.2
    have hxzv : H.mkW Fr.f xz = (π : E) • H.mkW Fr.f (πi • xz) := by
      refine Eq.trans ?_ (map_smul (H.mkW Fr.f) (π : E) (πi • xz))
      congr 1
      apply Subtype.ext
      show (xz : V) = (π : E) • (πi • (xz : V))
      rw [smul_smul, mul_comm, hinv, one_smul]
    have hu := hprim π (πi • xz) hvL hxzv
    exact hm.ne_top (hπ.trans (Ideal.span_singleton_eq_top.2 hu))
  have h1 : (1 : M.L.O) ∈ I := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨y0, hy0L, hy0z⟩ := (hI 1).1 h1
  have hy0z' : H.h (Fr.f (Fin.last r)) (y0 : V) = 1 := hy0z

  obtain ⟨w, hw⟩ : ∃ w : V, w = ∑ a : Fin r, H.h (y0 : V) (Fr.es a) • Fr.f a.castSucc := ⟨_, rfl⟩
  have hwX : w ∈ H.X Fr.f := by
    rw [hw]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Fj_le_X Fr _ (e_mem Fr a))
  have hwp : w ∈ H.perp (H.X Fr.f) := X_le_perp Fr hwX
  have hsumL : ∀ (g : Fin r → V) (u : V) (s : Finset (Fin r)),
      H.h (∑ a ∈ s, g a) u = ∑ a ∈ s, H.h (g a) u := by
    intro g u s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.sum_empty, Finset.sum_empty]
      exact H.h_zero_left u
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, ih]
  refine ⟨y0 - ⟨w, hwp⟩, ?_, ?_, ?_⟩
  · have hmk0 : H.mkW Fr.f ⟨w, hwp⟩ = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).2 hwX
    rw [map_sub, hmk0, sub_zero]
    exact hy0L
  · show H.h _ ((y0 : V) - w) = 1
    rw [h_sub_right, h_right H _ w, pairing_isotropicSpan_lastVector Fr w hwX, map_zero, sub_zero, hy0z']
  · intro b
    show H.h ((y0 : V) - w) (Fr.es b) = 0
    rw [h_sub_left, hw, hsumL]
    simp [H.h_smul_left, Fr.h_es]

end GlobalTheory.LocOver.InnerDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTermUnitaryMoveLocalTerm
section
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.LocOver

theorem isTerm_unitary_move {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    (r : ℕ) (g : V ≃ₗ[E] V) (t : Term V M r) (hg : IsUnitary H g) (ht : H.IsTerm t) :
    H.IsTerm (GlobalTheory.LocOver.move g t) :=
  GlobalTheory.LocOver.MoveTerm.isTerm_move H g t hg ht

end GlobalTheory.LocOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KfinCoefMulSplit
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.KFinCoefSplit

variable {k r : ℕ}

theorem kfin_smul {R : Rep k r} (a : ℂ) {v : R.H} (hv : R.KFin v) : R.KFin (a • v) := by
  obtain ⟨S, hfd, hv, hst⟩ := hv
  exact ⟨S, hfd, S.smul_mem a hv, hst⟩

theorem kfin_sum {R : Rep k r} {ι : Type} [Fintype ι] (x : ι → R.H) (hx : ∀ c, R.KFin (x c)) :
    R.KFin (∑ c, x c) := by
  choose S hfd hS hst using hx
  refine ⟨⨆ c, S c, inferInstance, Submodule.sum_mem _ fun c _ => Submodule.mem_iSup_of_mem c (hS c),
    fun g hg y hy => ?_⟩
  have hle : (⨆ c, S c) ≤ (⨆ c, S c).comap (R.σ g : R.H →ₗ[ℂ] R.H) :=
    iSup_le fun c z hz => Submodule.mem_iSup_of_mem c (hst c g hg z hz)
  exact hle hy

theorem kfin_coef_mul_split : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (om om' : ι → ℂ) (v v' : R.H), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → R.KFin v → R.KFin v' → (∀ I, (RI I).KFin (∑ c, pr I c (tm R om v c)) ∧ (RI I).KFin (∑ c, pr I c (tm R om' v' c))) ∧ ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om * ⟪v, R.σ g v'⟫_ℂ = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (tm R om v c), (RI I).σ g (∑ c, pr I c (tm R om' v' c))⟫_ℂ := by
  intro hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI om om' v v' hR hRI hF hT hv hv'
  obtain ⟨-, -, -, -, hRT, -, hRK, -, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR
  have hadj := (GlobalTheory.TensAdj.tens_adj hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hF hT).2.2.2.2
  have hkf := (GlobalTheory.tensor_decomposition_kfinite hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT.raw).2.1
  have hp : ∀ I (a : ι → ℂ) (w : R.H), R.KFin w → (RI I).KFin (∑ c, pr I c (tm R a w c)) := fun I a w hw =>
    kfin_sum _ fun c => hkf I c _ (kfin_smul (a c) hw)
  exact ⟨fun I => ⟨hp I om v hv, hp I om' v' hv'⟩,
    fun g hg => hadj om om' v (hRT v (hRK v hv)) v' (hRT v' (hRK v' hv')) g hg⟩

end GlobalTheory.KFinCoefSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSumEqTsumPairOrbitsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineLatticeMean_sum_eq_tsum_pair_orbits : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ k : ℕ, ∀ Lf : Ideal (𝓞 E) → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin (k + 1) → E), (∀ 𝔞 Λ' y, y ∈ Lf 𝔞 Λ' ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ') → ∀ (w : ℝ → ENNReal) (Φ : VecInf E (k + 1) → ENNReal), Measurable w → Measurable Φ → latMean E (k + 1) (fun L => w (covAt E (k + 1) L) * ∑' x : {x : VecInf E (k + 1) // x ∈ L ∧ x ≠ 0}, Φ x.1) = ∑' 𝔞 : {𝔞 : Ideal (𝓞 E) // 𝔞 ≠ ⊥}, ∑' c : Quot (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin k → E) // Submodule.IsFullLattice E Λ} => ∃ γ : GL (Fin k) E, ∀ y, (γ : Matrix (Fin k) (Fin k) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1), covol {x | x ∈ autGL E (k + 1) (Lf 𝔞.1 (Quot.out c).1) ∧ ∀ w a, x w a 0 = if a = 0 then 1 else 0} ((haarGL E (k + 1)).withDensity fun g => w (covAt E (k + 1) (latAt E (k + 1) (Lf 𝔞.1 (Quot.out c).1) g)) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0)) {g | 0 < detNorm E (k + 1) g} := by
  exact @GlobalTheory.PairOrbit.latMean_sum_eq_tsum_orbits
end

