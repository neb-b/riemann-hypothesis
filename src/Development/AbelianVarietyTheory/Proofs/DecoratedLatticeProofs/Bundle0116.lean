module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivPadicOfResidueCardUniformizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0109

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPartitionOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.RatPartition

theorem finite_ratW_mem {D : D7} (A T : HSp D) {C : Set (WO A T)} (hC : IsCompact C) :
    {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | ratW T A γ ∈ C}.Finite := by
  obtain ⟨i1, -, -, i4, i5, -⟩ := lattice_Mx D T.rank A.rank
  haveI := i1; haveI := i4; haveI := i5
  haveI : T1Space (Mx D T.rank A.rank) := @T2Space.t1Space _ _ i4
  have hLc : IsClosed (ratMx D T.rank A.rank : Set (Mx D T.rank A.rank)) := AddSubgroup.isClosed_of_discrete
  let φ : Matrix (Fin T.rank) (Fin A.rank) D.host.E → ratMx D T.rank A.rank := fun γ => ⟨ratW T A γ, γ, rfl⟩
  have hφ : Function.Injective φ := fun a b h =>
    Matrix.map_injective GlobalTheory.MixModel.incA_injective (congrArg Subtype.val h)
  have hs : IsCompact ((↑) ⁻¹' C : Set (ratMx D T.rank A.rank)) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
    exact hC.inter_right hLc
  exact (hs.finite_of_discrete.preimage (f := φ) hφ.injOn : _)

theorem exists_partition_one : ∀ (D : D7) (A T : HSp D), ∃ χ : WO A T → ℝ, Continuous χ ∧ HasCompactSupport χ ∧
    (∀ u, 0 ≤ χ u) ∧ ∀ u, HasSum (fun γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E => χ (ratW T A γ + u)) 1 := by
  intro D A T
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D T.rank A.rank
  haveI := i1; haveI := i2; haveI := i4
  haveI : RegularSpace (Mx D T.rank A.rank) := IsTopologicalAddGroup.regularSpace _
  haveI : ContinuousSub (Mx D T.rank A.rank) := IsTopologicalAddGroup.to_continuousSub
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  have hS : IsCompact (tsupport f) := hfc
  let g : Matrix (Fin T.rank) (Fin A.rank) D.host.E → WO A T → ℝ := fun γ u => f (ratW T A γ + u)
  have hgc : ∀ γ, Continuous (g γ) := fun γ => f.continuous.comp (continuous_const_add (ratW T A γ : WO A T))
  have hfin : ∀ N : Set (WO A T), IsCompact N → {γ | (Function.support (g γ) ∩ N).Nonempty}.Finite := by
    intro N hN
    refine (finite_ratW_mem A T ((hS.prod hN).image (continuous_fst.sub continuous_snd))).subset ?_
    rintro γ ⟨u, hu, huN⟩
    exact ⟨(ratW T A γ + u, u), ⟨subset_tsupport _ hu, huN⟩, add_sub_cancel_right _ _⟩
  have hlf : LocallyFinite fun γ => Function.support (g γ) := by
    intro u
    obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds u
    exact ⟨N, hN, hfin N hNc⟩
  have hpt : ∀ u, (Function.support fun γ => g γ u).Finite := by
    intro u
    refine (hfin {u} isCompact_singleton).subset ?_
    intro γ hγ
    exact ⟨u, hγ, rfl⟩
  let s : WO A T → ℝ := fun u => ∑ᶠ γ, g γ u
  have hs_cont : Continuous s := continuous_finsum hgc hlf
  have hg0 : ∀ γ u, 0 ≤ g γ u := fun γ u => (hf01 _).1
  have hs1 : ∀ u, 1 ≤ s u := by
    intro u
    obtain ⟨x, ⟨γ, rfl⟩, hx⟩ := hKc u
    have h1 : g γ u = 1 := hf1 hx
    rw [← h1]
    exact single_le_finsum γ (hpt u) (fun j => hg0 j u)
  have hs_inv : ∀ γ₀ u, s (ratW T A γ₀ + u) = s u := by
    intro γ₀ u
    have e : ∀ γ, g γ (ratW T A γ₀ + u) = g (γ + γ₀) u := by
      intro γ
      simp only [g, ratW]
      rw [Matrix.map_add _ (map_add (incA D)) γ γ₀, add_assoc]
    simp only [s, e]
    exact finsum_comp_equiv (Equiv.addRight γ₀) (f := fun γ => g γ u)
  have hpos : ∀ u, 0 < s u := fun u => zero_lt_one.trans_le (hs1 u)
  refine ⟨fun u => f u * (s u)⁻¹, f.continuous.mul (hs_cont.inv₀ fun u => (hpos u).ne'), hfc.mul_right,
    fun u => mul_nonneg (hf01 u).1 (inv_nonneg.2 (hpos u).le), fun u => ?_⟩
  have e : (fun γ => f (ratW T A γ + u) * (s (ratW T A γ + u))⁻¹) = fun γ => g γ u * (s u)⁻¹ := by
    funext γ
    rw [hs_inv]
  simp only [e]
  have h : HasSum (fun γ => g γ u) (∑ γ ∈ (hpt u).toFinset, g γ u) :=
    hasSum_sum_of_ne_finset_zero (fun γ hγ => by simpa using hγ)
  rw [← finsum_eq_sum _ (hpt u)] at h
  have h2 := h.mul_right (s u)⁻¹
  rwa [mul_inv_cancel₀ (hpos u).ne'] at h2

end GlobalTheory.RatPartition

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmallCompactLevelSymplecticCharacterTrivia
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.SmallLevel

theorem exists_open_subgroup (F : Type) [Field F] [NumberField F] (V : Set (Af F)) (hV : V ∈ 𝓝 (0 : Af F)) :
    ∃ S : AddSubgroup (Af F), IsOpen (S : Set (Af F)) ∧ (S : Set (Af F)) ⊆ V := by
  obtain ⟨M, hM, hMV⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F V hV
  let S : AddSubgroup (Af F) :=
    { carrier := {c | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ c = M • a}
      zero_mem' := ⟨0, fun v => zero_mem _, (smul_zero M).symm⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, fun v => add_mem (ha v) (hb v), (smul_add M a b).symm⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun v => neg_mem (ha v), (smul_neg M a).symm⟩ }
  refine ⟨S, S.isOpen_of_mem_nhds (g := 0) (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F M hM), ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact hMV a ha

theorem infPart_smul_eq_zero {D : D7} (y : Af D.host.F) (x : AE D) : infPart D (pairA D.host.F 0 y • x) = 0 := by
  rw [Algebra.smul_def, map_mul]
  have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 y)) = 0 := by
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  rw [this, zero_mul]

theorem exists_closed_level (D : D7) (m n : ℕ) (N : Set (Mx D m n)) (hN : N ∈ 𝓝 (0 : Mx D m n)) :
    ∃ K : AddSubgroup (Mx D m n), IsClosed (K : Set (Mx D m n)) ∧ (K : Set (Mx D m n)) ⊆ N ∧
      (∀ u ∈ K, u.map (infPart D) = 0) ∧
      ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → u ∈ K := by
  classical
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (AE D) := IsModuleTopology.topologicalAddGroup (AF D.host.F) _
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : T2Space (InfiniteAdeleRing D.host.F) := inferInstanceAs (T2Space ((v : InfinitePlace D.host.F) → v.Completion))
  let b := Module.finBasis D.host.F D.host.E
  let B := Algebra.TensorProduct.basis (AF D.host.F) b
  let Φ : (Fin m × Fin n × Fin (Module.finrank D.host.F D.host.E) → Af D.host.F) → Mx D m n :=
    fun x i j => ∑ k, pairA D.host.F 0 (x (i, j, k)) • B k
  have hΦ : Continuous Φ := by
    refine continuous_pi fun i => continuous_pi fun j => continuous_finsetSum _ fun k _ => ?_
    have h1 : Continuous fun x : Fin m × Fin n × Fin (Module.finrank D.host.F D.host.E) → Af D.host.F =>
        pairA D.host.F 0 (x (i, j, k)) := continuous_const.prodMk (continuous_apply _)
    exact h1.smul continuous_const
  have h0 : Φ 0 = 0 := by
    funext i j
    refine Finset.sum_eq_zero fun k _ => ?_
    exact zero_smul (AF D.host.F) (B k)
  have h1 : Φ ⁻¹' N ∈ 𝓝 0 := hΦ.continuousAt.preimage_mem_nhds (h0 ▸ hN)
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, -, t, ht, hsub⟩ := h1
  obtain ⟨S, hS, hSt⟩ := exists_open_subgroup D.host.F (⋂ p, t p) (Filter.iInter_mem.mpr ht)
  let c : Fin m × Fin n × Fin (Module.finrank D.host.F D.host.E) → Mx D m n →+ AF D.host.F := fun p =>
    { toFun := fun u => B.coord p.2.2 (u p.1 p.2.1)
      map_zero' := map_zero _
      map_add' := fun u u' => map_add _ _ _ }
  have hc : ∀ p, Continuous (c p) := fun p =>
    (IsModuleTopology.continuous_of_linearMap (B.coord p.2.2)).comp
      ((continuous_apply p.2.1).comp (continuous_apply p.1))
  let U : AddSubgroup (Mx D m n) := ⨅ p, S.comap ((sndA D.host.F).toRingHom.toAddMonoidHom.comp (c p))
  let Z : AddSubgroup (Mx D m n) := ⨅ p, ((fstA D.host.F).toRingHom.toAddMonoidHom.comp (c p)).ker
  have hU : ∀ u, u ∈ U ↔ ∀ p, (c p u).2 ∈ S := fun u => AddSubgroup.mem_iInf
  have hZ : ∀ u, u ∈ Z ↔ ∀ p, (c p u).1 = 0 := fun u => AddSubgroup.mem_iInf
  have hUe : (U : Set (Mx D m n)) = ⋂ p, (fun u => (c p u).2) ⁻¹' S := by
    ext u; rw [Set.mem_iInter]; exact hU u
  have hZe : (Z : Set (Mx D m n)) = ⋂ p, {u | (c p u).1 = 0} := by
    ext u; rw [Set.mem_iInter]; exact hZ u
  have hrec : ∀ u ∈ Z, Φ (fun p => (c p u).2) = u := by
    intro u hu
    funext i j
    conv_rhs => rw [← B.sum_repr (u i j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact Prod.ext ((hZ u).mp hu (i, j, k)).symm rfl
  refine ⟨U ⊓ Z, ?_, ?_, ?_, U, ?_, ?_⟩
  · rw [AddSubgroup.coe_inf, hUe, hZe]
    exact (isClosed_iInter fun p => (S.isClosed_of_isOpen hS).preimage (continuous_snd.comp (hc p))).inter
      (isClosed_iInter fun p => isClosed_eq (continuous_fst.comp (hc p)) continuous_const)
  · intro u hu
    have h4 : (fun p => (c p u).2) ∈ I.pi t := fun p _ => Set.mem_iInter.mp (hSt ((hU u).mp hu.1 p)) p
    have h5 := hsub h4
    rwa [Set.mem_preimage, hrec u hu.2] at h5
  · intro u hu
    funext i j
    have h4 : ∑ k, pairA D.host.F 0 (c (i, j, k) u).2 • B k = u i j := congrFun (congrFun (hrec u hu.2) i) j
    rw [Matrix.map_apply, ← h4]
    exact (infPart D).toAddMonoidHom.ker.sum_mem fun k _ => infPart_smul_eq_zero _ _
  · rw [hUe]
    exact isOpen_iInter_of_finite fun p => hS.preimage (continuous_snd.comp (hc p))
  · intro u hu hu'
    refine ⟨hu, (hZ u).mpr fun p => ?_⟩
    have h2 := GlobalTheory.FinTranslate.smul_eq_zero_of_inf (congrFun (congrFun hu' p.1) p.2.1)
    have h3 : GlobalTheory.FinTranslate.eInf D * c p u = 0 := by
      have := congrArg (B.coord p.2.2) h2
      rwa [map_smul, map_zero, smul_eq_mul] at this
    exact (one_mul _).symm.trans (congrArg Prod.fst h3)

theorem exists_small_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D), ∀ N ∈ 𝓝 (0 : WO A T), ∃ K : AddSubgroup (WO A T), IsCompact (K : Set (WO A T)) ∧ (K : Set (WO A T)) ⊆ N ∧ (∀ u ∈ K, u.map (infPart D) = 0) ∧ (∃ U : AddSubgroup (WO A T), IsOpen (U : Set (WO A T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → u ∈ K) ∧ ∀ u ∈ K, ∀ u' ∈ K, ψ (symplOH A T u u') = 1 := by
  intro D ψ hψ A T N hN
  haveI : LocallyCompactSpace (WO A T) := (GlobalTheory.MixModel.lattice_Mx D T.rank A.rank).2.1
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : WO A T)
  have hs : Continuous fun p : WO A T × WO A T => (symplOH A T p.1 p.2).2 :=
    continuous_snd.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_fst continuous_snd)
  have h2 := hs.continuousAt.preimage_mem_nhds (x := (0, 0)) (t := {a | ψ (pairA D.host.F 0 a) = 1})
    (by
      have h0 : (symplOH A T (0 : WO A T) 0).2 = 0 := congrArg Prod.snd (GlobalTheory.FinTranslate.symplOH_zero_left A T 0)
      have h1 := GlobalTheory.FinTranslate.ker_mem_nhds hψ.1.1 hψ.1.2.1
      rwa [← h0] at h1)
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := mem_nhds_prod_iff.mp h2
  obtain ⟨K, hK, hKN, hKf, hKU⟩ := exists_closed_level D T.rank A.rank (N ∩ C ∩ (P ∩ Q))
    (Filter.inter_mem (Filter.inter_mem hN hC0) (Filter.inter_mem hP hQ))
  refine ⟨K, hC.of_isClosed_subset hK fun u hu => (hKN hu).1.2, fun u hu => (hKN hu).1.1, hKf, hKU,
    fun u hu u' hu' => ?_⟩
  have h3 : GlobalTheory.FinTranslate.eInf D * symplOH A T u u' = 0 := by
    rw [← GlobalTheory.FinTranslate.symplOH_smul_right, GlobalTheory.FinTranslate.smul_fin (hKf u' hu'),
      GlobalTheory.FinTranslate.symplOH_zero_right]
  have h4 : symplOH A T u u' = pairA D.host.F 0 (symplOH A T u u').2 :=
    Prod.ext ((one_mul _).symm.trans (congrArg Prod.fst h3)) rfl
  rw [h4]
  have h5 := hPQ (Set.mk_mem_prod (hKN hu).2.1 (hKN hu').2.2)
  rw [Set.mem_preimage, Set.mem_setOf_eq] at h5
  exact h5

end GlobalTheory.SmallLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointFrameCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField

namespace GlobalTheory.InhPt

open GlobalTheory.MixPer

theorem exists_char : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ χ : AddChar k Circle, p.IsChar ψ χ ∧ Continuous χ := by
  intro D k _ _ _ _ p ψ hψ
  have hn : ∀ x : AF D.host.F, ‖ψ x‖ = 1 := hψ.1.2.1
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have htr : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun a : k => psiE ψ (p.sec a) := hψ.1.1.comp (htr.comp p.cont_sec)
  let χ : AddChar k Circle :=
    { toFun := fun a => ⟨psiE ψ (p.sec a), by simpa [Submonoid.unitSphere, psiE] using hn _⟩
      map_zero_eq_one' := by ext; simp [psiE]
      map_add_eq_mul' := by intro a b; ext; simp [psiE, map_add (f := _), AddChar.map_add_eq_mul]; rfl }
  exact ⟨χ, fun a => rfl, Continuous.subtype_mk hc _⟩

theorem exists_splitPt_frame_char : ∀ (D : D7), (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [IsTopologicalRing k] [CharZero k] (T : ℕ), T.Prime → Nat.card (IsLocalRing.ResidueField 𝒪[k]) = T → Irreducible (T : 𝒪[k]) → ∀ (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → IsSplitIdem D e → Ideal.absNorm w.asIdeal = T → ¬ (w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 D.host.E)}) → ∃ p : SplitPt D k, p.e = e) ∧ ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k), (∀ (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (b : Matrix (Fin S.rank) n k) (b' : Matrix n (Fin S.rank) k), b * b' = 1 → b' * b = 1 → ∃ β : Frame p S n, β.b = b) ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∃ χ : AddChar k Circle, p.IsChar ψ χ ∧ Continuous χ ∧ χ ≠ 1 ∧ (p.UnitAA → GlobalTheory.SplitWeil.HasConductor χ 1) := by
  intro D
  refine ⟨?_, ?_⟩
  · intro k _ _ _ _ _ _ T hT hcard hirr w e hw he hN hsq
    haveI := Fact.mk hT
    obtain ⟨φ, hφ, hφs, hφO⟩ := _root_.GlobalTheory.QpChar.exists_ringEquiv_padic k T hcard hirr
    obtain ⟨v, pr, sec, hab, h1, h2, hpr, hsec, hint⟩ := _root_.GlobalTheory.FinPl.SplitQT.exists_coord_padic D T w e hw he hN hsq
    refine ⟨⟨v, e, he, hab, φ.toRingHom.comp pr, sec.comp φ.symm.toRingHom.toAddMonoidHom, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    · intro a; simp [h1]
    · intro x; simp [h2]
    · exact hφ.comp hpr
    · exact hsec.comp hφs
    · intro a
      have := hφO (φ.symm a)
      simp only [RingEquiv.apply_symm_apply] at this
      simp [this, hint]
  · intro k _ _ _ _ p
    refine ⟨?_, ?_⟩
    · intro S n _ _ b b' h1 h2
      obtain ⟨gl, hs, hm⟩ := _root_.GlobalTheory.GlEmbed.exists_gl D k p S n b b' h1 h2
      exact ⟨⟨b, b', h1, h2, gl, hs, hm⟩, rfl⟩
    · intro ψ hψ
      obtain ⟨χ, hχ, hc⟩ := exists_char D k p ψ hψ
      obtain ⟨a, ha⟩ := _root_.GlobalTheory.FinPl.CharNontriv.exists_psiE_sec_ne_one D k p ψ hψ
      refine ⟨χ, hχ, hc, ?_, fun hu => _root_.GlobalTheory.SplitCharCond.hasConductor_one D k p ψ χ hψ hχ hu⟩
      intro h1
      apply ha
      rw [← hχ a, h1]
      simp

end GlobalTheory.InhPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitarySupportedAtPlaceOfDualIsotropicFramStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open GlobalTheory.IwaPlace.BuildQ in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitarySupportedAtPlace_of_dual_isotropic_frames : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (α β : Fin ρ → AE D) (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i, α i ∈ idAt D (· = v)) → (∀ i, β i ∈ idAt D (· = v)) → (∀ i, α i * β i = ε) → (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i j, c' i j ∈ idAt D (· = v)) → adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) → adj c' * (gA S * c') = 0 → ∃ q ∈ grpAt S (· = v), mt S q * d.jX = d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)) ∧ (∀ i, mt S q *ᵥ colMul d.jX i (α i) = fun k => (d.jX * b) k i) ∧ (∀ i, mt S q *ᵥ colMul d.jY i (cA D (β i)) = fun k => c' k i) := by
  intro D S S₀ ρ d v ε hεε hεc _ hε α β b c' hα hβ hαβ hb hc' H1 H2
  have mulVec_colMul {m n k : ℕ} (M : Mx D m n) (X : Mx D n k) (i : Fin k) (a : AE D) :
      M *ᵥ colMul X i a = fun r => a * (M * X) r i := by
    funext r
    simp only [colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have mul_tail₃ {a m n p k : ℕ} {A : Mx D a m} {B : Mx D m n} {B' : Mx D n p} {C : Mx D a p}
      (h : A * (B * B') = C) (X : Mx D p k) :
      A * (B * (B' * X)) = C * X := by
    rw [← h]
    simp only [Matrix.mul_assoc]
  have mul_tail₄ {a m n p q k : ℕ} {A : Mx D a m} {B : Mx D m n} {B' : Mx D n p} {B'' : Mx D p q} {C : Mx D a q}
      (h : A * (B * (B' * B'')) = C) (X : Mx D q k) :
      A * (B * (B' * (B'' * X))) = C * X := by
    rw [← h]
    simp only [Matrix.mul_assoc]
  have gXX {k : ℕ} (X : Mx D ρ k) : adj d.jX * (gA S * (d.jX * X)) = 0 := by
    rw [mul_tail₃ d.gram_XX, Matrix.zero_mul]
  have gYX {k : ℕ} (X : Mx D ρ k) : adj d.jY * (gA S * (d.jX * X)) = X := by
    rw [mul_tail₃ d.gram_YX, Matrix.one_mul]
  have g0X {k : ℕ} (X : Mx D ρ k) : adj d.j0 * (gA S * (d.jX * X)) = 0 := by
    rw [mul_tail₃ d.gram_0X, Matrix.zero_mul]
  have kill_left {ε : AE D} (hεε : ε * ε = ε) {m n k : ℕ} {x : Mx D m n} (hx : ε • x = x) (X : Mx D n k) :
      (1 - ε) • (x * X) = 0 := by
    rw [← Matrix.smul_mul, ← hx, smul_smul, one_sub_mul_self hεε, zero_smul, Matrix.zero_mul]
  have kill_mid₂ {ε : AE D} (hεε : ε * ε = ε) {m n p q k : ℕ} {x : Mx D p q} (hx : ε • x = x)
      (A : Mx D m n) (B : Mx D n p) (X : Mx D q k) : (1 - ε) • (A * (B * (x * X))) = 0 := by
    rw [← Matrix.mul_smul, ← Matrix.mul_smul, kill_left hεε hx, Matrix.mul_zero, Matrix.mul_zero]
  have absorb_mul {ε : AE D} {m n k : ℕ} {x : Mx D m n} (hx : ε • x = x) (X : Mx D n k) :
      x * (ε • X) = x * X := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, hx]
  have smul_sub_one {ε : AE D} (M : Mx D S.rank S.rank)
      (hX : ε • (M * d.jX - d.jX) = M * d.jX - d.jX) (h0 : ε • (M * d.j0 - d.j0) = M * d.j0 - d.j0)
      (hY : ε • (M * d.jY - d.jY) = M * d.jY - d.jY) : ε • (M - 1) = M - 1 := by
    have e : M - 1 = (M * d.jX - d.jX) * d.pX + (M * d.j0 - d.j0) * d.p0 + (M * d.jY - d.jY) * d.pY := by
      have e1 : M - 1 = (M - 1) * (d.jX * d.pX + d.j0 * d.p0 + d.jY * d.pY) := by
        rw [d.sum_eq_one, Matrix.mul_one]
      rw [e1]
      simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
    rw [e, smul_add, smul_add, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul, hX, h0, hY]
  have hb' : ε • b = b := smul_eq_of_mem hε hb
  have hc : ε • c' = c' := smul_eq_of_mem hε hc'
  have hαε : ∀ i, ε * α i = α i := fun i => (hε _).1 (hα i)
  have hβε : ∀ i, ε * β i = β i := fun i => (hε _).1 (hβ i)
  have hcA1 : cA D (1 - ε) = 1 - ε := by rw [map_sub, map_one, hεc]
  have h : HypDec.Images S S₀ (d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))
      (d.j0 - (d.jX * b) * (adj c' * (gA S * d.j0)))
      (c' * Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [adj_mul, Matrix.mul_assoc, gXX, Matrix.mul_zero]
    · simp only [adj_add, adj_mul, adj_smul, adj_diagonal, cA_cA, hcA1, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_assoc]
      simp only [mul_tail₃ H2, Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul, d.gram_YY,
        smul_zero, kill_mid₂ hεε hc, kill_left hεε (diag_absorb hαε), add_zero, Matrix.zero_mul]
    · simp only [adj_add, adj_mul, adj_smul, adj_diagonal, cA_cA, hcA1, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_assoc]
      simp only [mul_tail₄ H1, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul,
        gYX, d.gram_YX, kill_left hεε (diag_absorb hαε), kill_left hεε hb', add_zero, smul_smul]
      rw [zero_add, Matrix.diagonal_mul_diagonal, one_sub_sq hεε]
      rw [diag_const hαβ, smul_smul, hεε, ← add_smul, add_sub_cancel, one_smul]
    · simp only [adj_sub, adj_mul, adj_gA, adj_adj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
        d.gram_00, d.wittDecomp_gram_X_anisotropic, gXX, g0X, Matrix.mul_zero, sub_zero]
    · simp only [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, gXX, g0X, Matrix.mul_zero, sub_zero]
    · have adjH1 : adj b * (adj d.jX * (gA S * c')) = ε • (1 : Mx D ρ ρ) := by
        simpa only [adj_mul, adj_gA, adj_adj, adj_smul, adj_one, hεc, Matrix.mul_assoc] using congrArg adj H1
      simp only [adj_sub, adj_mul, adj_gA, adj_adj, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_assoc]
      rw [mul_tail₄ adjH1, Matrix.smul_mul, Matrix.one_mul, absorb_mul hc, sub_self, zero_add]
      simp only [Matrix.mul_smul, d.gram_0Y, d.gram_XY, Matrix.mul_one, smul_zero,
        kill_mid₂ hεε hc, sub_zero]
  have hjb : ε • (d.jX * b) = d.jX * b := by rw [← Matrix.mul_smul, hb']
  have hE : d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ))
      = (d.jX * b) * Matrix.diagonal β + (1 - ε) • d.jX := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]
  refine ⟨d.ofImages _ _ _ h, ?_, d.ofImages_jX h, fun i => ?_, fun i => ?_⟩
  · have key := smul_sub_one (ε := ε) (Formalism.L2.Theta.mt S (d.ofImages _ _ _ h))
      (by rw [d.ofImages_jX h, hE]; exact smul_shift hεε (by rw [← Matrix.smul_mul, hjb]) _)
      (by rw [d.wittDecomp_ofImages_inclAnisotropic h, sub_sub_cancel_left, smul_neg, ← Matrix.smul_mul, hjb])
      (by rw [d.ofImages_jY h]; exact smul_shift hεε (by rw [← Matrix.smul_mul, hc]) _)
    refine (mem_congGrp_iff S _ _).2 fun i j => (hε _).2 ?_
    exact congrFun (congrFun key i) j
  · rw [mulVec_colMul, d.ofImages_jX h, hE]
    funext k
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    exact scalar_X (hαε i) (hαβ i) (congrFun (congrFun hjb k) i)
  · rw [mulVec_colMul, d.ofImages_jY h]
    funext k
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    refine scalar_X ?_ ?_ (congrFun (congrFun hc k) i)
    · rw [← hεc, ← map_mul, hβε]
    · rw [← map_mul, mul_comm, hαβ, hεc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtZeroIncZeroMemLattice
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZeroAt

variable {D : D7}

theorem mulVec_idAt {m n : ℕ} (M : Mx D m n) {P : Pl D → Prop} {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D P) :
    ∀ i, (M *ᵥ y) i ∈ idAt D P := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem wittProjectionZero_mem_latticeCompletion_of_splits {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {P : Pl D → Prop}
    (hL₀ : Submodule.IsLattice D.host.E L₀) (hm : ∀ v, P v → MonoAt d L L₀ v) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : d.p0 *ᵥ y ∈ latV S₀ L₀ P := by
  refine (GlobalTheory.FinPlLoc.part_lat P S₀ L₀ _ hL₀).2 ⟨mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy), fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact ((hm v hv _).1 (GlobalTheory.FinPlLoc.smul_latV v he hy)).2.2

theorem wittCoreInclusion_mem_latticeCompletionAtPlace {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {P : Pl D → Prop}
    (hL : Submodule.IsLattice D.host.E L) (hm : ∀ v, P v → MonoAt d L L₀ v) {u : Fin T₀.rank → AE D}
    (hu : u ∈ latV T₀ L₀ P) : d.j0 *ᵥ u ∈ latV T L P := by
  refine (GlobalTheory.FinPlLoc.part_lat P T L _ hL).2 ⟨mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hu), fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact GlobalTheory.FinPl.VacFlat.wittCoreInclusion_mem_latticeCompletionAtPlace d (hm v hv) (GlobalTheory.FinPlLoc.smul_latV v he hu)

end GlobalTheory.FinPl.ExtZeroAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentRadicalSurjectsUnitriangularCharactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnipotentRadical_surjects_unitriangular_characters_agree : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), (∀ u : UX D (σ + 1), ∃ n ∈ flagN B.d, mt B.V n ⬝ x0 B = x0 B ⬝ u.1.1 ∧ (u ∈ UXQ D (σ + 1) → n ∈ GQ B.V)) ∧ ∀ (ψ : AddChar (AF D.host.F) ℂ), ∀ n ∈ flagN B.d, ∀ (h : GA D B.A) (u : UX D (σ + 1)), mt B.V (n * embA B.d B.o h) ⬝ x0 B = x0 B ⬝ u.1.1 → psiBes ψ B.d 1 (vecB B.o B.ζ) n = psiUni ψ u.1 := by
  first | exact @GlobalTheory.Unf.FB.uniRad_surj_psi | exact GlobalTheory.Unf.FB.uniRad_surj_psi | (intros; apply GlobalTheory.Unf.FB.uniRad_surj_psi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupportedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualLatticeAtPlace_comap_unitarySupported : ∀ (D : D7) (S : HSp D) (v : Pl D) (g : GA D S), g ∈ grpAt S (· = v) → ∀ Λ : AddSubgroup (Fin S.rank → AE D), IsSDAt S v Λ → IsSDAt S v (Λ.comap (Matrix.mulVecLin (mt S g)).toAddMonoidHom) := by
  first | exact @GlobalTheory.IwaPlace.SdComap.isSDAt_comap | exact GlobalTheory.IwaPlace.SdComap.isSDAt_comap | (intros; apply GlobalTheory.IwaPlace.SdComap.isSDAt_comap <;> assumption)
end

