module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0987
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneConstant
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixEvAdm

theorem coset_indicator_finprod : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (N : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F)),
    (∀ v, IsOpen (N v : Set (v.adicCompletion F))) → (∀ v, IsCompact (N v : Set (v.adicCompletion F))) →
    (∀ᶠ v in Filter.cofinite, (N v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) →
    ∀ a : κ → FiniteAdeleRing (𝓞 F) F, ∃ φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) → ℂ,
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ∧
      (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      ∀ y : κ → FiniteAdeleRing (𝓞 F) F,
        Set.indicator {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - a i) ∈ N v} 1 y =
          ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) := by
  intro F _ _ κ _ N hNo hNc hNcof a
  classical
  have hS : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∀ c : κ → v.adicCompletion F,
      IsOpen {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} ∧
      IsClosed {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} ∧
      IsCompact {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} := by
    intro v c
    have e : {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} =
        (fun x => x - c) ⁻¹' Set.pi Set.univ fun _ => (N v : Set (v.adicCompletion F)) := by
      ext x; simp
    have hcl : IsClosed (N v : Set (v.adicCompletion F)) := (N v).isClosed_of_isOpen (hNo v)
    refine ⟨?_, ?_, ?_⟩
    · rw [e]; exact (isOpen_set_pi Set.finite_univ fun _ _ => hNo v).preimage (continuous_sub_right c)
    · rw [e]; exact (isClosed_set_pi fun _ _ => hcl).preimage (continuous_sub_right c)
    · have e2 : {x : κ → v.adicCompletion F | ∀ i, x i - c i ∈ N v} =
          (Homeomorph.subRight c).symm '' Set.pi Set.univ fun _ => (N v : Set (v.adicCompletion F)) := by
        rw [e, Homeomorph.image_symm]; rfl
      rw [e2]
      exact (isCompact_univ_pi fun _ => hNc v).image (Homeomorph.subRight c).symm.continuous
  have hint : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, ∀ᶠ v in Filter.cofinite,
      ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F := fun y =>
    Filter.eventually_all.2 fun i => (y i).2
  refine ⟨fun v => Set.indicator {x | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (a i) ∈ N v} 1, fun v => ?_, ?_, fun y => ?_⟩
  · obtain ⟨ho, hc, hk⟩ := hS v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (a i)
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
      HasCompactSupport.intro hk fun y hy => Set.indicator_of_notMem hy _⟩
    set Sx := {x : κ → v.adicCompletion F | ∀ i, x i - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (a i) ∈ N v} with hSx
    by_cases hx : x ∈ Sx
    · filter_upwards [ho.mem_nhds hx] with z hz
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show z ∈ Sx from hz)]
      rfl
    · filter_upwards [hc.isOpen_compl.mem_nhds hx] with z hz
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show z ∉ Sx from hz)]
  · filter_upwards [hNcof, hint a] with v hv ha
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    refine forall_congr' fun i => ?_
    rw [← SetLike.mem_coe, hv, SetLike.mem_coe]
    exact ⟨fun h => by simpa using add_mem h (ha i), fun h => sub_mem h (ha i)⟩
  · by_cases hy : y ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - a i) ∈ N v}
    · rw [Set.indicator_of_mem hy, Pi.one_apply]
      refine (finprod_eq_one_of_forall_eq_one fun v => ?_).symm
      refine Set.indicator_of_mem (fun i => ?_) _
      simpa [map_sub] using hy i v
    · rw [Set.indicator_of_notMem hy]
      simp only [Set.mem_setOf_eq, not_forall] at hy
      obtain ⟨i, v, hv⟩ := hy
      refine (finprod_eq_zero _ v (Set.indicator_of_notMem (show (fun j => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y j)) ∉ {x | ∀ j, x j - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (a j) ∈ N v} from fun h => hv (by simpa [map_sub] using h i)) _) ?_).symm
      refine (Filter.eventually_cofinite.1 ((hNcof.and (hint a)).and (hint y))).subset fun w hw h' => hw ?_
      refine Set.indicator_of_mem (fun j => ?_) _
      rw [← SetLike.mem_coe, h'.1.1, SetLike.mem_coe]
      exact sub_mem (h'.2 j) (h'.1.2 j)

end GlobalTheory.MixEvAdm

namespace GlobalTheory.MixEvAdm

theorem sb_decomp : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ (m : ℕ) (c : Fin m → ℂ) (φ : Fin m → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) → ℂ),
      (∀ j v, φ j v ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ∧
      (∀ j, ∀ᶠ v in Filter.cofinite, φ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      g = ∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) := by
  intro F _ _ κ _ g hg
  classical
  have h1 : ∀ᶠ t in 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F), ∀ z ∈ tsupport g, g (z + t) = g z := by
    refine IsCompact.eventually_forall_of_forall_eventually hg.2 fun z _ => ?_
    have h2 : IsLocallyConstant fun q : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
        (g (q.2 + q.1), g q.2) :=
      (hg.1.comp_continuous (by fun_prop)).prodMk (hg.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, z)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨N, hNo, hNc, hNcof, hPn, hPV⟩ := _root_.GlobalTheory.FinAdeleNbhd.exists_prod_openCompact_subset F κ _ h1
  let U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    { carrier := {y | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ N v}
      zero_mem' := fun i v => by simp
      add_mem' := fun ha hb i v => by simpa [map_add (f := _)] using add_mem (ha i v) (hb i v)
      neg_mem' := fun ha i v => by simpa [map_neg] using neg_mem (ha i v) }
  have hinv : ∀ u ∈ U, ∀ z, g (z + u) = g z := fun u hu z => by
    by_cases hz : z ∈ tsupport g
    · exact hPV hu z hz
    by_cases hz' : z + u ∈ tsupport g
    · have := hPV (U.neg_mem hu) _ hz'
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']
  obtain ⟨t, -, ht⟩ := hg.2.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (U : Set _))
    (fun a _ => (continuous_sub_right a).continuousAt.preimage_mem_nhds (by show (U : Set _) ∈ 𝓝 (a - a); rw [sub_self]; exact hPn))
  set Tq := t.image (QuotientAddGroup.mk : _ → _ ⧸ U)
  have hind : ∀ (y : κ → FiniteAdeleRing (𝓞 F) F) (q : _ ⧸ U),
      Set.indicator {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} 1 y =
        if (y : _ ⧸ U) = q then (1 : ℂ) else 0 := by
    intro y q
    have : (y : _ ⧸ U) = q ↔ y - q.out ∈ U := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      exact QuotientAddGroup.eq_iff_sub_mem
    by_cases h : y - q.out ∈ U
    · rw [Set.indicator_of_mem (show y ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v,
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} from h), if_pos (this.mpr h), Pi.one_apply]
    · rw [Set.indicator_of_notMem (show y ∉ {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v,
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} from h), if_neg (fun h' => h (this.mp h'))]
  have key : ∀ y, g y = ∑ q ∈ Tq, g q.out *
      Set.indicator {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i - q.out i) ∈ N v} 1 y := by
    intro y
    simp only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']
    split_ifs with h
    · have h2 : -y + (y : _ ⧸ U).out ∈ U := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm
      have := hinv _ h2 y
      rw [add_neg_cancel_left] at this
      exact this.symm
    · by_contra hne
      have hy : y ∈ tsupport g := subset_tsupport _ hne
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
      refine h (Finset.mem_image.mpr ⟨x, hx, ?_⟩)
      exact (QuotientAddGroup.eq_iff_sub_mem.mpr hyx).symm
  choose φq hφSB hφstd hφeq using fun q : _ ⧸ U => coset_indicator_finprod F κ N hNo hNc hNcof q.out
  let e := Tq.equivFin
  refine ⟨Tq.card, fun j => g (e.symm j).1.out, fun j => φq (e.symm j).1, fun j v => hφSB _ v, fun j => hφstd _, ?_⟩
  funext y
  rw [key y]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hφeq]
  rw [← Finset.sum_coe_sort Tq]
  exact (Equiv.sum_comp e.symm (fun q : Tq => g q.1.out * ∏ᶠ v, φq q.1 v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i))).symm

end GlobalTheory.MixEvAdm

namespace GlobalTheory.MixEvAdm

theorem pullback_adm : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ _ hP₁ e hE l hl
  intro g hg
  obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := sb_decomp F (Fin n × Fin d) g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have hfam : ∀ j, ∀ᶠ v in Filter.cofinite, φ j v = M.vac v := fun j =>
    ((hstd j).and hP.good.std).mono fun v hv => hv.1.trans hv.2.symm
  have hψSB : ∀ j v, ev v (φ j v) ∈ SB (Fin n₁ × Fin d → Fv F v) := fun j v =>
    (hev v).2 ▸ Submodule.mem_map_of_mem (hφ j v)
  have hψstd : ∀ j, ∀ᶠ v in Filter.cofinite,
      ev v (φ j v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
    ((hfam j).and hP₁.good.std).mono fun v hv => by rw [hv.1, (hev v).1, hv.2]
  have hG : ∀ j, (fun y : Fin n₁ × Fin d → Af F => ∏ᶠ v, ev v (φ j v) fun i => evalV F v (y i)) ∈
      SB (Fin n₁ × Fin d → Af F) := fun j =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
  choose Tj hTj using fun j => hl _ (hG j)
  refine ⟨∑ j, c j • (Tj j).comp ei, fun f => ?_⟩
  have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
      (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
      ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.comp_apply, hsplit, map_sum, map_sum]
  simp only [map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hloc f (φ j) (hφ j) (hfam j)]
  exact congrArg (c j • ·) (hTj j (ei f))

end GlobalTheory.MixEvAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LatOpenCpt

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem exists_zsmul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E) (z : Fin n → E) : ∃ m : ℤ, m ≠ 0 ∧ m • z ∈ L := by
  exact _root_.GlobalTheory.IntegerMultipleMembership.exists_int_smul_mem L hL z

theorem vecMulVec_mem {E : Type} [Field E] [NumberField E] {n d : ℕ} {LX : Submodule (𝓞 E) (Fin n → E)}
    {LY : Submodule (𝓞 E) (Fin d → E)} (sX : Finset LX) (hsX : Submodule.span ℤ (sX : Set LX) = ⊤) (sY : Finset LY)
    (hsY : Submodule.span ℤ (sY : Set LY) = ⊤) (H : AddSubgroup (Matrix (Fin n) (Fin d) E))
    (hH : ∀ x ∈ sX, ∀ y ∈ sY, vecMulVec (x : Fin n → E) (y : Fin d → E) ∈ H) :
    ∀ x ∈ LX, ∀ y ∈ LY, vecMulVec x y ∈ H := by
  intro x hx y hy
  suffices h : ∀ z : LX, ∀ w : LY, vecMulVec (z : Fin n → E) (w : Fin d → E) ∈ H from h ⟨x, hx⟩ ⟨y, hy⟩
  intro z w
  have hz : z ∈ Submodule.span ℤ (sX : Set LX) := by rw [hsX]; trivial
  have hw : w ∈ Submodule.span ℤ (sY : Set LY) := by rw [hsY]; trivial
  induction hz using Submodule.span_induction with
  | mem a ha =>
    induction hw using Submodule.span_induction with
    | mem b hb => exact hH a ha b hb
    | zero =>
      have : vecMulVec (a : Fin n → E) ((0 : LY) : Fin d → E) = 0 := by ext; simp [vecMulVec_apply]
      rw [this]; exact H.zero_mem
    | add b c _ _ hb hc => rw [Submodule.coe_add, vecMulVec_add]; exact H.add_mem hb hc
    | smul k b _ hb => rw [Submodule.coe_smul_of_tower, vecMulVec_smul]; exact H.zsmul_mem hb k
  | zero =>
    have : vecMulVec ((0 : LX) : Fin n → E) (w : Fin d → E) = 0 := by ext; simp [vecMulVec_apply]
    rw [this]; exact H.zero_mem
  | add a b _ _ ha hb => rw [Submodule.coe_add, add_vecMulVec]; exact H.add_mem ha hb
  | smul k a _ ha => rw [Submodule.coe_smul_of_tower, smul_vecMulVec]; exact H.zsmul_mem ha k

theorem exists_gen {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsLattice E) : ∃ s : Finset L, Submodule.span ℤ (s : Set L) = ⊤ := by
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hL.fg
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  exact Module.Finite.fg_top

theorem locCo_smul {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : AF F) (w : W) :
    GlobalTheory.LatVac.locCo co v (a • w) = GlobalTheory.AdelicU.evFin F v a • GlobalTheory.LatVac.locCo co v w := by
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]
  ext k <;> simp [smul_eq_mul, map_mul]

end GlobalTheory.LatOpenCpt

namespace GlobalTheory.LatOpenCpt
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem incM_single {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (i : Fin n) (j : Fin d) (e : E) :
    incM F (Matrix.single i j e) = Matrix.single i j ((1 : AF F) ⊗ₜ[F] e) := by
  ext a b
  simp only [incM, Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> first | rfl | exact map_zero _

theorem single_eq_vecMulVec {E : Type} [Field E] {n d : ℕ} (i : Fin n) (j : Fin d) (e : E) :
    Matrix.single i j e = vecMulVec (Pi.single i e) (Pi.single j 1) := by
  ext a b
  simp only [Matrix.single_apply, vecMulVec_apply, Pi.single_apply]
  split_ifs <;> simp_all

theorem span_top {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    {LX : Submodule (𝓞 E) (Fin n → E)} {LY : Submodule (𝓞 E) (Fin d → E)} (hX : LX.IsFullLattice E) (hY : LY.IsFullLattice E)
    {ι : Type} (t : ι → Matrix (Fin n) (Fin d) E)
    (ht : ∀ x ∈ LX, ∀ y ∈ LY, incM F (vecMulVec x y) ∈ Submodule.span (AF F) (Set.range fun i => incM F (t i)))
    (Z : Matrix (Fin n) (Fin d) (AE F E)) : Z ∈ Submodule.span (AF F) (Set.range fun i => incM F (t i)) := by
  set S := Submodule.span (AF F) (Set.range fun i => incM F (t i))
  have hzs : ∀ (k : ℤ) (P : Matrix (Fin n) (Fin d) E), incM F (k • P) = k • incM F P := fun k P => by
    ext a b; simp [incM, map_zsmul]
  have hall : ∀ (x : Fin n → E) (y : Fin d → E), incM F (vecMulVec x y) ∈ S := by
    intro x y
    obtain ⟨m, hm, hmx⟩ := exists_zsmul_mem LX hX x
    obtain ⟨m', hm', hmy⟩ := exists_zsmul_mem LY hY y
    have h1 := ht _ hmx _ hmy
    rw [smul_vecMulVec, vecMulVec_smul, smul_smul, hzs] at h1
    have hk : ((m * m' : ℤ) : F) ≠ 0 := Int.cast_ne_zero.mpr (mul_ne_zero hm hm')
    have := S.smul_mem (algebraMap F (AF F) ((m * m' : ℤ) : F)⁻¹) h1
    rwa [← Int.cast_smul_eq_zsmul (AF F), smul_smul, ← map_intCast (algebraMap F (AF F)), ← map_mul,
      inv_mul_cancel₀ hk, map_one, one_smul] at this
  have hsingle : ∀ (i : Fin n) (j : Fin d) (z : AE F E), Matrix.single i j z ∈ S := by
    intro i j z
    induction z using TensorProduct.induction_on with
    | zero => rw [Matrix.single_zero]; exact S.zero_mem
    | tmul a e =>
      have h := S.smul_mem a (hall (Pi.single i e) (Pi.single j 1))
      rw [← single_eq_vecMulVec, incM_single, Matrix.smul_single, TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h
      exact h
    | add z z' hz hz' => rw [Matrix.single_add]; exact S.add_mem hz hz'
  rw [Matrix.matrix_eq_sum_single Z]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => hsingle i j (Z i j)

theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X Y,
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
      IsOpen (((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v).map (GlobalTheory.LatVac.locCo M.co v) :
        AddSubgroup ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) : Set ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) ∧
      IsCompact (((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v).map (GlobalTheory.LatVac.locCo M.co v) :
        AddSubgroup ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) : Set ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hX hY M _ v
  obtain ⟨sX, hsX⟩ := exists_gen X.L hX.lat.toIsLattice
  obtain ⟨sY, hsY⟩ := exists_gen Y.L hY.lat.toIsLattice
  let ι := ↥sX × ↥sY
  let t : ι → Matrix (Fin n) (Fin d) E := fun i => vecMulVec ((i.1 : X.L) : Fin n → E) ((i.2 : Y.L) : Fin d → E)
  let ρ : ι → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) := fun i => GlobalTheory.LatVac.locCo M.co v (incM F (t i))
  let φ : (ι → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun f => ∑ i, f i • ρ i
      map_add' := fun f g => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c f => by simp [Finset.smul_sum, smul_smul] }
  have hφ : ∀ f, φ f = ∑ i, f i • ρ i := fun f => rfl
  let Opi : AddSubgroup (ι → Fv F v) := AddSubgroup.pi Set.univ fun _ => (v.adicCompletionIntegers F).toSubring.toAddSubgroup
  have hO : ∀ f, f ∈ Opi ↔ ∀ i, f i ∈ v.adicCompletionIntegers F := fun f => by
    simp only [Opi, AddSubgroup.mem_pi, Set.mem_univ, true_implies]; rfl
  set Λ := (latAtV X Y v).map (GlobalTheory.LatVac.locCo M.co v) with hΛdef
  have hgen : ∀ x ∈ X.L, ∀ y ∈ Y.L, ∀ a : Fv F v, a ∈ v.adicCompletionIntegers F →
      a • GlobalTheory.LatVac.locCo M.co v (incM F (vecMulVec x y)) ∈ Λ := by
    intro x hx y hy a ha
    refine ⟨GlobalTheory.LatVac.liftV v a • incM F (vecMulVec x y), AddSubgroup.subset_closure
      ⟨GlobalTheory.LatVac.liftV v a, GlobalTheory.LatVac.at_liftV v a, by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha, x, hx, y, hy, rfl⟩, ?_⟩
    rw [locCo_smul, GlobalTheory.LatVac.evFin_liftV]
  have hle1 : Opi.map φ.toAddMonoidHom ≤ Λ := by
    rintro _ ⟨f, hf, rfl⟩
    replace hf := (hO _).1 hf
    show ∑ i, f i • ρ i ∈ Λ
    exact Λ.sum_mem fun i _ => hgen _ (i.1 : X.L).2 _ (i.2 : Y.L).2 _ (hf i)
  have hsmul : ∀ a ∈ v.adicCompletionIntegers F, ∀ w ∈ Opi.map φ.toAddMonoidHom, a • w ∈ Opi.map φ.toAddMonoidHom := by
    rintro a ha _ ⟨f, hf, rfl⟩
    replace hf := (hO _).1 hf
    exact ⟨a • f, (hO _).2 fun i => mul_mem ha (hf i), (φ.map_smul a f)⟩
  have hρ : ∀ x ∈ X.L, ∀ y ∈ Y.L,
      GlobalTheory.LatVac.locCo M.co v (incM F (vecMulVec x y)) ∈ Opi.map φ.toAddMonoidHom := by
    let rA : Matrix (Fin n) (Fin d) E →+ (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
      (GlobalTheory.LatVac.locCo M.co v).comp (AddMonoidHom.mapMatrix (inclR (F := F) (AF F)).toAddMonoidHom)
    refine vecMulVec_mem sX hsX sY hsY ((Opi.map φ.toAddMonoidHom).comap rA) ?_
    intro x hx y hy
    refine ⟨Pi.single (⟨x, hx⟩, ⟨y, hy⟩) 1, (hO _).2 fun i => ?_, ?_⟩
    · by_cases h : i = (⟨x, hx⟩, ⟨y, hy⟩)
      · rw [h]; simp
      · simp [Pi.single_apply, h]
    · show ∑ i, (Pi.single ((⟨x, hx⟩, ⟨y, hy⟩) : ι) (1 : Fv F v) : ι → Fv F v) i • ρ i = _
      rw [Finset.sum_eq_single ((⟨x, hx⟩, ⟨y, hy⟩) : ι) (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
      simp only [Pi.single_eq_same, one_smul]
      rfl
  have hle2 : Λ ≤ Opi.map φ.toAddMonoidHom := by
    rw [hΛdef, AddSubgroup.map_le_iff_le_comap, latAtV, AddSubgroup.closure_le]
    rintro _ ⟨a, -, ha, x, hx, y, hy, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, locCo_smul]
    exact hsmul _ ha _ (hρ x hx y hy)
  have hΛ : Λ = Opi.map φ.toAddMonoidHom := le_antisymm hle2 hle1
  have hsurj : ∀ u, ∃ f, φ f = u := by
    intro u
    let U : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
      (fun k => GlobalTheory.LatVac.liftV v (u.1 k), fun k => GlobalTheory.LatVac.liftV v (u.2 k))
    have ht : ∀ x ∈ X.L, ∀ y ∈ Y.L, incM F (vecMulVec x y) ∈ Submodule.span (AF F) (Set.range fun i => incM F (t i)) :=
      vecMulVec_mem sX hsX sY hsY ((Submodule.span (AF F) (Set.range fun i => incM F (t i))).toAddSubgroup.comap
        (AddMonoidHom.mapMatrix (inclR (F := F) (AF F)).toAddMonoidHom)) (fun x hx y hy => Submodule.subset_span ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩)
    have hZ := span_top hX.lat hY.lat t ht (M.co.e.symm U)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hZ
    refine ⟨fun i => GlobalTheory.AdelicU.evFin F v (c i), ?_⟩
    rw [hφ]
    have hu : GlobalTheory.LatVac.locCo M.co v (M.co.e.symm U) = u := by
      ext k <;> simp [GlobalTheory.LatVac.locCo, U, GlobalTheory.LatVac.evFin_liftV]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hu, ← hc, map_sum]
    exact Finset.sum_congr rfl fun i _ => (locCo_smul _ _ _ _).symm
  have hOc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have hOo : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hφc : Continuous φ := by
    rw [show (φ : (ι → Fv F v) → _) = fun f => ∑ i, f i • ρ i from rfl]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hset : ((Opi.map φ.toAddMonoidHom : AddSubgroup _) : Set _) =
      φ '' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext w
    simp only [AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, hO, Set.mem_pi, Set.mem_univ, true_implies]
    rfl
  choose f1 hf1 using fun k : Fin n × Fin d => hsurj (Pi.single k 1, 0)
  choose f2 hf2 using fun k : Fin n × Fin d => hsurj (0, Pi.single k 1)
  let sec : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → ι → Fv F v :=
    fun u => ∑ k, u.1 k • f1 k + ∑ k, u.2 k • f2 k
  have hsec : ∀ u, φ (sec u) = u := by
    intro u
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [sec, map_add (f := _), map_sum, map_smul, hf1, hf2]
    ext k <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hsc : Continuous sec :=
    (continuous_finsetSum _ fun k _ => ((continuous_apply k).comp continuous_fst).smul continuous_const).add
      (continuous_finsetSum _ fun k _ => ((continuous_apply k).comp continuous_snd).smul continuous_const)
  constructor
  · apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    have hU : IsOpen (sec ⁻¹' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
      (isOpen_set_pi Set.finite_univ fun _ _ => hOo).preimage hsc
    have h0 : (0 : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) ∈
        sec ⁻¹' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
      intro i _; simp [sec]
    refine Filter.mem_of_superset (hU.mem_nhds h0) ?_
    intro u hu
    rw [SetLike.mem_coe, hΛ]
    exact ⟨sec u, (hO _).2 fun i => hu i (Set.mem_univ _), hsec u⟩
  · rw [hΛ, hset]
    exact (isCompact_univ_pi fun _ => hOc).image hφc

end GlobalTheory.LatOpenCpt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.BotFormula

def toFinE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
  (Algebra.TensorProduct.comm ℚ D.host.E (FiniteAdeleRing (𝓞 ℚ) ℚ)).toRingEquiv.trans
    (GlobalTheory.LFun.finAdEquiv ℚ D.host.E)

def IsFinPt {D : D7} (WW : HSp D) (g : Formalism.L2.Theta.GA D WW) {n : ℕ} (h : Formalism.MainNotions.StandardLatticesGL3.GA D n) : Prop :=
  g ∈ GfC WW ∧ ∃ e : WW.rank = n, ∀ i j,
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom WW g : GL (Fin WW.rank) _) : Matrix (Fin WW.rank) (Fin WW.rank) _) i j) =
      toFinE D (((h : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (Fin.cast e i) (Fin.cast e j))

def minorF {D : D7} {a d a₁ d₁ : ℕ} {n : D.what₂.Tau → ℕ} (ha : a = a₁) (hd : d = d₁) (T : Tup D a d n) : PolF D d₁ a₁ :=
  MvPolynomial.rename (fun k : D.what₂.Tau × Fin d × Fin a => (k.1, Fin.cast hd k.2.1, Fin.cast ha k.2.2))
    (GlobalTheory.NormSum.minorPol D T)

theorem IsFinPt.cast {D : D7} {WW : HSp D} {g : Formalism.L2.Theta.GA D WW} {n n' : ℕ} (e : n' = n) {h : Formalism.MainNotions.StandardLatticesGL3.GA D n}
    (hg : IsFinPt WW g h) : IsFinPt WW g (e ▸ h : Formalism.MainNotions.StandardLatticesGL3.GA D n') := by
  subst e; exact hg

theorem lamC_mul {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) :
    lamC lam (x * y) = lamC lam x * lamC lam y := by
  unfold lamC
  rw [dite_eq_left (Qbar.mul_mem hx hy), dite_eq_left hx, dite_eq_left hy, ← map_mul]
  rfl

end GlobalTheory.BotFormula
end
end

