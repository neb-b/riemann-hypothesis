module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinGradedFrameIff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0041

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairIff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)

universe u v w

namespace FlagPairCharacterisation

section Flags

variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

theorem finrank_flag (w : Module.Basis (Fin N) Ω E) (i : Fin (N + 1)) :
    Module.finrank Ω (Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i})) = i := by
  classical
  have hli : LinearIndependent Ω (fun x : {j : Fin N | (j : ℕ) < i} => w x) :=
    w.linearIndependent.comp _ Subtype.val_injective
  rw [Set.image_eq_range, finrank_span_eq_card hli]
  simp only [Fintype.card_subtype, Set.mem_ofPred_eq]
  rw [Fin.card_filter_val_lt]
  exact min_eq_right (Nat.lt_succ_iff.mp i.isLt)

theorem flag_eq (w : Module.Basis (Fin N) Ω E) {Vs : Fin (N + 1) → Submodule Ω E} (mono : Monotone Vs)
    (dim : ∀ i, Module.finrank Ω (Vs i) = (i : ℕ)) (hmem : ∀ j, w j ∈ Vs j.succ) (i : Fin (N + 1)) :
    Vs i = Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) := by
  have : FiniteDimensional Ω E := Module.Finite.of_basis w
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_flag, dim])
  rw [Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  exact mono (Fin.le_def.mpr (by simpa using hj)) (hmem j)

theorem flag_mono (w : Module.Basis (Fin N) Ω E) :
    Monotone fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) :=
  fun _ _ hij => Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk (Fin.le_def.mp hij))

theorem mem_flag_iff (w : Module.Basis (Fin N) Ω E) (n : ℕ) (x : E) :
    x ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < n}) ↔ ∀ j : Fin N, n ≤ (j : ℕ) → w.repr x j = 0 := by
  rw [Module.Basis.mem_span_image]
  constructor
  · intro h j hj
    by_contra hne
    exact absurd (h (Finsupp.mem_support_iff.mpr hne)) (by simpa using hj)
  · intro h j hj
    by_contra hne
    exact Finsupp.mem_support_iff.mp hj (h j (by simpa using hne))

theorem linearIndependent_of_not_mem {Vs : Fin (N + 1) → Submodule Ω E} (mono : Monotone Vs)
    {gen : Fin N → E} (hmem : ∀ i, gen i ∈ Vs i.succ) (hnot : ∀ i, gen i ∉ Vs i.castSucc) :
    LinearIndependent Ω gen := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  by_contra hne
  push Not at hne
  set S := Finset.univ.filter (fun q : Fin N => a q ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨q, hq⟩ := hne
    exact ⟨q, by simp [hS, hq]⟩
  set i := S.max' hSne
  have hi : a i ≠ 0 := by
    have := S.max'_mem hSne
    simpa [hS] using this
  have hrest : ∑ q ∈ Finset.univ.erase i, a q • gen q ∈ Vs i.castSucc := by
    refine Submodule.sum_mem _ fun q hq => ?_
    by_cases haq : a q = 0
    · rw [haq, zero_smul]
      exact Submodule.zero_mem _
    · have hle : q ≤ i := S.le_max' q (by simp [hS, haq])
      have hlt : q < i := lt_of_le_of_ne hle (Finset.ne_of_mem_erase hq)
      exact Submodule.smul_mem _ _ (mono (Fin.le_def.mpr (by simp; omega)) (hmem q))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at ha
  have hai : a i • gen i ∈ Vs i.castSucc := by
    rw [eq_neg_of_add_eq_zero_left ha]
    exact Submodule.neg_mem _ hrest
  apply hnot i
  have := Submodule.smul_mem _ (a i)⁻¹ hai
  rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at this

end Flags

section Frames

variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
  {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {N : ℕ} {E : Type*}
  [AddCommGroup E] [Module Ω E] {B : ChartBundle o (segreVec y) N E}


omit [∀ k, Fintype (ι k)] in
theorem linearIndependent_gen {Vs : Fin (N + 1) → Submodule Ω E} (mono : Monotone Vs)
    (dim : ∀ i, Module.finrank Ω (Vs i) = (i : ℕ)) {m : Fin N → K → ℤ} {gen : Fin N → E}
    (hmem : ∀ i, gen i ∈ Vs i.succ) (hfr : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsGradedFrame o y B Vs m gen)
    {c : ∀ k, ι k} (hc : segreVec y c ≠ 0) : LinearIndependent Ω gen := by
  classical
  obtain ⟨k, fs, cs, -, -, hsum, hl⟩ := hfr c hc
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      simp at hsum
    · exact h0
  obtain ⟨b, hli, hsp, -, hb⟩ := hl ⟨0, hk⟩
  have : FiniteDimensional Ω E := Module.Finite.of_basis (Module.Basis.mk hli hsp.ge)
  refine linearIndependent_of_not_mem mono hmem fun i hi => ?_
  have hbV : ∀ j : Fin N, j ≤ i → b j ∈ Vs i.castSucc := by
    intro j hj
    obtain ⟨u, -, hu⟩ := hb j
    have h1 : gen j ∈ Vs i.castSucc := by
      rcases hj.lt_or_eq with hlt | rfl
      · exact mono (Fin.le_def.mpr (by simp; omega)) (hmem j)
      · exact hi
    have h2 : Vs j.castSucc ≤ Vs i.castSucc := mono (Fin.le_def.mpr (by simpa using hj))
    have := Submodule.add_mem _ (h2 hu) (Submodule.smul_mem _ (u * IndefiniteRowSideFullHecke.NumbersDVR.Bundles.chartMon y c (m j)) h1)
    simpa using this
  have hli' : LinearIndependent Ω
      (fun j : {j : Fin N // j ≤ i} => (⟨b j, hbV j j.2⟩ : Vs i.castSucc)) :=
    LinearIndependent.of_comp (Vs i.castSucc).subtype (hli.comp Subtype.val Subtype.val_injective)
  have hcard := hli'.fintype_card_le_finrank
  rw [dim] at hcard
  simp only [Fintype.card_subtype, Fin.val_castSucc] at hcard
  have hfl : (Finset.univ.filter fun j : Fin N => j ≤ i) =
      Finset.univ.filter fun j : Fin N => (j : ℕ) < (i : ℕ) + 1 := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
    omega
  rw [hfl, Fin.card_filter_val_lt, min_eq_right (Nat.succ_le_of_lt i.isLt)] at hcard
  omega

theorem eval_ne_zero {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
    [DecidableEq K] {b : K → ℤ} {f g : MRing ι O}
    (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (pointIdeal O y) b f g) : aeval y g ≠ 0 := by
  obtain ⟨⟨α, β, -, hβ, -⟩, -, hg, -⟩ := h
  intro h0
  apply hg
  rw [pointIdeal, RingHom.mem_ker, FlagTypings.pointConeMap_of_isMultiHomog y hβ, h0, map_zero,
    zero_mul]

end Frames

theorem proof : Statement.{u, v, w} := by
  intro O _ _ _ Ω _ _ K _ _ ι _ y N E _ _ B B' ϖ hϖ hP
  have hV : ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor (pointIdeal O y) ϖ b f g ↔
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O y) b f g :=
    fun b f g => (VerticalDivisorCharacterisation.proof O K ι (pointIdeal O y) ϖ b f g hϖ hP).symm
  have hG := fun (B₀ : ChartBundle O (segreVec y) N E) (w₀ : Module.Basis (Fin N) Ω E)
      (b : Fin N → K → ℤ) => GradedFrameCharacterisation.proof O Ω K ι y N E B₀ w₀ b
  refine ⟨fun w w' x x' f g => ⟨fun h => ?_, ?_⟩, fun hc F => ?_⟩
  · have hvert := fun i => (hV _ _ _).1 (h.vertical i)
    have hgy : ∀ i, aeval y (g i) ≠ 0 := fun i => eval_ne_zero (hvert i)
    have hflip := FlagTypings.triangular_flip w w' h.sameFlag
    have hspan : (fun i : Fin (N + 1) => Submodule.span Ω (w' '' {j : Fin N | (j : ℕ) < i})) =
        fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) := by
      funext i
      refine flag_eq w (flag_mono w') (finrank_flag w') (fun j => ?_) i
      rw [mem_flag_iff]
      intro q hq
      exact hflip.1 j q (Fin.lt_def.mpr (by simp at hq; omega))
    refine ⟨{ Vs := fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i})
              mono := flag_mono w
              dim := finrank_flag w
              top := ?_
              deg := x
              gen := w
              gen_mem := fun i => ?_
              frame := (hG B w x).1 h.flag
              deg' := x'
              gen' := w'
              gen'_mem := fun i => ?_
              frame' := ?_
              f := f
              g := g
              rel := fun i => ?_
              vert := hvert }, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · show Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (Fin.last N : ℕ)}) = ⊤
      have hu : {j : Fin N | (j : ℕ) < (Fin.last N : ℕ)} = Set.univ := by
        ext j
        simp
      rw [hu, Set.image_univ, w.span_eq]
    · show w i ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (i.succ : ℕ)})
      rw [mem_flag_iff]
      intro q hq
      rw [w.repr_self, Finsupp.single_apply, if_neg]
      rintro rfl
      simp at hq
    · show w' i ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (i.succ : ℕ)})
      rw [mem_flag_iff]
      intro q hq
      exact h.sameFlag i q (Fin.lt_def.mpr (by simp at hq; omega))
    · have := (hG B' w' x').1 h.flag'
      rwa [hspan] at this
    · show _ ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < (i.castSucc : ℕ)})
      rw [mem_flag_iff]
      intro q hq
      rw [map_sub, map_smul, w.repr_self, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
        Finsupp.single_apply]
      by_cases hiq : i = q
      · subst hiq
        rw [if_pos rfl, mul_one, h.generic i, mul_div_cancel_right₀ _ (hgy i), sub_self]
      · rw [if_neg hiq, mul_zero, sub_zero]
        exact h.sameFlag i q (lt_of_le_of_ne (Fin.le_def.mpr (by simpa using hq)) hiq)
  · rintro ⟨F, hgen, hgen', rfl, rfl, rfl, rfl⟩
    have hVs : F.Vs = fun i : Fin (N + 1) => Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) :=
      funext (flag_eq w F.mono F.dim fun j => by rw [← hgen]; exact F.gen_mem j)
    have hVs' : F.Vs = fun i : Fin (N + 1) => Submodule.span Ω (w' '' {j : Fin N | (j : ℕ) < i}) :=
      funext (flag_eq w' F.mono F.dim fun j => by rw [← hgen']; exact F.gen'_mem j)
    refine ⟨(hG B w F.deg).2 ?_, (hG B' w' F.deg').2 ?_, fun i j hij => ?_,
      fun i => (hV _ _ _).2 (F.vert i), fun i => ?_⟩
    · have := F.frame
      rwa [hVs, hgen] at this
    · have := F.frame'
      rwa [hVs', hgen'] at this
    · have := F.gen'_mem i
      rw [hVs, hgen'] at this
      exact (mem_flag_iff w _ _).1 this j (by simp; omega)
    · have := F.rel i
      rw [hVs, hgen, hgen'] at this
      have h2 := (GradedFrameCharacterisation.repr_of_sub_mem w this).2
      rw [h2, div_mul_cancel₀ _ (eval_ne_zero (F.vert i))]
  · obtain ⟨c, hc⟩ := hc
    exact ⟨linearIndependent_gen F.mono F.dim F.gen_mem F.frame hc,
      linearIndependent_gen F.mono F.dim F.gen'_mem F.frame' hc⟩

end FlagPairCharacterisation

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointNumbers
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

namespace JoinPointNumbers

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fieldNum_spec (F : Type) [Field F] {K' : Type} [Fintype K'] (κ : K' → Type) [∀ k, Fintype (κ k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F κ) := by
  classical
  exact Classical.epsilon_spec (p := fun I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F κ =>
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) ⟨_, IntNumIsFieldIntersection.full F K' κ⟩

theorem redIdeal_map_liftVar {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (W : Ideal (MRing ι O)) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O (W.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))) =
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W).map
        (rename (R := IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)) := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal
  change Ideal.map (MvPolynomial.map (IsLocalRing.residue O))
      (Ideal.map (rename (R := O) (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)).toRingHom W) =
    Ideal.map (rename (R := IsLocalRing.ResidueField O)
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)).toRingHom
      (Ideal.map (MvPolynomial.map (IsLocalRing.residue O)) W)
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun p => ?_
  simp [MvPolynomial.map_rename]

theorem monoList_pullDeg {r : ℕ} (deg : Fin r → K → ℤ) (μ : Fin r →₀ ℕ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) μ =
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ).map (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit)) := by
  simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList, List.map_flatMap, List.map_replicate]

theorem polyNum_join (hV : JoinVariety.Statement) (hN : JoinIntNum.Statement) (F : Type) [Field F]
    (V : Ideal (MRing ι F)) (d : ℕ) (hVd : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF V d) {r : ℕ}
    (deg : Fin r → K → ℤ) (H : MvPolynomial (Fin r) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F (Sum.elim ι ptIdx))
                              (V.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))) d
                              (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) H =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ bs => intNum F V bs) V d deg H := by
  have hV' := hV F K ι V d hVd
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  have hl := monoList_pullDeg deg μ
  by_cases h : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg μ).length = d
  · have h' : (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList
        (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) μ).length = d := by
      rw [hl, List.length_map, h]
    rw [dite_eq_left h', dite_eq_left h, Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full _ (fieldNum_spec F _) _ d _ hV']
    beta_reduce
    rw [← hN F K ι V d]
    congr 1
    funext j
    simp [hl]
  · have h' : ¬ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList
        (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) μ).length = d := by
      rwa [hl, List.length_map]
    rw [dite_eq_right h', dite_eq_right h]

theorem vEval_join (hV : JoinVariety.Statement) (hN : JoinIntNum.Statement) {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (d : ℕ) {r : ℕ} (deg : Fin r → K → ℤ)
    (H : MvPolynomial (Fin r) ℤ) (Z : Ideal (MRing ι O) →₀ ℤ)
    (hZ : ∀ W, Z W ≠ 0 → ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (specialIdeal W) d) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx)) V d
                              (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) H)
      (Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))) Z) =
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                              (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) V d deg H) Z := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finsupp.sum_congr fun W hW => ?_
  rw [redIdeal_map_liftVar]
  beta_reduce
  rw [polyNum_join hV hN _ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d (hZ W (Finsupp.mem_support_iff.mp hW))
    deg H]

theorem mem_divSupp_of_ne {R : Type} [CommRing R] [IsNoetherianRing R] (P : Ideal (MRing ι R))
    (s : MRing ι R) (W : Ideal (MRing ι R)) (h : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W ≠ 0) :
    W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s := by
  classical
  by_contra hW
  apply h
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
  rw [if_neg hW]

theorem intCycle_join (hD : JoinDivCycle.Statement) {R : Type} [CommRing R] [IsNoetherianRing R]
    (P : Ideal (MRing ι R)) (s : MRing ι R) :
    Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
        (P.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx) s)) =
      Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s)) := by
  rw [hD R K ι P s, Finsupp.mapDomain_mapRange _ _ _ _ fun x y => Nat.cast_add x y]

theorem proof (hI : JoinPointIdeal.Statement) (hD : JoinDivCycle.Statement)
    (hV : JoinVariety.Statement) (hN : JoinIntNum.Statement)
    (hF : VerticalComponentFibre.Statement) : JoinPointNumbers.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hM r deg H
  rw [hI O Ω K ι y]
  refine ⟨fun b f g hdiv => ?_, fun a ha => ?_⟩
  · have hc : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O
        ((pointIdeal O y).map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) f)
        (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) g) =
        Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (pointIdeal O y) f g) := by
      unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc
      rw [intCycle_join hD, intCycle_join hD, Finsupp.mapDomain_sub]
    rw [hc]
    refine vEval_join hV hN d deg H _ fun W hW => ?_
    have hvert : (C ϖ : MRing ι O) ∈ W :=
      hdiv.vertical W (by rwa [← BundleExamples.ratCyc_eq])
    obtain ⟨bf, bg, hf, hg, -⟩ := hdiv.degrees
    have hor : ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) f W ≠ 0 ∨
        ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) g W ≠ 0 := by
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      apply hW
      simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, hc.1, hc.2]
    rcases hor with h | h
    · have hs := mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι (pointIdeal O y) d hM f bf hf hdiv.num_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
    · have hs := mem_divSupp_of_ne _ _ _ h
      obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι (pointIdeal O y) d hM g bg hg hdiv.den_not_mem W hs.1 hs.2 hvert
      exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩
  · have hC : (C a : MRing (Sum.elim ι ptIdx) O) =
        rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx) (C a) := (rename_C _ _).symm
    rw [hC, intCycle_join hD]
    refine vEval_join hV hN d deg H _ fun W hW => ?_
    have h : ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) (C a) W ≠ 0 := by
      intro h0
      apply hW
      simp [h0]
    have hs := mem_divSupp_of_ne _ _ _ h
    have hWp : W.IsPrime := hs.1.1.1
    have hCa : (C a : MRing ι O) ∈ W := hs.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hnP : (C a : MRing ι O) ∉ pointIdeal O y := by
      intro hmem
      have hmem' : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := hmem
      rw [hM.noTorsion, Ideal.mem_bot] at hmem'
      exact ha hmem'
    have hvert : (C ϖ : MRing ι O) ∈ W := by
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
      rw [hu, C_mul, C_pow] at hCa
      rcases hWp.mem_or_mem hCa with h1 | h1
      · exact absurd (Ideal.eq_top_of_isUnit_mem _ h1 ((Units.isUnit u).map C)) hWp.ne_top
      · exact hWp.mem_of_pow_mem n h1
    obtain ⟨h1, h2⟩ := hF O ϖ hϖ K ι (pointIdeal O y) d hM (C a) 0 (isWeightedHomogeneous_C _ _) hnP W
      hs.1 hs.2 hvert
    exact ⟨(Objects.isMultiProjPrime_iff _).mp h1, h2⟩

end JoinPointNumbers

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairBundleTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PairBundleTrdeg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
      Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O (pairProjCoord y e φ φ' t)) =
        Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + ((N + 1 : ℕ) : Cardinal)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosureTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagClosureTrdeg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ k : ℕ, 1 ≤ k → k ≤ N →
      Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸
          pointIdeal O (flagClosurePt y w e φ φ' t k)) =
        Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + ((k + 1 : ℕ) : Cardinal)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

