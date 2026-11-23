module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0005
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExtWRec
public import Formalism.LocalToGlobal.GroupLattices.CloudFilling.FillInstRecEqWj
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActEEqOfConjRelated
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.BesselCoeffIndep

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    [Countable Γ]

theorem haar_eq_of_covolume_one (μ μ' : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure] {𝓕 𝓕' : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) (h' : IsFundamentalDomain Γ 𝓕' μ') (h1 : μ 𝓕 = 1) (h1' : μ' 𝓕' = 1) :
    μ' = μ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ'
  have e : μ' = (μ'.haarScalarFactor μ : ℝ≥0∞) • μ := Measure.isMulLeftInvariant_eq_smul μ' μ
  have h2 : IsFundamentalDomain Γ 𝓕 μ' := h.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have h3 : μ' 𝓕 = 1 := (h2.measure_eq h').trans h1'
  rw [e, Measure.smul_apply, h1, smul_eq_mul, mul_one] at h3
  rw [e, h3, one_smul]

theorem setIntegral_mul_right (μ : Measure G) [μ.IsHaarMeasure] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (g : G) :
    ∫ x in 𝓕, f (x * g) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have e : μ.map (· * g) = ((μ.map (· * g)).haarScalarFactor μ : ℝ≥0∞) • μ :=
    Measure.isMulLeftInvariant_eq_smul _ μ
  have h' : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv (f := (· * g)) ⟨(measurable_mul_const g).aemeasurable, by rw [e]; exact Measure.smul_absolutelyContinuous⟩
      Function.bijective_id fun γ x => mul_assoc _ _ _
  have h1 : μ.map (· * g) 𝓕 = μ 𝓕 :=
    ((MeasurableEquiv.mulRight g).map_apply 𝓕).trans (h'.measure_eq h)
  rw [e, Measure.smul_apply, smul_eq_mul] at h1
  have h2 := (ENNReal.mul_left_inj (h.measure_ne_zero (NeZero.ne μ)) hfin).1 (h1.trans (one_mul _).symm)
  rw [h2, one_smul] at e
  have hp : MeasurePreserving (· * g) μ μ := ⟨measurable_mul_const g, e⟩
  rw [← hp.setIntegral_preimage_emb (MeasurableEquiv.mulRight g).measurableEmbedding f 𝓕]
  exact h.setIntegral_eq h' (f := fun x => f (x * g)) fun γ x => by
    show f ((γ : G) * x * g) = _
    rw [mul_assoc, hf _ γ.2]

end General

section Character

open GlobalTheory.BesselCompare (hA_add hA_smul hA_sum hA_vec hA_coeff hD_swap_zero co co_surj)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem hA_act_e (d : BesselDatum A B ι) {n : GA D B} (hn : n ∈ d.NSet) {l i : Fin d.ρ} (h : l ≤ i) :
    hA B (actV B n (d.e l)) (vecA B (d.f i)) = if l = i then 1 else 0 := by
  obtain ⟨c, hc, e⟩ := hn.1 l
  rw [e, hA_add, hA_coeff B d.e d.f d.ef, hc i h, add_zero, hA_vec, d.ef]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem actE_eq_of_conj_related (d : BesselDatum A B ι) {n : GA D B} (hn : n ∈ d.NSet) (i : Fin d.ρ) :
    B.hD (d.aux i.succ) (d.f i) = 0 ∧ ∃ c : Fin d.ρ → AE D, (∀ l, i < l → c l = 0) ∧
      actV B n (d.aux i.succ) = vecA B (d.aux i.succ) + ∑ l, c l • vecA B (d.e l) := by
  unfold BesselDatum.aux
  by_cases hi : i.1 + 1 = d.ρ
  · have : i.succ = Fin.last d.ρ := Fin.ext hi
    rw [this, Fin.snoc_last]
    obtain ⟨c, e⟩ := hn.2 d.z fun j => hD_swap_zero (d.ez j)
    exact ⟨hD_swap_zero (d.fz i), c, fun l hl => absurd (show i.1 < l.1 from hl) (by have := l.2; omega), e⟩
  · have hlt : i.1 + 1 < d.ρ := by have := i.2; omega
    have : i.succ = Fin.castSucc (⟨i.1 + 1, hlt⟩ : Fin d.ρ) := Fin.ext rfl
    rw [this, Fin.snoc_castSucc]
    obtain ⟨c, hc, e⟩ := hn.1 ⟨i.1 + 1, hlt⟩
    refine ⟨?_, c, fun l hl => hc l (show i.1 + 1 ≤ l.1 from hl), e⟩
    rw [d.ef, if_neg (fun h => by have : i.1 + 1 = i.1 := congrArg Fin.val h; omega)]

theorem simpleSum_mul (d : BesselDatum A B ι) {n n' : GA D B} (hn : n ∈ d.NSet) (hn' : n' ∈ d.NSet) :
    d.simpleSum (n * n') = d.simpleSum n + d.simpleSum n' := by
  unfold BesselDatum.simpleSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨h0, c, hc, e⟩ := actE_eq_of_conj_related d hn' i
  have e1 : actV B (n * n') (d.aux i.succ) = actV B n (d.aux i.succ) + ∑ l, c l • actV B n (d.e l) := by
    have : actV B (n * n') (d.aux i.succ) = (mt B n).mulVec (actV B n' (d.aux i.succ)) := mulVec_mul _ _ _
    rw [this, e, Matrix.mulVec_add, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    rfl
  rw [e1, e, hA_add, hA_add, hA_coeff B d.e d.f d.ef, hA_vec, h0, RingHom.map_zero, zero_add, hA_sum,
    Finset.sum_eq_single i]
  · rw [hA_smul, hA_act_e d hn le_rfl, if_pos rfl, mul_one]
  · intro l _ hl
    rw [hA_smul]
    rcases lt_or_ge i l with h | h
    · rw [hc l h, zero_mul]
    · rw [hA_act_e d hn h, if_neg hl, mul_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem psiN_mul (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) {n n' : GA D B} (hn : n ∈ d.NSet)
    (hn' : n' ∈ d.NSet) : d.psiN ψ (n * n') = d.psiN ψ n * d.psiN ψ n' := by
  unfold BesselDatum.psiN
  rw [simpleSum_mul d hn hn', mul_add, LinearMap.map_add (f := _), AddChar.map_add_eq_mul]

theorem psiN_rat (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) {n : GA D B}
    (hn : n ∈ GQ B) : d.psiN ψ n = 1 := by
  obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
  have h1 : mt B n = (g : Matrix _ _ D.host.E).map (incA D) := (congrArg Units.val hg).symm
  have h2 : ∀ v, ∃ w, actV B n v = vecA B w := fun v => by
    obtain ⟨w, hw⟩ := co_surj B ((g : Matrix _ _ D.host.E).mulVec (co B v))
    refine ⟨w, funext fun k => ?_⟩
    have : vecA B w k = incA D (co B w k) := rfl
    rw [this, hw, RingHom.map_mulVec, actV, h1]
    rfl
  choose w hw using h2
  have h3 : ∀ e : D.host.E, Algebra.trace (AF D.host.F) (AE D) (incA D e) =
      algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := fun e => by
    show Algebra.trace (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) (1 ⊗ₜ e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  unfold BesselDatum.psiN BesselDatum.simpleSum
  simp only [hw, hA_vec]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum (incA D), ← RingHom.map_mul, h3, hψ.2.2.1]

end Character

theorem coeff_indep_and_equivariant : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ F : GA D B → ℂ, (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → (∀ ν' 𝓝', d.IsUnitPair ν' 𝓝' → d.coeff ψ ν' 𝓝' F = d.coeff ψ ν 𝓝 F) ∧ ∀ n ∈ d.N, ∀ g, d.coeff ψ ν 𝓝 F (n * g) = d.psiN ψ n * d.coeff ψ ν 𝓝 F g := by
  intro D A B ι d ψ hψ F hF ν 𝓝 ⟨hν, h𝓝, h1⟩
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hcl := (GlobalTheory.BesselClosed.N_eq_and_isClosed D A B ι d).2
  have : LocallyCompactSpace d.N := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology d.N := TopologicalSpace.Subtype.secondCountableTopology _
  have : BorelSpace d.N := Subtype.borelSpace _
  have : Countable d.NQ :=
    Function.Injective.countable (f := fun γ : d.NQ => (⟨γ.1.1, γ.2⟩ : GQ B)) fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun t : GQ B => (t : GA D B)) hab))
  have hS : ∀ n ∈ d.N, n ∈ d.NSet := fun n hn => (GlobalTheory.BesselClosed.N_eq_and_isClosed D A B ι d).1 ▸ SetLike.mem_coe.2 hn
  have hmul : ∀ n ∈ d.N, ∀ n' ∈ d.N, d.psiN ψ (n * n') = d.psiN ψ n * d.psiN ψ n' := fun n hn n' hn' =>
    psiN_mul d ψ (hS n hn) (hS n' hn')
  have hrat : ∀ n ∈ d.N, n ∈ GQ B → d.psiN ψ n = 1 := fun n _ hn' => psiN_rat d ψ hψ.1 hn'
  have hinv : ∀ g, ∀ γ ∈ d.NQ, ∀ x : d.N,
      F (((γ * x : d.N) : GA D B) * g) * star (d.psiN ψ ((γ * x : d.N) : GA D B)) =
        F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B)) := fun g γ hγ x => by
    rw [Subgroup.coe_mul, mul_assoc, hF (γ : GA D B) hγ, hmul _ γ.2 _ x.2, hrat _ γ.2 hγ, one_mul]
  refine ⟨fun ν' 𝓝' ⟨hν', h𝓝', h1'⟩ => ?_, fun n hn g => ?_⟩
  · obtain rfl := haar_eq_of_covolume_one d.NQ ν ν' h𝓝 h𝓝' h1 h1'
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup d.NQ
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup d.NQ ν'
    funext g
    exact h𝓝'.setIntegral_eq h𝓝 (f := fun x : d.N => F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B)))
      fun γ x => hinv g γ γ.2 x
  · have key := setIntegral_mul_right d.NQ ν h𝓝 (by rw [h1]; exact ENNReal.one_ne_top)
      (fun x : d.N => F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B))) (hinv g) ⟨n, hn⟩
    unfold BesselDatum.coeff
    rw [← key, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hu : d.psiN ψ n * star (d.psiN ψ n) = 1 := by
      have : ‖d.psiN ψ n‖ = 1 := hψ.1.2.1 _
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, this]; simp
    simp only [Subgroup.coe_mul]
    rw [hmul _ x.2 _ hn, star_mul', mul_assoc (x : GA D B)]
    linear_combination (-(F (x * (n * g)) * star (d.psiN ψ x))) * hu

end GlobalTheory.Mem.BesselCoeffIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddCharIsIntegral
section
noncomputable section

namespace GlobalTheory.Mem.AwayChar

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
open scoped TensorProduct

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adelic_ext {n : ℕ} (g h : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (H : ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) g = bc (prV (E := E) v) h) : g = h := by
  apply Units.ext
  ext i j
  rw [← sub_eq_zero]
  apply Formalism.UG.P.afsplit_inj
  intro w
  rw [map_sub]
  have h1 := congrArg Units.val (H w)
  rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplit_coe_bc_prV] at h1
  have := congrFun (congrFun h1 i) j
  simp only [Matrix.map_apply] at this
  rw [this, sub_self]

theorem exists_trivial_on {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (s : Finset (HeightOneSpectrum (𝓞 F)))
    (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ∃ k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), (∀ v ∈ s, bc (prV (E := E) v) k = 1) ∧
      ∀ v ∉ s, bc (prV (E := E) v) k = bc (prV (E := E) v) g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨g, hg, by simp, fun _ _ => rfl⟩
  | insert v s hv ih =>
    obtain ⟨k, hk, h1, h2⟩ := ih
    have hne : ∀ w, w ≠ v → bc (prV (E := E) w) (Formalism.UG.P.afsplitU v 1 k) = bc (prV (E := E) w) k := by
      intro w hw
      apply Units.ext
      rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw]
      rfl
    refine ⟨Formalism.UG.P.afsplitU v 1 k, Formalism.UG.P.afsplitU_mem v σ J 1 k (one_mem _) hk, fun w hw => ?_, fun w hw => ?_⟩
    · by_cases h : w = v
      · subst h; exact Formalism.UG.P.afsplit_right1 w 1 k
      · rw [hne w h]; exact h1 w ((Finset.mem_insert.1 hw).resolve_left h)
    · rw [Finset.mem_insert, not_or] at hw
      rw [hne w hw.1]; exact h2 w hw.2

theorem finite_over (p : ℕ) (hp : p ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem exists_away_mem (S : StepLevel F E σ J T f bad) (p : ℕ) (hp : p ≠ 0)
    (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hw : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) g ∈ S.Uloc w) :
    ∃ κ : S.U, (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) κ.1 = 1) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) κ.1 = bc (prV (E := E) w) g := by
  obtain ⟨k, hk, h1, h2⟩ := exists_trivial_on σ J (finite_over (F := F) p hp).toFinset g hg
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h1 h2
  refine ⟨⟨k, (S.U_eq k).2 ⟨hk, fun v => ?_⟩⟩, h1, h2⟩
  by_cases hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
  · rw [h1 v hv]; exact one_mem _
  · rw [h2 v hv]; exact hw v hv

theorem addChar_isIntegral {A : Type} [AddCommGroup A] [Finite A] (ψ : AddChar A ℂ) (x : A) : IsIntegral ℤ (ψ x) := by
  have h : ψ x ^ Nat.card A = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  exact IsIntegral.of_pow Nat.card_pos (by rw [h]; exact isIntegral_one)

theorem chi_isIntegral {gp : Fin 2 → ℕ} {S : StepLevel F E σ J T f bad} {G : GLoc F E σ gp} {a t skip fc : ℕ} {zl : Bool}
    (X : GLev S G a t 0 skip fc zl) (κ : S.U) : IsIntegral ℤ ((S.chi κ : ℂˣ) : ℂ) := by
  rw [X.chi_eq κ]
  refine IsIntegral.prod _ fun i _ => ?_
  refine finprod_induction (fun z : ℂ => IsIntegral ℤ z) isIntegral_one (fun _ _ hx hy => hx.mul hy) fun v => ?_
  refine finprod_induction (fun z : ℂ => IsIntegral ℤ z) isIntegral_one (fun _ _ hx hy => hx.mul hy) fun h => ?_
  haveI : Finite (kv F v) := Formalism.UG.P.glint_finite_residueField v
  unfold lamJ
  rw [Finset.range_zero, Finset.prod_empty, mul_one, ← AddChar.map_neg_eq_inv]
  exact addChar_isIntegral _ _

end Adelic

theorem exists_inv_char {U LL O Kf : Type} [Group U] [Field LL] [CommRing O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (χ : U →* ℂˣ) (embLL : LL →+* ℂ) (e : LL →+* Kf)
    (h : ∀ κ, ∃ r : LL, embLL r = (χ κ : ℂ) ∧ e r ∈ Set.range (algebraMap O Kf)) :
    ∃ c : U →* Oˣ, ∀ κ, ∃ r : LL, embLL r = (χ κ : ℂ) ∧ algebraMap O Kf ((c κ : Oˣ) : O) * e r = 1 := by
  choose r hr o ho using h
  have r1 : r 1 = 1 := embLL.injective (by rw [hr]; simp)
  have rm : ∀ a b, r (a * b) = r a * r b := fun a b => embLL.injective (by rw [map_mul, hr, hr, hr]; simp)
  let o' : U →* O :=
    { toFun := o
      map_one' := hinj (by rw [ho, r1, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [map_mul, ho, ho, ho, rm, map_mul]) }
  refine ⟨o'.toHomUnits⁻¹, fun κ => ⟨r κ, hr κ, ?_⟩⟩
  rw [← ho κ, ← map_mul]
  have : o κ = ((o'.toHomUnits κ : Oˣ) : O) := rfl
  rw [this, MonoidHom.inv_apply, Units.inv_mul, map_one]

section Gen

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem exists_psiTied {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E sp.cm.sig J T f bad) (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) (hp : p ≠ 0) (hk : R.k = n)
    (hJ : ∀ x y, J x y = sp.gram0 (Fin.cast hk.symm x) (Fin.cast hk.symm y))
    (hU : ∀ v, S.Uloc v = (L.Uloc v).map (reGL hk _).toMonoidHom)
    {LL O Kf : Type} [Field LL] [CommRing O] [Field Kf] [Algebra O Kf] (hinj : Function.Injective (algebraMap O Kf))
    (embLL : LL →+* ℂ) (e : LL →+* Kf)
    (h : ∀ κ, ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ e r ∈ Set.range (algebraMap O Kf)) :
    ∃ ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ, PsiTied S L p hk embLL e ψ := by
  obtain ⟨c, hc⟩ := exists_inv_char hinj S.chi embLL e h
  have hex : ∀ a : Formalism.L2.Herm.awayFrom₂ L p, ∃ κ : S.U,
      (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) κ.1 = 1) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
        bc (prV (E := E) w) κ.1 = bc (prV (E := E) w) (reGL hk _ a.1) := by
    intro a
    obtain ⟨h2, h3⟩ := (mem_awayP_iff L p a.1).1 a.2
    refine exists_away_mem S p hp _ (reGL_mem_UPts hk sp.cm.sig sp.gram0 J hJ _ _ h2) fun w hw => ?_
    rw [bc_reGL, hU w]
    exact Subgroup.mem_map.2 ⟨_, h3 w hw, rfl⟩
  choose κ h1 h2 using hex
  have huniq : ∀ (a : Formalism.L2.Herm.awayFrom₂ L p) (k : S.U),
      (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k.1 = 1) →
      (∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
        bc (prV (E := E) w) k.1 = bc (prV (E := E) w) (reGL hk _ a.1)) → κ a = k := by
    intro a k k1 k2
    refine Subtype.ext (adelic_ext _ _ fun v => ?_)
    by_cases hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
    · rw [h1 a v hv, k1 v hv]
    · rw [h2 a v hv, k2 v hv]
  let K : Formalism.L2.Herm.awayFrom₂ L p →* S.U := MonoidHom.mk' κ fun a b => by
    refine huniq _ _ (fun v hv => ?_) (fun v hv => ?_)
    · rw [Subgroup.coe_mul, map_mul, h1 a v hv, h1 b v hv, mul_one]
    · rw [Subgroup.coe_mul, map_mul, h2 a v hv, h2 b v hv, Subgroup.coe_mul, map_mul, map_mul]
  refine ⟨c.comp K, fun a k k1 k2 => ?_⟩
  obtain rfl := huniq a k k1 k2
  exact hc (κ a)

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar


set_option maxHeartbeats 4000000 in
theorem exists_psi : ∀ (D : D7) (L0 : LevelData D) (T : ∀ u : D.what₂.Word, Forms0 D u), (∀ u, Joint0 L0 u (T u)) → (∀ u, LevelZeroCharacterRational T u) →
    ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ∃ ψ : Formalism.L2.Herm.awayFrom₂ (L0 u) (D.what₂.places.resChar w) →*
        (ORec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w)))))ˣ,
      PsiTied (LL := D.what₂.LL) (O := ORec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w)))))
        (Kf := KfRec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) ((T u).cls0).lev (L0 u)
        (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        (embRec D w (orderOf (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) ψ := by
  intro D L0 T hJ hψ u w _
  refine exists_psiTied ((T u).cls0).lev (L0 u) _ (D.what₂.places.resChar_prime w).ne_zero (rank_eq_first_level D.R) (Formalism.L2.G.Cmp.gramN_zero D)
    (hJ u).Uloc_eq Subtype.val_injective _ _ fun κ => ?_
  obtain ⟨r, hr⟩ := chiRatAll_rec T u (hψ u) κ
  refine ⟨r, hr, (embRec_int D w _ r).1 ((val_nonneg_iff D w r).2 ?_)⟩
  have h1 : IsIntegral ℤ (D.what₂.embLL r) := hr ▸ chi_isIntegral ((T u).glev0) κ
  have h2 : IsIntegral ℤ r := (isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective).1 h1
  exact (D.plEq w).valuation_le_one (K := D.what₂.LL) (⟨r, h2⟩ : 𝓞 D.what₂.LL)

end GlobalTheory.Mem.AwayChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosableOfSmoothing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem closable_of_smoothing : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A : H →ₗ[ℂ] E), (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ⟪A (σ g u), A (σ g w)⟫_ℂ = ⟪A u, A w⟫_ℂ) → (∀ u ∈ smSub G (trRep σ P), ∀ f : E, Continuous fun g : Formalism.REAL.UJ ε => ⟪f, A (σ (umat g) u)⟫_ℂ) → (∀ φ, IsTest φ → Continuous fun w => A (gard ε σ φ w)) → (∀ φ, IsTest φ → ∀ w ∈ smSub G (trRep σ P), ∀ f : E, ⟪f, A (gard ε σ φ w)⟫_ℂ = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪f, A (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε)) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ smSub G (trRep σ P)) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0) := by
  intro n ε H _ _ _ σ P G hP hG hσ E _ _ A h1 h2 h3 h4 u f hu hu0 hA
  have hmul : ∀ (g : Formalism.REAL.UJ ε) (v : H), σ (umat g) (σ (umat g⁻¹) v) = v := by
    intro g v
    have e : σ (umat g * umat g⁻¹) = _ := hσ.1.2 _ g.2 _ (g⁻¹).2
    have e1 : umat g * umat g⁻¹ = 1 := by
      have : umat (g * g⁻¹) = umat (1 : Formalism.REAL.UJ ε) := by rw [mul_inv_cancel]
      exact this
    rw [e1, hσ.1.1] at e
    exact (congrArg (fun T : H →L[ℂ] H => T v) e).symm
  have key : ∀ v ∈ smSub G (trRep σ P), ⟪A v, f⟫_ℂ = 0 := by
    intro v hv
    have hmem : ∀ g : Formalism.REAL.UJ ε, σ (umat g⁻¹) v ∈ smSub G (trRep σ P) := fun g =>
      sigma_mem hP hG hσ hv (g⁻¹).2
    have hc : ∀ y : E, Continuous fun g : Formalism.REAL.UJ ε => ⟪A (σ (umat g⁻¹) v), y⟫_ℂ := by
      intro y
      have := Complex.continuous_conj.comp ((h2 v hv y).comp continuous_inv)
      simpa only [Function.comp_def, inner_conj_symm] using this
    have hnorm : ∀ g : Formalism.REAL.UJ ε, ‖A (σ (umat g⁻¹) v)‖ = ‖A v‖ := by
      intro g
      have := h1 _ (g⁻¹).2 v hv v hv
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) (A v)]
      exact congrArg (fun z => √(RCLike.re z)) this
    have h0 := eq_zero_of_forall_test (F := fun g : Formalism.REAL.UJ ε => ⟪A (σ (umat g⁻¹) v), f⟫_ℂ) (hc f) (by
      intro φ hφ
      have hg0 : gard ε σ φ 0 = 0 := by simp [gard]
      have t1 : Tendsto (fun i => ⟪A v, A (gard ε σ φ (u i))⟫_ℂ) atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := A v)).inner (𝕜 := ℂ) (((h3 φ hφ).tendsto 0).comp hu0)
        simpa [hg0, Function.comp_def] using this
      have e : ∀ i, ⟪A v, A (gard ε σ φ (u i))⟫_ℂ
          = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪A (σ (umat g⁻¹) v), A (u i)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
        intro i
        rw [h4 φ hφ _ (hu i)]
        congr 1
        funext g
        rw [← h1 _ g.2 _ (hmem g) _ (hu i)]
        erw [hmul]
      have hψi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) (Formalism.REAL.muG ε) := by
        simpa using hφ.integrable (F := fun _ : Formalism.REAL.UJ ε => (1 : ℝ)) continuous_const
      have t2 : Tendsto (fun i => ⟪A v, A (gard ε σ φ (u i))⟫_ℂ) atTop
          (𝓝 (∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪A (σ (umat g⁻¹) v), f⟫_ℂ ∂(Formalism.REAL.muG ε))) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        have t3 : Tendsto (fun i => (∫ g : Formalism.REAL.UJ ε, ‖φ (umat g)‖ ∂(Formalism.REAL.muG ε)) * (‖A v‖ * ‖A (u i) - f‖))
            atTop (𝓝 0) := by
          have := ((tendsto_iff_norm_sub_tendsto_zero.1 hA).const_mul ‖A v‖).const_mul
            (∫ g : Formalism.REAL.UJ ε, ‖φ (umat g)‖ ∂(Formalism.REAL.muG ε))
          simpa using this
        refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) t3
        rw [e, ← integral_sub (hφ.integrable (hc _)) (hφ.integrable (hc _)), ← integral_mul_const]
        refine norm_integral_le_of_norm_le (hψi.norm.mul_const _) (Eventually.of_forall fun g => ?_)
        rw [← smul_sub, norm_smul, ← inner_sub_right, ← hnorm g]
        exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
      exact tendsto_nhds_unique t2 t1)
    have e : σ (umat (1 : Formalism.REAL.UJ ε)⁻¹) v = v := by
      rw [inv_one]
      show σ 1 v = v
      rw [hσ.1.1]; rfl
    simpa only [e] using h0
  have t := hA.inner (𝕜 := ℂ) (tendsto_const_nhds (x := f))
  simp only [key _ (hu _)] at t
  exact inner_self_eq_zero.1 (tendsto_nhds_unique t tendsto_const_nhds)

end GlobalTheory.SmVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffIntegrableContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.CoefInt

theorem coeff_integrable_continuous : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → ∀ F : GA D B → ℂ, Continuous F → (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → (∀ g, IntegrableOn (fun n : d.N => F ((n : GA D B) * g) * star (d.psiN ψ (n : GA D B))) 𝓝 ν) ∧ Continuous (d.coeff ψ ν 𝓝 F) ∧ ∀ C : Set (GA D B), IsCompact C → ∃ M : ℝ, ∀ n ∈ d.N, ∀ g ∈ C, ‖F (n * g)‖ ≤ M :=
  coeff_integrable_continuous_of fun D B ρ e he => (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1

end GlobalTheory.RootExch.CoefInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousInnerL2Translate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem continuous_inner_l2_translate :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a : H →ₗ[ℂ] (X → ℂ)) (A : H →ₗ[ℂ] Lp ℂ 2 ν), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), (A w : X → ℂ) =ᵐ[ν] a w) → ∀ u ∈ smSub G (trRep σ P), ∀ f : Lp ℂ 2 ν, Continuous fun g : Formalism.REAL.UJ ε => ⟪f, A (σ (umat g) u)⟫_ℂ := by
  intro n ε H _ _ _ σ P G hP hG hσ X _ _ _ _ ν _ act hact a A ha _ hA u hu f
  obtain ⟨hc, ⟨C, hC⟩, heq⟩ := ha u hu
  have hfi : Integrable (f : X → ℂ) ν := (Lp.memLp f).integrable (by norm_num)
  have key : (fun g : Formalism.REAL.UJ ε => ⟪f, A (σ (umat g) u)⟫_ℂ)
      = fun g => ∫ x, ⟪f x, a u (act g x)⟫_ℂ ∂ν := by
    funext g
    rw [L2.inner_def]
    have hm : σ (umat g) u ∈ smSub G (trRep σ P) := by
      exact sigma_mem hP hG hσ hu g.2
    refine integral_congr_ae ?_
    filter_upwards [hA _ hm] with x hx
    rw [hx, heq]
  rw [key]
  refine continuous_of_dominated (bound := fun x => ‖f x‖ * C) ?_ ?_ (hfi.norm.mul_const C) ?_
  · intro g
    refine AEStronglyMeasurable.inner hfi.aestronglyMeasurable ?_
    exact (hc.comp (hact.comp (Continuous.prodMk_right g))).aestronglyMeasurable
  · intro g
    refine Eventually.of_forall fun x => ?_
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
  · refine Eventually.of_forall fun x => ?_
    exact continuous_const.inner (hc.comp (hact.comp (Continuous.prodMk_left x)))

end GlobalTheory.SmVec
end

