module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0044

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiHomogRename
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)

namespace RowChartAct

variable {S : Type} [CommRing S] {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_mul {f g : MRingOver S ι} {a b : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf m₁ hm₁ k, hg m₂ hm₂ k, Pi.add_apply]

theorem isMultiHomog_rename [DecidableEq K] (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {f : MvPolynomial (Fin (N + 1)) S}
    {d : ℕ} (hf : f.IsHomogeneous d) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog
      (rename (fun j => (⟨k₀, e.symm j⟩ : Σ k, ι k)) f) (Pi.single k₀ d) := by
  classical
  have hρ : Function.Injective (fun j => (⟨k₀, e.symm j⟩ : Σ k, ι k)) := fun j j' h =>
    e.symm.injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  intro m' hm' k
  rw [support_rename_of_injective hρ] at hm'
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
  have hd := hf (mem_support_iff.mp hm)
  by_cases hk : k = k₀
  · subst hk
    have hval : ∀ i, Finsupp.mapDomain (fun j => (⟨k, e.symm j⟩ : Σ k, ι k)) m ⟨k, i⟩ = m (e i) := fun i => by
      have hi : (⟨k, i⟩ : Σ k, ι k) = (fun j => (⟨k, e.symm j⟩ : Σ k, ι k)) (e i) := by simp
      rw [hi, Finsupp.mapDomain_apply_of_injective hρ]
    simp_rw [hval]
    rw [Pi.single_eq_same, Equiv.sum_comp e (fun j => m j), ← hd]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Pi.single_eq_of_ne hk]
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨j, hj⟩
    exact hk (congrArg Sigma.fst hj).symm

end RowChartAct

theorem RowChartAct.proof : RowChartAct.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y k₀ N e γ J I r a hr ha
  obtain ⟨f, s, d, hs, hf, hsd, rfl⟩ := hr
  set ρ : Fin (N + 1) → Σ k, ι k := fun j => ⟨k₀, e.symm j⟩ with hρ
  have hsmem : rename ρ s ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) := by
    have hle : (Kleiman.monos (S := S) J.1).map (rename ρ : MvPolynomial _ S →ₐ[S] MRingOver S ι).toRingHom.toMonoidHom ≤
        ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) := by
      rw [Kleiman.monos, MonoidHom.map_mclosure]
      refine Submonoid.closure_le.mpr ?_
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      refine Submonoid.subset_closure ⟨k₀, e.symm j, ?_, by simp [ρ]⟩
      unfold baseCell
      rw [Function.update_self]
      exact Finset.mem_union_right _ (Finset.mem_map_of_mem _ hj)
    exact hle ⟨s, hs, rfl⟩
  unfold cellSec at ha ⊢
  split_ifs at ha ⊢ with hM
  · induction ha using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, t, b, ht, htb, hγ, hg, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨rename ρ f * g, rename ρ s * t, b + Pi.single k₀ d, mul_mem hsmem ht, ?_, ?_, ?_, ?_⟩
      · rw [add_comm b]
        exact RowChartAct.isMultiHomog_mul (RowChartAct.isMultiHomog_rename k₀ e hsd) htb
      · intro k
        have h1 := hγ k
        simp only [Pi.add_apply, Nat.cast_add]
        omega
      · have h2 := RowChartAct.isMultiHomog_mul (RowChartAct.isMultiHomog_rename k₀ e hf) hg
        have heq : (Pi.single k₀ d + fun k => (γ k + b k).toNat) =
            fun k => (γ k + ((b + Pi.single k₀ d : K → ℕ) k : ℕ)).toNat := funext fun k => by
          have h1 := hγ k
          simp only [Pi.add_apply, Nat.cast_add]
          omega
        rw [heq] at h2
        exact h2
      · simp only [map_mul, aeval_rename]
        rw [div_mul_div_comm]
        rfl
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | smul c u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu
  · rw [Submodule.mem_bot] at ha ⊢
    rw [ha, mul_zero]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeSegreLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

noncomputable section

namespace SegreNef

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem map_id_ideal {σ : Type*} (I : Ideal (MvPolynomial σ F)) :
    I.map (MvPolynomial.map (RingHom.id F)) = I := by
  have h : (MvPolynomial.map (RingHom.id F) : MvPolynomial σ F →+* MvPolynomial σ F) = RingHom.id _ :=
    RingHom.ext MvPolynomial.map_id
  rw [h, Ideal.map_id]

theorem comap_segreLift (W : Ideal (MRing ι F)) : (segreLift ι F W).comap (segreIncl ι F) = W := by
  have h : (segreLiftMap ι F W).comp (segreIncl ι F) =
      (Polynomial.CAlgHom : (MRing ι F ⧸ W) →ₐ[F] Polynomial (MRing ι F ⧸ W)).comp
        (Ideal.Quotient.mkₐ F W) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [segreIncl, segreLiftMap, segreLiftVal]
  ext g
  rw [Ideal.mem_comap, segreLift, RingHom.mem_ker]
  have hg := congrArg (fun φ => φ g) h
  simp only [AlgHom.comp_apply] at hg
  rw [hg, Polynomial.CAlgHom_apply, Polynomial.C_eq_zero, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem]

theorem genPt_block_ne_zero (W : Ideal (MRing ι F)) [W.IsPrime] (hW : IsMultiProjPrime W) :
    ∀ k, ∃ i, ModelGenericPoint.genPt W ⟨k, i⟩ ≠ 0 := fun k => by
  obtain ⟨i, hi⟩ := hW.relevant k
  exact ⟨i, (ModelGenericPoint.genPt_ne_zero W _).mpr hi⟩

theorem segreJoin_block_ne_zero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, segreJoin y ⟨k, i⟩ ≠ 0
  | Sum.inl () => ⟨fun k => (hy k).choose,
      show ∏ k, y ⟨k, (hy k).choose⟩ ≠ 0 from Finset.prod_ne_zero_iff.mpr fun k _ => (hy k).choose_spec⟩
  | Sum.inr k => hy k

theorem segreLift_eq_mIdealOver (W : Ideal (MRing ι F)) [W.IsPrime] (hW : IsMultiProjPrime W) :
    segreLift ι F W = mIdealOver F (segreJoin (ModelGenericPoint.genPt W)) := by
  have hy : mIdealOver F (ModelGenericPoint.genPt W) = W :=
    ModelGenericPoint.mIdealOver_genPt W hW.multiHomog
  have hP' : IsMultiProjPrime (mIdealOver F (segreJoin (ModelGenericPoint.genPt W))) :=
    isMultiProjPrime_mIdealOver _ (segreJoin_block_ne_zero _ (genPt_block_ne_zero W hW))
  obtain ⟨hrel, hle, hlift⟩ := SegreFibreIdeal.proof F _ F (RingHom.id F) K ι (ModelGenericPoint.genPt W)
  simp only [map_id_ideal] at hrel hle hlift
  have hc : (mIdealOver F (segreJoin (ModelGenericPoint.genPt W))).comap (segreIncl ι F) = W := by
    refine le_antisymm ?_ (hy.ge.trans hle)
    have h := hlift W hy.le
    exact (Ideal.comap_mono h).trans (comap_segreLift W).le
  calc segreLift ι F W
      = segreLift ι F ((mIdealOver F (segreJoin (ModelGenericPoint.genPt W))).comap (segreIncl ι F)) := by
        rw [hc]
    _ = _ := ((SegreLiftComap.proof F K ι _ hP' hrel).2).symm

theorem isMultiProjPrime_segreLift (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) :
    IsMultiProjPrime (segreLift ι F W) := by
  have := hW.isPrime
  rw [segreLift_eq_mIdealOver W hW]
  exact isMultiProjPrime_mIdealOver _ (segreJoin_block_ne_zero _ (genPt_block_ne_zero W hW))

end SegreNef

open SegreNef

theorem SegreLiftRelDim.proof_of_segreDim (hD : SegreDim.Statement) : SegreLiftRelDim.Statement := by
  intro F _ K _ _ ι _ W hW
  have := hW.isPrime
  rw [segreLift_eq_mIdealOver W hW,
    hD F K ι _ (ModelGenericPoint.genPt W) (genPt_block_ne_zero W hW),
    ModelGenericPoint.mIdealOver_genPt W hW.multiHomog]

theorem SegreLiftIntNum.proof_of_segreNum (hN : SegreNum.Statement) : SegreLiftIntNum.Statement := by
  intro F _ K _ _ ι _ W hW β
  have := hW.isPrime
  have h := hN F K ι _ (ModelGenericPoint.genPt W) (genPt_block_ne_zero W hW) 1 ![β]
  have hfun : (fun j : Fin 1 => IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) (![β] j)) = ![IndefiniteRowSideFullHecke.Kleiman2.pullDeg β] := by
    funext j
    fin_cases j
    rfl
  rw [hfun, ModelGenericPoint.mIdealOver_genPt W hW.multiHomog] at h
  rw [segreLift_eq_mIdealOver W hW]
  exact h

theorem SegreNef.proof_of_lift (hC : SegreLiftRelDim.Statement) (hN : SegreLiftIntNum.Statement) :
    SegreNef.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y _ β
  have h := segreFibresNef_of_map SegreLiftComap.proof (fun F _ K _ _ ι _ W hW => isMultiProjPrime_segreLift W hW)
    hC hN SegreFibreIdeal.proof F Ω F (RingHom.id F) K ι y β
  rw [map_id_ideal, map_id_ideal] at h
  exact h

theorem SegreNef.proof (hD : SegreDim.Statement) (hN : SegreNum.Statement) : SegreNef.Statement :=
  SegreNef.proof_of_lift (SegreLiftRelDim.proof_of_segreDim hD) (SegreLiftIntNum.proof_of_segreNum hN)

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PChartSecMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section Charts

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]
  [Algebra S Ω]

theorem prod_zpow_add_baseDeg (y : (Σ k, ι k) → Ω) (k₀ : K) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (δ : K → ℤ) (m : ℤ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(δ + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      (∏ k, y ⟨k, c k⟩ ^ (-δ k)) * y ⟨k₀, c k₀⟩ ^ (-m) := by
  have hterm : ∀ k, y ⟨k, c k⟩ ^ (-(δ + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      y ⟨k, c k⟩ ^ (-δ k) * (if k = k₀ then y ⟨k, c k⟩ ^ (-m) else 1) := by
    intro k
    simp only [Pi.add_apply, Pi.smul_apply, IndefiniteRowSideFullHecke.Kleiman2.baseDeg, smul_eq_mul]
    by_cases hk : k = k₀
    · subst hk
      rw [Pi.single_eq_same, if_pos rfl, mul_one, neg_add, zpow_add₀ (hc _)]
    · rw [Pi.single_eq_of_ne hk, if_neg hk, mul_zero, add_zero, mul_one]
  rw [Finset.prod_congr rfl (fun k _ => hterm k), Finset.prod_mul_distrib, Finset.prod_ite_eq',
    if_pos (Finset.mem_univ _)]

def baseRatio (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (c : ∀ k, ι k) : Ω :=
  Kleiman.xProd I * (y ⟨k₀, c k₀⟩ ^ I.1.card)⁻¹


omit [Fintype K] [DecidableEq K] in
theorem baseRatio_mem (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (c : ∀ k, ι k) :
    baseRatio y k₀ I c ∈ chartRingOver S y c := by
  have h : baseRatio y k₀ I c = ∏ i ∈ I.1, y ⟨k₀, e.symm i⟩ / y ⟨k₀, c k₀⟩ := by
    rw [Finset.prod_div_distrib, Finset.prod_const, div_eq_mul_inv]
    rfl
  rw [h]
  exact prod_mem fun i _ => Algebra.subset_adjoin ⟨⟨k₀, e.symm i⟩, rfl⟩

theorem mem_chartSecOver_iff (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (δ : K → ℤ)
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (t : Ω) :
    t ∈ chartSecOver S y k₀ e δ I ↔ ∃ n : ℕ, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      baseRatio y k₀ I c ^ n * (t * ∏ k, y ⟨k, c k⟩ ^ (-δ k)) ∈ chartRingOver S y c := by
  simp only [chartSecOver, Set.mem_ofPred_eq]
  refine exists_congr fun n => ?_
  rw [mem_secOver_iff_charts]
  refine forall_congr' fun c => forall_congr' fun hc => ?_
  rw [prod_zpow_add_baseDeg y k₀ c hc]
  have h : Kleiman.xProd I ^ n * t * ((∏ k, y ⟨k, c k⟩ ^ (-δ k)) *
      y ⟨k₀, c k₀⟩ ^ (-(((n * I.1.card : ℕ) : ℤ)))) =
      baseRatio y k₀ I c ^ n * (t * ∏ k, y ⟨k, c k⟩ ^ (-δ k)) := by
    rw [zpow_neg, zpow_natCast, baseRatio, mul_pow, inv_pow, ← pow_mul, mul_comm I.1.card n]
    ring
  rw [h]


omit [DecidableEq K] in
theorem exists_forall_baseRatio [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ}
    {e : ι k₀ ≃ Fin (N + 1)} (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (w : (∀ k, ι k) → Ω)
    (h : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      ∃ n : ℕ, baseRatio y k₀ I c ^ n * w c ∈ chartRingOver S y c) :
    ∃ n : ℕ, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      baseRatio y k₀ I c ^ n * w c ∈ chartRingOver S y c := by
  have hev : ∀ c : ∀ k, ι k, ∀ᶠ n : ℕ in Filter.atTop, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      baseRatio y k₀ I c ^ n * w c ∈ chartRingOver S y c := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n₀, hn₀⟩ := h c hc
      refine Filter.eventually_atTop.mpr ⟨n₀, fun n hn _ => ?_⟩
      have hsplit : baseRatio y k₀ I c ^ n * w c =
          baseRatio y k₀ I c ^ (n - n₀) * (baseRatio y k₀ I c ^ n₀ * w c) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
      rw [hsplit]
      exact mul_mem (pow_mem (baseRatio_mem y k₀ I c) _) hn₀
    · exact Filter.Eventually.of_forall fun _ h' => absurd h' hc
  exact (Filter.eventually_all.mpr hev).exists

theorem prod_zpow_mem_secOver (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ : K → ℤ) (hδ : ∀ k, 0 ≤ δ k) :
    ∏ k, y ⟨k, c k⟩ ^ δ k ∈ secOver S y δ := by
  rw [mem_secOver_iff_charts]
  intro c' _
  rw [← Finset.prod_mul_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (hδ k)
  have h : y ⟨k, c k⟩ ^ δ k * y ⟨k, c' k⟩ ^ (-δ k) = (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ m := by
    rw [hm, zpow_neg, zpow_natCast, zpow_natCast, div_pow, div_eq_mul_inv]
  rw [h]
  refine pow_mem ?_ m
  exact Algebra.subset_adjoin ⟨⟨k, c k⟩, rfl⟩

end Charts

theorem ChartSecMul.proof (h₁ : BundleOfDeg.Statement) : ChartSecMul.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y k₀ N e hM γ β I
  have hsub : ∀ δ : K → ℤ, ∃ Q : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm),
      (Q.sub I : Set Ω) = chartSecOver S y k₀ e δ I := by
    intro δ
    obtain ⟨Q, hQ⟩ := h₁ S K ι Ω y k₀ N e hM δ
    refine ⟨Q, Set.ext fun t => ?_⟩
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [Kleiman.SubSystem.gam, hQ]
  choose Q hQ using hsub
  have hmemP : ∀ δ t, t ∈ (Q δ).sub I ↔ t ∈ chartSecOver S y k₀ e δ I := fun δ t =>
    Set.ext_iff.mp (hQ δ) t

  have hmul : ∀ a b c : K → ℤ, a + b = c → (Q a).sub I * (Q b).sub I ≤ (Q c).sub I := by
    rintro a b _ rfl
    rw [Submodule.mul_le]
    intro g hg f hf
    rw [hmemP, mem_chartSecOver_iff] at hg hf ⊢
    obtain ⟨n₁, hn₁⟩ := hg
    obtain ⟨n₂, hn₂⟩ := hf
    refine ⟨n₁ + n₂, fun c hc => ?_⟩
    have hY : ∏ k, y ⟨k, c k⟩ ^ (-(a + b) k) =
        (∏ k, y ⟨k, c k⟩ ^ (-a k)) * ∏ k, y ⟨k, c k⟩ ^ (-b k) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, neg_add, zpow_add₀ (hc k)]
    have hsplit : baseRatio y k₀ I c ^ (n₁ + n₂) * (g * f * ∏ k, y ⟨k, c k⟩ ^ (-(a + b) k)) =
        (baseRatio y k₀ I c ^ n₁ * (g * ∏ k, y ⟨k, c k⟩ ^ (-a k))) *
          (baseRatio y k₀ I c ^ n₂ * (f * ∏ k, y ⟨k, c k⟩ ^ (-b k))) := by
      rw [hY, pow_add]
      ring
    rw [hsplit]
    exact mul_mem (hn₁ c hc) (hn₂ c hc)

  have hA : ∀ a : Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I, (a : Ω) ∈ (Q 0).sub I := by
    intro a
    have h1 : (1 : Ω) ∈ (Q 0).sub I := by
      refine (hmemP 0 1).mpr (mem_chartSecOver_of_mem S y k₀ e 0 I ?_)
      rw [mem_secOver_iff_charts]
      intro c _
      simp
    have := ((Q 0).sub I).smul_mem a h1
    rwa [Kleiman.chartRing_smul_def, mul_one] at this

  have hinv : ∀ δ : K → ℤ, (∀ k, 0 ≤ δ k) → 1 ≤ (Q δ).sub I * (Q (-δ)).sub I := by
    intro δ hδ
    obtain ⟨Q', hQ'⟩ := (Q δ).invertible I
    rw [← hQ']
    refine mul_le_mul_right (fun z hz => ?_) _
    rw [hmemP, mem_chartSecOver_iff]
    refine exists_forall_baseRatio y k₀ I _ fun c hc => ?_
    have hyc : (∏ k, y ⟨k, c k⟩ ^ δ k) ∈ (Q δ).sub I :=
      (hmemP δ _).mpr (mem_chartSecOver_of_mem S y k₀ e δ I (prod_zpow_mem_secOver y c δ hδ))
    have hw : z * ∏ k, y ⟨k, c k⟩ ^ δ k ∈ (1 : Submodule (Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) Ω) := by
      rw [← hQ', mul_comm z]
      exact Submodule.mul_mem_mul hyc hz
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp hw
    obtain ⟨n, hn⟩ := (mem_chartSecOver_iff y k₀ e 0 I _).mp ((hmemP 0 _).mp (hA a))
    refine ⟨n, ?_⟩
    have he : z * ∏ k, y ⟨k, c k⟩ ^ (-(-δ) k) = (a : Ω) * ∏ k, y ⟨k, c k⟩ ^ (-(0 : K → ℤ) k) := by
      simp only [Pi.neg_apply, neg_neg, Pi.zero_apply, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]
      exact ha.symm
    rw [he]
    exact hn c hc
  have hshift : ∀ ε δ : K → ℤ, (∀ k, 0 ≤ δ k) →
      (Q ε).sub I ≤ (Q (ε + δ)).sub I * (Q (-δ)).sub I := by
    intro ε δ hδ
    calc (Q ε).sub I = (Q ε).sub I * 1 := (mul_one _).symm
      _ ≤ (Q ε).sub I * ((Q δ).sub I * (Q (-δ)).sub I) := mul_le_mul_right (hinv δ hδ) _
      _ = (Q ε).sub I * (Q δ).sub I * (Q (-δ)).sub I := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_left (hmul _ _ _ rfl) _
  have hshift' : ∀ ε δ : K → ℤ, (∀ k, 0 ≤ δ k) →
      (Q ε).sub I ≤ (Q (ε - δ)).sub I * (Q δ).sub I := by
    intro ε δ hδ
    calc (Q ε).sub I = (Q ε).sub I * 1 := (mul_one _).symm
      _ ≤ (Q ε).sub I * ((Q δ).sub I * (Q (-δ)).sub I) := mul_le_mul_right (hinv δ hδ) _
      _ = (Q ε).sub I * (Q (-δ)).sub I * (Q δ).sub I := by rw [mul_comm ((Q δ).sub I), mul_assoc]
      _ ≤ _ := mul_le_mul_left (hmul _ _ _ (sub_eq_add_neg ε δ).symm) _

  have hbp : ∀ k, 0 ≤ (fun k => max (β k) 0) k := fun k => le_max_right _ _
  have hbm : ∀ k, 0 ≤ (fun k => max (-β k) 0) k := fun k => le_max_right _ _
  have hγ : γ + β + (fun k => max (-β k) 0) - (fun k => max (β k) 0) = γ := by
    funext k
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [max_def, max_def]
    split_ifs <;> omega
  have hβ : (fun k => max (β k) 0) + -(fun k => max (-β k) 0) = β := by
    funext k
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [max_def, max_def]
    split_ifs <;> omega
  have hle : (Q (γ + β)).sub I ≤ (Q γ).sub I * (Q β).sub I := by
    calc (Q (γ + β)).sub I
        ≤ (Q (γ + β + fun k => max (-β k) 0)).sub I * (Q (-fun k => max (-β k) 0)).sub I :=
          hshift _ _ hbm
      _ ≤ (Q (γ + β + (fun k => max (-β k) 0) - fun k => max (β k) 0)).sub I *
            (Q fun k => max (β k) 0).sub I * (Q (-fun k => max (-β k) 0)).sub I :=
          mul_le_mul_left (hshift' _ _ hbp) _
      _ = (Q γ).sub I * ((Q fun k => max (β k) 0).sub I * (Q (-fun k => max (-β k) 0)).sub I) := by
          rw [hγ, mul_assoc]
      _ ≤ (Q γ).sub I * (Q β).sub I := mul_le_mul_right (hmul _ _ _ hβ) _
  have heq : (Q γ).sub I * (Q β).sub I = (Q (γ + β)).sub I := le_antisymm (hmul _ _ _ rfl) hle
  rw [← hQ γ, ← hQ β, ← Submodule.mul_eq_span_mul_set, heq, hQ]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

