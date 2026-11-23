module

public import Mathlib
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPartnerLift
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianNormFibreDilation
section
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal NNReal

namespace GlobalTheory.FibreScaling

variable {P Q : ℕ}

theorem qf_continuous : Continuous (qf : Sp P Q → ℝ) := by
  unfold qf
  fun_prop

theorem qf_real_smul (r : ℝ) (x : Sp P Q) : qf (r • x) = r ^ 2 * qf x := by
  simp only [qf, Pi.smul_apply, Complex.real_smul, map_mul, Complex.normSq_ofReal, mul_sub,
    Finset.mul_sum, sq]

theorem finrank_sp : Module.finrank ℝ (Sp P Q) = 2 * (P + Q) := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]

theorem map_dx_smul {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (P + Q)) • (dx P Q).map (fun y => Real.sqrt t • y) = dx P Q := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hm : AEMeasurable (fun y : Sp P Q => Real.sqrt t • y) (volume : Measure (Sp P Q)) :=
    (continuous_const_smul _).aemeasurable
  have h := Measure.map_addHaar_smul (volume : Measure (Sp P Q)) hs
  rw [finrank_sp, pow_mul, Real.sq_sqrt ht.le, abs_of_pos (by positivity)] at h
  rw [dx, Measure.map_smul _ hm, h, smul_comm, smul_smul (ENNReal.ofReal _),
    ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one,
    one_smul]

theorem lintegral_inv_mul {t : ℝ} (ht : 0 < t) (g : ℝ → ℝ≥0∞) :
    ∫⁻ b, g (t⁻¹ * b) = ENNReal.ofReal t * ∫⁻ b, g b := by
  have h := (Homeomorph.mulLeft₀ t⁻¹ (inv_ne_zero ht.ne')).measurableEmbedding.lintegral_map
    (μ := volume) g
  rw [Homeomorph.coe_mulLeft₀, Real.map_volume_mul_left (inv_ne_zero ht.ne'), inv_inv,
    abs_of_pos ht, lintegral_smul_measure, smul_eq_mul] at h
  exact h.symm

theorem isDxDq_scale {fib : ℝ → Measure (Sp P Q)} (h : IsDxDq fib) {t : ℝ} (ht : 0 < t) :
    IsDxDq fun b => ENNReal.ofReal (t ^ (P + Q) / t) •
      (fib (t⁻¹ * b)).map (fun y => Real.sqrt t • y) := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hc : Continuous (fun y : Sp P Q => Real.sqrt t • y) := continuous_const_smul _
  have hm := hc.measurable
  have hpre : (fun y : Sp P Q => Real.sqrt t • y) ⁻¹' {x : Sp P Q | x ≠ 0} = {x | x ≠ 0} :=
    Set.ext fun x => by simp [hs]
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφ hsu hts => ?_⟩
  · have hS : MeasurableSet (qf ⁻¹' {id b} ∩ {x : Sp P Q | x ≠ 0})ᶜ :=
      ((qf_continuous.measurable (measurableSet_singleton _)).inter isOpen_ne.measurableSet).compl
    have h0 : ((fib (t⁻¹ * b)).map (fun y => Real.sqrt t • y))
        (qf ⁻¹' {id b} ∩ {x : Sp P Q | x ≠ 0})ᶜ = 0 := by
      rw [Measure.map_apply hm hS]
      convert h.1 (t⁻¹ * b) using 2
      rw [Set.preimage_compl, Set.preimage_inter, hpre]
      congr 2
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, id, qf_real_smul, Real.sq_sqrt ht.le]
      exact (eq_inv_mul_iff_mul_eq₀ ht.ne').symm
    rw [Measure.smul_apply, h0, smul_zero]
  · simp only [lintegral_smul_measure, lintegral_map hφ hm, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_inv_mul ht fun b => ∫⁻ y, φ (Real.sqrt t • y) ∂(fib b),
      ← h.2.1 (fun x => φ (Real.sqrt t • x)) (hφ.comp hm), ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ ht.ne']
    conv_lhs => rw [← map_dx_smul ht]
    rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
      Measure.restrict_map hm isOpen_ne.measurableSet, lintegral_map hφ hm, hpre]
  · have hs' : HasCompactSupport (φ ∘ fun y : Sp P Q => Real.sqrt t • y) :=
      hsu.comp_homeomorph (Homeomorph.smulOfNeZero (Real.sqrt t) hs)
    have ht' : tsupport (φ ∘ fun y : Sp P Q => Real.sqrt t • y) ⊆ {x | x ≠ 0} := by
      rw [← hpre]
      exact (tsupport_comp_subset_preimage φ hc).trans (Set.preimage_mono hts)
    obtain ⟨h1, h2⟩ := h.2.2 _ (hφ.comp hc) hs' ht'
    refine ⟨fun b _ => ?_, ?_⟩
    · exact ((integrable_map_measure hφ.aestronglyMeasurable hm.aemeasurable).2
        (h1 _ trivial)).smul_measure ENNReal.ofReal_ne_top
    · simp only [integral_smul_measure, integral_map hm.aemeasurable hφ.aestronglyMeasurable]
      exact (((continuousOn_univ.1 h2).comp (continuous_const_mul t⁻¹)).const_smul
        (ENNReal.ofReal (t ^ (P + Q) / t)).toReal).continuousOn

theorem lintegral_fibre_scale : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β t : ℝ), IsDxDq fib →
    β ≠ 0 → 0 < t → ∀ φ : Sp P Q → ℝ≥0∞, Measurable φ →
      ∫⁻ y, φ y ∂(fib (t * β)) =
        ENNReal.ofReal (t ^ (P + Q) / t) * ∫⁻ y, φ (Real.sqrt t • y) ∂(fib β) := by
  intro P Q fib β t h hβ ht φ hφ
  have hO : (qf : Sp P Q → ℝ) ⁻¹' {t * β} ⊆ {x | x ≠ 0} := by
    rintro x hx rfl
    exact mul_ne_zero ht.ne' hβ (by simpa [qf] using hx.symm)
  have e := GlobalTheory.IsFibreFamily_eq_at (dx P Q) qf {x | x ≠ 0} {x | x ≠ 0} {x | x ≠ 0} Set.univ
    Set.univ fib _ (t * β) qf_continuous.measurable isOpen_ne subset_rfl subset_rfl hO isOpen_univ
    isOpen_univ trivial trivial h (isDxDq_scale h ht)
  rw [e, lintegral_smul_measure, smul_eq_mul, inv_mul_cancel_left₀ ht.ne',
    lintegral_map hφ (continuous_const_smul _).measurable]

end GlobalTheory.FibreScaling
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPowLeCardFlagQuotient
section
open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Classical

namespace GlobalTheory.LoopC.AdmissibleOrder

open GlobalTheory.LoopC.Partner

theorem one_mem_of_local {E : Type} [Field E] [NumberField E] (g : 𝓞 E) (J : Ideal (𝓞 E)) (hg : g ∈ J)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), g ∈ P.asIdeal → ∃ s ∈ J, s ∉ P.asIdeal) : (1 : 𝓞 E) ∈ J := by
  by_contra h1
  have hJ : J ≠ ⊤ := fun hJ => h1 (hJ ▸ Submodule.mem_top)
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJ
  have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField E)
  obtain ⟨s, hsJ, hsM⟩ := h ⟨M, hM.isPrime, hM0⟩ (hJM hg)
  exact hsM (hJM hsJ)

theorem pow_card_le {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] [Finite Q] (I : Ideal R) {n : ℕ}
    (q : Fin n → Q) (h : ∀ c : Fin n → R, ∑ b, c b • q b = 0 → ∀ b, c b ∈ I) :
    Nat.card (R ⧸ I) ^ n ≤ Nat.card Q := by
  have key : ∀ c c' : Fin n → R, ∑ b, c b • q b = ∑ b, c' b • q b →
      ∀ b, Ideal.Quotient.mk I (c b) = Ideal.Quotient.mk I (c' b) := by
    intro c c' hcc b
    rw [Ideal.Quotient.eq]
    have hz : ∑ b, (c - c') b • q b = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hcc, sub_self]
    simpa using h (c - c') hz b
  let f : Q → (Fin n → R ⧸ I) := fun x =>
    if hx : ∃ c : Fin n → R, ∑ b, c b • q b = x then fun b => Ideal.Quotient.mk I (hx.choose b) else 0
  have hf : Function.Surjective f := by
    intro t
    choose c hc using fun b => Ideal.Quotient.mk_surjective (I := I) (t b)
    have hx : ∃ c' : Fin n → R, ∑ b, c' b • q b = ∑ b, c b • q b := ⟨c, rfl⟩
    refine ⟨∑ b, c b • q b, ?_⟩
    simp only [f, dif_pos hx]
    funext b
    rw [key _ c hx.choose_spec b, hc]
  have hle := Nat.card_le_card_of_surjective f hf
  simpa [Nat.card_fun] using hle

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem frame_indep (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) (b : Fin (r + 1) → E)
    (hb : ∑ j, b j • F'.fvec j = 0) : b = 0 := by
  have hlast : T' * b (Fin.last r) = 0 := by
    have h0 := hT_fvec_sum F' b (Fin.last r)
    rw [hb, map_zero] at h0
    simpa using h0.symm
  have hZ : (Zhat F F').mulVec b = Pi.single (Fin.last r) (T * (0 : Fin (r + 1) → E) (Fin.last r)) := by
    funext i
    have h0 : S.hT (F.fvec i) (∑ j, b j • F'.fvec j) = 0 := by rw [hb, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h0
    simp only [map_smul, smul_eq_mul] at h0
    simp only [Pi.zero_apply, mul_zero, Pi.single_zero]
    rw [← h0]
    simp only [Matrix.mulVec, dotProduct, Zhat, brS]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h2 : (Zhat F F').conjTranspose.mulVec (0 : Fin (r + 1) → E) = Pi.single (Fin.last r) (T' * b (Fin.last r)) := by
    rw [hlast, Matrix.mulVec_zero, Pi.single_zero]
  have hd1 : Dl F F' (r + 1) = (Zhat F F').det := by
    unfold Dl leadMinorE
    rw [dif_pos le_rfl]
    congr 1
  have hd0 : Dl F F' r = ((Zhat F F').submatrix Fin.castSucc Fin.castSucc).det := by
    unfold Dl leadMinorE
    rw [dif_pos (Nat.le_succ r)]
    congr 1
  have hG' := hG
  unfold Gflag at hG'
  rw [hd1, hd0] at hG'
  exact (pair_eq_zero (Zhat F F') 0 b T T' hG' hZ h2).2

variable {Λ : Submodule (𝓞 E) S.V}

theorem exists_div {g : ℕ} {x : S.V} (hx : x ∈ Λ) (h : ModG S Λ g x) : ∃ w ∈ Λ, (g : 𝓞 E) • w = x := by
  set J : Ideal (𝓞 E) := (Ideal.span {(g : 𝓞 E)} • Λ).colon {x} with hJ
  have hmem : ∀ s : 𝓞 E, s ∈ J ↔ s • x ∈ Ideal.span {(g : 𝓞 E)} • Λ := fun s =>
    Submodule.mem_colon_singleton
  have h1 : (1 : 𝓞 E) ∈ J := by
    refine one_mem_of_local (g : 𝓞 E) J
      ((hmem _).2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx)) ?_
    intro P hP
    obtain ⟨s, hs, hsx⟩ := h P hP
    exact ⟨s, (hmem s).2 hsx, hs⟩
  have hx1 := (hmem 1).1 h1
  rw [one_smul, Submodule.ideal_span_singleton_smul] at hx1
  obtain ⟨w, hw, hwx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx1
  exact ⟨w, hw, hwx⟩

theorem coeff_mem {g : ℕ} (F : LFlag S r T) (hL : IsLift Λ F) (hC : IsFixedConv Λ g F)
    (hind : ∀ b : Fin (r + 1) → E, ∑ j, b j • frame F j = 0 → b = 0) (c : Fin (r + 1) → 𝓞 E) {q : S.V}
    (hq : q ∈ XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt}) (h : ∑ j, c j • frame F j = (g : 𝓞 E) • q) (b : Fin (r + 1)) :
    c b ∈ Ideal.span {(g : 𝓞 E)} := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hq
  obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hy
  set J : Ideal (𝓞 E) := (Ideal.span {(g : 𝓞 E)}).colon {c b} with hJ
  have hmem : ∀ s : 𝓞 E, s ∈ J ↔ s • c b ∈ Ideal.span {(g : 𝓞 E)} := fun s =>
    Submodule.mem_colon_singleton
  have key : ∀ s : 𝓞 E, s • x ∈ Submodule.span (𝓞 E) (Set.range F.fl.e) → s ∈ J := by
    intro s hs
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hs
    let d' : Fin (r + 1) → 𝓞 E := Fin.snoc (α := fun _ => 𝓞 E) d (s * o)
    have e1 : ∑ j, d' j • frame F j = s • x + (s * o) • F.zt := by
      rw [Fin.sum_univ_castSucc]
      simp only [d', frame, FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last, hd, hL.2]
    have hsum : ∑ j, ((s * c j - (g : 𝓞 E) * d' j : 𝓞 E) : E) • frame F j = 0 := by
      simp only [smul_coe]
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
      rw [← Finset.smul_sum, ← Finset.smul_sum, h, e1]
      module
    have hb0 : ((s * c b - (g : 𝓞 E) * d' b : 𝓞 E) : E) = 0 := congrFun (hind _ hsum) b
    have hb1 : s * c b = (g : 𝓞 E) * d' b := by
      rw [← sub_eq_zero]
      exact_mod_cast hb0
    rw [hmem, smul_eq_mul, hb1]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h1 : (1 : 𝓞 E) ∈ J := by
    refine one_mem_of_local (g : 𝓞 E) J ?_ ?_
    · rw [hmem, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro P hP
      obtain ⟨cc, -, hc1, hloc⟩ := hC.1 P
      have hx' : x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F)) := by
        show ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ XLam Λ F
        exact ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
      rw [hloc] at hx'
      obtain ⟨s, hs, hsx⟩ := hx'
      refine ⟨s, key s ?_, hs⟩
      have hfun : (fun a => cc a • F.fl.e a) = F.fl.e := funext fun a => by rw [hc1 hP a, one_smul]
      rwa [hfun] at hsx
  simpa using (hmem 1).1 h1

theorem NE_pow_le_card_BQ : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (T T' : E) (F : LFlag S r T) (F' : LFlag S r T'), g ≠ 0 → IsLift Λ F → IsLift Λ F' → (∀ b, frame F b ∈ Λ) → (∀ b, frame F' b ∈ Λ) → IsFixedConv Λ g F' → IsAdmissible Λ g F F' → Gval F F' ≠ 0 → Finite (BQ Λ F F') → NE (E := E) g ^ (r + 1) ≤ (Nat.card (BQ Λ F F') : ℝ) := by
  intro E _ _ _ S r Λ g T T' F F' hg hL hL' hF hF' hC' hAdm hGv hfin
  obtain ⟨ξ, -, -, hξ⟩ := hAdm
  have hfX : ∀ b, frameAct (frame F) ξ b ∈ Xplus F :=
    fun b => (mem_Xplus_iff F.fl _).2 ⟨fun a => ((ξ a b : 𝓞 E) : E), rfl⟩
  have hf'X : ∀ b, frame F' b ∈ Xplus F' := fun b =>
    (mem_Xplus_iff F'.fl _).2 ⟨Pi.single b 1, by simp [Pi.single_apply, ite_smul]⟩
  have hxΛ : ∀ b, frame F' b - frameAct (frame F) ξ b ∈ Λ := by
    intro b
    refine Λ.sub_mem (hF' b) (Λ.sum_mem fun a _ => ?_)
    rw [smul_coe]
    exact Λ.smul_mem _ (hF a)
  choose w hwΛ hw using fun b => exists_div (hxΛ b) (hξ b)
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  have hwB : ∀ b, w b ∈ BLat Λ F F' := by
    intro b
    refine Submodule.mem_inf.2 ⟨hwΛ b, ?_⟩
    show w b ∈ UUE Λ F F'
    rw [UUE_eq F F' hL hL' hF hF']
    have hwb : w b = (g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b) := by
      rw [← hw b, ← smul_coe, smul_smul]
      have hc : (((g : 𝓞 E) : E)) = (g : E) := by simp
      rw [hc, inv_mul_cancel₀ hgE, one_smul]
    rw [hwb]
    exact Submodule.smul_mem _ _
      (Submodule.sub_mem _ (Submodule.mem_sup_right (hf'X b)) (Submodule.mem_sup_left (hfX b)))
  have _hfin := hfin
  let q : Fin (r + 1) → BQ Λ F F' := fun b => Submodule.Quotient.mk ⟨w b, hwB b⟩
  have key : ∀ c : Fin (r + 1) → 𝓞 E, ∑ b, c b • q b = 0 → ∀ b, c b ∈ Ideal.span {(g : 𝓞 E)} := by
    intro c hc
    have hc' : ∑ b, c b • w b ∈ UU Λ F F' := by
      have h0 : (Submodule.mkQ ((UU Λ F F').comap (BLat Λ F F').subtype))
          (∑ b, c b • (⟨w b, hwB b⟩ : BLat Λ F F')) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simpa only [map_smul, Submodule.mkQ_apply, q] using hc
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h0
      simpa using h0
    rw [UU_eq] at hc'
    obtain ⟨u, hu, u', hu', huu⟩ := Submodule.mem_sup.1 hc'
    have hgsum : ∑ b, c b • (frame F' b - frameAct (frame F) ξ b) = (g : 𝓞 E) • u + (g : 𝓞 E) • u' := by
      rw [← smul_add, huu, Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← hw b, smul_comm]
    simp only [smul_sub, Finset.sum_sub_distrib] at hgsum
    have hA : ∑ b, c b • frame F' b - (g : 𝓞 E) • u' =
        ∑ b, c b • frameAct (frame F) ξ b + (g : 𝓞 E) • u := by
      calc ∑ b, c b • frame F' b - (g : 𝓞 E) • u'
          = (∑ b, c b • frame F' b - ∑ b, c b • frameAct (frame F) ξ b) +
              ∑ b, c b • frameAct (frame F) ξ b - (g : 𝓞 E) • u' := by abel
        _ = ((g : 𝓞 E) • u + (g : 𝓞 E) • u') + ∑ b, c b • frameAct (frame F) ξ b - (g : 𝓞 E) • u' := by
              rw [hgsum]
        _ = ∑ b, c b • frameAct (frame F) ξ b + (g : 𝓞 E) • u := by abel
    have huX : u ∈ Xplus F := (Submodule.mem_inf.1 (half_le F hL hu)).2
    have hu'X : u' ∈ Xplus F' := (Submodule.mem_inf.1 (half_le F' hL' hu')).2
    have hmF' : ∑ b, c b • frame F' b - (g : 𝓞 E) • u' ∈ Xplus F' :=
      Submodule.sub_mem _ (Submodule.sum_mem _ fun b _ => Submodule.smul_of_tower_mem _ _ (hf'X b))
        (Submodule.smul_of_tower_mem _ _ hu'X)
    have hmF : ∑ b, c b • frameAct (frame F) ξ b + (g : 𝓞 E) • u ∈ Xplus F :=
      Submodule.add_mem _ (Submodule.sum_mem _ fun b _ => Submodule.smul_of_tower_mem _ _ (hfX b))
        (Submodule.smul_of_tower_mem _ _ huX)
    have hm : ∑ b, c b • frame F' b - (g : 𝓞 E) • u' ∈ F.fl.Xplus ⊓ F'.fl.Xplus :=
      Submodule.mem_inf.2 ⟨hA ▸ hmF, hmF'⟩
    rw [Xplus_inf F.fl F'.fl hGv] at hm
    have hfin2 : ∑ b, c b • frame F' b = (g : 𝓞 E) • u' := sub_eq_zero.1 ((Submodule.mem_bot E).1 hm)
    exact coeff_mem F' hL' hC' (fun b hb => frame_indep F.fl F'.fl hGv b hb) c hu' hfin2
  have hcard := pow_card_le (Ideal.span {(g : 𝓞 E)}) q key
  have hN : ((Nat.card (𝓞 E ⧸ Ideal.span {(g : 𝓞 E)}) : ℕ) : ℝ) = NE (E := E) g := by
    have hn := Ideal.absNorm_span_singleton ((g : 𝓞 E))
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
    rw [hn, NE]
    have hg' : ((g : 𝓞 E)) = algebraMap ℤ (𝓞 E) (g : ℤ) := by simp
    rw [hg', Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp
  rw [← hN]
  exact_mod_cast hcard

end GlobalTheory.LoopC.AdmissibleOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PolarSqCompare
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

namespace GlobalTheory.PolarCompare

theorem abs_qf_le_sum_sq {P Q : ℕ} (z : Sp P Q) : |qf z| ≤ ∑ i, ‖z i‖ ^ 2 := by
  have h1 : 0 ≤ ∑ i : Fin P, ‖z (Sum.inl i)‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h2 : 0 ≤ ∑ j : Fin Q, ‖z (Sum.inr j)‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  rw [Fintype.sum_sum_type]
  simp only [qf, Complex.normSq_eq_norm_sq]
  rw [abs_le]
  constructor <;> linarith

theorem sq_compare_left {T S N r s : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hN : 0 ≤ N)
    (hr0 : 0 < r) (hr1 : r < 1 / 2) (hr : 3 * r < 1 - s) (h1 : N ≤ T + S)
    (h : T ^ 2 + 2 * S < s * r ^ 2) : N ^ 2 + 2 * S < r ^ 2 := by

  have hr2 : 0 < r ^ 2 := by positivity
  have hs : s < 1 := by linarith
  have hsr : s * r ^ 2 < r ^ 2 := by nlinarith
  have hS2 : 2 * S < r ^ 2 := by nlinarith
  have hT2 : T ^ 2 < r ^ 2 := by nlinarith
  have hTr : T < r := by nlinarith
  have hN2 : N * N ≤ (T + S) * (T + S) := mul_self_le_mul_self hN h1
  have a1 : T * S ≤ r * S := mul_le_mul_of_nonneg_right hTr.le hS
  have a2 : r * (2 * S) ≤ r * r ^ 2 := mul_le_mul_of_nonneg_left hS2.le hr0.le
  have a3 : (2 * S) * (2 * S) ≤ r ^ 2 * r ^ 2 := mul_self_le_mul_self (by linarith) hS2.le
  have a4 : r * r ^ 2 * r ≤ r * r ^ 2 * (1 / 2) :=
    mul_le_mul_of_nonneg_left hr1.le (by positivity)
  have a5 : 3 * r * r ^ 2 < (1 - s) * r ^ 2 := mul_lt_mul_of_pos_right hr hr2
  nlinarith [mul_pos hr0 hr2]

theorem sq_compare_right {T S N E r s : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hN : 0 ≤ N)
    (hr0 : 0 < r) (hr1 : r < 1 / 2) (hr : 11 * r < s - 1) (h1 : E ≤ N + S) (h2 : T ≤ 2 * E)
    (h3 : T ≤ 2 → T - T ^ 3 / 16 ≤ E)
    (h : N ^ 2 + 2 * S < r ^ 2) : T ^ 2 + 2 * S < s * r ^ 2 := by

  have hr2 : 0 < r ^ 2 := by positivity
  have hS2 : 2 * S < r ^ 2 := by nlinarith
  have hNr : N < r := by nlinarith
  have hrr : r ^ 2 < r / 2 := by nlinarith [mul_pos hr0 (sub_pos.mpr hr1)]
  have hT3r : T ≤ 3 * r := by linarith
  have hTE : T - T ^ 3 / 16 ≤ E := h3 (by linarith)
  have hc1 : T * T ≤ 3 * r * (3 * r) := mul_self_le_mul_self hT hT3r
  have hc2 : T * T * T ≤ 3 * r * (3 * r) * (3 * r) := mul_le_mul hc1 hT3r hT (by positivity)
  have hr3 : r ^ 2 * r ≤ r ^ 2 * (1 / 2) := mul_le_mul_of_nonneg_left hr1.le (sq_nonneg r)
  have hb0 : 0 ≤ S + T ^ 3 / 16 := by positivity
  have hb2 : S + T ^ 3 / 16 ≤ 2 * r ^ 2 := by nlinarith
  have hTNb : T ≤ N + (S + T ^ 3 / 16) := by linarith
  have hT2 : T * T ≤ (N + (S + T ^ 3 / 16)) * (N + (S + T ^ 3 / 16)) :=
    mul_self_le_mul_self hT hTNb
  have a1 : N * (S + T ^ 3 / 16) ≤ r * (S + T ^ 3 / 16) :=
    mul_le_mul_of_nonneg_right hNr.le hb0
  have a2 : r * (S + T ^ 3 / 16) ≤ r * (2 * r ^ 2) := mul_le_mul_of_nonneg_left hb2 hr0.le
  have a3 : (S + T ^ 3 / 16) * (S + T ^ 3 / 16) ≤ (2 * r ^ 2) * (2 * r ^ 2) :=
    mul_self_le_mul_self hb0 hb2
  have a4 : r * r ^ 2 * r ≤ r * r ^ 2 * (1 / 2) :=
    mul_le_mul_of_nonneg_left hr1.le (by positivity)
  have a5 : 11 * r * r ^ 2 < (s - 1) * r ^ 2 := mul_lt_mul_of_pos_right hr hr2
  nlinarith [mul_pos hr0 hr2]

theorem polar_sq_compare : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u : ℝ × Sp P' Q', u.1 ∈ Set.Ioo (-Real.pi) Real.pi → (tanSq u < (t⁻¹ * r) ^ 2 → ptSq e (polarPt e u) < r ^ 2) ∧ (ptSq e (polarPt e u) < r ^ 2 → tanSq u < (t * r) ^ 2) := by
  intro P Q P' Q' e t ht
  have ht0 : 0 < t := by linarith
  have hA : 0 < 1 - t⁻¹ ^ 2 := by
    have h1 : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
    have h2 : 0 < t⁻¹ := inv_pos.mpr ht0
    nlinarith
  have hB : 0 < t ^ 2 - 1 := by nlinarith
  have hc : 0 < min (1 / 2 : ℝ) (min ((1 - t⁻¹ ^ 2) / 3) ((t ^ 2 - 1) / 11)) :=
    lt_min (by norm_num) (lt_min (div_pos hA (by norm_num)) (div_pos hB (by norm_num)))
  filter_upwards [inter_mem_nhdsWithin (Set.Ioi (0 : ℝ)) (Iio_mem_nhds hc)] with r hr
  obtain ⟨hr0, hrc⟩ := hr
  simp only [Set.mem_Ioi, Set.mem_Iio] at hr0 hrc
  have hr1 : r < 1 / 2 := lt_of_lt_of_le hrc (min_le_left _ _)
  have hr2 : 3 * r < 1 - t⁻¹ ^ 2 := by
    have := lt_of_lt_of_le hrc ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hr3 : 11 * r < t ^ 2 - 1 := by
    have := lt_of_lt_of_le hrc ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  rintro ⟨θ, z⟩ hu
  simp only [Set.mem_Ioo] at hu
  have hθ : |θ| ≤ Real.pi := abs_le.mpr ⟨hu.1.le, hu.2.le⟩

  have hq : |sg (e none) * qf z| ≤ ∑ i, ‖z i‖ ^ 2 := by
    rw [abs_mul]
    rcases sg_eq (e none) with h | h <;> rw [h] <;> simpa using abs_qf_le_sum_sq z
  have hρ1 := (abs_sqrt_sub_one_le (sg (e none) * qf z)).trans hq
  have hw1 : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hpt : ptSq e (polarPt e (θ, z)) =
      ‖(Real.sqrt (1 - sg (e none) * qf z) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 +
        2 * ∑ i, ‖z i‖ ^ 2 := by
    simp only [ptSq, polarPt_none, polarPt_some]
  have htan : tanSq (θ, z) = |θ| ^ 2 + 2 * ∑ i, ‖z i‖ ^ 2 := by
    simp only [tanSq, sq_abs]
  obtain ⟨hb1, hb2, hb3⟩ := exp_bounds θ hθ
  rw [hpt, htan]
  generalize Real.sqrt (1 - sg (e none) * qf z) = ρ at hρ1 ⊢
  generalize Complex.exp ((θ : ℂ) * Complex.I) = w at hw1 hb1 hb2 hb3 ⊢
  generalize ∑ i, ‖z i‖ ^ 2 = S at hρ1 ⊢
  have hS0 : 0 ≤ S := (abs_nonneg _).trans hρ1
  have hdiff : ‖(ρ : ℂ) * w - w‖ = |ρ - 1| := by
    have : (ρ : ℂ) * w - w = ((ρ - 1 : ℝ) : ℂ) * w := by push_cast; ring
    rw [this, norm_mul, hw1, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hNE : ‖(ρ : ℂ) * w - 1‖ ≤ |θ| + S := by
    have := norm_sub_le_norm_sub_add_norm_sub ((ρ : ℂ) * w) w 1
    rw [hdiff] at this
    linarith
  have hEN : ‖w - 1‖ ≤ ‖(ρ : ℂ) * w - 1‖ + S := by
    have := norm_sub_le_norm_sub_add_norm_sub w ((ρ : ℂ) * w) 1
    rw [norm_sub_rev w ((ρ : ℂ) * w), hdiff] at this
    linarith
  constructor
  · intro h
    rw [mul_pow] at h
    exact sq_compare_left (abs_nonneg θ) hS0 (norm_nonneg _) hr0 hr1 hr2 hNE h
  · intro h
    rw [mul_pow]
    exact sq_compare_right (abs_nonneg θ) hS0 (norm_nonneg _) hr0 hr1 hr3 hEN hb2 hb3 h

end GlobalTheory.PolarCompare
end

